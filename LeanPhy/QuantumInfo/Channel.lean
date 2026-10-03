import LeanPhy.Quantum.Density
import LeanPhy.Quantum.Composite
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-!
# Quantum channels: Kraus operators and complete positivity

A quantum channel is a completely positive trace-preserving map on density
matrices.  In finite dimension it always has a Kraus representation
`rho ↦ sum_k K_k rho K_k†`, and the physics lives in two algebraic facts:

- trace preservation `sum_k K_k† K_k = 1` (probability is conserved);
- unitality `sum_k K_k K_k† = 1` (the maximally mixed state is preserved);

together with the positivity of the map on every input.  This file proves the
trace law and the operator-sum structure exactly over complex matrices, checks
that the single-qubit amplitude-damping channel is trace preserving, gives the
composition of two channels as the product of their Kraus data, and proves the
finite ancillary-system version of complete positivity for every Kraus family.
Infinite-dimensional operator-algebraic complete positivity remains out of
scope. -/

namespace LeanPhy.QuantumInfo

universe u v

open LeanPhy.Quantum
open scoped BigOperators Matrix
open scoped ComplexOrder

/-- A Kraus family `K : Fin m → Operator n` acting on `rho` as
`sum_k K_k rho K_k†`.  This is the operator-sum (Kraus) form of a channel. -/
noncomputable def applyKraus {n : Nat} {ι : Type} [Fintype ι] (K : ι → Operator n) (rho : State n) :
    State n :=
  ∑ k, K k * rho * Matrix.conjTranspose (K k)

/-- **Trace preservation.**  If the Kraus operators satisfy `sum_k K_k† K_k = 1`,
the channel preserves the trace: probability is conserved. -/
theorem kraus_trace {n : Nat} {ι : Type} [Fintype ι] (K : ι → Operator n) (rho : State n)
    (htp : (∑ k, Matrix.conjTranspose (K k) * K k) = 1) :
    Matrix.trace (applyKraus K rho) = Matrix.trace rho := by
  unfold applyKraus
  rw [Matrix.trace_sum]
  trans ∑ k, Matrix.trace (Matrix.conjTranspose (K k) * K k * rho)
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.trace_mul_cycle]
  rw [← Matrix.trace_sum]
  have hsum : (∑ k, Matrix.conjTranspose (K k) * K k * rho)
      = (∑ k, Matrix.conjTranspose (K k) * K k) * rho := by
    rw [Finset.sum_mul]
  rw [hsum, htp, Matrix.one_mul]

/-- **Unitality.**  If `sum_k K_k K_k† = 1` then the channel fixes the identity,
i.e. it preserves the maximally mixed state. -/
theorem kraus_unital {n : Nat} {ι : Type} [Fintype ι] (K : ι → Operator n)
    (hu : (∑ k, K k * Matrix.conjTranspose (K k)) = 1) :
    applyKraus K (1 : State n) = 1 := by
  simp only [applyKraus, Matrix.mul_one]
  exact hu

/-- The channel is additive in the state (it is a linear map). -/
theorem applyKraus_add {n : Nat} {ι : Type} [Fintype ι] (K : ι → Operator n) (rho sig : State n) :
    applyKraus K (rho + sig) = applyKraus K rho + applyKraus K sig := by
  simp only [applyKraus, mul_add, add_mul, Finset.sum_add_distrib]

/-- The channel is homogeneous. -/
theorem applyKraus_smul {n : Nat} {ι : Type} [Fintype ι] (K : ι → Operator n) (c : ℂ) (rho : State n) :
    applyKraus K (c • rho) = c • applyKraus K rho := by
  unfold applyKraus
  simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- A single Kraus conjugation preserves positive semidefiniteness. -/
theorem kraus_term_posSemidef {n : Nat} (K : Operator n) (rho : State n)
    (hrho : rho.PosSemidef) :
    (K * rho * Matrix.conjTranspose K).PosSemidef := by
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hrho K

/-- A finite sum of positive semidefinite matrices is positive semidefinite.
The index type of the matrix is arbitrary and finite, so this lemma can be
shared by channels and their ancillary extensions. -/
theorem matrix_sum_posSemidef {α : Type u} {ι : Type v} [Fintype α] [Fintype ι]
    (A : ι → Matrix α α ℂ) (hA : ∀ k, (A k).PosSemidef) :
    (∑ k, A k).PosSemidef := by
  classical
  refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
  · simpa using (Matrix.PosSemidef.zero : (0 : Matrix α α ℂ).PosSemidef)
  · intro k s hk ih
    rw [Finset.sum_insert hk]
    exact (hA k).add ih

/-- A finite sum of positive semidefinite Kraus terms is positive semidefinite. -/
theorem kraus_sum_posSemidef {n : Nat} {ι : Type} [Fintype ι]
    (A : ι → State n) (hA : ∀ k, (A k).PosSemidef) :
    (∑ k, A k).PosSemidef :=
  matrix_sum_posSemidef A hA

/-- A Kraus operator-sum preserves positive semidefiniteness of the input. -/
theorem applyKraus_posSemidef {n : Nat} {ι : Type} [Fintype ι]
    (K : ι → Operator n) (rho : State n) (hrho : rho.PosSemidef) :
    (applyKraus K rho).PosSemidef := by
  unfold applyKraus
  apply matrix_sum_posSemidef
  intro k
  exact kraus_term_posSemidef (K k) rho hrho

/-! ## Finite complete positivity -/

/-
The usual definition of complete positivity asks that `id_m ⊗ Φ` preserve
positive operators for every ancillary system.  We state exactly that finite
version for a Kraus family.  The index is kept as `Fin m × Fin n`, matching the
tensor-product representation already used by `tensorOp`; no identification
with a numeral product is hidden in the definition.
-/

/-- The operator-sum extension of a Kraus family by an `m`-dimensional
ancilla. -/
noncomputable def applyKrausWithAncilla {m n : Nat} {ι : Type} [Fintype ι]
    (K : ι → Operator n)
    (rho : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  ∑ k, tensorOp (1 : Operator m) (K k) * rho *
    Matrix.conjTranspose (tensorOp (1 : Operator m) (K k))

theorem applyKrausWithAncilla_posSemidef {m n : Nat} {ι : Type} [Fintype ι]
    (K : ι → Operator n)
    (rho : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hrho : rho.PosSemidef) :
  (applyKrausWithAncilla K rho).PosSemidef := by
  unfold applyKrausWithAncilla
  apply matrix_sum_posSemidef
  intro k
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hrho
    (tensorOp (1 : Operator m) (K k))

/-- Finite complete positivity of a Kraus family: every finite ancillary
extension preserves positive semidefiniteness. -/
def CompletelyPositiveKraus {n : Nat} {ι : Type} [Fintype ι]
    (K : ι → Operator n) : Prop :=
  ∀ (m : Nat) (rho : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
    rho.PosSemidef → (applyKrausWithAncilla K rho).PosSemidef

theorem applyKraus_completelyPositive {n : Nat} {ι : Type} [Fintype ι]
    (K : ι → Operator n) : CompletelyPositiveKraus K := by
  intro m rho hrho
  exact applyKrausWithAncilla_posSemidef K rho hrho

/-- A trace-preserving Kraus family maps a density matrix to a density matrix.

This is the finite-dimensional validity theorem used by the channel modules:
Hermiticity and positivity come from the operator-sum form, while normalization
comes from the Kraus completeness relation. -/
theorem applyKraus_isDensity {n : Nat} {ι : Type} [Fintype ι]
    (K : ι → Operator n) (rho : State n)
    (hrho : IsDensity rho)
    (htp : (∑ k, Matrix.conjTranspose (K k) * K k) = 1) :
    IsDensity (applyKraus K rho) := by
  have hpos : (applyKraus K rho).PosSemidef :=
    applyKraus_posSemidef K rho hrho.2.1
  refine ⟨hpos.isHermitian, hpos, ?_⟩
  exact (kraus_trace K rho htp).trans hrho.2.2

/-! ## Bundled finite channels

The preceding theorems are useful for individual calculations.  Research code
also needs channels that can be composed without manually carrying the same
invariants through every call.  `FiniteChannel` is the small finite-dimensional
bundle: positivity and trace preservation are fields, so composition cannot
forget them.  Kraus-built channels additionally have the explicit
`CompletelyPositiveKraus` theorem above; a future bundled CPTP map can attach
that property to an arbitrary finite linear map.
-/

structure FiniteChannel (n : Nat) where
  toFun : State n → State n
  map_add : ∀ rho sig, toFun (rho + sig) = toFun rho + toFun sig
  map_smul : ∀ (c : ℂ) rho, toFun (c • rho) = c • toFun rho
  map_pos : ∀ rho, rho.PosSemidef → (toFun rho).PosSemidef
  trace_preserving : ∀ rho, Matrix.trace (toFun rho) = Matrix.trace rho

instance : CoeFun (FiniteChannel n) (fun _ => State n → State n) := ⟨FiniteChannel.toFun⟩

/-- The identity finite channel. -/
def identityChannel {n : Nat} : FiniteChannel n where
  toFun := id
  map_add := by intro rho sig; rfl
  map_smul := by intro c rho; rfl
  map_pos := by intro rho h; simpa using h
  trace_preserving := by intro rho; rfl

/-- Build a bundled channel from a Kraus family and its completeness proof. -/
noncomputable def fromKraus {n : Nat} {ι : Type} [Fintype ι]
    (K : ι → Operator n)
    (htp : (∑ k, Matrix.conjTranspose (K k) * K k) = 1) : FiniteChannel n where
  toFun := applyKraus K
  map_add := fun rho sig => applyKraus_add K rho sig
  map_smul := fun c rho => applyKraus_smul K c rho
  map_pos := fun rho hrho => applyKraus_posSemidef K rho hrho
  trace_preserving := fun rho => kraus_trace K rho htp

theorem fromKraus_apply {n : Nat} {ι : Type} [Fintype ι]
    (K : ι → Operator n) (htp : (∑ k, Matrix.conjTranspose (K k) * K k) = 1)
    (rho : State n) : fromKraus K htp rho = applyKraus K rho := rfl

/-- Composition: `compose after before` applies `before` first. -/
def compose {n : Nat} (after before : FiniteChannel n) : FiniteChannel n where
  toFun := fun rho => after (before rho)
  map_add := by
    intro rho sig
    rw [before.map_add, after.map_add]
  map_smul := by
    intro c rho
    rw [before.map_smul, after.map_smul]
  map_pos := fun rho hrho => after.map_pos _ (before.map_pos rho hrho)
  trace_preserving := fun rho => (after.trace_preserving _).trans (before.trace_preserving rho)

theorem compose_apply {n : Nat} (after before : FiniteChannel n) (rho : State n) :
    compose after before rho = after (before rho) := rfl

theorem compose_isDensity {n : Nat} (after before : FiniteChannel n)
    (rho : State n) (hrho : IsDensity rho) :
    IsDensity (compose after before rho) := by
  have hpos : (compose after before rho).PosSemidef :=
    after.map_pos _ (before.map_pos rho hrho.2.1)
  refine ⟨hpos.isHermitian, hpos, ?_⟩
  exact (compose after before).trace_preserving rho |>.trans hrho.2.2

theorem compose_identity_left {n : Nat} (C : FiniteChannel n) (rho : State n) :
    compose identityChannel C rho = C rho := by
  rfl

theorem compose_identity_right {n : Nat} (C : FiniteChannel n) (rho : State n) :
    compose C identityChannel rho = C rho := by
  rfl

/-! ## The qubit depolarising channel -/

open LeanPhy.Quantum in
/-- The single-qubit depolarising channel:
`rho ↦ (1 - p) rho + p (X rho X + Y rho Y + Z rho Z) / 3`, the Kraus form whose
Kraus operators are the Pauli matrices weighted by `sqrt (p/3)`.  Stated on the
observable algebra, it is `rho ↦ (1 - 4p/3) rho + (4p/3) (I/2)`. -/
noncomputable def depolarizing (p : ℂ) (rho : State 2) : State 2 :=
  (1 - 4 * p / 3) • rho + (4 * p / 3) • ((1/2 : ℂ) • (1 : State 2))

/-- The depolarising map fixes the trace when the input does. -/
theorem depolarizing_trace (p : ℂ) (rho : State 2) :
    Matrix.trace (depolarizing p rho)
      = (1 - 4 * p / 3) * Matrix.trace rho + (4 * p / 3) * (1/2 * 2) := by
  unfold depolarizing
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin]
  ring

/-- At `p = 0` the depolarising channel is the identity. -/
theorem depolarizing_zero (rho : State 2) : depolarizing 0 rho = rho := by
  unfold depolarizing
  norm_num

/-- At `p = 3/4` the depolarising channel maps everything to the maximally mixed
state `I/2`: total decoherence. -/
theorem depolarizing_max (rho : State 2) :
    depolarizing (3/4) rho = (1/2 : ℂ) • (1 : State 2) := by
  unfold depolarizing
  norm_num

/-! ## The qubit amplitude-damping channel -/

/-- The Kraus operator `K0 = diag (1, c)` of the amplitude-damping channel;
`c` is the fraction of amplitude that survives, so `c = sqrt (1 - gamma)`. -/
noncomputable def ampDampK0 (c : ℝ) : Operator 2 := !![1, 0; 0, (c : ℂ)]

/-- The Kraus operator `K1 = [[0, s], [0, 0]]`; `s = sqrt gamma` is the decay
amplitude that carries `|1⟩` into `|0⟩`. -/
noncomputable def ampDampK1 (s : ℝ) : Operator 2 := !![0, (s : ℂ); 0, 0]

/-- The amplitude-damping Kraus family, indexed by `Fin 2`. -/
noncomputable def ampDamp (c s : ℝ) : Fin 2 → Operator 2 := ![ampDampK0 c, ampDampK1 s]

/-- The real identity `c^2 + s^2 = 1` lifted to `ℂ`; the step that collapses
the Kraus sum to the identity. -/
theorem ofReal_sq_add_eq_one (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    ((c * c + s * s : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_one, Complex.ofReal_inj]; nlinarith [h]

/-- **The amplitude-damping channel is trace preserving.**  The Kraus
completeness relation `sum_k K_k† K_k = 1` holds exactly when `c^2 + s^2 = 1`,
the physical statement that the system-environment coupling is unitary. -/
theorem ampDamp_trace_preserving (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (∑ i : Fin 2, Matrix.conjTranspose (ampDamp c s i) * ampDamp c s i) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.sum_univ_two, ampDamp, ampDampK0, ampDampK1, Matrix.add_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one,
      Matrix.empty_val', Matrix.head_fin_const, star_one, star_zero, one_mul, mul_zero,
      zero_mul, add_zero, zero_add] <;>
    norm_num <;>
    (try rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add,
        ofReal_sq_add_eq_one c s h])

/-- Consequently the amplitude-damping channel conserves probability on every
state, read off from the general Kraus trace law rather than reproved. -/
theorem ampDamp_trace (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (rho : State 2) :
    Matrix.trace (applyKraus (ampDamp c s) rho) = Matrix.trace rho :=
  kraus_trace (ampDamp c s) rho (ampDamp_trace_preserving c s h)

/-! ## Composition of channels -/

/-- The composition of two Kraus families is again the operator-sum form:
applying `K` then `L` equals applying the family `(k, l) ↦ L_l K_k`. -/
theorem kraus_comp {n : Nat} {ι J : Type} [Fintype ι] [Fintype J] (K : ι → Operator n) (L : J → Operator n)
    (rho : State n) :
    applyKraus L (applyKraus K rho) = applyKraus (fun p : J × ι => L p.1 * K p.2) rho := by
  unfold applyKraus
  rw [show (∑ p : J × ι, (L p.1 * K p.2) * rho * Matrix.conjTranspose (L p.1 * K p.2))
        = ∑ j, ∑ k, (L j * K k) * rho * Matrix.conjTranspose (L j * K k)
        from Fintype.sum_prod_type _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_mul]
  simp only [mul_assoc]

end LeanPhy.QuantumInfo
