import LeanPhy.FieldTheory.FermionVacuum
import LeanPhy.FieldTheory.FermionicMoment
import LeanPhy.FieldTheory.FermionPolynomial

set_option autoImplicit false

/-!
# Arbitrary ordered vacuum moments from CAR

Sliding the leftmost annihilation part through the remaining probes derives the
full contraction recursion, including contact terms for repeated probes. The
remaining annihilation operator kills the actual density. No moment-factorization
assumption, canonical-probe condition, or fixed number of insertions is supplied.

The same operation evaluates existing fermion words and symbolic interaction
expressions in an actual vacuum. This is not a thermal, general Gaussian,
time-ordered or interacting-ground-state Wick theorem.
-/

namespace LeanPhy.FieldTheory

open scoped Matrix

namespace FermionProbe

open LeanPhy.Quantum

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-- The symmetric contact kernel must be retained when actual probes are swapped. -/
theorem operator_anticommutator (p q : FermionProbe ι)
    (M : MultiModeCAR ι (Matrix σ σ ℂ)) :
    ⟪p.operator M, q.operator M⟫ =
      (p.contraction q + q.contraction p) • (1 : Matrix σ σ ℂ) := by
  calc
    _ = ⟪M.annihilation p.ann, M.annihilation q.ann⟫ +
        ⟪M.annihilation p.ann, M.creation q.cre⟫ +
        ⟪M.annihilation q.ann, M.creation p.cre⟫ +
        ⟪M.creation p.cre, M.creation q.cre⟫ := by
      simp only [operator, anticommutator, add_mul, mul_add]
      abel
    _ = _ := by
      rw [M.annihilation_annihilation, M.creation_creation,
        M.annihilation_creation, M.annihilation_creation]
      simp only [zero_add, add_zero, ← add_smul, contraction]

/-- Interpret a symbolic letter as a linear probe with one nonzero coefficient. -/
def ofLetter : FermionWord.Letter ι → FermionProbe ι
  | Sum.inl i => ⟨0, Pi.single i 1⟩
  | Sum.inr i => ⟨Pi.single i 1, 0⟩

@[simp] theorem operator_ofLetter (M : MultiModeCAR ι (Matrix σ σ ℂ))
    (a : FermionWord.Letter ι) :
    (ofLetter a).operator M = FermionWord.generator M a := by
  cases a <;> simp [ofLetter, operator, MultiModeCAR.annihilation,
    MultiModeCAR.creation, FermionWord.generator, Pi.single_apply]

end FermionProbe

namespace FermionWord

variable {ι : Type} [DecidableEq ι]

/-- Ordered vacuum kernel: only annihilation followed by creation can contract.
This differs from the symmetric CAR contact kernel used for normal ordering. -/
def vacuumContraction : Letter ι → Letter ι → ℤ
  | Sum.inr i, Sum.inl j => if i = j then 1 else 0
  | _, _ => 0

/-- Executable integer vacuum readout for an arbitrary word. -/
def vacuumMoment (w : Word ι) : ℤ := FermionicWick.moment vacuumContraction w

theorem contraction_ofLetter [Fintype ι] (a b : Letter ι) :
    (FermionProbe.ofLetter a).contraction (FermionProbe.ofLetter b) =
      (vacuumContraction a b : ℂ) := by
  cases a <;> cases b <;>
    simp [FermionProbe.contraction, FermionProbe.ofLetter, vacuumContraction,
      Pi.single_apply, eq_comm]

end FermionWord

namespace FermionPolynomial

/-- A symbolic expression is evaluated using exact integer word readouts. -/
def vacuumValue {R ι : Type} [CommRing R] [DecidableEq ι]
    (p : Expression R ι) : R :=
  (p.map (fun t => t.1 * (FermionWord.vacuumMoment t.2 : R))).sum

end FermionPolynomial

namespace FermionVacuum

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable (V : FermionVacuum ι σ)

noncomputable def probeProduct (ps : List (FermionProbe ι)) : Matrix σ σ ℂ :=
  (ps.map (fun p => p.operator V.car)).prod

@[simp] theorem probeProduct_nil : V.probeProduct [] = 1 := rfl
@[simp] theorem probeProduct_cons (p : FermionProbe ι) (ps : List (FermionProbe ι)) :
    V.probeProduct (p :: ps) = p.operator V.car * V.probeProduct ps := rfl
@[simp] theorem probeProduct_append (ps qs : List (FermionProbe ι)) :
    V.probeProduct (ps ++ qs) = V.probeProduct ps * V.probeProduct qs := by
  simp [probeProduct]

/-- A moment is the actual trace of the specified ordered operator product. -/
noncomputable def moment (ps : List (FermionProbe ι)) : ℂ :=
  V.expectation (V.probeProduct ps)

@[simp] theorem moment_nil : V.moment [] = 1 := V.expectation_one

/-- Moving one annihilation probe across a tail retains every signed deletion.
The before records the actual order of all operators that have been crossed. -/
theorem annihilation_moment (p : FermionProbe ι) (before tail : List (FermionProbe ι)) :
    V.expectation (V.probeProduct before *
      (V.car.annihilation p.ann * V.probeProduct tail)) =
      ((FermionicWick.removals tail).map (fun t =>
        (t.1 : ℂ) * p.contraction t.2.1 * V.moment (before ++ t.2.2))).sum := by
  induction tail generalizing before with
  | nil => simp [FermionicWick.removals]
  | cons q qs ih =>
    rw [probeProduct_cons, V.ann_probe_tail, mul_sub, mul_smul_comm,
      V.expectation_sub, V.expectation_smul]
    have h := ih (before ++ [q])
    simp only [probeProduct_append, probeProduct_cons, probeProduct_nil, mul_one, mul_assoc] at h
    rw [h]
    simp only [FermionicWick.removals, List.map_cons, List.map_map, List.sum_cons,
      Function.comp_def, Int.cast_one, one_mul, Int.cast_neg, neg_mul,
      List.append_assoc, List.singleton_append]
    simp only [moment, probeProduct_append, mul_assoc,
      sub_eq_add_neg]
    congr 1
    simpa only [List.map_map, Function.comp_def] using
      (List.sum_neg ((FermionicWick.removals qs).map (fun t =>
        (t.1 : ℂ) * (p.contraction t.2.1 *
          V.expectation (V.probeProduct before * V.probeProduct (q :: t.2.2))))))

/-- Full actual-state Wick recursion, with no assumption of factorization. -/
theorem moment_cons (p : FermionProbe ι) (ps : List (FermionProbe ι)) :
    V.moment (p :: ps) =
      ((FermionicWick.removals ps).map (fun t =>
        (t.1 : ℂ) * p.contraction t.2.1 * V.moment t.2.2)).sum := by
  change V.expectation (p.operator V.car * V.probeProduct ps) = _
  rw [V.expectation_probe_left]
  simpa using V.annihilation_moment p [] ps

/-- The terminating coefficient-only recursion computes the actual trace for
any finite number of modes and any ordered list of complex linear probes. -/
theorem moment_eq (ps : List (FermionProbe ι)) :
    V.moment ps = FermionicWick.moment FermionProbe.contraction ps := by
  induction hn : ps.length using Nat.strong_induction_on generalizing ps with
  | h n ih =>
    cases ps with
    | nil => simp
    | cons p ps =>
      rw [V.moment_cons, FermionicWick.moment_cons]
      congr 1
      apply List.map_congr_left
      intro t ht
      rw [ih t.2.2.length (by
        have hlen := FermionicWick.removal_length ht
        simp only [List.length_cons] at hn
        omega) t.2.2 rfl]

/-- Odd actual vacuum moments vanish even when probes mix creation/annihilation. -/
theorem moment_odd (ps : List (FermionProbe ι)) (hodd : ps.length % 2 = 1) :
    V.moment ps = 0 := by
  rw [V.moment_eq]
  exact FermionicWick.moment_odd _ ps hodd

/-- Swapping adjacent actual probes produces a shorter moment with its CAR
contact term, in any surrounding ordered product. -/
theorem moment_exchange (before after : List (FermionProbe ι)) (p q : FermionProbe ι) :
    V.moment (before ++ p :: q :: after) + V.moment (before ++ q :: p :: after) =
      (p.contraction q + q.contraction p) * V.moment (before ++ after) := by
  have h := p.operator_anticommutator q V.car
  unfold LeanPhy.Quantum.anticommutator at h
  have hop : V.probeProduct (before ++ p :: q :: after) +
      V.probeProduct (before ++ q :: p :: after) =
      (p.contraction q + q.contraction p) • V.probeProduct (before ++ after) := by
    simp only [probeProduct_append, probeProduct_cons]
    rw [← mul_add, ← mul_assoc (p.operator V.car), ← mul_assoc (q.operator V.car),
      ← add_mul, h]
    simp only [smul_mul_assoc, one_mul, mul_smul_comm]
  rw [moment, moment, ← V.expectation_add, hop, V.expectation_smul]
  rfl

theorem probeProduct_letters (w : FermionWord.Word ι) :
    V.probeProduct (w.map FermionProbe.ofLetter) = FermionWord.eval V.car w := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]

/-- Kernel-checked integer computation determines the actual represented trace. -/
theorem word_expectation (w : FermionWord.Word ι) :
    V.expectation (FermionWord.eval V.car w) = (FermionWord.vacuumMoment w : ℂ) := by
  rw [← V.probeProduct_letters]
  change V.moment (w.map FermionProbe.ofLetter) = _
  rw [V.moment_eq, FermionicWick.moment_map]
  simp only [FermionWord.contraction_ofLetter, FermionWord.vacuumMoment]
  exact (FermionicWick.map_moment (Int.castRingHom ℂ) FermionWord.vacuumContraction w).symm

/-- Symbolic couplings specialize after exact vacuum evaluation. This reads an
interaction expression in the supplied vacuum; it does not select its ground state. -/
theorem expression_expectation {R : Type} [CommRing R] (f : R →+* ℂ)
    (p : FermionPolynomial.Expression R ι) :
    V.expectation (FermionPolynomial.eval f V.car p) =
      f (FermionPolynomial.vacuumValue p) := by
  induction p with
  | nil => simp [FermionPolynomial.vacuumValue, expectation]
  | cons t p ih =>
    rcases t with ⟨c, w⟩
    simp only [FermionPolynomial.eval_cons, expectation_add, expectation_smul,
      V.word_expectation, ih, FermionPolynomial.vacuumValue, List.map_cons,
      List.sum_cons, map_add, map_mul, map_intCast]

end FermionVacuum

namespace FermionVacuum

variable {ι σ : Type} [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
variable (V : FermionVacuum ι σ)

/-- Existing CAR compilation preserves this actual-state readout. -/
theorem compiled_expectation {R : Type} [CommRing R] [DecidableEq R]
    (f : R →+* ℂ) (p : FermionPolynomial.Expression R ι) :
    V.expectation (FermionPolynomial.eval f V.car (FermionPolynomial.compile p)) =
      f (FermionPolynomial.vacuumValue p) := by
  rw [FermionPolynomial.eval_compile, V.expression_expectation]

end FermionVacuum
end LeanPhy.FieldTheory
