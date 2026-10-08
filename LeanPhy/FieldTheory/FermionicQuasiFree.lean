import LeanPhy.FieldTheory.FermionicWick
import LeanPhy.Condensed.JordanWigner
import LeanPhy.Quantum.FiniteDensity
import LeanPhy.Quantum.Projector

set_option autoImplicit false

/-!
# Ordered finite fermionic quasi-free states

`FermionicWick.fourPoint` is an algebraic Pfaffian kernel whose contraction is
antisymmetric in the *ordered slots*.  A physical operator expectation is not
itself antisymmetric: the CAR contact term is present when two slots are
reversed.  This module makes that distinction explicit and provides a small
proof-bearing interface for finite quasi-free calculations.

The certificate stores an actual finite density matrix, an ordered list of
generators, its two-point contractions, and the four-point Wick identity.  The
identity is a proposition consumed by later calculations; it is never inferred
from the name of a state.  The concrete one-mode vacuum below is checked from
the explicit Jordan--Wigner matrices and serves as a regression anchor for
larger Gaussian-state adapters.
-/

namespace LeanPhy.FieldTheory

open LeanPhy.Quantum LeanPhy.Condensed
open scoped Matrix

/-! ## A reusable certificate boundary -/

structure OrderedQuasiFreeCertificate (σ J : Type*)
    [Fintype σ] [Fintype J] where
  state : FiniteDensity σ
  generator : J → Matrix σ σ ℂ
  slots : Fin 4 → J
  contraction : Fin 4 → Fin 4 → ℂ
  contraction_antisymm : ∀ i j, contraction j i = -contraction i j
  twoPoint_ordered : ∀ {i j : Fin 4}, i < j →
    contraction i j =
      Matrix.trace (state.rho * (generator (slots i) * generator (slots j)))
  fourPoint_wick :
    Matrix.trace (state.rho *
      (generator (slots 0) * generator (slots 1) *
        generator (slots 2) * generator (slots 3))) =
      FermionicWick.fourPoint contraction 0 1 2 3

namespace OrderedQuasiFreeCertificate

variable {σ J : Type*} [Fintype σ] [Fintype J]

def expectation (C : OrderedQuasiFreeCertificate σ J)
    (A : Matrix σ σ ℂ) : ℂ := Matrix.trace (C.state.rho * A)

theorem expectation_fourPoint (C : OrderedQuasiFreeCertificate σ J) :
    expectation C
      (C.generator (C.slots 0) * C.generator (C.slots 1) *
        C.generator (C.slots 2) * C.generator (C.slots 3)) =
      FermionicWick.fourPoint C.contraction 0 1 2 3 :=
  C.fourPoint_wick

theorem contraction_eq_expectation (C : OrderedQuasiFreeCertificate σ J)
    {i j : Fin 4} (hij : i < j) :
    C.contraction i j =
      expectation C (C.generator (C.slots i) * C.generator (C.slots j)) :=
  C.twoPoint_ordered hij

end OrderedQuasiFreeCertificate

/-! ## Explicit one-mode vacuum -/

namespace SingleModeVacuum

abbrev Generator := Fin 2

noncomputable def vacuumKet : Ket 2 := fun i => if i = 0 then 1 else 0

theorem vacuumKet_normalized : braket vacuumKet vacuumKet = 1 := by
  simp [vacuumKet, braket]

noncomputable def state : FiniteDensity (Fin 2) :=
  { rho := rankOneProjector vacuumKet
    valid :=
      ⟨rankOneProjector_conjTranspose vacuumKet,
        rankOneProjector_posSemidef vacuumKet,
        normalized_rankOneProjector_trace vacuumKet vacuumKet_normalized⟩ }

noncomputable def generator : Generator → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => smMat
  | 1 => spMat

noncomputable def expectation (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Matrix.trace (state.rho * A)

noncomputable def orderedContraction (g : Fin 4 → Generator) (i j : Fin 4) : ℂ :=
  if i < j then expectation (generator (g i) * generator (g j))
  else if j < i then -expectation (generator (g j) * generator (g i))
  else 0

theorem orderedContraction_antisymm (g : Fin 4 → Generator) (i j : Fin 4) :
    orderedContraction g j i = -orderedContraction g i j := by
  unfold orderedContraction
  by_cases hij : i < j
  · have hji : ¬ j < i := by exact not_lt_of_ge (Nat.le_of_lt hij)
    simp [hij, hji]
  · by_cases hji : j < i
    · have hij' : ¬ i < j := by exact not_lt_of_ge (Nat.le_of_lt hji)
      simp [hij', hji]
    · have heq : i = j := by omega
      simp [hij, hji, heq]

def slots (a b c d : Generator) : Fin 4 → Generator
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d

theorem vacuum_fourPoint (a b c d : Generator) :
    expectation
      (generator a * generator b * generator c * generator d) =
      FermionicWick.fourPoint (orderedContraction (slots a b c d)) 0 1 2 3 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [expectation, orderedContraction, slots, generator, state, vacuumKet,
      rankOneProjector, ketbra, braket, Matrix.trace, smMat, spMat,
      FermionicWick.fourPoint, Matrix.mul_apply, Fin.sum_univ_succ]

noncomputable def certificate (a b c d : Generator) :
    OrderedQuasiFreeCertificate (Fin 2) Generator where
  state := state
  generator := generator
  slots := slots a b c d
  contraction := orderedContraction (slots a b c d)
  contraction_antisymm := orderedContraction_antisymm (slots a b c d)
  twoPoint_ordered := by
    intro i j hij
    simp [orderedContraction, expectation, hij]
  fourPoint_wick := vacuum_fourPoint a b c d

theorem certificate_readout (a b c d : Generator) :
    OrderedQuasiFreeCertificate.expectation (certificate a b c d)
      (generator a * generator b * generator c * generator d) =
      FermionicWick.fourPoint (orderedContraction (slots a b c d)) 0 1 2 3 :=
  OrderedQuasiFreeCertificate.expectation_fourPoint (certificate a b c d)

end SingleModeVacuum

/-! ## Explicit two-mode vacuum

The one-mode anchor above is useful for signs, but it cannot detect a missing
Jordan--Wigner parity string.  The following certificate uses the actual two
mode matrices from `Condensed.JordanWigner` and a rank-one density on the
four-dimensional occupation space.  The checked word contains both modes and
both creation/annihilation sectors; the public certificate remains
parameterised by its ordered slots, so an external calculation can replace
the state or the word without changing the interface.
-/

namespace TwoModeVacuum

open scoped Matrix ComplexOrder

abbrev Generator := Fin 4

noncomputable def vacuumKet : Idx2q → ℂ :=
  fun x => if x = (0, 0) then 1 else 0

noncomputable def rho : Matrix Idx2q Idx2q ℂ :=
  Matrix.vecMulVec vacuumKet (star vacuumKet)

theorem rho_conjTranspose : rhoᴴ = rho := by
  ext i j
  simp [rho, Matrix.conjTranspose_apply, Matrix.vecMulVec]
  ring

theorem rho_pos : rho.PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star vacuumKet

theorem vacuum_normalized : ∑ i, star (vacuumKet i) * vacuumKet i = 1 := by
  classical
  rw [Fintype.sum_eq_single (0, 0)]
  · simp [vacuumKet]
  · intro x hx
    simp [vacuumKet, hx]

theorem rho_trace : Matrix.trace rho = 1 := by
  classical
  unfold rho Matrix.trace Matrix.vecMulVec
  rw [Fintype.sum_eq_single (0, 0)]
  · simp [vacuumKet]
  · intro x hx
    simp [vacuumKet, hx]

noncomputable def state : FiniteDensity Idx2q :=
  { rho := rho
    valid := ⟨rho_conjTranspose, rho_pos, rho_trace⟩ }

noncomputable def generator : Generator → Matrix Idx2q Idx2q ℂ
  | 0 => jwC0
  | 1 => jwC0dag
  | 2 => jwC1
  | 3 => jwC1dag

noncomputable def expectation (A : Matrix Idx2q Idx2q ℂ) : ℂ :=
  Matrix.trace (state.rho * A)

theorem expectation_eq_vacuum_entry (A : Matrix Idx2q Idx2q ℂ) :
    expectation A = A (0, 0) (0, 0) := by
  simp [expectation, state, rho, Matrix.trace, Matrix.vecMulVec, vacuumKet,
    Matrix.mul_apply]

noncomputable def orderedContraction (g : Fin 4 → Generator) (i j : Fin 4) : ℂ :=
  if i < j then expectation (generator (g i) * generator (g j))
  else if j < i then -expectation (generator (g j) * generator (g i))
  else 0

theorem orderedContraction_antisymm (g : Fin 4 → Generator) (i j : Fin 4) :
    orderedContraction g j i = -orderedContraction g i j := by
  unfold orderedContraction
  by_cases hij : i < j
  · have hji : ¬ j < i := by exact not_lt_of_ge (Nat.le_of_lt hij)
    simp [hij, hji]
  · by_cases hji : j < i
    · have hij' : ¬ i < j := by exact not_lt_of_ge (Nat.le_of_lt hji)
      simp [hij', hji]
    · have heq : i = j := by omega
      simp [hij, hji, heq]

def slots (a b c d : Generator) : Fin 4 → Generator
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d

/-- A cross-mode four-point Wick identity checked from the explicit matrices. -/
theorem vacuum_fourPoint_mixed :
    expectation
      (generator 0 * generator 1 * generator 2 * generator 3) =
      FermionicWick.fourPoint (orderedContraction (slots 0 1 2 3)) 0 1 2 3 := by
  simp only [orderedContraction, slots, generator, FermionicWick.fourPoint,
    expectation_eq_vacuum_entry]
  simp [jwC0, jwC0dag, jwC1, jwC1dag, kron, Matrix.kroneckerMap,
    Matrix.mul_apply, Fintype.sum_prod_type, smMat, spMat, zMat]

/-- The mixed two-mode calculation packaged for downstream research clients. -/
noncomputable def certificate :
    OrderedQuasiFreeCertificate Idx2q Generator where
  state := state
  generator := generator
  slots := slots 0 1 2 3
  contraction := orderedContraction (slots 0 1 2 3)
  contraction_antisymm := orderedContraction_antisymm (slots 0 1 2 3)
  twoPoint_ordered := by
    intro i j hij
    simp [orderedContraction, expectation, hij]
  fourPoint_wick := vacuum_fourPoint_mixed

theorem certificate_readout :
    OrderedQuasiFreeCertificate.expectation certificate
      (generator 0 * generator 1 * generator 2 * generator 3) =
      FermionicWick.fourPoint
        (orderedContraction (slots 0 1 2 3)) 0 1 2 3 :=
  OrderedQuasiFreeCertificate.expectation_fourPoint certificate

end TwoModeVacuum

end LeanPhy.FieldTheory
