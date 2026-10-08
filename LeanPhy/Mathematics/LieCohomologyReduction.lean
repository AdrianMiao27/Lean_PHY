import LeanPhy.Mathematics.CohomologyReduction
import LeanPhy.Mathematics.CentralExtension
import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Coordinates for certified Lie-cohomology calculations

A certified reduction of the declared CE maps identifies the actual `H2`
quotient with its parameter space. This file also supplies reusable coordinate
equivalences for one- and two-cochains on a three-dimensional carrier. The
bracket and coefficient action remain explicit inputs, and coordinate tables
must still be proved to represent their differentials.
-/

namespace LeanPhy.Mathematics

namespace LieCohomology

variable {R V M H : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
variable {L : LieAlgebra R V} (𝒨 : LieModule L M)

/-- A complete reduction of the declared degree-one and degree-two CE maps. -/
abbrev Reduction (H : Type*) [AddCommGroup H] [Module R H] :=
  CohomologyReduction (A := V →ₗ[R] M) (C := V →ₗ[R] V →ₗ[R] V →ₗ[R] M)
    (differential1Linear 𝒨) (differential2Linear 𝒨) H

noncomputable def Reduction.h2Equiv (S : Reduction 𝒨 H) : H2 𝒨 ≃ₗ[R] H :=
  S.quotientEquiv

@[simp] theorem Reduction.h2Equiv_classOf (S : Reduction 𝒨 H)
    (ω : LieCochain2 L 𝒨) (hω : IsTwoCocycle 𝒨 ω) :
    S.h2Equiv 𝒨 (classOf 𝒨 ω hω) = S.project ω := rfl

end LieCohomology

namespace LieCochainCoordinates

variable {R : Type*} [CommRing R]

/-- Standard coordinate vectors, shared by coordinate maps and their proofs. -/
def e {n : Nat} (i : Fin n) : Fin n → R := Pi.single i 1

/-- Equality of two-cochains can be checked on pairs of basis vectors. -/
theorem ext_basis {n : Nat} {L : LieAlgebra R (Fin n → R)}
    {M : Type*} [AddCommGroup M] [Module R M] {𝒨 : LieModule L M}
    {ω η : LieCochain2 L 𝒨} (h : ∀ i j, ω (e i) (e j) = η (e i) (e j)) : ω = η := by
  apply LieCochain2.nativeEquiv.injective
  apply Subtype.ext
  apply LinearMap.ext_basis (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin n))
  intro i j
  simp only [Pi.basisFun_apply]
  change ω (Pi.single i 1) (Pi.single j 1) = η (Pi.single i 1) (Pi.single j 1)
  exact h i j

/-- One-cochains are determined by their values on coordinate vectors. -/
noncomputable def oneEquiv (n : Nat) : ((Fin n → R) →ₗ[R] R) ≃ₗ[R] (Fin n → R) where
  toFun φ i := φ (e i)
  invFun := (Pi.basisFun R (Fin n)).constr R
  left_inv φ := (Pi.basisFun R (Fin n)).ext (fun i => by simp [e, Pi.single_apply, eq_comm])
  right_inv a := by funext i; simp [e, Pi.single_apply, eq_comm]
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The three independent components are ordered `(01, 02, 12)`. -/
def twoComponents {L : LieAlgebra R (Fin 3 → R)} {𝒨 : LieModule L R}
    (ω : LieCochain2 L 𝒨) : Fin 3 → R := ![ω (e 0) (e 1), ω (e 0) (e 2), ω (e 1) (e 2)]

def twoOfComponents {L : LieAlgebra R (Fin 3 → R)} {𝒨 : LieModule L R}
    (a : Fin 3 → R) : LieCochain2 L 𝒨 where
  eval x y := a 0 * (x 0 * y 1 - x 1 * y 0) +
    a 1 * (x 0 * y 2 - x 2 * y 0) + a 2 * (x 1 * y 2 - x 2 * y 1)
  map_add_left' := by intros; simp; ring
  map_add_right' := by intros; simp; ring
  map_smul_left' := by intros; simp; ring
  map_smul_right' := by intros; simp; ring
  alternating' := by intros; ring

/-- Explicit coordinates for every two-cochain, not only a chosen ansatz. -/
noncomputable def twoEquiv (L : LieAlgebra R (Fin 3 → R)) (𝒨 : LieModule L R) :
    LieCochain2 L 𝒨 ≃ₗ[R] (Fin 3 → R) where
  toFun := twoComponents
  invFun := twoOfComponents
  left_inv ω := by
    apply ext_basis
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [twoOfComponents, twoComponents, e, LieCochain2.alternating]
    all_goals exact (ω.skew _ _).symm
  right_inv a := by
    ext i
    fin_cases i <;> simp [twoComponents, twoOfComponents, e]
  map_add' := by intros; ext i; fin_cases i <;> simp [twoComponents]
  map_smul' := by intros; ext i; fin_cases i <;> simp [twoComponents]

end LieCochainCoordinates

end LeanPhy.Mathematics
