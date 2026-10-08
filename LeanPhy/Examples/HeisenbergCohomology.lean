import LeanPhy.Mathematics.LieCohomologyReduction
import LeanPhy.Examples.Generated.HeisenbergReduction
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Complete degree-two cohomology of the rational Heisenberg algebra

The generated matrix certificate is connected to the declared Lie bracket,
including completeness of the cochain coordinates. It yields an actual
`H2 ≃ₗ[ℚ] (Fin 2 → ℚ)`, a primitive for every exact cocycle, and the two
parameters classifying the supplied central extensions fixing base and center.
-/

namespace LeanPhy.Examples.HeisenbergCohomology

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates

abbrev Space := Fin 3 → ℚ

def bracket (x y : Space) : Space := ![0, 0, x 0 * y 1 - x 1 * y 0]

def algebra : LeanPhy.Mathematics.LieAlgebra ℚ Space where
  bracket := bracket
  add_left := by intros; ext i; fin_cases i <;> simp [bracket]; ring
  add_right := by intros; ext i; fin_cases i <;> simp [bracket]; ring
  smul_left := by intros; ext i; fin_cases i <;> simp [bracket]; ring
  smul_right := by intros; ext i; fin_cases i <;> simp [bracket]; ring
  zero_left := by intros; ext i; fin_cases i <;> simp [bracket]
  alternating := by intros; ext i; fin_cases i <;> simp [bracket]; ring
  antisymm := by intros; ext i; fin_cases i <;> simp [bracket]; ring
  jacobi := by intros; ext i; fin_cases i <;> simp [bracket]

abbrev coefficients : LeanPhy.Mathematics.LieModule algebra ℚ := trivialLieModule algebra

abbrev C2 := LieCochain2 algebra coefficients

noncomputable def coordinates : C2 ≃ₗ[ℚ] Space := twoEquiv algebra coefficients

/-- All alternating two-cochains on this particular algebra are closed. -/
theorem all_closed (ω : C2) : IsTwoCocycle coefficients ω := by
  rw [← coordinates.symm_apply_apply ω]
  rw [twoCocycle_trivial_iff]
  intro x y z
  change twoOfComponents (coordinates ω) x (bracket y z) +
    twoOfComponents (coordinates ω) y (bracket z x) +
    twoOfComponents (coordinates ω) z (bracket x y) = 0
  simp [twoOfComponents, bracket]
  ring

/-- The first generated matrix is the differential of the declared bracket. -/
theorem differential1_coordinates (φ : Space →ₗ[ℚ] ℚ) :
    coordinates (differential1 coefficients φ) =
      LeanPhy.Generated.Heisenberg.d1.toLin' (oneEquiv 3 φ) := by
  have hzero : (![0, 0, 0] : Space) = 0 := by ext i; fin_cases i <;> rfl
  have htwo : (![0, 0, 1] : Space) = Pi.single 2 1 := by ext i; fin_cases i <;> simp
  change twoComponents (differential1 coefficients φ) = _
  ext i
  fin_cases i <;>
    simp [twoComponents, differential1, coefficients,
      trivialLieModule, algebra, bracket, e, LeanPhy.Generated.Heisenberg.d1,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, oneEquiv, hzero, htwo]

/-- Transfer the computed reduction to the full CE maps, not only their tables. -/
noncomputable def reduction : Reduction coefficients (Fin 2 → ℚ) :=
  LeanPhy.Generated.Heisenberg.certificate.toReduction.transport
    (oneEquiv 3) coordinates 0 differential1_coordinates
    (by intro ω; simp [LeanPhy.Generated.Heisenberg.d2])
    (by intro ω _; exact all_closed ω)

noncomputable def h2Equiv : H2 coefficients ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  reduction.h2Equiv coefficients

/-- The quotient has exactly two independent rational parameters. -/
theorem h2_finrank : Module.finrank ℚ (H2 coefficients) = 2 := by
  rw [h2Equiv.finrank_eq]
  simp

def parameters (ω : C2) : Fin 2 → ℚ := ![ω (e 0) (e 2), ω (e 1) (e 2)]

@[simp] theorem project_eq_parameters (ω : C2) : reduction.project ω = parameters ω := by
  ext i
  fin_cases i <;>
    simp [reduction, CohomologyReduction.transport, MatrixCohomologyReduction.toReduction,
      LeanPhy.Generated.Heisenberg.certificate, LeanPhy.Generated.Heisenberg.project,
      coordinates, twoEquiv, twoComponents, parameters,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

@[simp] theorem h2Equiv_classOf (ω : C2) :
    h2Equiv (classOf coefficients ω (all_closed ω)) = parameters ω :=
  project_eq_parameters ω

/-- A direct zero test for the class of any two-cochain in this model. -/
theorem boundary_iff (ω : C2) :
    IsTwoCoboundary coefficients ω ↔ ω (e 0) (e 2) = 0 ∧ ω (e 1) (e 2) = 0 := by
  change (∃ φ, differential1Linear coefficients φ = ω) ↔ _
  rw [reduction.exact_iff ω (all_closed ω), project_eq_parameters]
  simp [parameters, funext_iff, Fin.forall_fin_succ]

/-- Every cocycle has its representative and primitive computed explicitly. -/
theorem normal_form (ω : C2) :
    differential1 coefficients (reduction.primitive ω) +
      reduction.represent (parameters ω) = ω := by
  have h := reduction.normal_form ω (all_closed ω)
  rw [project_eq_parameters] at h
  change differential1 coefficients (reduction.primitive ω) + reduction.represent (parameters ω) = ω at h
  exact h

/-- Completeness of the two parameters for base- and center-preserving extensions. -/
theorem extension_equivalence_iff (ω η : C2) :
    Nonempty (CentralExtension.Equivalence ω η) ↔ parameters ω = parameters η := by
  rw [← CentralExtension.class_eq_iff_nonempty_equivalence ω η (all_closed ω) (all_closed η)]
  rw [← h2Equiv.injective.eq_iff, h2Equiv_classOf, h2Equiv_classOf]

end LeanPhy.Examples.HeisenbergCohomology
