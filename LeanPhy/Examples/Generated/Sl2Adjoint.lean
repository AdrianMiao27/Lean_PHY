import LeanPhy.Mathematics.LieDeformationReduction
import LeanPhy.Mathematics.FiniteLieCohomology
import Mathlib.LinearAlgebra.Dimension.Constructions

/- Generated candidate: compile with `lake env lean` before treating it as checked.
Input SHA-256: d858c52c4957887064e161637a0f59b9a6487d8bdfb52b9f6b6edc8d286b15f8
The matrices below are the mathematical input; no physical interpretation is inferred. -/
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace LeanPhy.Generated.Sl2AdjointCE

open LeanPhy.Mathematics

def d1 : Matrix (Fin 9) (Fin 9) ℚ :=
  !![0, 0, -1, -2, 0, 0, 0, 0, 0;
    2, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, -4, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 2, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 4, 0;
    -2, 0, 0, 0, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 1, 0, 0, 0, 1;
    0, -1, 0, 0, 0, 0, -2, 0, 0;
    0, 0, -1, -2, 0, 0, 0, 0, 0]

def d2 : Matrix (Fin 3) (Fin 9) ℚ :=
  !![0, -1, 0, 0, 0, -1, 0, 0, 0;
    0, 0, 0, 2, 0, 0, 0, 2, 0;
    2, 0, 0, 0, 0, 0, 0, 0, -2]

def project : Matrix (Fin 0) (Fin 9) ℚ :=
  0

def represent : Matrix (Fin 9) (Fin 0) ℚ :=
  0

def primitive : Matrix (Fin 9) (Fin 9) ℚ :=
  !![0, 0, 0, 0, 0, (-1 / 2), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, (-1 / 2), 1, 0, 0;
    0, 0, (-1 / 4), 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, (1 / 4), 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0]

def correction : Matrix (Fin 9) (Fin 3) ℚ :=
  !![0, 0, (1 / 2);
    -1, 0, 0;
    0, 0, 0;
    0, (1 / 2), 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0]

def certificate : MatrixCohomologyReduction d1 d2 0 where
  project := project
  represent := represent
  primitive := primitive
  correction := correction
  chain := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project, represent, primitive, correction, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply]
  closed := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project, represent, primitive, correction, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply]
  boundary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project, represent, primitive, correction, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply]
  retract := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project, represent, primitive, correction, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply]
  decompose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project, represent, primitive, correction, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply]

noncomputable def cohomologyEquiv :
    CohomologyReduction.Cohomology d1.toLin' d2.toLin' ≃ₗ[ℚ] (Fin 0 → ℚ) :=
  certificate.toReduction.quotientEquiv

theorem exact_iff (x : Fin 9 → ℚ) (hx : d2.toLin' x = 0) :
    (∃ a, d1.toLin' a = x) ↔ project.toLin' x = 0 :=
  certificate.toReduction.exact_iff x hx

end LeanPhy.Generated.Sl2AdjointCE

/- The following namespace proves that the matrices above compute the actual
Lie H2 of the declared structure constants and coefficient representation. -/
namespace LeanPhy.Generated.Sl2Adjoint

-- Three nested linear maps with vector coefficients need this elaboration depth.
set_option maxSynthPendingDepth 5

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates

abbrev Space := Fin 3 → ℚ
abbrev Coeff := Fin 3 → ℚ

def bracket (x y : Space) : Space := ![(1) * (x 1 * y 2 - x 2 * y 1), (2) * (x 0 * y 1 - x 1 * y 0), (-2) * (x 0 * y 2 - x 2 * y 0)]

def algebra : LeanPhy.Mathematics.LieAlgebra ℚ Space where
  bracket := bracket
  add_left := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  add_right := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  smul_left := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  smul_right := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  zero_left := by intros; ext r; fin_cases r <;> simp [bracket]
  alternating := by intros; ext r; fin_cases r <;> dsimp [bracket] <;> ring
  antisymm := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  jacobi := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring

def action (x : Space) (v : Coeff) : Coeff := bracket x v

def coefficients : LeanPhy.Mathematics.LieModule algebra Coeff := adjointLieModule algebra

theorem coefficients_adjoint : coefficients = adjointLieModule algebra := rfl

abbrev C2 := LieCochain2 algebra coefficients

def oneValues (φ : Space →ₗ[ℚ] Coeff) : Fin 9 → ℚ := ![φ (e 0) 0, φ (e 0) 1, φ (e 0) 2, φ (e 1) 0, φ (e 1) 1, φ (e 1) 2, φ (e 2) 0, φ (e 2) 1, φ (e 2) 2]

def oneFrom (a : Fin 9 → ℚ) : Space →ₗ[ℚ] Coeff where
  toFun x := ![a 0 * x 0 + a 3 * x 1 + a 6 * x 2, a 1 * x 0 + a 4 * x 1 + a 7 * x 2, a 2 * x 0 + a 5 * x 1 + a 8 * x 2]
  map_add' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul' := by intros; ext r; fin_cases r <;> simp <;> ring

noncomputable def oneCoordinates : (Space →ₗ[ℚ] Coeff) ≃ₗ[ℚ] (Fin 9 → ℚ) where
  toFun := oneValues
  invFun := oneFrom
  left_inv φ := by
    apply (Pi.basisFun ℚ (Fin 3)).ext
    intro i
    ext r
    fin_cases i <;> fin_cases r <;> simp [oneFrom, oneValues, e, Pi.basisFun_apply]
  right_inv a := by
    ext r
    fin_cases r <;> simp [oneFrom, oneValues, e]
  map_add' := by intros; ext r; fin_cases r <;> simp [oneValues]
  map_smul' := by intros; ext r; fin_cases r <;> simp [oneValues]

def twoValues (ω : C2) : Fin 9 → ℚ := ![ω (e 0) (e 1) 0, ω (e 0) (e 1) 1, ω (e 0) (e 1) 2, ω (e 0) (e 2) 0, ω (e 0) (e 2) 1, ω (e 0) (e 2) 2, ω (e 1) (e 2) 0, ω (e 1) (e 2) 1, ω (e 1) (e 2) 2]

def twoFrom (a : Fin 9 → ℚ) : C2 where
  eval x y := ![a 0 * (x 0 * y 1 - x 1 * y 0) + a 3 * (x 0 * y 2 - x 2 * y 0) + a 6 * (x 1 * y 2 - x 2 * y 1), a 1 * (x 0 * y 1 - x 1 * y 0) + a 4 * (x 0 * y 2 - x 2 * y 0) + a 7 * (x 1 * y 2 - x 2 * y 1), a 2 * (x 0 * y 1 - x 1 * y 0) + a 5 * (x 0 * y 2 - x 2 * y 0) + a 8 * (x 1 * y 2 - x 2 * y 1)]
  map_add_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_add_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  alternating' := by intros; ext r; fin_cases r <;> dsimp <;> ring

noncomputable def twoCoordinates : C2 ≃ₗ[ℚ] (Fin 9 → ℚ) where
  toFun := twoValues
  invFun := twoFrom
  left_inv ω := by
    apply ext_basis
    intro i j
    ext r
    fin_cases i <;> fin_cases j <;> fin_cases r <;>
      simp [twoFrom, twoValues, e, LieCochain2.alternating]
    all_goals exact congrFun (ω.skew _ _).symm _
  right_inv a := by
    ext r
    fin_cases r <;> simp [twoFrom, twoValues, e]
  map_add' := by intros; ext r; fin_cases r <;> simp [twoValues]
  map_smul' := by intros; ext r; fin_cases r <;> simp [twoValues]

def readThird : (Space →ₗ[ℚ] Space →ₗ[ℚ] Space →ₗ[ℚ] Coeff) →ₗ[ℚ] (Fin 3 → ℚ) where
  toFun t := ![t (e 0) (e 1) (e 2) 0, t (e 0) (e 1) (e 2) 1, t (e 0) (e 1) (e 2) 2]
  map_add' := by intros; ext r; fin_cases r <;> rfl
  map_smul' := by intros; ext r; fin_cases r <;> rfl

theorem readThird_detect (ω : C2) (hz : readThird (differential2 coefficients ω) = 0) :
    differential2 coefficients ω = 0 := by
  have sample_0_1_2 : differential2 coefficients ω (e 0) (e 1) (e 2) = 0 := by
    ext r
    fin_cases r
    · exact congrFun hz 0
    · exact congrFun hz 1
    · exact congrFun hz 2
  apply differential2_eq_zero_of_increasing
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hij <;> norm_num at hjk
  all_goals first | omega | exact sample_0_1_2

theorem differential1_coordinates (φ : Space →ₗ[ℚ] Coeff) :
    twoCoordinates (differential1 coefficients φ) = Sl2AdjointCE.d1.toLin' (oneCoordinates φ) := by
  obtain ⟨a, rfl⟩ := oneCoordinates.symm.surjective φ
  rw [oneCoordinates.apply_symm_apply]
  change twoValues (differential1 coefficients (oneFrom a)) = Sl2AdjointCE.d1.toLin' a
  ext r
  fin_cases r <;>
    simp [twoValues, differential1, coefficients, adjointLieModule, action, algebra, bracket, oneFrom, e,
      Sl2AdjointCE.d1, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem differential2_coordinates (ω : C2) :
    Sl2AdjointCE.d2.toLin' (twoCoordinates ω) = readThird (differential2 coefficients ω) := by
  obtain ⟨a, rfl⟩ := twoCoordinates.symm.surjective ω
  rw [twoCoordinates.apply_symm_apply]
  change Sl2AdjointCE.d2.toLin' a = readThird (differential2 coefficients (twoFrom a))
  ext r
  fin_cases r <;>
    simp [readThird, differential2_apply, coefficients, adjointLieModule, action, algebra, bracket, twoFrom, e,
      Sl2AdjointCE.d2, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

noncomputable def reduction : Reduction coefficients (Fin 0 → ℚ) :=
  Sl2AdjointCE.certificate.toReduction.transport oneCoordinates twoCoordinates readThird
    differential1_coordinates differential2_coordinates readThird_detect

noncomputable def h2Equiv : H2 coefficients ≃ₗ[ℚ] (Fin 0 → ℚ) := reduction.h2Equiv coefficients

theorem h2_finrank : Module.finrank ℚ (H2 coefficients) = 0 := by
  rw [h2Equiv.finrank_eq]
  simp

theorem boundary_iff (ω : C2) (hω : IsTwoCocycle coefficients ω) :
    IsTwoCoboundary coefficients ω ↔ reduction.project ω = 0 :=
  reduction.exact_iff ω hω

theorem normal_form (ω : C2) (hω : IsTwoCocycle coefficients ω) :
    differential1 coefficients (reduction.primitive ω) +
      reduction.represent (reduction.project ω) = ω := reduction.normal_form ω hω

/-- Every coordinate tuple supplies a closed representative and an actual first-order Lie algebra. -/
noncomputable def representativeDeformation :=
  LieDeformation.Reduction.deformation (reduction)

/-- Closed deformation directions are equivalent exactly when their computed coordinates agree. -/
theorem deformation_equivalent_iff (ω η : (C2))
    (hω : IsTwoCocycle (coefficients) ω) (hη : IsTwoCocycle (coefficients) η) :
    Nonempty (LieDeformation.Equivalence ω η) ↔ (reduction).project ω = (reduction).project η :=
  LieDeformation.Reduction.equivalent_iff (reduction) ω η hω hη

/-- A concrete invertible generator change puts a closed direction in normal form. -/
noncomputable def normalizeDeformation (ω : (C2)) (hω : IsTwoCocycle (coefficients) ω) :
    LieDeformation.Equivalence ω ((reduction).represent ((reduction).project ω)) :=
  LieDeformation.Reduction.normalize (reduction) ω hω

theorem deformation_removable_iff (ω : (C2)) (hω : IsTwoCocycle (coefficients) ω) :
    Nonempty (LieDeformation.Equivalence ω 0) ↔ (reduction).project ω = 0 :=
  LieDeformation.Reduction.removable_iff (reduction) ω hω

/-- Vanishing coordinates give an explicit trivializing change of generators. -/
noncomputable def trivializeDeformation (ω : (C2)) (hω : IsTwoCocycle (coefficients) ω)
    (h : (reduction).project ω = 0) : LieDeformation.Equivalence ω 0 :=
  LieDeformation.Reduction.trivialize (reduction) ω hω h

end LeanPhy.Generated.Sl2Adjoint
