import LeanPhy.Mathematics.FiniteLieCohomology
import Mathlib.LinearAlgebra.Dimension.Constructions

/- Generated candidate: compile with `lake env lean` before treating it as checked.
Input SHA-256: eae7f191db3d45a5b2ad601c29253794d037d61b15bf24bb6a167dcd3f42c2fe
The matrices below are the mathematical input; no physical interpretation is inferred. -/
namespace LeanPhy.Generated.AffineTrivialCE

open LeanPhy.Mathematics

def d1 : Matrix (Fin 1) (Fin 2) ℚ :=
  !![0, -1]

def d2 : Matrix (Fin 0) (Fin 1) ℚ :=
  0

def project : Matrix (Fin 0) (Fin 1) ℚ :=
  0

def represent : Matrix (Fin 1) (Fin 0) ℚ :=
  0

def primitive : Matrix (Fin 2) (Fin 1) ℚ :=
  !![0;
    -1]

def correction : Matrix (Fin 1) (Fin 0) ℚ :=
  0

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

theorem exact_iff (x : Fin 1 → ℚ) (hx : d2.toLin' x = 0) :
    (∃ a, d1.toLin' a = x) ↔ project.toLin' x = 0 :=
  certificate.toReduction.exact_iff x hx

end LeanPhy.Generated.AffineTrivialCE

/- The following namespace proves that the matrices above compute the actual
Lie H2 of the declared structure constants and coefficient representation. -/
namespace LeanPhy.Generated.AffineTrivial

-- Three nested linear maps with vector coefficients need this elaboration depth.
set_option maxSynthPendingDepth 5

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates

abbrev Space := Fin 2 → ℚ
abbrev Coeff := Fin 1 → ℚ

def bracket (x y : Space) : Space := ![0, (1) * (x 0 * y 1 - x 1 * y 0)]

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

def action (x : Space) (v : Coeff) : Coeff := ![0]

def coefficients : LeanPhy.Mathematics.LieModule algebra Coeff where
  act := action
  act_add_left' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  act_smul_left' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  act_add_right' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  act_smul_right' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  bracket_act' := by intros; ext r; fin_cases r <;> simp [algebra, bracket, action] <;> ring

abbrev C2 := LieCochain2 algebra coefficients

def oneValues (φ : Space →ₗ[ℚ] Coeff) : Fin 2 → ℚ := ![φ (e 0) 0, φ (e 1) 0]

def oneFrom (a : Fin 2 → ℚ) : Space →ₗ[ℚ] Coeff where
  toFun x := ![a 0 * x 0 + a 1 * x 1]
  map_add' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul' := by intros; ext r; fin_cases r <;> simp <;> ring

noncomputable def oneCoordinates : (Space →ₗ[ℚ] Coeff) ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun := oneValues
  invFun := oneFrom
  left_inv φ := by
    apply (Pi.basisFun ℚ (Fin 2)).ext
    intro i
    ext r
    fin_cases i <;> fin_cases r <;> simp [oneFrom, oneValues, e, Pi.basisFun_apply]
  right_inv a := by
    ext r
    fin_cases r <;> simp [oneFrom, oneValues, e]
  map_add' := by intros; ext r; fin_cases r <;> simp [oneValues]
  map_smul' := by intros; ext r; fin_cases r <;> simp [oneValues]

def twoValues (ω : C2) : Fin 1 → ℚ := ![ω (e 0) (e 1) 0]

def twoFrom (a : Fin 1 → ℚ) : C2 where
  eval x y := ![a 0 * (x 0 * y 1 - x 1 * y 0)]
  map_add_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_add_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  alternating' := by intros; ext r; fin_cases r <;> dsimp <;> ring

noncomputable def twoCoordinates : C2 ≃ₗ[ℚ] (Fin 1 → ℚ) where
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

def readThird : (Space →ₗ[ℚ] Space →ₗ[ℚ] Space →ₗ[ℚ] Coeff) →ₗ[ℚ] (Fin 0 → ℚ) where
  toFun t := ![]
  map_add' := by intros; ext r; fin_cases r <;> rfl
  map_smul' := by intros; ext r; fin_cases r <;> rfl

theorem readThird_detect (ω : C2) (hz : readThird (differential2 coefficients ω) = 0) :
    differential2 coefficients ω = 0 := by

  apply differential2_eq_zero_of_increasing
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hij <;> norm_num at hjk
  all_goals first | omega

theorem differential1_coordinates (φ : Space →ₗ[ℚ] Coeff) :
    twoCoordinates (differential1 coefficients φ) = AffineTrivialCE.d1.toLin' (oneCoordinates φ) := by
  obtain ⟨a, rfl⟩ := oneCoordinates.symm.surjective φ
  rw [oneCoordinates.apply_symm_apply]
  change twoValues (differential1 coefficients (oneFrom a)) = AffineTrivialCE.d1.toLin' a
  ext r
  fin_cases r <;>
    simp [twoValues, differential1, coefficients, action, algebra, bracket, oneFrom, e,
      AffineTrivialCE.d1, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem differential2_coordinates (ω : C2) :
    AffineTrivialCE.d2.toLin' (twoCoordinates ω) = readThird (differential2 coefficients ω) := by
  obtain ⟨a, rfl⟩ := twoCoordinates.symm.surjective ω
  rw [twoCoordinates.apply_symm_apply]
  change AffineTrivialCE.d2.toLin' a = readThird (differential2 coefficients (twoFrom a))
  ext r
  fin_cases r <;>
    simp [readThird, differential2_apply, coefficients, action, algebra, bracket, twoFrom, e,
      AffineTrivialCE.d2, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

noncomputable def reduction : Reduction coefficients (Fin 0 → ℚ) :=
  AffineTrivialCE.certificate.toReduction.transport oneCoordinates twoCoordinates readThird
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

end LeanPhy.Generated.AffineTrivial
