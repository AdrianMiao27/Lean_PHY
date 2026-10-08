import LeanPhy.Mathematics.FiniteLieCohomology3
import LeanPhy.Mathematics.LieDeformationObstruction
import LeanPhy.Mathematics.FiniteLieCohomology
import Mathlib.LinearAlgebra.Dimension.Constructions

/- Generated candidate: compile with `lake env lean` before treating it as checked.
Input SHA-256: 9031e3f00adf35dfadb5d35637dca838accc9d8dc7e5554a1a62756ff393d4e8
The matrices below are the mathematical input; no physical interpretation is inferred. -/
namespace LeanPhy.Generated.AffineFourThirdCE

open LeanPhy.Mathematics

def d1 : Matrix (Fin 6) (Fin 4) ℚ :=
  !![0, -1, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]

def d2 : Matrix (Fin 4) (Fin 6) ℚ :=
  !![0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0]

def project : Matrix (Fin 3) (Fin 6) ℚ :=
  !![0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1]

def represent : Matrix (Fin 6) (Fin 3) ℚ :=
  !![0, 0, 0;
    1, 0, 0;
    0, 1, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 1]

def primitive : Matrix (Fin 4) (Fin 6) ℚ :=
  !![0, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0]

def correction : Matrix (Fin 6) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    -1, 0, 0, 0;
    0, -1, 0, 0;
    0, 0, 0, 0]

def certificate : MatrixCohomologyReduction d1 d2 3 where
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
    CohomologyReduction.Cohomology d1.toLin' d2.toLin' ≃ₗ[ℚ] (Fin 3 → ℚ) :=
  certificate.toReduction.quotientEquiv

theorem exact_iff (x : Fin 6 → ℚ) (hx : d2.toLin' x = 0) :
    (∃ a, d1.toLin' a = x) ↔ project.toLin' x = 0 :=
  certificate.toReduction.exact_iff x hx

end LeanPhy.Generated.AffineFourThirdCE

/- The following namespace proves that the matrices above compute the actual
Lie H2 of the declared structure constants and coefficient representation. -/
namespace LeanPhy.Generated.AffineFourThird

-- Three nested linear maps with vector coefficients need this elaboration depth.
set_option maxSynthPendingDepth 5

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates

abbrev Space := Fin 4 → ℚ
abbrev Coeff := Fin 1 → ℚ

def bracket (x y : Space) : Space := ![0, (1) * (x 0 * y 1 - x 1 * y 0), 0, 0]

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

def oneValues (φ : Space →ₗ[ℚ] Coeff) : Fin 4 → ℚ := ![φ (e 0) 0, φ (e 1) 0, φ (e 2) 0, φ (e 3) 0]

def oneFrom (a : Fin 4 → ℚ) : Space →ₗ[ℚ] Coeff where
  toFun x := ![a 0 * x 0 + a 1 * x 1 + a 2 * x 2 + a 3 * x 3]
  map_add' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul' := by intros; ext r; fin_cases r <;> simp <;> ring

noncomputable def oneCoordinates : (Space →ₗ[ℚ] Coeff) ≃ₗ[ℚ] (Fin 4 → ℚ) where
  toFun := oneValues
  invFun := oneFrom
  left_inv φ := by
    apply (Pi.basisFun ℚ (Fin 4)).ext
    intro i
    ext r
    fin_cases i <;> fin_cases r <;> simp [oneFrom, oneValues, e, Pi.basisFun_apply]
  right_inv a := by
    ext r
    fin_cases r <;> simp [oneFrom, oneValues, e]
  map_add' := by intros; ext r; fin_cases r <;> simp [oneValues]
  map_smul' := by intros; ext r; fin_cases r <;> simp [oneValues]

def twoValues (ω : C2) : Fin 6 → ℚ := ![ω (e 0) (e 1) 0, ω (e 0) (e 2) 0, ω (e 0) (e 3) 0, ω (e 1) (e 2) 0, ω (e 1) (e 3) 0, ω (e 2) (e 3) 0]

def twoFrom (a : Fin 6 → ℚ) : C2 where
  eval x y := ![a 0 * (x 0 * y 1 - x 1 * y 0) + a 1 * (x 0 * y 2 - x 2 * y 0) + a 2 * (x 0 * y 3 - x 3 * y 0) + a 3 * (x 1 * y 2 - x 2 * y 1) + a 4 * (x 1 * y 3 - x 3 * y 1) + a 5 * (x 2 * y 3 - x 3 * y 2)]
  map_add_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_add_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  alternating' := by intros; ext r; fin_cases r <;> dsimp <;> ring

noncomputable def twoCoordinates : C2 ≃ₗ[ℚ] (Fin 6 → ℚ) where
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

def readThird : (Space →ₗ[ℚ] Space →ₗ[ℚ] Space →ₗ[ℚ] Coeff) →ₗ[ℚ] (Fin 4 → ℚ) where
  toFun t := ![t (e 0) (e 1) (e 2) 0, t (e 0) (e 1) (e 3) 0, t (e 0) (e 2) (e 3) 0, t (e 1) (e 2) (e 3) 0]
  map_add' := by intros; ext r; fin_cases r <;> rfl
  map_smul' := by intros; ext r; fin_cases r <;> rfl

theorem readThird_detect (ω : C2) (hz : readThird (differential2 coefficients ω) = 0) :
    differential2 coefficients ω = 0 := by
  have sample_0_1_2 : differential2 coefficients ω (e 0) (e 1) (e 2) = 0 := by
    ext r
    fin_cases r
    · exact congrFun hz 0
  have sample_0_1_3 : differential2 coefficients ω (e 0) (e 1) (e 3) = 0 := by
    ext r
    fin_cases r
    · exact congrFun hz 1
  have sample_0_2_3 : differential2 coefficients ω (e 0) (e 2) (e 3) = 0 := by
    ext r
    fin_cases r
    · exact congrFun hz 2
  have sample_1_2_3 : differential2 coefficients ω (e 1) (e 2) (e 3) = 0 := by
    ext r
    fin_cases r
    · exact congrFun hz 3
  apply differential2_eq_zero_of_increasing
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hij <;> norm_num at hjk
  all_goals first | omega | exact sample_0_1_2 | exact sample_0_1_3 | exact sample_0_2_3 | exact sample_1_2_3

theorem differential1_coordinates (φ : Space →ₗ[ℚ] Coeff) :
    twoCoordinates (differential1 coefficients φ) = AffineFourThirdCE.d1.toLin' (oneCoordinates φ) := by
  obtain ⟨a, rfl⟩ := oneCoordinates.symm.surjective φ
  rw [oneCoordinates.apply_symm_apply]
  change twoValues (differential1 coefficients (oneFrom a)) = AffineFourThirdCE.d1.toLin' a
  ext r
  fin_cases r <;>
    simp [twoValues, differential1, coefficients, action, algebra, bracket, oneFrom, e,
      AffineFourThirdCE.d1, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem differential2_coordinates (ω : C2) :
    AffineFourThirdCE.d2.toLin' (twoCoordinates ω) = readThird (differential2 coefficients ω) := by
  obtain ⟨a, rfl⟩ := twoCoordinates.symm.surjective ω
  rw [twoCoordinates.apply_symm_apply]
  change AffineFourThirdCE.d2.toLin' a = readThird (differential2 coefficients (twoFrom a))
  ext r
  fin_cases r <;>
    simp [readThird, differential2_apply, coefficients, action, algebra, bracket, twoFrom, e,
      AffineFourThirdCE.d2, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

noncomputable def reduction : Reduction coefficients (Fin 3 → ℚ) :=
  AffineFourThirdCE.certificate.toReduction.transport oneCoordinates twoCoordinates readThird
    differential1_coordinates differential2_coordinates readThird_detect

noncomputable def h2Equiv : H2 coefficients ≃ₗ[ℚ] (Fin 3 → ℚ) := reduction.h2Equiv coefficients

theorem h2_finrank : Module.finrank ℚ (H2 coefficients) = 3 := by
  rw [h2Equiv.finrank_eq]
  simp

theorem boundary_iff (ω : C2) (hω : IsTwoCocycle coefficients ω) :
    IsTwoCoboundary coefficients ω ↔ reduction.project ω = 0 :=
  reduction.exact_iff ω hω

theorem normal_form (ω : C2) (hω : IsTwoCocycle coefficients ω) :
    differential1 coefficients (reduction.primitive ω) +
      reduction.represent (reduction.project ω) = ω := reduction.normal_form ω hω

end LeanPhy.Generated.AffineFourThird

namespace LeanPhy.Generated.AffineFourThirdThirdCE

open LeanPhy.Mathematics

def d1 : Matrix (Fin 4) (Fin 6) ℚ :=
  !![0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0]

def d2 : Matrix (Fin 1) (Fin 4) ℚ :=
  !![0, 0, 0, -1]

def project : Matrix (Fin 1) (Fin 4) ℚ :=
  !![0, 0, 1, 0]

def represent : Matrix (Fin 4) (Fin 1) ℚ :=
  !![0;
    0;
    1;
    0]

def primitive : Matrix (Fin 6) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    -1, 0, 0, 0;
    0, -1, 0, 0;
    0, 0, 0, 0]

def correction : Matrix (Fin 4) (Fin 1) ℚ :=
  !![0;
    0;
    0;
    -1]

def certificate : MatrixCohomologyReduction d1 d2 1 where
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
    CohomologyReduction.Cohomology d1.toLin' d2.toLin' ≃ₗ[ℚ] (Fin 1 → ℚ) :=
  certificate.toReduction.quotientEquiv

theorem exact_iff (x : Fin 4 → ℚ) (hx : d2.toLin' x = 0) :
    (∃ a, d1.toLin' a = x) ↔ project.toLin' x = 0 :=
  certificate.toReduction.exact_iff x hx

end LeanPhy.Generated.AffineFourThirdThirdCE

namespace LeanPhy.Generated.AffineFourThird
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates
set_option maxSynthPendingDepth 7
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

abbrev C3 := LieCochain3 algebra coefficients

def threeExpr (a : Fin 4 → ℚ) (x y z : Space) : Coeff := ![a 0 * (x 0 * y 1 * z 2 - x 0 * y 2 * z 1 - x 1 * y 0 * z 2 + x 1 * y 2 * z 0 + x 2 * y 0 * z 1 - x 2 * y 1 * z 0) + a 1 * (x 0 * y 1 * z 3 - x 0 * y 3 * z 1 - x 1 * y 0 * z 3 + x 1 * y 3 * z 0 + x 3 * y 0 * z 1 - x 3 * y 1 * z 0) + a 2 * (x 0 * y 2 * z 3 - x 0 * y 3 * z 2 - x 2 * y 0 * z 3 + x 2 * y 3 * z 0 + x 3 * y 0 * z 2 - x 3 * y 2 * z 0) + a 3 * (x 1 * y 2 * z 3 - x 1 * y 3 * z 2 - x 2 * y 1 * z 3 + x 2 * y 3 * z 1 + x 3 * y 1 * z 2 - x 3 * y 2 * z 1)]

def threeLinear (a : Fin 4 → ℚ) : Space →ₗ[ℚ] Space →ₗ[ℚ] Space →ₗ[ℚ] Coeff where
  toFun x := {
    toFun y := {
      toFun z := threeExpr a x y z
      map_add' := by intros; ext r; fin_cases r <;> simp [threeExpr] <;> ring
      map_smul' := by intros; ext r; fin_cases r <;> simp [threeExpr] <;> ring }
    map_add' := by
      intro y₁ y₂; apply LinearMap.ext; intro z
      change threeExpr a x (y₁+y₂) z = threeExpr a x y₁ z + threeExpr a x y₂ z
      ext r; fin_cases r <;> simp [threeExpr] <;> ring
    map_smul' := by
      intro r y; apply LinearMap.ext; intro z
      change threeExpr a x (r • y) z = r • threeExpr a x y z
      ext r; fin_cases r <;> simp [threeExpr] <;> ring }
  map_add' := by
    intro x₁ x₂; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
    change threeExpr a (x₁+x₂) y z = threeExpr a x₁ y z + threeExpr a x₂ y z
    ext r; fin_cases r <;> simp [threeExpr] <;> ring
  map_smul' := by
    intro r x; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
    change threeExpr a (r • x) y z = r • threeExpr a x y z
    ext r; fin_cases r <;> simp [threeExpr] <;> ring

def threeFrom (a : Fin 4 → ℚ) : C3 := ⟨threeLinear a,by
  constructor
  · intro x z; change threeExpr a x x z = 0
    ext r; fin_cases r <;> dsimp [threeExpr] <;> ring
  · intro x y; change threeExpr a x y y = 0
    ext r; fin_cases r <;> dsimp [threeExpr] <;> ring⟩

def threeValues (t : C3) : Fin 4 → ℚ := readThird t.val

/-- Coordinates cover all alternating three-cochains. -/
noncomputable def threeCoordinates : C3 ≃ₗ[ℚ] (Fin 4 → ℚ) where
  toFun := threeValues
  invFun := threeFrom
  left_inv t := by
    apply three_ext_increasing
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> fin_cases k <;> norm_num at hjk
    all_goals ext r; fin_cases r <;> simp [threeFrom,threeLinear,threeExpr,threeValues,readThird,e]
  right_inv a := by
    ext r; fin_cases r <;> simp [threeValues,readThird,threeFrom,threeLinear,threeExpr,e]
  map_add' := by intros; ext r; fin_cases r <;> rfl
  map_smul' := by intros; ext r; fin_cases r <;> rfl

def readFourth : (Space →ₗ[ℚ] Space →ₗ[ℚ] Space →ₗ[ℚ] Space →ₗ[ℚ] Coeff) →ₗ[ℚ] (Fin 1 → ℚ) where
  toFun t := ![t (e 0) (e 1) (e 2) (e 3) 0]
  map_add' := by intros; ext r; fin_cases r <;> rfl
  map_smul' := by intros; ext r; fin_cases r <;> rfl

theorem readFourth_detect (t : C3) (hz : readFourth (differential3 coefficients t) = 0) :
    differential3 coefficients t = 0 := by
  have sample_0_1_2_3 : differential3 coefficients t (e 0) (e 1) (e 2) (e 3) = 0 := by
    ext r
    fin_cases r
    · exact congrFun hz 0
  apply differential3_eq_zero_of_increasing
  intro i j k l hij hjk hkl
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> fin_cases k <;> norm_num at hjk <;> fin_cases l <;> norm_num at hkl
  all_goals first | omega | exact sample_0_1_2_3

theorem differential2_third_coordinates (ω : C2) :
    threeCoordinates (differential2ToThree coefficients ω) = AffineFourThirdThirdCE.d1.toLin' (twoCoordinates ω) :=
  (differential2_coordinates ω).symm

theorem differential3_coordinates (t : C3) :
    AffineFourThirdThirdCE.d2.toLin' (threeCoordinates t) = readFourth (differential3 coefficients t) := by
  obtain ⟨a,rfl⟩ := threeCoordinates.symm.surjective t
  rw [threeCoordinates.apply_symm_apply]
  change AffineFourThirdThirdCE.d2.toLin' a = readFourth (differential3 coefficients (threeFrom a))
  ext r; fin_cases r <;>
    simp [readFourth,differential3_apply,differential3Expr,coefficients,adjointLieModule,action,algebra,
      bracket,threeFrom,threeLinear,threeExpr,e,AffineFourThirdThirdCE.d2,Matrix.toLin'_apply,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

noncomputable def thirdReduction : ThirdReduction coefficients (Fin 1 → ℚ) :=
  AffineFourThirdThirdCE.certificate.toReduction.transport twoCoordinates threeCoordinates readFourth
    differential2_third_coordinates differential3_coordinates readFourth_detect

noncomputable def h3Equiv : H3 coefficients ≃ₗ[ℚ] (Fin 1 → ℚ) := thirdReduction.h3Equiv coefficients

theorem h3_finrank : Module.finrank ℚ (H3 coefficients) = 1 := by
  rw [h3Equiv.finrank_eq]; simp

theorem third_boundary_iff (t : C3) (ht : IsThreeCocycle coefficients t) :
    IsThreeCoboundary coefficients t ↔ thirdReduction.project t = 0 := thirdReduction.exact_iff t ht

theorem third_normal_form (t : C3) (ht : IsThreeCocycle coefficients t) :
    differential2ToThree coefficients (thirdReduction.primitive t) +
      thirdReduction.represent (thirdReduction.project t) = t := thirdReduction.normal_form t ht

end LeanPhy.Generated.AffineFourThird
