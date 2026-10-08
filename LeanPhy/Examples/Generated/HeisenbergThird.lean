import LeanPhy.Mathematics.FiniteLieCohomology3
import LeanPhy.Mathematics.LieDeformationObstruction
import LeanPhy.Mathematics.LieDeformationReduction
import LeanPhy.Mathematics.FiniteLieCohomology
import Mathlib.LinearAlgebra.Dimension.Constructions

/- Generated candidate: compile with `lake env lean` before treating it as checked.
Input SHA-256: f20649361852d199e9b02d20f4b5e62df006554fcab33b654da519b5dfb79099
The matrices below are the mathematical input; no physical interpretation is inferred. -/
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace LeanPhy.Generated.HeisenbergThirdCE

open LeanPhy.Mathematics

def d1 : Matrix (Fin 9) (Fin 9) ℚ :=
  !![0, 0, 0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, -1, 0;
    1, 0, 0, 0, 1, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, -1, 0, 0]

def d2 : Matrix (Fin 3) (Fin 9) ℚ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 1, 0]

def project : Matrix (Fin 5) (Fin 9) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, -1;
    0, 1, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0]

def represent : Matrix (Fin 9) (Fin 5) ℚ :=
  !![1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 0, 0, 0;
    0, 0, 0, 0, -1;
    0, 0, 1, 0, 0;
    0, 0, 0, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1;
    0, 0, 0, 0, 0]

def primitive : Matrix (Fin 9) (Fin 9) ℚ :=
  !![0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0]

def correction : Matrix (Fin 9) (Fin 3) ℚ :=
  !![0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 1;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0]

def certificate : MatrixCohomologyReduction d1 d2 5 where
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
    CohomologyReduction.Cohomology d1.toLin' d2.toLin' ≃ₗ[ℚ] (Fin 5 → ℚ) :=
  certificate.toReduction.quotientEquiv

theorem exact_iff (x : Fin 9 → ℚ) (hx : d2.toLin' x = 0) :
    (∃ a, d1.toLin' a = x) ↔ project.toLin' x = 0 :=
  certificate.toReduction.exact_iff x hx

end LeanPhy.Generated.HeisenbergThirdCE

/- The following namespace proves that the matrices above compute the actual
Lie H2 of the declared structure constants and coefficient representation. -/
namespace LeanPhy.Generated.HeisenbergThird

-- Three nested linear maps with vector coefficients need this elaboration depth.
set_option maxSynthPendingDepth 5

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates

abbrev Space := Fin 3 → ℚ
abbrev Coeff := Fin 3 → ℚ

def bracket (x y : Space) : Space := ![0, 0, (1) * (x 0 * y 1 - x 1 * y 0)]

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
    twoCoordinates (differential1 coefficients φ) = HeisenbergThirdCE.d1.toLin' (oneCoordinates φ) := by
  obtain ⟨a, rfl⟩ := oneCoordinates.symm.surjective φ
  rw [oneCoordinates.apply_symm_apply]
  change twoValues (differential1 coefficients (oneFrom a)) = HeisenbergThirdCE.d1.toLin' a
  ext r
  fin_cases r <;>
    simp [twoValues, differential1, coefficients, adjointLieModule, action, algebra, bracket, oneFrom, e,
      HeisenbergThirdCE.d1, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem differential2_coordinates (ω : C2) :
    HeisenbergThirdCE.d2.toLin' (twoCoordinates ω) = readThird (differential2 coefficients ω) := by
  obtain ⟨a, rfl⟩ := twoCoordinates.symm.surjective ω
  rw [twoCoordinates.apply_symm_apply]
  change HeisenbergThirdCE.d2.toLin' a = readThird (differential2 coefficients (twoFrom a))
  ext r
  fin_cases r <;>
    simp [readThird, differential2_apply, coefficients, adjointLieModule, action, algebra, bracket, twoFrom, e,
      HeisenbergThirdCE.d2, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

noncomputable def reduction : Reduction coefficients (Fin 5 → ℚ) :=
  HeisenbergThirdCE.certificate.toReduction.transport oneCoordinates twoCoordinates readThird
    differential1_coordinates differential2_coordinates readThird_detect

noncomputable def h2Equiv : H2 coefficients ≃ₗ[ℚ] (Fin 5 → ℚ) := reduction.h2Equiv coefficients

theorem h2_finrank : Module.finrank ℚ (H2 coefficients) = 5 := by
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

end LeanPhy.Generated.HeisenbergThird

namespace LeanPhy.Generated.HeisenbergThirdThirdCE

open LeanPhy.Mathematics

def d1 : Matrix (Fin 3) (Fin 9) ℚ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 1, 0]

def d2 : Matrix (Fin 0) (Fin 3) ℚ :=
  0

def project : Matrix (Fin 2) (Fin 3) ℚ :=
  !![1, 0, 0;
    0, 1, 0]

def represent : Matrix (Fin 3) (Fin 2) ℚ :=
  !![1, 0;
    0, 1;
    0, 0]

def primitive : Matrix (Fin 9) (Fin 3) ℚ :=
  !![0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 1;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0]

def correction : Matrix (Fin 3) (Fin 0) ℚ :=
  0

def certificate : MatrixCohomologyReduction d1 d2 2 where
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
    CohomologyReduction.Cohomology d1.toLin' d2.toLin' ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  certificate.toReduction.quotientEquiv

theorem exact_iff (x : Fin 3 → ℚ) (hx : d2.toLin' x = 0) :
    (∃ a, d1.toLin' a = x) ↔ project.toLin' x = 0 :=
  certificate.toReduction.exact_iff x hx

end LeanPhy.Generated.HeisenbergThirdThirdCE

namespace LeanPhy.Generated.HeisenbergThird
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates
set_option maxSynthPendingDepth 7
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

abbrev C3 := LieCochain3 algebra coefficients

def threeExpr (a : Fin 3 → ℚ) (x y z : Space) : Coeff := ![a 0 * (x 0 * y 1 * z 2 - x 0 * y 2 * z 1 - x 1 * y 0 * z 2 + x 1 * y 2 * z 0 + x 2 * y 0 * z 1 - x 2 * y 1 * z 0), a 1 * (x 0 * y 1 * z 2 - x 0 * y 2 * z 1 - x 1 * y 0 * z 2 + x 1 * y 2 * z 0 + x 2 * y 0 * z 1 - x 2 * y 1 * z 0), a 2 * (x 0 * y 1 * z 2 - x 0 * y 2 * z 1 - x 1 * y 0 * z 2 + x 1 * y 2 * z 0 + x 2 * y 0 * z 1 - x 2 * y 1 * z 0)]

def threeLinear (a : Fin 3 → ℚ) : Space →ₗ[ℚ] Space →ₗ[ℚ] Space →ₗ[ℚ] Coeff where
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

def threeFrom (a : Fin 3 → ℚ) : C3 := ⟨threeLinear a,by
  constructor
  · intro x z; change threeExpr a x x z = 0
    ext r; fin_cases r <;> dsimp [threeExpr] <;> ring
  · intro x y; change threeExpr a x y y = 0
    ext r; fin_cases r <;> dsimp [threeExpr] <;> ring⟩

def threeValues (t : C3) : Fin 3 → ℚ := readThird t.val

/-- Coordinates cover all alternating three-cochains. -/
noncomputable def threeCoordinates : C3 ≃ₗ[ℚ] (Fin 3 → ℚ) where
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

def readFourth : (Space →ₗ[ℚ] Space →ₗ[ℚ] Space →ₗ[ℚ] Space →ₗ[ℚ] Coeff) →ₗ[ℚ] (Fin 0 → ℚ) where
  toFun t := ![]
  map_add' := by intros; ext r; fin_cases r <;> rfl
  map_smul' := by intros; ext r; fin_cases r <;> rfl

theorem readFourth_detect (t : C3) (hz : readFourth (differential3 coefficients t) = 0) :
    differential3 coefficients t = 0 := by

  apply differential3_eq_zero_of_increasing
  intro i j k l hij hjk hkl
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> fin_cases k <;> norm_num at hjk <;> fin_cases l <;> norm_num at hkl
  all_goals first | omega

theorem differential2_third_coordinates (ω : C2) :
    threeCoordinates (differential2ToThree coefficients ω) = HeisenbergThirdThirdCE.d1.toLin' (twoCoordinates ω) :=
  (differential2_coordinates ω).symm

theorem differential3_coordinates (t : C3) :
    HeisenbergThirdThirdCE.d2.toLin' (threeCoordinates t) = readFourth (differential3 coefficients t) := by
  obtain ⟨a,rfl⟩ := threeCoordinates.symm.surjective t
  rw [threeCoordinates.apply_symm_apply]
  change HeisenbergThirdThirdCE.d2.toLin' a = readFourth (differential3 coefficients (threeFrom a))
  ext r; fin_cases r <;>
    simp [readFourth,differential3_apply,differential3Expr,coefficients,adjointLieModule,action,algebra,
      bracket,threeFrom,threeLinear,threeExpr,e,HeisenbergThirdThirdCE.d2,Matrix.toLin'_apply,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

noncomputable def thirdReduction : ThirdReduction coefficients (Fin 2 → ℚ) :=
  HeisenbergThirdThirdCE.certificate.toReduction.transport twoCoordinates threeCoordinates readFourth
    differential2_third_coordinates differential3_coordinates readFourth_detect

noncomputable def h3Equiv : H3 coefficients ≃ₗ[ℚ] (Fin 2 → ℚ) := thirdReduction.h3Equiv coefficients

theorem h3_finrank : Module.finrank ℚ (H3 coefficients) = 2 := by
  rw [h3Equiv.finrank_eq]; simp

theorem third_boundary_iff (t : C3) (ht : IsThreeCocycle coefficients t) :
    IsThreeCoboundary coefficients t ↔ thirdReduction.project t = 0 := thirdReduction.exact_iff t ht

theorem third_normal_form (t : C3) (ht : IsThreeCocycle coefficients t) :
    differential2ToThree coefficients (thirdReduction.primitive t) +
      thirdReduction.represent (thirdReduction.project t) = t := thirdReduction.normal_form t ht

/-- Coordinates of the intrinsic obstruction, with its closedness proved generically. -/
noncomputable def intrinsicObstruction (ω : C2) := thirdReduction.project (LieDeformation.obstructionCochain ω)

theorem intrinsicObstruction_class (ω : C2) (hω : IsTwoCocycle coefficients ω) :
    h3Equiv (LieDeformation.obstructionClass ω hω) = intrinsicObstruction ω := rfl

theorem intrinsic_extension_iff (ω : C2) (hω : IsTwoCocycle coefficients ω) :
    LieDeformation.SecondExtendable ω ↔ intrinsicObstruction ω = 0 := by
  rw [LieDeformation.secondExtendable_iff_obstructionClass_zero ω hω]
  exact (map_eq_zero_iff h3Equiv h3Equiv.injective).symm

/-- A concrete correction obtained from the H³ reduction primitive. -/
noncomputable def intrinsicCorrection (ω : C2) : C2 :=
  LieDeformation.ThirdReduction.correction thirdReduction ω

theorem intrinsicCorrection_cancels (ω : C2) (hω : IsTwoCocycle coefficients ω)
    (h : intrinsicObstruction ω = 0) : LieDeformation.secondResidual ω (intrinsicCorrection ω) = 0 :=
  LieDeformation.ThirdReduction.correction_cancels thirdReduction ω hω h

noncomputable def intrinsicModel (ω : C2) (hω : IsTwoCocycle coefficients ω)
    (h : intrinsicObstruction ω = 0) : LeanPhy.Mathematics.LieAlgebra ℚ (Space × Space × Space) :=
  LieDeformation.ThirdReduction.model thirdReduction ω hω h

theorem intrinsicModel_bracket (ω : C2) (hω : IsTwoCocycle coefficients ω)
    (h : intrinsicObstruction ω = 0) :
    (intrinsicModel ω hω h).bracket = LieDeformation.secondBracket ω (intrinsicCorrection ω) := rfl

end LeanPhy.Generated.HeisenbergThird
