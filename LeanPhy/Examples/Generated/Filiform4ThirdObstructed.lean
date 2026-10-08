import LeanPhy.Mathematics.LieDeformationThirdSearch
/- Generated proof candidate. Input SHA-256: f17dd07acb3be5dda78cf30e4789d1a8e1cc734cf99ecc09d24970abe68b1ad0. Compile the entire file with Lean. -/
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
namespace LeanPhy.Generated.Filiform4ThirdObstructedCE
def d1 : Matrix (Fin 24) (Fin 16) ℚ := !![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0]
def d2 : Matrix (Fin 16) (Fin 24) ℚ := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
end LeanPhy.Generated.Filiform4ThirdObstructedCE
namespace LeanPhy.Generated.Filiform4ThirdObstructedThirdCE
def d1 : Matrix (Fin 16) (Fin 24) ℚ := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
def d2 : Matrix (Fin 4) (Fin 16) ℚ := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
end LeanPhy.Generated.Filiform4ThirdObstructedThirdCE
namespace LeanPhy.Generated.Filiform4ThirdObstructed

-- Three nested linear maps with vector coefficients need this elaboration depth.
set_option maxSynthPendingDepth 5

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates

abbrev Space := Fin 4 → ℚ
abbrev Coeff := Fin 4 → ℚ

def bracket (x y : Space) : Space := ![0, 0, (1) * (x 0 * y 1 - x 1 * y 0), (1) * (x 0 * y 2 - x 2 * y 0)]

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

def oneValues (φ : Space →ₗ[ℚ] Coeff) : Fin 16 → ℚ := ![φ (e 0) 0, φ (e 0) 1, φ (e 0) 2, φ (e 0) 3, φ (e 1) 0, φ (e 1) 1, φ (e 1) 2, φ (e 1) 3, φ (e 2) 0, φ (e 2) 1, φ (e 2) 2, φ (e 2) 3, φ (e 3) 0, φ (e 3) 1, φ (e 3) 2, φ (e 3) 3]

def oneFrom (a : Fin 16 → ℚ) : Space →ₗ[ℚ] Coeff where
  toFun x := ![a 0 * x 0 + a 4 * x 1 + a 8 * x 2 + a 12 * x 3, a 1 * x 0 + a 5 * x 1 + a 9 * x 2 + a 13 * x 3, a 2 * x 0 + a 6 * x 1 + a 10 * x 2 + a 14 * x 3, a 3 * x 0 + a 7 * x 1 + a 11 * x 2 + a 15 * x 3]
  map_add' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul' := by intros; ext r; fin_cases r <;> simp <;> ring

noncomputable def oneCoordinates : (Space →ₗ[ℚ] Coeff) ≃ₗ[ℚ] (Fin 16 → ℚ) where
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

def twoValues (ω : C2) : Fin 24 → ℚ := ![ω (e 0) (e 1) 0, ω (e 0) (e 1) 1, ω (e 0) (e 1) 2, ω (e 0) (e 1) 3, ω (e 0) (e 2) 0, ω (e 0) (e 2) 1, ω (e 0) (e 2) 2, ω (e 0) (e 2) 3, ω (e 0) (e 3) 0, ω (e 0) (e 3) 1, ω (e 0) (e 3) 2, ω (e 0) (e 3) 3, ω (e 1) (e 2) 0, ω (e 1) (e 2) 1, ω (e 1) (e 2) 2, ω (e 1) (e 2) 3, ω (e 1) (e 3) 0, ω (e 1) (e 3) 1, ω (e 1) (e 3) 2, ω (e 1) (e 3) 3, ω (e 2) (e 3) 0, ω (e 2) (e 3) 1, ω (e 2) (e 3) 2, ω (e 2) (e 3) 3]

def twoFrom (a : Fin 24 → ℚ) : C2 where
  eval x y := ![a 0 * (x 0 * y 1 - x 1 * y 0) + a 4 * (x 0 * y 2 - x 2 * y 0) + a 8 * (x 0 * y 3 - x 3 * y 0) + a 12 * (x 1 * y 2 - x 2 * y 1) + a 16 * (x 1 * y 3 - x 3 * y 1) + a 20 * (x 2 * y 3 - x 3 * y 2), a 1 * (x 0 * y 1 - x 1 * y 0) + a 5 * (x 0 * y 2 - x 2 * y 0) + a 9 * (x 0 * y 3 - x 3 * y 0) + a 13 * (x 1 * y 2 - x 2 * y 1) + a 17 * (x 1 * y 3 - x 3 * y 1) + a 21 * (x 2 * y 3 - x 3 * y 2), a 2 * (x 0 * y 1 - x 1 * y 0) + a 6 * (x 0 * y 2 - x 2 * y 0) + a 10 * (x 0 * y 3 - x 3 * y 0) + a 14 * (x 1 * y 2 - x 2 * y 1) + a 18 * (x 1 * y 3 - x 3 * y 1) + a 22 * (x 2 * y 3 - x 3 * y 2), a 3 * (x 0 * y 1 - x 1 * y 0) + a 7 * (x 0 * y 2 - x 2 * y 0) + a 11 * (x 0 * y 3 - x 3 * y 0) + a 15 * (x 1 * y 2 - x 2 * y 1) + a 19 * (x 1 * y 3 - x 3 * y 1) + a 23 * (x 2 * y 3 - x 3 * y 2)]
  map_add_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_add_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  alternating' := by intros; ext r; fin_cases r <;> dsimp <;> ring

noncomputable def twoCoordinates : C2 ≃ₗ[ℚ] (Fin 24 → ℚ) where
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

def readThird : (Space →ₗ[ℚ] Space →ₗ[ℚ] Space →ₗ[ℚ] Coeff) →ₗ[ℚ] (Fin 16 → ℚ) where
  toFun t := ![t (e 0) (e 1) (e 2) 0, t (e 0) (e 1) (e 2) 1, t (e 0) (e 1) (e 2) 2, t (e 0) (e 1) (e 2) 3, t (e 0) (e 1) (e 3) 0, t (e 0) (e 1) (e 3) 1, t (e 0) (e 1) (e 3) 2, t (e 0) (e 1) (e 3) 3, t (e 0) (e 2) (e 3) 0, t (e 0) (e 2) (e 3) 1, t (e 0) (e 2) (e 3) 2, t (e 0) (e 2) (e 3) 3, t (e 1) (e 2) (e 3) 0, t (e 1) (e 2) (e 3) 1, t (e 1) (e 2) (e 3) 2, t (e 1) (e 2) (e 3) 3]
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
    · exact congrFun hz 3
  have sample_0_1_3 : differential2 coefficients ω (e 0) (e 1) (e 3) = 0 := by
    ext r
    fin_cases r
    · exact congrFun hz 4
    · exact congrFun hz 5
    · exact congrFun hz 6
    · exact congrFun hz 7
  have sample_0_2_3 : differential2 coefficients ω (e 0) (e 2) (e 3) = 0 := by
    ext r
    fin_cases r
    · exact congrFun hz 8
    · exact congrFun hz 9
    · exact congrFun hz 10
    · exact congrFun hz 11
  have sample_1_2_3 : differential2 coefficients ω (e 1) (e 2) (e 3) = 0 := by
    ext r
    fin_cases r
    · exact congrFun hz 12
    · exact congrFun hz 13
    · exact congrFun hz 14
    · exact congrFun hz 15
  apply differential2_eq_zero_of_increasing
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hij <;> norm_num at hjk
  all_goals first | omega | exact sample_0_1_2 | exact sample_0_1_3 | exact sample_0_2_3 | exact sample_1_2_3

theorem differential1_coordinates (φ : Space →ₗ[ℚ] Coeff) :
    twoCoordinates (differential1 coefficients φ) = Filiform4ThirdObstructedCE.d1.toLin' (oneCoordinates φ) := by
  obtain ⟨a, rfl⟩ := oneCoordinates.symm.surjective φ
  rw [oneCoordinates.apply_symm_apply]
  change twoValues (differential1 coefficients (oneFrom a)) = Filiform4ThirdObstructedCE.d1.toLin' a
  ext r
  fin_cases r <;>
    simp [twoValues, differential1, coefficients, adjointLieModule, action, algebra, bracket, oneFrom, e,
      Filiform4ThirdObstructedCE.d1, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem differential2_coordinates (ω : C2) :
    Filiform4ThirdObstructedCE.d2.toLin' (twoCoordinates ω) = readThird (differential2 coefficients ω) := by
  obtain ⟨a, rfl⟩ := twoCoordinates.symm.surjective ω
  rw [twoCoordinates.apply_symm_apply]
  change Filiform4ThirdObstructedCE.d2.toLin' a = readThird (differential2 coefficients (twoFrom a))
  ext r
  fin_cases r <;>
    simp [readThird, differential2_apply, coefficients, adjointLieModule, action, algebra, bracket, twoFrom, e,
      Filiform4ThirdObstructedCE.d2, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

set_option maxSynthPendingDepth 7
set_option maxRecDepth 4096
abbrev C3 := LieCochain3 algebra coefficients

def threeExpr (a : Fin 16 → ℚ) (x y z : Space) : Coeff := ![a 0 * (x 0 * y 1 * z 2 - x 0 * y 2 * z 1 - x 1 * y 0 * z 2 + x 1 * y 2 * z 0 + x 2 * y 0 * z 1 - x 2 * y 1 * z 0) + a 4 * (x 0 * y 1 * z 3 - x 0 * y 3 * z 1 - x 1 * y 0 * z 3 + x 1 * y 3 * z 0 + x 3 * y 0 * z 1 - x 3 * y 1 * z 0) + a 8 * (x 0 * y 2 * z 3 - x 0 * y 3 * z 2 - x 2 * y 0 * z 3 + x 2 * y 3 * z 0 + x 3 * y 0 * z 2 - x 3 * y 2 * z 0) + a 12 * (x 1 * y 2 * z 3 - x 1 * y 3 * z 2 - x 2 * y 1 * z 3 + x 2 * y 3 * z 1 + x 3 * y 1 * z 2 - x 3 * y 2 * z 1), a 1 * (x 0 * y 1 * z 2 - x 0 * y 2 * z 1 - x 1 * y 0 * z 2 + x 1 * y 2 * z 0 + x 2 * y 0 * z 1 - x 2 * y 1 * z 0) + a 5 * (x 0 * y 1 * z 3 - x 0 * y 3 * z 1 - x 1 * y 0 * z 3 + x 1 * y 3 * z 0 + x 3 * y 0 * z 1 - x 3 * y 1 * z 0) + a 9 * (x 0 * y 2 * z 3 - x 0 * y 3 * z 2 - x 2 * y 0 * z 3 + x 2 * y 3 * z 0 + x 3 * y 0 * z 2 - x 3 * y 2 * z 0) + a 13 * (x 1 * y 2 * z 3 - x 1 * y 3 * z 2 - x 2 * y 1 * z 3 + x 2 * y 3 * z 1 + x 3 * y 1 * z 2 - x 3 * y 2 * z 1), a 2 * (x 0 * y 1 * z 2 - x 0 * y 2 * z 1 - x 1 * y 0 * z 2 + x 1 * y 2 * z 0 + x 2 * y 0 * z 1 - x 2 * y 1 * z 0) + a 6 * (x 0 * y 1 * z 3 - x 0 * y 3 * z 1 - x 1 * y 0 * z 3 + x 1 * y 3 * z 0 + x 3 * y 0 * z 1 - x 3 * y 1 * z 0) + a 10 * (x 0 * y 2 * z 3 - x 0 * y 3 * z 2 - x 2 * y 0 * z 3 + x 2 * y 3 * z 0 + x 3 * y 0 * z 2 - x 3 * y 2 * z 0) + a 14 * (x 1 * y 2 * z 3 - x 1 * y 3 * z 2 - x 2 * y 1 * z 3 + x 2 * y 3 * z 1 + x 3 * y 1 * z 2 - x 3 * y 2 * z 1), a 3 * (x 0 * y 1 * z 2 - x 0 * y 2 * z 1 - x 1 * y 0 * z 2 + x 1 * y 2 * z 0 + x 2 * y 0 * z 1 - x 2 * y 1 * z 0) + a 7 * (x 0 * y 1 * z 3 - x 0 * y 3 * z 1 - x 1 * y 0 * z 3 + x 1 * y 3 * z 0 + x 3 * y 0 * z 1 - x 3 * y 1 * z 0) + a 11 * (x 0 * y 2 * z 3 - x 0 * y 3 * z 2 - x 2 * y 0 * z 3 + x 2 * y 3 * z 0 + x 3 * y 0 * z 2 - x 3 * y 2 * z 0) + a 15 * (x 1 * y 2 * z 3 - x 1 * y 3 * z 2 - x 2 * y 1 * z 3 + x 2 * y 3 * z 1 + x 3 * y 1 * z 2 - x 3 * y 2 * z 1)]

def threeLinear (a : Fin 16 → ℚ) : Space →ₗ[ℚ] Space →ₗ[ℚ] Space →ₗ[ℚ] Coeff where
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

def threeFrom (a : Fin 16 → ℚ) : C3 := ⟨threeLinear a,by
  constructor
  · intro x z; change threeExpr a x x z = 0
    ext r; fin_cases r <;> dsimp [threeExpr] <;> ring
  · intro x y; change threeExpr a x y y = 0
    ext r; fin_cases r <;> dsimp [threeExpr] <;> ring⟩

def threeValues (t : C3) : Fin 16 → ℚ := readThird t.val

/-- Coordinates cover all alternating three-cochains. -/
noncomputable def threeCoordinates : C3 ≃ₗ[ℚ] (Fin 16 → ℚ) where
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

def readFourth : (Space →ₗ[ℚ] Space →ₗ[ℚ] Space →ₗ[ℚ] Space →ₗ[ℚ] Coeff) →ₗ[ℚ] (Fin 4 → ℚ) where
  toFun t := ![t (e 0) (e 1) (e 2) (e 3) 0, t (e 0) (e 1) (e 2) (e 3) 1, t (e 0) (e 1) (e 2) (e 3) 2, t (e 0) (e 1) (e 2) (e 3) 3]
  map_add' := by intros; ext r; fin_cases r <;> rfl
  map_smul' := by intros; ext r; fin_cases r <;> rfl

theorem readFourth_detect (t : C3) (hz : readFourth (differential3 coefficients t) = 0) :
    differential3 coefficients t = 0 := by
  have sample_0_1_2_3 : differential3 coefficients t (e 0) (e 1) (e 2) (e 3) = 0 := by
    ext r
    fin_cases r
    · exact congrFun hz 0
    · exact congrFun hz 1
    · exact congrFun hz 2
    · exact congrFun hz 3
  apply differential3_eq_zero_of_increasing
  intro i j k l hij hjk hkl
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> fin_cases k <;> norm_num at hjk <;> fin_cases l <;> norm_num at hkl
  all_goals first | omega | exact sample_0_1_2_3

theorem differential2_third_coordinates (ω : C2) :
    threeCoordinates (differential2ToThree coefficients ω) = Filiform4ThirdObstructedThirdCE.d1.toLin' (twoCoordinates ω) :=
  (differential2_coordinates ω).symm

theorem differential3_coordinates (t : C3) :
    Filiform4ThirdObstructedThirdCE.d2.toLin' (threeCoordinates t) = readFourth (differential3 coefficients t) := by
  obtain ⟨a,rfl⟩ := threeCoordinates.symm.surjective t
  rw [threeCoordinates.apply_symm_apply]
  change Filiform4ThirdObstructedThirdCE.d2.toLin' a = readFourth (differential3 coefficients (threeFrom a))
  ext r; fin_cases r <;>
    simp [readFourth,differential3_apply,differential3Expr,coefficients,adjointLieModule,action,algebra,
      bracket,threeFrom,threeLinear,threeExpr,e,Filiform4ThirdObstructedThirdCE.d2,Matrix.toLin'_apply,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

end LeanPhy.Generated.Filiform4ThirdObstructed

/- Generated candidate: compile with `lake env lean` before treating it as checked.
Input SHA-256: f17dd07acb3be5dda78cf30e4789d1a8e1cc734cf99ecc09d24970abe68b1ad0
The matrices below are the mathematical input; no physical interpretation is inferred. -/
namespace LeanPhy.Generated.Filiform4ThirdObstructedJointImage

open LeanPhy.Mathematics

def d1 : Matrix (Fin 32) (Fin 48) ℚ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0;
    0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

def d2 : Matrix (Fin 0) (Fin 32) ℚ :=
  0

def project : Matrix (Fin 12) (Fin 32) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 / 2), 0, 0, (1 / 2), 0, (1 / 2), 0, 0, (-1 / 2), 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1 / 2), 0, 0, 0, 0, (-1 / 2), 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 / 2), 0, 0, 0, 0, (1 / 2), 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, (-1 / 2), 0, 0, (-1 / 2), 0, (-1 / 2), 0, 0, (1 / 2), 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0]

def represent : Matrix (Fin 32) (Fin 12) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def primitive : Matrix (Fin 48) (Fin 32) ℚ :=
  !![0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, (1 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 / 2), 0, 0, 0, 0, (1 / 2), 0, 0, (1 / 2), 0, (-1 / 2), (1 / 2), 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 / 2), 0, 0, (1 / 2), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 / 2), 0, 0, 0, 0, (1 / 2), 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1 / 2), 0, 0, (-1 / 2), 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 / 2), 0, 0, (1 / 2), 0, (1 / 2), 0, 0, (-1 / 2), 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1 / 2), 0, 0, 0, 0, (-1 / 2), 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1 / 2), 0, 0, (-1 / 2), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, (1 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 / 2), 0, 0, 0, 0, (1 / 2), 0, 0, (1 / 2), 0, (1 / 2), (1 / 2), 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, (-1 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1 / 2), 0, 0, 0, 0, (1 / 2), 0, 0, (1 / 2), 0, (-1 / 2), (1 / 2), 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def correction : Matrix (Fin 32) (Fin 0) ℚ :=
  0

theorem chain_checked : (d2 * d1 : Matrix (Fin 0) (Fin 48) ℚ) = 0 := by
  ext i j
  fin_cases i

theorem closed_checked : (d2 * represent : Matrix (Fin 0) (Fin 12) ℚ) = 0 := by
  ext i j
  fin_cases i

theorem boundary_row_0 : ∀ j : Fin 48,
    ((project * d1) : Matrix (Fin 12) (Fin 48) ℚ) 0 j = (0 : Matrix (Fin 12) (Fin 48) ℚ) 0 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem boundary_row_1 : ∀ j : Fin 48,
    ((project * d1) : Matrix (Fin 12) (Fin 48) ℚ) 1 j = (0 : Matrix (Fin 12) (Fin 48) ℚ) 1 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem boundary_row_2 : ∀ j : Fin 48,
    ((project * d1) : Matrix (Fin 12) (Fin 48) ℚ) 2 j = (0 : Matrix (Fin 12) (Fin 48) ℚ) 2 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem boundary_row_3 : ∀ j : Fin 48,
    ((project * d1) : Matrix (Fin 12) (Fin 48) ℚ) 3 j = (0 : Matrix (Fin 12) (Fin 48) ℚ) 3 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem boundary_row_4 : ∀ j : Fin 48,
    ((project * d1) : Matrix (Fin 12) (Fin 48) ℚ) 4 j = (0 : Matrix (Fin 12) (Fin 48) ℚ) 4 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem boundary_row_5 : ∀ j : Fin 48,
    ((project * d1) : Matrix (Fin 12) (Fin 48) ℚ) 5 j = (0 : Matrix (Fin 12) (Fin 48) ℚ) 5 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem boundary_row_6 : ∀ j : Fin 48,
    ((project * d1) : Matrix (Fin 12) (Fin 48) ℚ) 6 j = (0 : Matrix (Fin 12) (Fin 48) ℚ) 6 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem boundary_row_7 : ∀ j : Fin 48,
    ((project * d1) : Matrix (Fin 12) (Fin 48) ℚ) 7 j = (0 : Matrix (Fin 12) (Fin 48) ℚ) 7 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem boundary_row_8 : ∀ j : Fin 48,
    ((project * d1) : Matrix (Fin 12) (Fin 48) ℚ) 8 j = (0 : Matrix (Fin 12) (Fin 48) ℚ) 8 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem boundary_row_9 : ∀ j : Fin 48,
    ((project * d1) : Matrix (Fin 12) (Fin 48) ℚ) 9 j = (0 : Matrix (Fin 12) (Fin 48) ℚ) 9 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem boundary_row_10 : ∀ j : Fin 48,
    ((project * d1) : Matrix (Fin 12) (Fin 48) ℚ) 10 j = (0 : Matrix (Fin 12) (Fin 48) ℚ) 10 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem boundary_row_11 : ∀ j : Fin 48,
    ((project * d1) : Matrix (Fin 12) (Fin 48) ℚ) 11 j = (0 : Matrix (Fin 12) (Fin 48) ℚ) 11 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem boundary_checked : (project * d1 : Matrix (Fin 12) (Fin 48) ℚ) = 0 := by
  ext i j
  fin_cases i
  · exact boundary_row_0 j
  · exact boundary_row_1 j
  · exact boundary_row_2 j
  · exact boundary_row_3 j
  · exact boundary_row_4 j
  · exact boundary_row_5 j
  · exact boundary_row_6 j
  · exact boundary_row_7 j
  · exact boundary_row_8 j
  · exact boundary_row_9 j
  · exact boundary_row_10 j
  · exact boundary_row_11 j

theorem retract_row_0 : ∀ j : Fin 12,
    ((project * represent) : Matrix (Fin 12) (Fin 12) ℚ) 0 j = (1 : Matrix (Fin 12) (Fin 12) ℚ) 0 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem retract_row_1 : ∀ j : Fin 12,
    ((project * represent) : Matrix (Fin 12) (Fin 12) ℚ) 1 j = (1 : Matrix (Fin 12) (Fin 12) ℚ) 1 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem retract_row_2 : ∀ j : Fin 12,
    ((project * represent) : Matrix (Fin 12) (Fin 12) ℚ) 2 j = (1 : Matrix (Fin 12) (Fin 12) ℚ) 2 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem retract_row_3 : ∀ j : Fin 12,
    ((project * represent) : Matrix (Fin 12) (Fin 12) ℚ) 3 j = (1 : Matrix (Fin 12) (Fin 12) ℚ) 3 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem retract_row_4 : ∀ j : Fin 12,
    ((project * represent) : Matrix (Fin 12) (Fin 12) ℚ) 4 j = (1 : Matrix (Fin 12) (Fin 12) ℚ) 4 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem retract_row_5 : ∀ j : Fin 12,
    ((project * represent) : Matrix (Fin 12) (Fin 12) ℚ) 5 j = (1 : Matrix (Fin 12) (Fin 12) ℚ) 5 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem retract_row_6 : ∀ j : Fin 12,
    ((project * represent) : Matrix (Fin 12) (Fin 12) ℚ) 6 j = (1 : Matrix (Fin 12) (Fin 12) ℚ) 6 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem retract_row_7 : ∀ j : Fin 12,
    ((project * represent) : Matrix (Fin 12) (Fin 12) ℚ) 7 j = (1 : Matrix (Fin 12) (Fin 12) ℚ) 7 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem retract_row_8 : ∀ j : Fin 12,
    ((project * represent) : Matrix (Fin 12) (Fin 12) ℚ) 8 j = (1 : Matrix (Fin 12) (Fin 12) ℚ) 8 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem retract_row_9 : ∀ j : Fin 12,
    ((project * represent) : Matrix (Fin 12) (Fin 12) ℚ) 9 j = (1 : Matrix (Fin 12) (Fin 12) ℚ) 9 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem retract_row_10 : ∀ j : Fin 12,
    ((project * represent) : Matrix (Fin 12) (Fin 12) ℚ) 10 j = (1 : Matrix (Fin 12) (Fin 12) ℚ) 10 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem retract_row_11 : ∀ j : Fin 12,
    ((project * represent) : Matrix (Fin 12) (Fin 12) ℚ) 11 j = (1 : Matrix (Fin 12) (Fin 12) ℚ) 11 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem retract_checked : (project * represent : Matrix (Fin 12) (Fin 12) ℚ) = 1 := by
  ext i j
  fin_cases i
  · exact retract_row_0 j
  · exact retract_row_1 j
  · exact retract_row_2 j
  · exact retract_row_3 j
  · exact retract_row_4 j
  · exact retract_row_5 j
  · exact retract_row_6 j
  · exact retract_row_7 j
  · exact retract_row_8 j
  · exact retract_row_9 j
  · exact retract_row_10 j
  · exact retract_row_11 j

theorem decompose_row_0 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 0 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 0 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_1 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 1 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 1 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_2 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 2 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 2 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_3 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 3 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 3 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_4 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 4 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 4 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_5 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 5 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 5 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_6 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 6 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 6 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_7 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 7 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 7 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_8 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 8 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 8 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_9 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 9 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 9 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_10 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 10 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 10 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_11 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 11 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 11 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_12 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 12 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 12 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_13 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 13 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 13 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_14 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 14 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 14 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_15 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 15 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 15 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_16 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 16 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 16 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_17 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 17 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 17 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_18 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 18 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 18 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_19 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 19 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 19 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_20 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 20 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 20 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_21 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 21 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 21 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_22 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 22 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 22 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_23 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 23 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 23 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_24 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 24 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 24 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_25 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 25 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 25 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_26 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 26 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 26 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_27 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 27 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 27 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_28 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 28 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 28 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_29 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 29 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 29 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_30 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 30 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 30 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_31 : ∀ j : Fin 32,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 32) (Fin 32) ℚ) 31 j = (1 : Matrix (Fin 32) (Fin 32) ℚ) 31 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_checked : (d1 * primitive + represent * project + correction * d2 : Matrix (Fin 32) (Fin 32) ℚ) = 1 := by
  ext i j
  fin_cases i
  · exact decompose_row_0 j
  · exact decompose_row_1 j
  · exact decompose_row_2 j
  · exact decompose_row_3 j
  · exact decompose_row_4 j
  · exact decompose_row_5 j
  · exact decompose_row_6 j
  · exact decompose_row_7 j
  · exact decompose_row_8 j
  · exact decompose_row_9 j
  · exact decompose_row_10 j
  · exact decompose_row_11 j
  · exact decompose_row_12 j
  · exact decompose_row_13 j
  · exact decompose_row_14 j
  · exact decompose_row_15 j
  · exact decompose_row_16 j
  · exact decompose_row_17 j
  · exact decompose_row_18 j
  · exact decompose_row_19 j
  · exact decompose_row_20 j
  · exact decompose_row_21 j
  · exact decompose_row_22 j
  · exact decompose_row_23 j
  · exact decompose_row_24 j
  · exact decompose_row_25 j
  · exact decompose_row_26 j
  · exact decompose_row_27 j
  · exact decompose_row_28 j
  · exact decompose_row_29 j
  · exact decompose_row_30 j
  · exact decompose_row_31 j

def certificate : MatrixCohomologyReduction d1 d2 12 where
  project := project
  represent := represent
  primitive := primitive
  correction := correction
  chain := chain_checked
  closed := closed_checked
  boundary := boundary_checked
  retract := retract_checked
  decompose := decompose_checked

noncomputable def cohomologyEquiv :
    CohomologyReduction.Cohomology d1.toLin' d2.toLin' ≃ₗ[ℚ] (Fin 12 → ℚ) :=
  certificate.toReduction.quotientEquiv

theorem exact_iff (x : Fin 32 → ℚ) (hx : d2.toLin' x = 0) :
    (∃ a, d1.toLin' a = x) ↔ project.toLin' x = 0 :=
  certificate.toReduction.exact_iff x hx

end LeanPhy.Generated.Filiform4ThirdObstructedJointImage

namespace LeanPhy.Generated.Filiform4ThirdObstructed
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieDeformation LeanPhy.Mathematics.LieCochainCoordinates
set_option maxSynthPendingDepth 7
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

/-- The first direction is supplied; both higher corrections are searched. -/
def direction : C2 := twoFrom ![-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]

theorem direction_coordinates : twoCoordinates direction = ![-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] :=
  twoCoordinates.apply_symm_apply _

/-- Linear dependence of the third Jacobi term on the second correction. -/
def mixed : Matrix (Fin 16) (Fin 24) ℚ := !![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem mixed_row_0 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 0 =
      mixed.toLin' a 0 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 0) (e 1) (e 2) 0 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 0) (e 1) (e 2)) 0
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_1 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 1 =
      mixed.toLin' a 1 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 0) (e 1) (e 2) 1 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 0) (e 1) (e 2)) 1
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_2 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 2 =
      mixed.toLin' a 2 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 0) (e 1) (e 2) 2 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 0) (e 1) (e 2)) 2
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_3 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 3 =
      mixed.toLin' a 3 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 0) (e 1) (e 2) 3 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 0) (e 1) (e 2)) 3
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_4 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 4 =
      mixed.toLin' a 4 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 0) (e 1) (e 3) 0 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 0) (e 1) (e 3)) 0
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_5 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 5 =
      mixed.toLin' a 5 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 0) (e 1) (e 3) 1 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 0) (e 1) (e 3)) 1
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_6 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 6 =
      mixed.toLin' a 6 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 0) (e 1) (e 3) 2 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 0) (e 1) (e 3)) 2
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_7 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 7 =
      mixed.toLin' a 7 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 0) (e 1) (e 3) 3 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 0) (e 1) (e 3)) 3
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_8 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 8 =
      mixed.toLin' a 8 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 0) (e 2) (e 3) 0 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 0) (e 2) (e 3)) 0
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_9 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 9 =
      mixed.toLin' a 9 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 0) (e 2) (e 3) 1 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 0) (e 2) (e 3)) 1
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_10 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 10 =
      mixed.toLin' a 10 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 0) (e 2) (e 3) 2 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 0) (e 2) (e 3)) 2
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_11 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 11 =
      mixed.toLin' a 11 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 0) (e 2) (e 3) 3 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 0) (e 2) (e 3)) 3
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_12 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 12 =
      mixed.toLin' a 12 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 1) (e 2) (e 3) 0 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 1) (e 2) (e 3)) 0
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_13 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 13 =
      mixed.toLin' a 13 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 1) (e 2) (e 3) 1 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 1) (e 2) (e 3)) 1
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_14 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 14 =
      mixed.toLin' a 14 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 1) (e 2) (e 3) 2 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 1) (e 2) (e 3)) 2
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_15 (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 15 =
      mixed.toLin' a 15 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 1) (e 2) (e 3) 3 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 1) (e 2) (e 3)) 3
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring


theorem mixed_bridge (a : Fin 24 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) = mixed.toLin' a := by
  change readThird (thirdObstructionCochain direction (twoFrom a)).val = _
  ext i
  fin_cases i
  · exact mixed_row_0 a
  · exact mixed_row_1 a
  · exact mixed_row_2 a
  · exact mixed_row_3 a
  · exact mixed_row_4 a
  · exact mixed_row_5 a
  · exact mixed_row_6 a
  · exact mixed_row_7 a
  · exact mixed_row_8 a
  · exact mixed_row_9 a
  · exact mixed_row_10 a
  · exact mixed_row_11 a
  · exact mixed_row_12 a
  · exact mixed_row_13 a
  · exact mixed_row_14 a
  · exact mixed_row_15 a


theorem joint_matrix_row_0 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 0 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 0 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_1 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 1 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 1 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_2 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 2 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 2 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_3 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 3 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 3 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_4 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 4 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 4 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_5 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 5 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 5 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_6 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 6 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 6 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_7 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 7 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 7 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_8 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 8 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 8 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_9 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 9 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 9 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_10 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 10 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 10 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_11 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 11 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 11 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_12 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 12 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 12 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_13 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 13 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 13 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_14 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 14 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 14 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_15 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 15 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 15 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_16 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 16 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 16 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_17 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 17 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 17 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_18 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 18 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 18 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_19 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 19 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 19 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_20 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 20 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 20 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_21 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 21 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 21 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_22 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 22 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 22 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_23 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 23 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 23 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_24 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 24 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 24 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_25 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 25 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 25 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_26 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 26 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 26 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_27 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 27 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 27 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_28 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 28 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 28 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_29 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 29 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 29 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_30 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 30 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 30 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_31 (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) 31 =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) 31 := by
  simp [Filiform4ThirdObstructedJointImage.d1,Filiform4ThirdObstructedThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring


theorem joint_matrix_bridge (a b : Fin 24 → ℚ) :
    Fin.append (Filiform4ThirdObstructedThirdCE.d1.toLin' a) (Filiform4ThirdObstructedThirdCE.d1.toLin' b + mixed.toLin' a) =
      Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append a b) := by
  ext i
  fin_cases i
  · exact joint_matrix_row_0 a b
  · exact joint_matrix_row_1 a b
  · exact joint_matrix_row_2 a b
  · exact joint_matrix_row_3 a b
  · exact joint_matrix_row_4 a b
  · exact joint_matrix_row_5 a b
  · exact joint_matrix_row_6 a b
  · exact joint_matrix_row_7 a b
  · exact joint_matrix_row_8 a b
  · exact joint_matrix_row_9 a b
  · exact joint_matrix_row_10 a b
  · exact joint_matrix_row_11 a b
  · exact joint_matrix_row_12 a b
  · exact joint_matrix_row_13 a b
  · exact joint_matrix_row_14 a b
  · exact joint_matrix_row_15 a b
  · exact joint_matrix_row_16 a b
  · exact joint_matrix_row_17 a b
  · exact joint_matrix_row_18 a b
  · exact joint_matrix_row_19 a b
  · exact joint_matrix_row_20 a b
  · exact joint_matrix_row_21 a b
  · exact joint_matrix_row_22 a b
  · exact joint_matrix_row_23 a b
  · exact joint_matrix_row_24 a b
  · exact joint_matrix_row_25 a b
  · exact joint_matrix_row_26 a b
  · exact joint_matrix_row_27 a b
  · exact joint_matrix_row_28 a b
  · exact joint_matrix_row_29 a b
  · exact joint_matrix_row_30 a b
  · exact joint_matrix_row_31 a b


noncomputable def pairTwoCoordinates : (C2 × C2) ≃ₗ[ℚ] (Fin 48 → ℚ) :=
  (twoCoordinates.prodCongr twoCoordinates).trans (pairCoordinates 24)

noncomputable def pairThreeCoordinates : (C3 × C3) ≃ₗ[ℚ] (Fin 32 → ℚ) :=
  (threeCoordinates.prodCongr threeCoordinates).trans (pairCoordinates 16)

theorem joint_bridge (q : C2 × C2) :
    pairThreeCoordinates (jointDifferential direction q) = Filiform4ThirdObstructedJointImage.d1.toLin' (pairTwoCoordinates q) := by
  obtain ⟨a,ha⟩ := twoCoordinates.symm.surjective q.1
  obtain ⟨b,hb⟩ := twoCoordinates.symm.surjective q.2
  have hq : q = (twoFrom a,twoFrom b) := Prod.ext ha.symm hb.symm
  rw [hq]
  change Fin.append (threeCoordinates (differential2Cochain coefficients (twoFrom a)))
    (threeCoordinates (differential2Cochain coefficients (twoFrom b) +
      thirdObstructionCochain direction (twoFrom a))) =
    Filiform4ThirdObstructedJointImage.d1.toLin' (Fin.append (twoCoordinates (twoFrom a)) (twoCoordinates (twoFrom b)))
  rw [map_add]
  erw [differential2_third_coordinates,differential2_third_coordinates,mixed_bridge]
  simp only [show twoCoordinates (twoFrom a) = a from twoCoordinates.apply_symm_apply a,
    show twoCoordinates (twoFrom b) = b from twoCoordinates.apply_symm_apply b]
  exact joint_matrix_bridge a b

/-- Complete block-image reduction transported to all actual cochain pairs. -/
noncomputable def jointReduction : JointReduction direction (Fin 12 → ℚ) :=
  Filiform4ThirdObstructedJointImage.certificate.toReduction.transport pairTwoCoordinates pairThreeCoordinates
    (0 : ℚ →ₗ[ℚ] (Fin 0 → ℚ)) joint_bridge
    (by intro q; ext i; exact Fin.elim0 i) (by intros; rfl)

def targetValues : Fin 32 → ℚ := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def obstructionValues : Fin 12 → ℚ := ![0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
def correctionValues : Fin 48 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem target_bridge : pairThreeCoordinates (jointTarget direction) = targetValues := by
  change Fin.append (threeCoordinates (-obstructionCochain direction)) (threeCoordinates 0) = _
  rw [map_neg,map_zero]
  change Fin.append (-readThird (obstructionTrilinear direction)) 0 = _
  apply funext
  norm_num [Fin.forall_fin_succ,readThird,obstructionTrilinear,obstruction,direction,twoFrom,e,targetValues,
      Fin.append,Fin.addCases]

theorem obstruction_coordinates :
    JointReduction.obstructionCoordinates jointReduction = obstructionValues := by
  change Filiform4ThirdObstructedJointImage.project.toLin' (pairThreeCoordinates (jointTarget direction)) = _
  rw [target_bridge]
  apply funext
  norm_num [Fin.forall_fin_succ,obstructionValues,targetValues,Filiform4ThirdObstructedJointImage.project,
      Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem correction_coordinates :
    pairTwoCoordinates (JointReduction.corrections jointReduction) = correctionValues := by
  change pairTwoCoordinates (pairTwoCoordinates.symm
    (Filiform4ThirdObstructedJointImage.primitive.toLin' (pairThreeCoordinates (jointTarget direction)))) = _
  rw [LinearEquiv.apply_symm_apply,target_bridge]
  apply funext
  norm_num [Fin.forall_fin_succ,correctionValues,targetValues,Filiform4ThirdObstructedJointImage.primitive,
      Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

/-- Closedness is retained even if the block target has zero projection. -/
def SearchConditions : Prop := IsTwoCocycle coefficients direction ∧ obstructionValues = 0

theorem search_exists_iff : ThirdDirectionExtendable direction ↔ SearchConditions := by
  rw [JointReduction.extendable_iff jointReduction,obstruction_coordinates]
  rfl

noncomputable def searchedCorrections : C2 × C2 := JointReduction.corrections jointReduction

noncomputable def searchedModel (h : SearchConditions) :
    LeanPhy.Mathematics.LieAlgebra ℚ (ThirdJet Space) :=
  JointReduction.model jointReduction h.1 (by rw [obstruction_coordinates]; exact h.2)

theorem searchedModel_bracket (h : SearchConditions) :
    (searchedModel h).bracket = thirdBracket direction searchedCorrections.1 searchedCorrections.2 := rfl

theorem all_pairs_iff (ν ρ : C2) (h : SearchConditions) :
    (∃ D : LeanPhy.Mathematics.LieAlgebra ℚ (ThirdJet Space), D.bracket = thirdBracket direction ν ρ) ↔
      Filiform4ThirdObstructedJointImage.d1.toLin' (pairTwoCoordinates (ν,ρ) - correctionValues) = 0 := by
  rw [JointReduction.all_models_iff jointReduction ν ρ h.1
    (by rw [obstruction_coordinates]; exact h.2)]
  rw [← LinearEquiv.map_eq_zero_iff pairThreeCoordinates]
  erw [joint_bridge]
  erw [pairTwoCoordinates.map_sub,correction_coordinates]
  rfl

theorem direction_closed : IsTwoCocycle coefficients direction := by
  apply readThird_detect
  rw [← differential2_coordinates]
  change Filiform4ThirdObstructedCE.d2.toLin' (twoCoordinates direction) = 0
  rw [direction_coordinates]
  apply funext
  norm_num [Fin.forall_fin_succ,Filiform4ThirdObstructedCE.d2,
      Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

/-- A separate witness distinguishes a genuine third-order obstruction from an earlier failure. -/
def secondCandidate : C2 := twoFrom ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0]

theorem secondCandidate_cancels : secondResidual direction secondCandidate = 0 := by
  apply secondResidual_eq_zero_of_increasing
  intro i j k hij hjk
  change differential2 coefficients secondCandidate (e i) (e j) (e k) +
    obstruction direction (e i) (e j) (e k) = 0
  simp only [differential2_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hij <;> norm_num at hjk
  all_goals ext r; fin_cases r <;>
    norm_num [obstruction,direction,secondCandidate,
      twoFrom,coefficients,adjointLieModule,algebra,bracket,e]

theorem second_order_succeeds : SecondExtendable direction :=
  ⟨secondCandidate,secondAlgebra direction secondCandidate direction_closed
    ((secondResidual_eq_zero_iff _ _).mp secondCandidate_cancels),rfl⟩

theorem search_impossible : ¬ThirdDirectionExtendable direction := by
  intro h
  have hr := congrFun (search_exists_iff.mp h).2 4
  norm_num [obstructionValues] at hr

end LeanPhy.Generated.Filiform4ThirdObstructed
