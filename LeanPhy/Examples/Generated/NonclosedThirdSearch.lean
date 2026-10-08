import LeanPhy.Mathematics.LieDeformationThirdSearch
/- Generated proof candidate. Input SHA-256: ef38d1dd24e6fdfbcf4c605184cc5aeb4dc1a4d941dd09bfd782aa291aab2748. Compile the entire file with Lean. -/
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
namespace LeanPhy.Generated.NonclosedThirdSearchCE
def d1 : Matrix (Fin 9) (Fin 9) ℚ := !![0, 0, 0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, -1, 0;
    1, 0, 0, 0, 1, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, -1, 0, 0]
def d2 : Matrix (Fin 3) (Fin 9) ℚ := !![0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 1, 0]
end LeanPhy.Generated.NonclosedThirdSearchCE
namespace LeanPhy.Generated.NonclosedThirdSearchThirdCE
def d1 : Matrix (Fin 3) (Fin 9) ℚ := !![0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 1, 0]
def d2 : Matrix (Fin 0) (Fin 3) ℚ := 0
end LeanPhy.Generated.NonclosedThirdSearchThirdCE
namespace LeanPhy.Generated.NonclosedThirdSearch

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
    twoCoordinates (differential1 coefficients φ) = NonclosedThirdSearchCE.d1.toLin' (oneCoordinates φ) := by
  obtain ⟨a, rfl⟩ := oneCoordinates.symm.surjective φ
  rw [oneCoordinates.apply_symm_apply]
  change twoValues (differential1 coefficients (oneFrom a)) = NonclosedThirdSearchCE.d1.toLin' a
  ext r
  fin_cases r <;>
    simp [twoValues, differential1, coefficients, adjointLieModule, action, algebra, bracket, oneFrom, e,
      NonclosedThirdSearchCE.d1, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem differential2_coordinates (ω : C2) :
    NonclosedThirdSearchCE.d2.toLin' (twoCoordinates ω) = readThird (differential2 coefficients ω) := by
  obtain ⟨a, rfl⟩ := twoCoordinates.symm.surjective ω
  rw [twoCoordinates.apply_symm_apply]
  change NonclosedThirdSearchCE.d2.toLin' a = readThird (differential2 coefficients (twoFrom a))
  ext r
  fin_cases r <;>
    simp [readThird, differential2_apply, coefficients, adjointLieModule, action, algebra, bracket, twoFrom, e,
      NonclosedThirdSearchCE.d2, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

set_option maxSynthPendingDepth 7
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
    threeCoordinates (differential2ToThree coefficients ω) = NonclosedThirdSearchThirdCE.d1.toLin' (twoCoordinates ω) :=
  (differential2_coordinates ω).symm

theorem differential3_coordinates (t : C3) :
    NonclosedThirdSearchThirdCE.d2.toLin' (threeCoordinates t) = readFourth (differential3 coefficients t) := by
  obtain ⟨a,rfl⟩ := threeCoordinates.symm.surjective t
  rw [threeCoordinates.apply_symm_apply]
  change NonclosedThirdSearchThirdCE.d2.toLin' a = readFourth (differential3 coefficients (threeFrom a))
  ext r; fin_cases r <;>
    simp [readFourth,differential3_apply,differential3Expr,coefficients,adjointLieModule,action,algebra,
      bracket,threeFrom,threeLinear,threeExpr,e,NonclosedThirdSearchThirdCE.d2,Matrix.toLin'_apply,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

end LeanPhy.Generated.NonclosedThirdSearch

/- Generated candidate: compile with `lake env lean` before treating it as checked.
Input SHA-256: ef38d1dd24e6fdfbcf4c605184cc5aeb4dc1a4d941dd09bfd782aa291aab2748
The matrices below are the mathematical input; no physical interpretation is inferred. -/
namespace LeanPhy.Generated.NonclosedThirdSearchJointImage

open LeanPhy.Mathematics

def d1 : Matrix (Fin 6) (Fin 18) ℚ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]

def d2 : Matrix (Fin 0) (Fin 6) ℚ :=
  0

def project : Matrix (Fin 2) (Fin 6) ℚ :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0]

def represent : Matrix (Fin 6) (Fin 2) ℚ :=
  !![1, 0;
    0, 1;
    0, 0;
    0, 0;
    0, 0;
    0, 0]

def primitive : Matrix (Fin 18) (Fin 6) ℚ :=
  !![0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0]

def correction : Matrix (Fin 6) (Fin 0) ℚ :=
  0

theorem chain_checked : (d2 * d1 : Matrix (Fin 0) (Fin 18) ℚ) = 0 := by
  ext i j
  fin_cases i

theorem closed_checked : (d2 * represent : Matrix (Fin 0) (Fin 2) ℚ) = 0 := by
  ext i j
  fin_cases i

theorem boundary_row_0 : ∀ j : Fin 18,
    ((project * d1) : Matrix (Fin 2) (Fin 18) ℚ) 0 j = (0 : Matrix (Fin 2) (Fin 18) ℚ) 0 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem boundary_row_1 : ∀ j : Fin 18,
    ((project * d1) : Matrix (Fin 2) (Fin 18) ℚ) 1 j = (0 : Matrix (Fin 2) (Fin 18) ℚ) 1 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem boundary_checked : (project * d1 : Matrix (Fin 2) (Fin 18) ℚ) = 0 := by
  ext i j
  fin_cases i
  · exact boundary_row_0 j
  · exact boundary_row_1 j

theorem retract_row_0 : ∀ j : Fin 2,
    ((project * represent) : Matrix (Fin 2) (Fin 2) ℚ) 0 j = (1 : Matrix (Fin 2) (Fin 2) ℚ) 0 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem retract_row_1 : ∀ j : Fin 2,
    ((project * represent) : Matrix (Fin 2) (Fin 2) ℚ) 1 j = (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem retract_checked : (project * represent : Matrix (Fin 2) (Fin 2) ℚ) = 1 := by
  ext i j
  fin_cases i
  · exact retract_row_0 j
  · exact retract_row_1 j

theorem decompose_row_0 : ∀ j : Fin 6,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 6) (Fin 6) ℚ) 0 j = (1 : Matrix (Fin 6) (Fin 6) ℚ) 0 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_1 : ∀ j : Fin 6,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 6) (Fin 6) ℚ) 1 j = (1 : Matrix (Fin 6) (Fin 6) ℚ) 1 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_2 : ∀ j : Fin 6,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 6) (Fin 6) ℚ) 2 j = (1 : Matrix (Fin 6) (Fin 6) ℚ) 2 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_3 : ∀ j : Fin 6,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 6) (Fin 6) ℚ) 3 j = (1 : Matrix (Fin 6) (Fin 6) ℚ) 3 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_4 : ∀ j : Fin 6,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 6) (Fin 6) ℚ) 4 j = (1 : Matrix (Fin 6) (Fin 6) ℚ) 4 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_row_5 : ∀ j : Fin 6,
    ((d1 * primitive + represent * project + correction * d2) : Matrix (Fin 6) (Fin 6) ℚ) 5 j = (1 : Matrix (Fin 6) (Fin 6) ℚ) 5 j := by
    norm_num [Fin.forall_fin_succ,d1,d2,project,represent,primitive,correction,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]

theorem decompose_checked : (d1 * primitive + represent * project + correction * d2 : Matrix (Fin 6) (Fin 6) ℚ) = 1 := by
  ext i j
  fin_cases i
  · exact decompose_row_0 j
  · exact decompose_row_1 j
  · exact decompose_row_2 j
  · exact decompose_row_3 j
  · exact decompose_row_4 j
  · exact decompose_row_5 j

def certificate : MatrixCohomologyReduction d1 d2 2 where
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
    CohomologyReduction.Cohomology d1.toLin' d2.toLin' ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  certificate.toReduction.quotientEquiv

theorem exact_iff (x : Fin 6 → ℚ) (hx : d2.toLin' x = 0) :
    (∃ a, d1.toLin' a = x) ↔ project.toLin' x = 0 :=
  certificate.toReduction.exact_iff x hx

end LeanPhy.Generated.NonclosedThirdSearchJointImage

namespace LeanPhy.Generated.NonclosedThirdSearch
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieDeformation LeanPhy.Mathematics.LieCochainCoordinates
set_option maxSynthPendingDepth 7
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

/-- The first direction is supplied; both higher corrections are searched. -/
def direction : C2 := twoFrom ![0, 0, 0, 1, 0, 0, 0, 0, 0]

theorem direction_coordinates : twoCoordinates direction = ![0, 0, 0, 1, 0, 0, 0, 0, 0] :=
  twoCoordinates.apply_symm_apply _

/-- Linear dependence of the third Jacobi term on the second correction. -/
def mixed : Matrix (Fin 3) (Fin 9) ℚ := !![0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0]

theorem mixed_row_0 (a : Fin 9 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 0 =
      mixed.toLin' a 0 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 0) (e 1) (e 2) 0 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 0) (e 1) (e 2)) 0
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_1 (a : Fin 9 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 1 =
      mixed.toLin' a 1 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 0) (e 1) (e 2) 1 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 0) (e 1) (e 2)) 1
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem mixed_row_2 (a : Fin 9 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) 2 =
      mixed.toLin' a 2 := by
    calc
      _ = thirdObstruction direction (twoFrom a) (e 0) (e 1) (e 2) 2 :=
        congrFun (thirdObstructionCochain_apply direction (twoFrom a) (e 0) (e 1) (e 2)) 2
      _ = _ := by
        simp [thirdObstruction,direction,twoFrom,e,mixed,
          Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring


theorem mixed_bridge (a : Fin 9 → ℚ) :
    threeCoordinates (thirdObstructionCochain direction (twoFrom a)) = mixed.toLin' a := by
  change readThird (thirdObstructionCochain direction (twoFrom a)).val = _
  ext i
  fin_cases i
  · exact mixed_row_0 a
  · exact mixed_row_1 a
  · exact mixed_row_2 a


theorem joint_matrix_row_0 (a b : Fin 9 → ℚ) :
    Fin.append (NonclosedThirdSearchThirdCE.d1.toLin' a) (NonclosedThirdSearchThirdCE.d1.toLin' b + mixed.toLin' a) 0 =
      NonclosedThirdSearchJointImage.d1.toLin' (Fin.append a b) 0 := by
  simp [NonclosedThirdSearchJointImage.d1,NonclosedThirdSearchThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_1 (a b : Fin 9 → ℚ) :
    Fin.append (NonclosedThirdSearchThirdCE.d1.toLin' a) (NonclosedThirdSearchThirdCE.d1.toLin' b + mixed.toLin' a) 1 =
      NonclosedThirdSearchJointImage.d1.toLin' (Fin.append a b) 1 := by
  simp [NonclosedThirdSearchJointImage.d1,NonclosedThirdSearchThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_2 (a b : Fin 9 → ℚ) :
    Fin.append (NonclosedThirdSearchThirdCE.d1.toLin' a) (NonclosedThirdSearchThirdCE.d1.toLin' b + mixed.toLin' a) 2 =
      NonclosedThirdSearchJointImage.d1.toLin' (Fin.append a b) 2 := by
  simp [NonclosedThirdSearchJointImage.d1,NonclosedThirdSearchThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_3 (a b : Fin 9 → ℚ) :
    Fin.append (NonclosedThirdSearchThirdCE.d1.toLin' a) (NonclosedThirdSearchThirdCE.d1.toLin' b + mixed.toLin' a) 3 =
      NonclosedThirdSearchJointImage.d1.toLin' (Fin.append a b) 3 := by
  simp [NonclosedThirdSearchJointImage.d1,NonclosedThirdSearchThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_4 (a b : Fin 9 → ℚ) :
    Fin.append (NonclosedThirdSearchThirdCE.d1.toLin' a) (NonclosedThirdSearchThirdCE.d1.toLin' b + mixed.toLin' a) 4 =
      NonclosedThirdSearchJointImage.d1.toLin' (Fin.append a b) 4 := by
  simp [NonclosedThirdSearchJointImage.d1,NonclosedThirdSearchThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem joint_matrix_row_5 (a b : Fin 9 → ℚ) :
    Fin.append (NonclosedThirdSearchThirdCE.d1.toLin' a) (NonclosedThirdSearchThirdCE.d1.toLin' b + mixed.toLin' a) 5 =
      NonclosedThirdSearchJointImage.d1.toLin' (Fin.append a b) 5 := by
  simp [NonclosedThirdSearchJointImage.d1,NonclosedThirdSearchThirdCE.d1,mixed,Fin.append,Fin.addCases,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring


theorem joint_matrix_bridge (a b : Fin 9 → ℚ) :
    Fin.append (NonclosedThirdSearchThirdCE.d1.toLin' a) (NonclosedThirdSearchThirdCE.d1.toLin' b + mixed.toLin' a) =
      NonclosedThirdSearchJointImage.d1.toLin' (Fin.append a b) := by
  ext i
  fin_cases i
  · exact joint_matrix_row_0 a b
  · exact joint_matrix_row_1 a b
  · exact joint_matrix_row_2 a b
  · exact joint_matrix_row_3 a b
  · exact joint_matrix_row_4 a b
  · exact joint_matrix_row_5 a b


noncomputable def pairTwoCoordinates : (C2 × C2) ≃ₗ[ℚ] (Fin 18 → ℚ) :=
  (twoCoordinates.prodCongr twoCoordinates).trans (pairCoordinates 9)

noncomputable def pairThreeCoordinates : (C3 × C3) ≃ₗ[ℚ] (Fin 6 → ℚ) :=
  (threeCoordinates.prodCongr threeCoordinates).trans (pairCoordinates 3)

theorem joint_bridge (q : C2 × C2) :
    pairThreeCoordinates (jointDifferential direction q) = NonclosedThirdSearchJointImage.d1.toLin' (pairTwoCoordinates q) := by
  obtain ⟨a,ha⟩ := twoCoordinates.symm.surjective q.1
  obtain ⟨b,hb⟩ := twoCoordinates.symm.surjective q.2
  have hq : q = (twoFrom a,twoFrom b) := Prod.ext ha.symm hb.symm
  rw [hq]
  change Fin.append (threeCoordinates (differential2Cochain coefficients (twoFrom a)))
    (threeCoordinates (differential2Cochain coefficients (twoFrom b) +
      thirdObstructionCochain direction (twoFrom a))) =
    NonclosedThirdSearchJointImage.d1.toLin' (Fin.append (twoCoordinates (twoFrom a)) (twoCoordinates (twoFrom b)))
  rw [map_add]
  erw [differential2_third_coordinates,differential2_third_coordinates,mixed_bridge]
  simp only [show twoCoordinates (twoFrom a) = a from twoCoordinates.apply_symm_apply a,
    show twoCoordinates (twoFrom b) = b from twoCoordinates.apply_symm_apply b]
  exact joint_matrix_bridge a b

/-- Complete block-image reduction transported to all actual cochain pairs. -/
noncomputable def jointReduction : JointReduction direction (Fin 2 → ℚ) :=
  NonclosedThirdSearchJointImage.certificate.toReduction.transport pairTwoCoordinates pairThreeCoordinates
    (0 : ℚ →ₗ[ℚ] (Fin 0 → ℚ)) joint_bridge
    (by intro q; ext i; exact Fin.elim0 i) (by intros; rfl)

def targetValues : Fin 6 → ℚ := ![0, 0, 0, 0, 0, 0]
def obstructionValues : Fin 2 → ℚ := ![0, 0]
def correctionValues : Fin 18 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem target_bridge : pairThreeCoordinates (jointTarget direction) = targetValues := by
  change Fin.append (threeCoordinates (-obstructionCochain direction)) (threeCoordinates 0) = _
  rw [map_neg,map_zero]
  change Fin.append (-readThird (obstructionTrilinear direction)) 0 = _
  apply funext
  norm_num [Fin.forall_fin_succ,readThird,obstructionTrilinear,obstruction,direction,twoFrom,e,targetValues,
      Fin.append,Fin.addCases]

theorem obstruction_coordinates :
    JointReduction.obstructionCoordinates jointReduction = obstructionValues := by
  change NonclosedThirdSearchJointImage.project.toLin' (pairThreeCoordinates (jointTarget direction)) = _
  rw [target_bridge]
  apply funext
  norm_num [Fin.forall_fin_succ,obstructionValues,targetValues,NonclosedThirdSearchJointImage.project,
      Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem correction_coordinates :
    pairTwoCoordinates (JointReduction.corrections jointReduction) = correctionValues := by
  change pairTwoCoordinates (pairTwoCoordinates.symm
    (NonclosedThirdSearchJointImage.primitive.toLin' (pairThreeCoordinates (jointTarget direction)))) = _
  rw [LinearEquiv.apply_symm_apply,target_bridge]
  apply funext
  norm_num [Fin.forall_fin_succ,correctionValues,targetValues,NonclosedThirdSearchJointImage.primitive,
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
      NonclosedThirdSearchJointImage.d1.toLin' (pairTwoCoordinates (ν,ρ) - correctionValues) = 0 := by
  rw [JointReduction.all_models_iff jointReduction ν ρ h.1
    (by rw [obstruction_coordinates]; exact h.2)]
  rw [← LinearEquiv.map_eq_zero_iff pairThreeCoordinates]
  erw [joint_bridge]
  erw [pairTwoCoordinates.map_sub,correction_coordinates]
  rfl

theorem direction_not_closed : ¬IsTwoCocycle coefficients direction := by
  intro h
  have hc := differential2_coordinates direction
  rw [h,map_zero] at hc
  rw [direction_coordinates] at hc
  have hr := congrFun hc 2
  norm_num [NonclosedThirdSearchCE.d2,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hr

theorem search_impossible : ¬ThirdDirectionExtendable direction := by
  intro h
  exact direction_not_closed (search_exists_iff.mp h).1

end LeanPhy.Generated.NonclosedThirdSearch
