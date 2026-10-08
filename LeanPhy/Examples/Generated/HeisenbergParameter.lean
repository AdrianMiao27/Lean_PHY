import LeanPhy.Mathematics.FiniteLieCohomology
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/- Generated candidate: compile with Lean before using any conclusion.
Input SHA-256: 9f1a69c9f3e7d0ef8cf352596d6f72254977fb9f157d31c28c3bacb87fedff59
Parameter order: g.
The decision tree includes all zero and nonzero branches under the declared
input conditions. No numerical sampling or physical interpretation is assumed. -/
namespace LeanPhy.Generated.HeisenbergParameterCE

open LeanPhy.Mathematics
open scoped _root_.Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

def d1 (x : Fin 1 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, (-1 * (x 0));
    0, 0, 0;
    0, 0, 0]

def d2 (x : Fin 1 → K) : Matrix (Fin 1) (Fin 3) K :=
  0

def project_0 (x : Fin 1 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0;
    0, 1, 0;
    0, 0, 1]

def represent_0 (x : Fin 1 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0;
    0, 1, 0;
    0, 0, 1]

def primitive_0 (x : Fin 1 → K) : Matrix (Fin 3) (Fin 3) K :=
  0

def correction_0 (x : Fin 1 → K) : Matrix (Fin 3) (Fin 1) K :=
  0

def branch_0 (x : Fin 1 → K) (h0 : (x 0) = 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 3 where
  project := project_0 x
  represent := represent_0 x
  primitive := primitive_0 x
  correction := correction_0 x
  chain := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  closed := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  boundary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  retract := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  decompose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

def project_1 (x : Fin 1 → K) : Matrix (Fin 2) (Fin 3) K :=
  !![0, 1, 0;
    0, 0, 1]

def represent_1 (x : Fin 1 → K) : Matrix (Fin 3) (Fin 2) K :=
  !![0, 0;
    1, 0;
    0, 1]

def primitive_1 (x : Fin 1 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0;
    0, 0, 0;
    (-1 * ((x 0))⁻¹), 0, 0]

def correction_1 (x : Fin 1 → K) : Matrix (Fin 3) (Fin 1) K :=
  0

def branch_1 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 2 where
  project := project_1 x
  represent := represent_1 x
  primitive := primitive_1 x
  correction := correction_1 x
  chain := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  closed := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  boundary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  retract := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  decompose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

def dimension (x : Fin 1 → K) : Nat :=
  (if (x 0) = 0 then 3 else 2)

def certificate (x : Fin 1 → K) :
    MatrixCohomologyReduction (d1 x) (d2 x) (dimension x) := by
  by_cases h0 : (x 0) = 0
  · unfold dimension
    rw [ite_eq_left h0]
    exact branch_0 x h0
  · unfold dimension
    rw [ite_eq_right h0]
    exact branch_1 x h0

def cohomologyEquiv (x : Fin 1 → K) :
    CohomologyReduction.Cohomology (d1 x).toLin' (d2 x).toLin' ≃ₗ[K] (Fin (dimension x) → K) :=
  (certificate x).toReduction.quotientEquiv

theorem finrank_eq (x : Fin 1 → K) :
    Module.finrank K (CohomologyReduction.Cohomology (d1 x).toLin' (d2 x).toLin') = dimension x := by
  rw [(cohomologyEquiv x).finrank_eq]
  simp

theorem exact_iff (x : Fin 1 → K)
    (ω : Fin 3 → K) (hω : (d2 x).toLin' ω = 0) :
    (∃ φ, (d1 x).toLin' φ = ω) ↔ (certificate x).project.toLin' ω = 0 :=
  (certificate x).toReduction.exact_iff ω hω

theorem normal_form (x : Fin 1 → K)
    (ω : Fin 3 → K) (hω : (d2 x).toLin' ω = 0) :
    (d1 x).toLin' ((certificate x).primitive.toLin' ω) +
      (certificate x).represent.toLin' ((certificate x).project.toLin' ω) = ω :=
  (certificate x).toReduction.normal_form ω hω

end
end LeanPhy.Generated.HeisenbergParameterCE

/- The model and every H2 conclusion below retain the declared parameter
conditions. The preceding matrices are connected to complete CE cochains. -/
namespace LeanPhy.Generated.HeisenbergParameter

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates
open scoped _root_.Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
set_option maxSynthPendingDepth 5
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

abbrev Space (K : Type*) := Fin 3 → K
abbrev Coeff (K : Type*) := Fin 1 → K

/-- All input constraints are proof fields, not unchecked metadata. -/
structure Conditions (p : Fin 1 → K) : Prop where


def bracket (p : Fin 1 → K) (x y : Space K) : Space K := ![0, 0, ((p 0)) * (x 0 * y 1 - x 1 * y 0)]

def algebra (p : Fin 1 → K) (hp : Conditions p) : LeanPhy.Mathematics.LieAlgebra K (Space K) where
  bracket := bracket p
  add_left := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  add_right := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  smul_left := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  smul_right := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  zero_left := by intros; ext r; fin_cases r <;> simp [bracket]
  alternating := by intros; ext r; fin_cases r <;> dsimp [bracket] <;> ring
  antisymm := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  jacobi := by intros; ext r; fin_cases r <;> simp [bracket] <;> (try ring_nf) <;> grind

def action (p : Fin 1 → K) (x : Space K) (v : Coeff K) : Coeff K := ![0]

def coefficients (p : Fin 1 → K) (hp : Conditions p) : LeanPhy.Mathematics.LieModule (algebra p hp) (Coeff K) where
  act := action p
  act_add_left' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  act_smul_left' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  act_add_right' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  act_smul_right' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  bracket_act' := by intros; ext r; fin_cases r <;> simp [algebra, bracket, action] <;> (try ring_nf) <;> grind

abbrev C2 (p : Fin 1 → K) (hp : Conditions p) := LieCochain2 (algebra p hp) (coefficients p hp)

def oneValues (φ : Space K →ₗ[K] Coeff K) : Fin 3 → K := ![φ (e 0) 0, φ (e 1) 0, φ (e 2) 0]

def oneFrom (a : Fin 3 → K) : Space K →ₗ[K] Coeff K where
  toFun x := ![a 0 * x 0 + a 1 * x 1 + a 2 * x 2]
  map_add' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul' := by intros; ext r; fin_cases r <;> simp <;> ring

def oneCoordinates : (Space K →ₗ[K] Coeff K) ≃ₗ[K] (Fin 3 → K) where
  toFun := oneValues
  invFun := oneFrom
  left_inv φ := by
    apply (Pi.basisFun K (Fin 3)).ext
    intro i
    ext r
    fin_cases i <;> fin_cases r <;> simp [oneFrom, oneValues, e, Pi.basisFun_apply]
  right_inv a := by
    ext r
    fin_cases r <;> simp [oneFrom, oneValues, e]
  map_add' := by intros; ext r; fin_cases r <;> simp [oneValues]
  map_smul' := by intros; ext r; fin_cases r <;> simp [oneValues]

def twoValues (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp) : Fin 3 → K := ![ω (e 0) (e 1) 0, ω (e 0) (e 2) 0, ω (e 1) (e 2) 0]

def twoFrom (p : Fin 1 → K) (hp : Conditions p) (a : Fin 3 → K) : C2 p hp where
  eval x y := ![a 0 * (x 0 * y 1 - x 1 * y 0) + a 1 * (x 0 * y 2 - x 2 * y 0) + a 2 * (x 1 * y 2 - x 2 * y 1)]
  map_add_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_add_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  alternating' := by intros; ext r; fin_cases r <;> dsimp <;> ring

def twoCoordinates (p : Fin 1 → K) (hp : Conditions p) : C2 p hp ≃ₗ[K] (Fin 3 → K) where
  toFun := twoValues p hp
  invFun := twoFrom p hp
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

def readThird : (Space K →ₗ[K] Space K →ₗ[K] Space K →ₗ[K] Coeff K) →ₗ[K] (Fin 1 → K) where
  toFun t := ![t (e 0) (e 1) (e 2) 0]
  map_add' := by intros; ext r; fin_cases r <;> rfl
  map_smul' := by intros; ext r; fin_cases r <;> rfl

theorem readThird_detect (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp)
    (hz : readThird (differential2 (coefficients p hp) ω) = 0) :
    differential2 (coefficients p hp) ω = 0 := by
  have sample_0_1_2 : differential2 (coefficients p hp) ω (e 0) (e 1) (e 2) = 0 := by
    ext r
    fin_cases r
    · exact congrFun hz 0
  apply differential2_eq_zero_of_increasing
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hij <;> norm_num at hjk
  all_goals first | omega | exact sample_0_1_2

theorem differential1_coordinates (p : Fin 1 → K) (hp : Conditions p) (φ : Space K →ₗ[K] Coeff K) :
    twoCoordinates p hp (differential1 (coefficients p hp) φ) =
      (HeisenbergParameterCE.d1 p).toLin' (oneCoordinates φ) := by
  obtain ⟨a, rfl⟩ := oneCoordinates.symm.surjective φ
  rw [oneCoordinates.apply_symm_apply]
  change twoValues p hp (differential1 (coefficients p hp) (oneFrom a)) = (HeisenbergParameterCE.d1 p).toLin' a
  ext r
  fin_cases r <;>
    simp [twoValues, differential1, coefficients, action, algebra, bracket, oneFrom, e,
      HeisenbergParameterCE.d1, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem differential2_coordinates (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp) :
    (HeisenbergParameterCE.d2 p).toLin' (twoCoordinates p hp ω) = readThird (differential2 (coefficients p hp) ω) := by
  obtain ⟨a, rfl⟩ := (twoCoordinates p hp).symm.surjective ω
  rw [LinearEquiv.apply_symm_apply]
  change (HeisenbergParameterCE.d2 p).toLin' a = readThird (differential2 (coefficients p hp) (twoFrom p hp a))
  ext r
  fin_cases r <;>
    simp [readThird, differential2_apply, coefficients, action, algebra, bracket, twoFrom, e,
      HeisenbergParameterCE.d2, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

def reduction (p : Fin 1 → K) (hp : Conditions p) :
    Reduction (coefficients p hp) (Fin (HeisenbergParameterCE.dimension p) → K) :=
  (HeisenbergParameterCE.certificate p).toReduction.transport oneCoordinates (twoCoordinates p hp) readThird
    (differential1_coordinates p hp) (differential2_coordinates p hp) (readThird_detect p hp)

def h2Equiv (p : Fin 1 → K) (hp : Conditions p) :
    H2 (coefficients p hp) ≃ₗ[K] (Fin (HeisenbergParameterCE.dimension p) → K) := (reduction p hp).h2Equiv _

theorem h2_finrank (p : Fin 1 → K) (hp : Conditions p) :
    Module.finrank K (H2 (coefficients p hp)) = HeisenbergParameterCE.dimension p := by
  rw [(h2Equiv p hp).finrank_eq]
  simp

theorem boundary_iff (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp)
    (hω : IsTwoCocycle (coefficients p hp) ω) :
    IsTwoCoboundary (coefficients p hp) ω ↔ (reduction p hp).project ω = 0 :=
  (reduction p hp).exact_iff ω hω

theorem normal_form (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp)
    (hω : IsTwoCocycle (coefficients p hp) ω) :
    differential1 (coefficients p hp) ((reduction p hp).primitive ω) +
      (reduction p hp).represent ((reduction p hp).project ω) = ω := (reduction p hp).normal_form ω hω

end
end LeanPhy.Generated.HeisenbergParameter
