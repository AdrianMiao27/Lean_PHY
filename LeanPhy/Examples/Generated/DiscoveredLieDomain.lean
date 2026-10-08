import LeanPhy.Mathematics.FiniteLieCohomology
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/- Generated candidate: compile with Lean before using any conclusion.
Input SHA-256: deb7a94945770388238113743248dceb333f9664c6fcef4b96c40f94daf62712
Parameter order: a, b, t.
The decision tree includes all zero and nonzero branches under the declared
input conditions. No numerical sampling or physical interpretation is assumed. -/
namespace LeanPhy.Generated.DiscoveredLieDomainCE

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

def d1 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![(-1 * (x 0)), (x 2), 0;
    0, 0, (x 2);
    0, (-1 * (x 1)), 0]

def d2 (x : Fin 3 → K) : Matrix (Fin 1) (Fin 3) K :=
  !![(x 1), (-1 * (x 0)), (x 2)]

def project_0 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0;
    0, 1, 0;
    0, 0, 1]

def represent_0 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0;
    0, 1, 0;
    0, 0, 1]

def primitive_0 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  0

def correction_0 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 1) K :=
  0

def branch_0 (x : Fin 3 → K) (q0 : ((x 0) * (x 1)) = 0) (q1 : ((x 0) * (x 2)) = 0) (h0 : (x 0) = 0) (h1 : (x 2) = 0) (h2 : (x 1) = 0) :
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

def project_1 (x : Fin 3 → K) : Matrix (Fin 1) (Fin 3) K :=
  !![0, 1, 0]

def represent_1 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 1) K :=
  !![0;
    1;
    0]

def primitive_1 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0;
    0, 0, (-1 * ((x 1))⁻¹);
    0, 0, 0]

def correction_1 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 1) K :=
  !![((x 1))⁻¹;
    0;
    0]

def branch_1 (x : Fin 3 → K) (q0 : ((x 0) * (x 1)) = 0) (q1 : ((x 0) * (x 2)) = 0) (h0 : (x 0) = 0) (h1 : (x 2) = 0) (h2 : (x 1) ≠ 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 1 where
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

def project_2 (x : Fin 3 → K) : Matrix (Fin 0) (Fin 3) K :=
  0

def represent_2 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 0) K :=
  0

def primitive_2 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0;
    ((x 2))⁻¹, 0, 0;
    0, ((x 2))⁻¹, 0]

def correction_2 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 1) K :=
  !![0;
    0;
    ((x 2))⁻¹]

def branch_2 (x : Fin 3 → K) (q0 : ((x 0) * (x 1)) = 0) (q1 : ((x 0) * (x 2)) = 0) (h0 : (x 0) = 0) (h1 : (x 2) ≠ 0) (h2 : (x 1) = 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 0 where
  project := project_2 x
  represent := represent_2 x
  primitive := primitive_2 x
  correction := correction_2 x
  chain := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_2, represent_2, primitive_2, correction_2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  closed := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_2, represent_2, primitive_2, correction_2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  boundary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_2, represent_2, primitive_2, correction_2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  retract := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_2, represent_2, primitive_2, correction_2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  decompose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_2, represent_2, primitive_2, correction_2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

def project_3 (x : Fin 3 → K) : Matrix (Fin 0) (Fin 3) K :=
  0

def represent_3 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 0) K :=
  0

def primitive_3 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0;
    0, 0, (-1 * ((x 1))⁻¹);
    0, ((x 2))⁻¹, 0]

def correction_3 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 1) K :=
  !![((x 1))⁻¹;
    0;
    0]

def branch_3 (x : Fin 3 → K) (q0 : ((x 0) * (x 1)) = 0) (q1 : ((x 0) * (x 2)) = 0) (h0 : (x 0) = 0) (h1 : (x 2) ≠ 0) (h2 : (x 1) ≠ 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 0 where
  project := project_3 x
  represent := represent_3 x
  primitive := primitive_3 x
  correction := correction_3 x
  chain := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_3, represent_3, primitive_3, correction_3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  closed := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_3, represent_3, primitive_3, correction_3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  boundary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_3, represent_3, primitive_3, correction_3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  retract := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_3, represent_3, primitive_3, correction_3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  decompose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_3, represent_3, primitive_3, correction_3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

def project_4 (x : Fin 3 → K) : Matrix (Fin 1) (Fin 3) K :=
  !![0, 0, 1]

def represent_4 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 1) K :=
  !![0;
    0;
    1]

def primitive_4 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![(-1 * ((x 0))⁻¹), 0, 0;
    0, 0, 0;
    0, 0, 0]

def correction_4 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 1) K :=
  !![0;
    (-1 * ((x 0))⁻¹);
    0]

def branch_4 (x : Fin 3 → K) (q0 : ((x 0) * (x 1)) = 0) (q1 : ((x 0) * (x 2)) = 0) (h0 : (x 0) ≠ 0) (h1 : (x 1) = 0) (h2 : (x 2) = 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 1 where
  project := project_4 x
  represent := represent_4 x
  primitive := primitive_4 x
  correction := correction_4 x
  chain := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_4, represent_4, primitive_4, correction_4, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  closed := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_4, represent_4, primitive_4, correction_4, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  boundary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_4, represent_4, primitive_4, correction_4, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  retract := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_4, represent_4, primitive_4, correction_4, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  decompose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_4, represent_4, primitive_4, correction_4, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

def project_5 (x : Fin 3 → K) : Matrix (Fin 1) (Fin 3) K :=
  !![0, 0, 1]

def represent_5 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 1) K :=
  !![0;
    ((x 2) * ((x 0))⁻¹);
    1]

def primitive_5 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![(-1 * ((x 0))⁻¹), 0, 0;
    0, 0, 0;
    0, ((x 2))⁻¹, (-1 * ((x 0))⁻¹)]

def correction_5 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 1) K :=
  0

def branch_5 (x : Fin 3 → K) (q0 : ((x 0) * (x 1)) = 0) (q1 : ((x 0) * (x 2)) = 0) (h0 : (x 0) ≠ 0) (h1 : (x 1) = 0) (h2 : (x 2) ≠ 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 1 where
  project := project_5 x
  represent := represent_5 x
  primitive := primitive_5 x
  correction := correction_5 x
  chain := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_5, represent_5, primitive_5, correction_5, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  closed := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_5, represent_5, primitive_5, correction_5, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  boundary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_5, represent_5, primitive_5, correction_5, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  retract := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_5, represent_5, primitive_5, correction_5, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  decompose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_5, represent_5, primitive_5, correction_5, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

def project_6 (x : Fin 3 → K) : Matrix (Fin 1) (Fin 3) K :=
  !![0, 1, 0]

def represent_6 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 1) K :=
  !![((x 0) * ((x 1))⁻¹);
    1;
    0]

def primitive_6 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![(-1 * ((x 0))⁻¹), ((x 1))⁻¹, 0;
    0, 0, (-1 * ((x 1))⁻¹);
    0, 0, 0]

def correction_6 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 1) K :=
  0

def branch_6 (x : Fin 3 → K) (q0 : ((x 0) * (x 1)) = 0) (q1 : ((x 0) * (x 2)) = 0) (h0 : (x 0) ≠ 0) (h1 : (x 1) ≠ 0) (h2 : (x 2) = 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 1 where
  project := project_6 x
  represent := represent_6 x
  primitive := primitive_6 x
  correction := correction_6 x
  chain := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_6, represent_6, primitive_6, correction_6, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  closed := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_6, represent_6, primitive_6, correction_6, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  boundary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_6, represent_6, primitive_6, correction_6, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  retract := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_6, represent_6, primitive_6, correction_6, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  decompose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_6, represent_6, primitive_6, correction_6, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem impossible_7 (x : Fin 3 → K) (q0 : ((x 0) * (x 1)) = 0) (q1 : ((x 0) * (x 2)) = 0) (h0 : (x 0) ≠ 0) (h1 : (x 1) ≠ 0) (h2 : (x 2) ≠ 0) : False := by
  grind

def dimension (x : Fin 3 → K) : Nat :=
  (if (x 0) = 0 then (if (x 2) = 0 then (if (x 1) = 0 then 3 else 1) else (if (x 1) = 0 then 0 else 0)) else (if (x 1) = 0 then (if (x 2) = 0 then 1 else 1) else (if (x 2) = 0 then 1 else 0)))

def certificate (x : Fin 3 → K) (q0 : ((x 0) * (x 1)) = 0) (q1 : ((x 0) * (x 2)) = 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) (dimension x) := by
  by_cases h0 : (x 0) = 0
  · by_cases h1 : (x 2) = 0
    · by_cases h2 : (x 1) = 0
      · unfold dimension
        rw [ite_eq_left h0, ite_eq_left h1, ite_eq_left h2]
        exact branch_0 x q0 q1 h0 h1 h2
      · unfold dimension
        rw [ite_eq_left h0, ite_eq_left h1, ite_eq_right h2]
        exact branch_1 x q0 q1 h0 h1 h2
    · by_cases h2 : (x 1) = 0
      · unfold dimension
        rw [ite_eq_left h0, ite_eq_right h1, ite_eq_left h2]
        exact branch_2 x q0 q1 h0 h1 h2
      · unfold dimension
        rw [ite_eq_left h0, ite_eq_right h1, ite_eq_right h2]
        exact branch_3 x q0 q1 h0 h1 h2
  · by_cases h1 : (x 1) = 0
    · by_cases h2 : (x 2) = 0
      · unfold dimension
        rw [ite_eq_right h0, ite_eq_left h1, ite_eq_left h2]
        exact branch_4 x q0 q1 h0 h1 h2
      · unfold dimension
        rw [ite_eq_right h0, ite_eq_left h1, ite_eq_right h2]
        exact branch_5 x q0 q1 h0 h1 h2
    · by_cases h2 : (x 2) = 0
      · unfold dimension
        rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2]
        exact branch_6 x q0 q1 h0 h1 h2
      · exact (impossible_7 x q0 q1 h0 h1 h2).elim

def cohomologyEquiv (x : Fin 3 → K) (q0 : ((x 0) * (x 1)) = 0) (q1 : ((x 0) * (x 2)) = 0) :
    CohomologyReduction.Cohomology (d1 x).toLin' (d2 x).toLin' ≃ₗ[K] (Fin (dimension x) → K) :=
  (certificate x q0 q1).toReduction.quotientEquiv

theorem finrank_eq (x : Fin 3 → K) (q0 : ((x 0) * (x 1)) = 0) (q1 : ((x 0) * (x 2)) = 0) :
    Module.finrank K (CohomologyReduction.Cohomology (d1 x).toLin' (d2 x).toLin') = dimension x := by
  rw [(cohomologyEquiv x q0 q1).finrank_eq]
  simp

theorem exact_iff (x : Fin 3 → K) (q0 : ((x 0) * (x 1)) = 0) (q1 : ((x 0) * (x 2)) = 0)
    (ω : Fin 3 → K) (hω : (d2 x).toLin' ω = 0) :
    (∃ φ, (d1 x).toLin' φ = ω) ↔ (certificate x q0 q1).project.toLin' ω = 0 :=
  (certificate x q0 q1).toReduction.exact_iff ω hω

theorem normal_form (x : Fin 3 → K) (q0 : ((x 0) * (x 1)) = 0) (q1 : ((x 0) * (x 2)) = 0)
    (ω : Fin 3 → K) (hω : (d2 x).toLin' ω = 0) :
    (d1 x).toLin' ((certificate x q0 q1).primitive.toLin' ω) +
      (certificate x q0 q1).represent.toLin' ((certificate x q0 q1).project.toLin' ω) = ω :=
  (certificate x q0 q1).toReduction.normal_form ω hω

end
end LeanPhy.Generated.DiscoveredLieDomainCE

/- The model and every H2 conclusion below retain the declared parameter
conditions. The preceding matrices are connected to complete CE cochains. -/
namespace LeanPhy.Generated.DiscoveredLieDomain

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
structure Conditions (p : Fin 3 → K) : Prop where
  q0 : ((p 0) * (p 1)) = 0
  q1 : ((p 0) * (p 2)) = 0

def bracket (p : Fin 3 → K) (x y : Space K) : Space K := ![((p 0)) * (x 0 * y 1 - x 1 * y 0), ((p 1)) * (x 1 * y 2 - x 2 * y 1), 0]

def algebra (p : Fin 3 → K) (hp : Conditions p) : LeanPhy.Mathematics.LieAlgebra K (Space K) where
  bracket := bracket p
  add_left := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  add_right := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  smul_left := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  smul_right := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  zero_left := by intros; ext r; fin_cases r <;> simp [bracket]
  alternating := by intros; ext r; fin_cases r <;> dsimp [bracket] <;> ring
  antisymm := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  jacobi := by rcases hp with ⟨q0, q1⟩; intros; ext r; fin_cases r <;> simp [bracket] <;> (try ring_nf) <;> grind

def action (p : Fin 3 → K) (x : Space K) (v : Coeff K) : Coeff K := ![((p 2)) * (x 0 * v 0)]

def coefficients (p : Fin 3 → K) (hp : Conditions p) : LeanPhy.Mathematics.LieModule (algebra p hp) (Coeff K) where
  act := action p
  act_add_left' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  act_smul_left' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  act_add_right' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  act_smul_right' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  bracket_act' := by rcases hp with ⟨q0, q1⟩; intros; ext r; fin_cases r <;> simp [algebra, bracket, action] <;> (try ring_nf) <;> grind

/-- Extra restrictions supplied by the user, separate from discovered laws. -/
structure UserConditions (p : Fin 3 → K) : Prop where


/-- The full laws on arbitrary vectors, independent of any parameter equations. -/
structure ModelLaws (p : Fin 3 → K) : Prop where
  jacobi : ∀ x y z : Space K,
    bracket p x (bracket p y z) + bracket p y (bracket p z x) + bracket p z (bracket p x y) = 0
  representation : ∀ (x y : Space K) (v : Coeff K),
    action p (bracket p x y) v = action p x (action p y v) - action p y (action p x v)

/-- Exact admissibility: neither a missing equation nor an unnecessary extra
law restriction can pass both directions of this theorem. -/
theorem conditions_iff (p : Fin 3 → K) :
    Conditions p ↔ UserConditions p ∧ ModelLaws p := by
  constructor
  · intro hp
    refine ⟨⟨⟩, ?_⟩
    constructor
    · exact (algebra p hp).jacobi
    · exact (coefficients p hp).bracket_act'
  · rintro ⟨hu, hl⟩
    constructor
    · have hs := congrFun (hl.jacobi (e 0) (e 1) (e 2)) 0
      norm_num [bracket, action, e] at hs
      all_goals (try norm_num [bracket, action, e]) <;> grind
    · have hs := congrFun (hl.representation (e 0) (e 1) (e 0)) 0
      norm_num [bracket, action, e] at hs
      all_goals (try norm_num [bracket, action, e]) <;> grind

/-- Actual Lie algebra and module structures exist with exactly the supplied
bracket/action iff the discovered equations and user restrictions hold. -/
theorem conditions_iff_model (p : Fin 3 → K) :
    Conditions p ↔ UserConditions p ∧
      ∃ L : LeanPhy.Mathematics.LieAlgebra K (Space K), L.bracket = bracket p ∧
        ∃ M : LeanPhy.Mathematics.LieModule L (Coeff K), M.act = action p := by
  constructor
  · intro hp
    exact ⟨((conditions_iff p).mp hp).1, algebra p hp, rfl, coefficients p hp, rfl⟩
  · rintro ⟨hu, L, hL, M, hM⟩
    apply (conditions_iff p).mpr
    refine ⟨hu, ?_⟩
    constructor
    · intro x y z
      simpa only [hL] using L.jacobi x y z
    · intro x y v
      simpa only [hL, hM] using M.bracket_act' x y v

theorem invalid_of_conditions_fail (p : Fin 3 → K)
    (hu : UserConditions p) (h : ¬Conditions p) : ¬ModelLaws p := by
  intro hl
  exact h ((conditions_iff p).mpr ⟨hu, hl⟩)

abbrev C2 (p : Fin 3 → K) (hp : Conditions p) := LieCochain2 (algebra p hp) (coefficients p hp)

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

def twoValues (p : Fin 3 → K) (hp : Conditions p) (ω : C2 p hp) : Fin 3 → K := ![ω (e 0) (e 1) 0, ω (e 0) (e 2) 0, ω (e 1) (e 2) 0]

def twoFrom (p : Fin 3 → K) (hp : Conditions p) (a : Fin 3 → K) : C2 p hp where
  eval x y := ![a 0 * (x 0 * y 1 - x 1 * y 0) + a 1 * (x 0 * y 2 - x 2 * y 0) + a 2 * (x 1 * y 2 - x 2 * y 1)]
  map_add_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_add_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  alternating' := by intros; ext r; fin_cases r <;> dsimp <;> ring

def twoCoordinates (p : Fin 3 → K) (hp : Conditions p) : C2 p hp ≃ₗ[K] (Fin 3 → K) where
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

theorem readThird_detect (p : Fin 3 → K) (hp : Conditions p) (ω : C2 p hp)
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

theorem differential1_coordinates (p : Fin 3 → K) (hp : Conditions p) (φ : Space K →ₗ[K] Coeff K) :
    twoCoordinates p hp (differential1 (coefficients p hp) φ) =
      (DiscoveredLieDomainCE.d1 p).toLin' (oneCoordinates φ) := by
  obtain ⟨a, rfl⟩ := oneCoordinates.symm.surjective φ
  rw [oneCoordinates.apply_symm_apply]
  change twoValues p hp (differential1 (coefficients p hp) (oneFrom a)) = (DiscoveredLieDomainCE.d1 p).toLin' a
  ext r
  fin_cases r <;>
    simp [twoValues, differential1, coefficients, action, algebra, bracket, oneFrom, e,
      DiscoveredLieDomainCE.d1, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem differential2_coordinates (p : Fin 3 → K) (hp : Conditions p) (ω : C2 p hp) :
    (DiscoveredLieDomainCE.d2 p).toLin' (twoCoordinates p hp ω) = readThird (differential2 (coefficients p hp) ω) := by
  obtain ⟨a, rfl⟩ := (twoCoordinates p hp).symm.surjective ω
  rw [LinearEquiv.apply_symm_apply]
  change (DiscoveredLieDomainCE.d2 p).toLin' a = readThird (differential2 (coefficients p hp) (twoFrom p hp a))
  ext r
  fin_cases r <;>
    simp [readThird, differential2_apply, coefficients, action, algebra, bracket, twoFrom, e,
      DiscoveredLieDomainCE.d2, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

def reduction (p : Fin 3 → K) (hp : Conditions p) :
    Reduction (coefficients p hp) (Fin (DiscoveredLieDomainCE.dimension p) → K) :=
  (DiscoveredLieDomainCE.certificate p hp.q0 hp.q1).toReduction.transport oneCoordinates (twoCoordinates p hp) readThird
    (differential1_coordinates p hp) (differential2_coordinates p hp) (readThird_detect p hp)

def h2Equiv (p : Fin 3 → K) (hp : Conditions p) :
    H2 (coefficients p hp) ≃ₗ[K] (Fin (DiscoveredLieDomainCE.dimension p) → K) := (reduction p hp).h2Equiv _

theorem h2_finrank (p : Fin 3 → K) (hp : Conditions p) :
    Module.finrank K (H2 (coefficients p hp)) = DiscoveredLieDomainCE.dimension p := by
  rw [(h2Equiv p hp).finrank_eq]
  simp

theorem boundary_iff (p : Fin 3 → K) (hp : Conditions p) (ω : C2 p hp)
    (hω : IsTwoCocycle (coefficients p hp) ω) :
    IsTwoCoboundary (coefficients p hp) ω ↔ (reduction p hp).project ω = 0 :=
  (reduction p hp).exact_iff ω hω

theorem normal_form (p : Fin 3 → K) (hp : Conditions p) (ω : C2 p hp)
    (hω : IsTwoCocycle (coefficients p hp) ω) :
    differential1 (coefficients p hp) ((reduction p hp).primitive ω) +
      (reduction p hp).represent ((reduction p hp).project ω) = ω := (reduction p hp).normal_form ω hω

end
end LeanPhy.Generated.DiscoveredLieDomain
