import LeanPhy.Mathematics.FiniteLieCohomology3
import LeanPhy.Mathematics.LieDeformationObstruction
import LeanPhy.Mathematics.LieDeformationReduction
import LeanPhy.Mathematics.FiniteLieCohomology
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/- Generated candidate: compile with Lean before using any conclusion.
Input SHA-256: c10403ba6f251c073c596fa5b0d681186046b760eeb7b9bcd1ae73f3b6cc7d89
Parameter order: g.
The decision tree includes all zero and nonzero branches under the declared
input conditions. No numerical sampling or physical interpretation is assumed. -/
namespace LeanPhy.Generated.HeisenbergThirdParameterCE

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

def d1 (x : Fin 1 → K) : Matrix (Fin 9) (Fin 9) K :=
  !![0, 0, 0, 0, 0, 0, (-1 * (x 0)), 0, 0;
    0, 0, 0, 0, 0, 0, 0, (-1 * (x 0)), 0;
    (x 0), 0, 0, 0, (x 0), 0, 0, 0, (-1 * (x 0));
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, (x 0), 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, (-1 * (x 0)), 0, 0]

def d2 (x : Fin 1 → K) : Matrix (Fin 3) (Fin 9) K :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, (x 0), 0, 0, 0, (x 0), 0]

def project_0 (x : Fin 1 → K) : Matrix (Fin 9) (Fin 9) K :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1]

def represent_0 (x : Fin 1 → K) : Matrix (Fin 9) (Fin 9) K :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1]

def primitive_0 (x : Fin 1 → K) : Matrix (Fin 9) (Fin 9) K :=
  0

def correction_0 (x : Fin 1 → K) : Matrix (Fin 9) (Fin 3) K :=
  0

theorem chain_0 (x : Fin 1 → K) (h0 : (x 0) = 0) :
    d2 x * d1 x = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem closed_0 (x : Fin 1 → K) (h0 : (x 0) = 0) :
    d2 x * represent_0 x = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem boundary_0 (x : Fin 1 → K) (h0 : (x 0) = 0) :
    project_0 x * d1 x = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem retract_0 (x : Fin 1 → K) (h0 : (x 0) = 0) :
    project_0 x * represent_0 x = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_0_row_0 (x : Fin 1 → K) (h0 : (x 0) = 0) (j : Fin 9) :
    (d1 x * primitive_0 x + represent_0 x * project_0 x + correction_0 x * d2 x) 0 j = (1 : Matrix (Fin 9) (Fin 9) K) 0 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_0_row_1 (x : Fin 1 → K) (h0 : (x 0) = 0) (j : Fin 9) :
    (d1 x * primitive_0 x + represent_0 x * project_0 x + correction_0 x * d2 x) 1 j = (1 : Matrix (Fin 9) (Fin 9) K) 1 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_0_row_2 (x : Fin 1 → K) (h0 : (x 0) = 0) (j : Fin 9) :
    (d1 x * primitive_0 x + represent_0 x * project_0 x + correction_0 x * d2 x) 2 j = (1 : Matrix (Fin 9) (Fin 9) K) 2 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_0_row_3 (x : Fin 1 → K) (h0 : (x 0) = 0) (j : Fin 9) :
    (d1 x * primitive_0 x + represent_0 x * project_0 x + correction_0 x * d2 x) 3 j = (1 : Matrix (Fin 9) (Fin 9) K) 3 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_0_row_4 (x : Fin 1 → K) (h0 : (x 0) = 0) (j : Fin 9) :
    (d1 x * primitive_0 x + represent_0 x * project_0 x + correction_0 x * d2 x) 4 j = (1 : Matrix (Fin 9) (Fin 9) K) 4 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_0_row_5 (x : Fin 1 → K) (h0 : (x 0) = 0) (j : Fin 9) :
    (d1 x * primitive_0 x + represent_0 x * project_0 x + correction_0 x * d2 x) 5 j = (1 : Matrix (Fin 9) (Fin 9) K) 5 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_0_row_6 (x : Fin 1 → K) (h0 : (x 0) = 0) (j : Fin 9) :
    (d1 x * primitive_0 x + represent_0 x * project_0 x + correction_0 x * d2 x) 6 j = (1 : Matrix (Fin 9) (Fin 9) K) 6 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_0_row_7 (x : Fin 1 → K) (h0 : (x 0) = 0) (j : Fin 9) :
    (d1 x * primitive_0 x + represent_0 x * project_0 x + correction_0 x * d2 x) 7 j = (1 : Matrix (Fin 9) (Fin 9) K) 7 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_0_row_8 (x : Fin 1 → K) (h0 : (x 0) = 0) (j : Fin 9) :
    (d1 x * primitive_0 x + represent_0 x * project_0 x + correction_0 x * d2 x) 8 j = (1 : Matrix (Fin 9) (Fin 9) K) 8 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_0 (x : Fin 1 → K) (h0 : (x 0) = 0) :
    d1 x * primitive_0 x + represent_0 x * project_0 x + correction_0 x * d2 x = 1 := by
  ext i j
  fin_cases i
  · exact decompose_0_row_0 x h0 j
  · exact decompose_0_row_1 x h0 j
  · exact decompose_0_row_2 x h0 j
  · exact decompose_0_row_3 x h0 j
  · exact decompose_0_row_4 x h0 j
  · exact decompose_0_row_5 x h0 j
  · exact decompose_0_row_6 x h0 j
  · exact decompose_0_row_7 x h0 j
  · exact decompose_0_row_8 x h0 j

def branch_0 (x : Fin 1 → K) (h0 : (x 0) = 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 9 where
  project := project_0 x
  represent := represent_0 x
  primitive := primitive_0 x
  correction := correction_0 x
  chain := chain_0 x h0
  closed := closed_0 x h0
  boundary := boundary_0 x h0
  retract := retract_0 x h0
  decompose := decompose_0 x h0

def project_1 (x : Fin 1 → K) : Matrix (Fin 5) (Fin 9) K :=
  !![1, 0, 0, 0, 0, 0, 0, 0, -1;
    0, 1, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0]

def represent_1 (x : Fin 1 → K) : Matrix (Fin 9) (Fin 5) K :=
  !![1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 0, 0, 0;
    0, 0, 0, 0, -1;
    0, 0, 1, 0, 0;
    0, 0, 0, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1;
    0, 0, 0, 0, 0]

def primitive_1 (x : Fin 1 → K) : Matrix (Fin 9) (Fin 9) K :=
  !![0, 0, ((x 0))⁻¹, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-1 * ((x 0))⁻¹);
    0, 0, 0, 0, 0, ((x 0))⁻¹, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0]

def correction_1 (x : Fin 1 → K) : Matrix (Fin 9) (Fin 3) K :=
  !![0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, ((x 0))⁻¹;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0]

theorem chain_1 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) :
    d2 x * d1 x = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem closed_1 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) :
    d2 x * represent_1 x = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem boundary_1 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) :
    project_1 x * d1 x = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem retract_1 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) :
    project_1 x * represent_1 x = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_1_row_0 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) (j : Fin 9) :
    (d1 x * primitive_1 x + represent_1 x * project_1 x + correction_1 x * d2 x) 0 j = (1 : Matrix (Fin 9) (Fin 9) K) 0 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_1_row_1 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) (j : Fin 9) :
    (d1 x * primitive_1 x + represent_1 x * project_1 x + correction_1 x * d2 x) 1 j = (1 : Matrix (Fin 9) (Fin 9) K) 1 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_1_row_2 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) (j : Fin 9) :
    (d1 x * primitive_1 x + represent_1 x * project_1 x + correction_1 x * d2 x) 2 j = (1 : Matrix (Fin 9) (Fin 9) K) 2 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_1_row_3 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) (j : Fin 9) :
    (d1 x * primitive_1 x + represent_1 x * project_1 x + correction_1 x * d2 x) 3 j = (1 : Matrix (Fin 9) (Fin 9) K) 3 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_1_row_4 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) (j : Fin 9) :
    (d1 x * primitive_1 x + represent_1 x * project_1 x + correction_1 x * d2 x) 4 j = (1 : Matrix (Fin 9) (Fin 9) K) 4 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_1_row_5 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) (j : Fin 9) :
    (d1 x * primitive_1 x + represent_1 x * project_1 x + correction_1 x * d2 x) 5 j = (1 : Matrix (Fin 9) (Fin 9) K) 5 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_1_row_6 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) (j : Fin 9) :
    (d1 x * primitive_1 x + represent_1 x * project_1 x + correction_1 x * d2 x) 6 j = (1 : Matrix (Fin 9) (Fin 9) K) 6 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_1_row_7 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) (j : Fin 9) :
    (d1 x * primitive_1 x + represent_1 x * project_1 x + correction_1 x * d2 x) 7 j = (1 : Matrix (Fin 9) (Fin 9) K) 7 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_1_row_8 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) (j : Fin 9) :
    (d1 x * primitive_1 x + represent_1 x * project_1 x + correction_1 x * d2 x) 8 j = (1 : Matrix (Fin 9) (Fin 9) K) 8 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_1 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) :
    d1 x * primitive_1 x + represent_1 x * project_1 x + correction_1 x * d2 x = 1 := by
  ext i j
  fin_cases i
  · exact decompose_1_row_0 x h0 j
  · exact decompose_1_row_1 x h0 j
  · exact decompose_1_row_2 x h0 j
  · exact decompose_1_row_3 x h0 j
  · exact decompose_1_row_4 x h0 j
  · exact decompose_1_row_5 x h0 j
  · exact decompose_1_row_6 x h0 j
  · exact decompose_1_row_7 x h0 j
  · exact decompose_1_row_8 x h0 j

def branch_1 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 5 where
  project := project_1 x
  represent := represent_1 x
  primitive := primitive_1 x
  correction := correction_1 x
  chain := chain_1 x h0
  closed := closed_1 x h0
  boundary := boundary_1 x h0
  retract := retract_1 x h0
  decompose := decompose_1 x h0

def dimension (x : Fin 1 → K) : Nat :=
  (if (x 0) = 0 then 9 else 5)

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
    (ω : Fin 9 → K) (hω : (d2 x).toLin' ω = 0) :
    (∃ φ, (d1 x).toLin' φ = ω) ↔ (certificate x).project.toLin' ω = 0 :=
  (certificate x).toReduction.exact_iff ω hω

theorem normal_form (x : Fin 1 → K)
    (ω : Fin 9 → K) (hω : (d2 x).toLin' ω = 0) :
    (d1 x).toLin' ((certificate x).primitive.toLin' ω) +
      (certificate x).represent.toLin' ((certificate x).project.toLin' ω) = ω :=
  (certificate x).toReduction.normal_form ω hω

end
end LeanPhy.Generated.HeisenbergThirdParameterCE

/- The model and every H2 conclusion below retain the declared parameter
conditions. The preceding matrices are connected to complete CE cochains. -/
namespace LeanPhy.Generated.HeisenbergThirdParameter

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
abbrev Coeff (K : Type*) := Fin 3 → K

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

def action (p : Fin 1 → K) (x : Space K) (v : Coeff K) : Coeff K := bracket p x v

def coefficients (p : Fin 1 → K) (hp : Conditions p) :
    LeanPhy.Mathematics.LieModule (algebra p hp) (Coeff K) := adjointLieModule (algebra p hp)

theorem coefficients_adjoint (p : Fin 1 → K) (hp : Conditions p) :
    coefficients p hp = adjointLieModule (algebra p hp) := rfl

abbrev C2 (p : Fin 1 → K) (hp : Conditions p) := LieCochain2 (algebra p hp) (coefficients p hp)

def oneValues (φ : Space K →ₗ[K] Coeff K) : Fin 9 → K := ![φ (e 0) 0, φ (e 0) 1, φ (e 0) 2, φ (e 1) 0, φ (e 1) 1, φ (e 1) 2, φ (e 2) 0, φ (e 2) 1, φ (e 2) 2]

def oneFrom (a : Fin 9 → K) : Space K →ₗ[K] Coeff K where
  toFun x := ![a 0 * x 0 + a 3 * x 1 + a 6 * x 2, a 1 * x 0 + a 4 * x 1 + a 7 * x 2, a 2 * x 0 + a 5 * x 1 + a 8 * x 2]
  map_add' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul' := by intros; ext r; fin_cases r <;> simp <;> ring

def oneCoordinates : (Space K →ₗ[K] Coeff K) ≃ₗ[K] (Fin 9 → K) where
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

def twoValues (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp) : Fin 9 → K := ![ω (e 0) (e 1) 0, ω (e 0) (e 1) 1, ω (e 0) (e 1) 2, ω (e 0) (e 2) 0, ω (e 0) (e 2) 1, ω (e 0) (e 2) 2, ω (e 1) (e 2) 0, ω (e 1) (e 2) 1, ω (e 1) (e 2) 2]

def twoFrom (p : Fin 1 → K) (hp : Conditions p) (a : Fin 9 → K) : C2 p hp where
  eval x y := ![a 0 * (x 0 * y 1 - x 1 * y 0) + a 3 * (x 0 * y 2 - x 2 * y 0) + a 6 * (x 1 * y 2 - x 2 * y 1), a 1 * (x 0 * y 1 - x 1 * y 0) + a 4 * (x 0 * y 2 - x 2 * y 0) + a 7 * (x 1 * y 2 - x 2 * y 1), a 2 * (x 0 * y 1 - x 1 * y 0) + a 5 * (x 0 * y 2 - x 2 * y 0) + a 8 * (x 1 * y 2 - x 2 * y 1)]
  map_add_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_add_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  alternating' := by intros; ext r; fin_cases r <;> dsimp <;> ring

def twoCoordinates (p : Fin 1 → K) (hp : Conditions p) : C2 p hp ≃ₗ[K] (Fin 9 → K) where
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

def readThird : (Space K →ₗ[K] Space K →ₗ[K] Space K →ₗ[K] Coeff K) →ₗ[K] (Fin 3 → K) where
  toFun t := ![t (e 0) (e 1) (e 2) 0, t (e 0) (e 1) (e 2) 1, t (e 0) (e 1) (e 2) 2]
  map_add' := by intros; ext r; fin_cases r <;> rfl
  map_smul' := by intros; ext r; fin_cases r <;> rfl

theorem readThird_detect (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp)
    (hz : readThird (differential2 (coefficients p hp) ω) = 0) :
    differential2 (coefficients p hp) ω = 0 := by
  have sample_0_1_2 : differential2 (coefficients p hp) ω (e 0) (e 1) (e 2) = 0 := by
    ext r
    fin_cases r
    · exact congrFun hz 0
    · exact congrFun hz 1
    · exact congrFun hz 2
  apply differential2_eq_zero_of_increasing
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hij <;> norm_num at hjk
  all_goals first | omega | exact sample_0_1_2

theorem differential1_coordinates (p : Fin 1 → K) (hp : Conditions p) (φ : Space K →ₗ[K] Coeff K) :
    twoCoordinates p hp (differential1 (coefficients p hp) φ) =
      (HeisenbergThirdParameterCE.d1 p).toLin' (oneCoordinates φ) := by
  obtain ⟨a, rfl⟩ := oneCoordinates.symm.surjective φ
  rw [oneCoordinates.apply_symm_apply]
  change twoValues p hp (differential1 (coefficients p hp) (oneFrom a)) = (HeisenbergThirdParameterCE.d1 p).toLin' a
  ext r
  fin_cases r <;>
    simp [twoValues, differential1, coefficients, adjointLieModule, action, algebra, bracket, oneFrom, e,
      HeisenbergThirdParameterCE.d1, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem differential2_coordinates (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp) :
    (HeisenbergThirdParameterCE.d2 p).toLin' (twoCoordinates p hp ω) = readThird (differential2 (coefficients p hp) ω) := by
  obtain ⟨a, rfl⟩ := (twoCoordinates p hp).symm.surjective ω
  rw [LinearEquiv.apply_symm_apply]
  change (HeisenbergThirdParameterCE.d2 p).toLin' a = readThird (differential2 (coefficients p hp) (twoFrom p hp a))
  ext r
  fin_cases r <;>
    simp [readThird, differential2_apply, coefficients, adjointLieModule, action, algebra, bracket, twoFrom, e,
      HeisenbergThirdParameterCE.d2, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

def reduction (p : Fin 1 → K) (hp : Conditions p) :
    Reduction (coefficients p hp) (Fin (HeisenbergThirdParameterCE.dimension p) → K) :=
  (HeisenbergThirdParameterCE.certificate p).toReduction.transport oneCoordinates (twoCoordinates p hp) readThird
    (differential1_coordinates p hp) (differential2_coordinates p hp) (readThird_detect p hp)

def h2Equiv (p : Fin 1 → K) (hp : Conditions p) :
    H2 (coefficients p hp) ≃ₗ[K] (Fin (HeisenbergThirdParameterCE.dimension p) → K) := (reduction p hp).h2Equiv _

theorem h2_finrank (p : Fin 1 → K) (hp : Conditions p) :
    Module.finrank K (H2 (coefficients p hp)) = HeisenbergThirdParameterCE.dimension p := by
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

/-- Every coordinate tuple supplies a closed representative and an actual first-order Lie algebra. -/
noncomputable def representativeDeformation (p : Fin 1 → K) (hp : Conditions p) :=
  LieDeformation.Reduction.deformation (reduction p hp)

/-- Closed deformation directions are equivalent exactly when their computed coordinates agree. -/
theorem deformation_equivalent_iff (p : Fin 1 → K) (hp : Conditions p) (ω η : (C2 p hp))
    (hω : IsTwoCocycle (coefficients p hp) ω) (hη : IsTwoCocycle (coefficients p hp) η) :
    Nonempty (LieDeformation.Equivalence ω η) ↔ (reduction p hp).project ω = (reduction p hp).project η :=
  LieDeformation.Reduction.equivalent_iff (reduction p hp) ω η hω hη

/-- A concrete invertible generator change puts a closed direction in normal form. -/
noncomputable def normalizeDeformation (p : Fin 1 → K) (hp : Conditions p) (ω : (C2 p hp)) (hω : IsTwoCocycle (coefficients p hp) ω) :
    LieDeformation.Equivalence ω ((reduction p hp).represent ((reduction p hp).project ω)) :=
  LieDeformation.Reduction.normalize (reduction p hp) ω hω

theorem deformation_removable_iff (p : Fin 1 → K) (hp : Conditions p) (ω : (C2 p hp)) (hω : IsTwoCocycle (coefficients p hp) ω) :
    Nonempty (LieDeformation.Equivalence ω 0) ↔ (reduction p hp).project ω = 0 :=
  LieDeformation.Reduction.removable_iff (reduction p hp) ω hω

/-- Vanishing coordinates give an explicit trivializing change of generators. -/
noncomputable def trivializeDeformation (p : Fin 1 → K) (hp : Conditions p) (ω : (C2 p hp)) (hω : IsTwoCocycle (coefficients p hp) ω)
    (h : (reduction p hp).project ω = 0) : LieDeformation.Equivalence ω 0 :=
  LieDeformation.Reduction.trivialize (reduction p hp) ω hω h

end
end LeanPhy.Generated.HeisenbergThirdParameter

namespace LeanPhy.Generated.HeisenbergThirdParameterThirdCE

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

def d1 (x : Fin 1 → K) : Matrix (Fin 3) (Fin 9) K :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, (x 0), 0, 0, 0, (x 0), 0]

def d2 (x : Fin 1 → K) : Matrix (Fin 0) (Fin 3) K :=
  0

def project_0 (x : Fin 1 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0;
    0, 1, 0;
    0, 0, 1]

def represent_0 (x : Fin 1 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0;
    0, 1, 0;
    0, 0, 1]

def primitive_0 (x : Fin 1 → K) : Matrix (Fin 9) (Fin 3) K :=
  0

def correction_0 (x : Fin 1 → K) : Matrix (Fin 3) (Fin 0) K :=
  0

theorem chain_0 (x : Fin 1 → K) (h0 : (x 0) = 0) :
    d2 x * d1 x = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem closed_0 (x : Fin 1 → K) (h0 : (x 0) = 0) :
    d2 x * represent_0 x = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem boundary_0 (x : Fin 1 → K) (h0 : (x 0) = 0) :
    project_0 x * d1 x = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem retract_0 (x : Fin 1 → K) (h0 : (x 0) = 0) :
    project_0 x * represent_0 x = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_0_row_0 (x : Fin 1 → K) (h0 : (x 0) = 0) (j : Fin 3) :
    (d1 x * primitive_0 x + represent_0 x * project_0 x + correction_0 x * d2 x) 0 j = (1 : Matrix (Fin 3) (Fin 3) K) 0 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_0_row_1 (x : Fin 1 → K) (h0 : (x 0) = 0) (j : Fin 3) :
    (d1 x * primitive_0 x + represent_0 x * project_0 x + correction_0 x * d2 x) 1 j = (1 : Matrix (Fin 3) (Fin 3) K) 1 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_0_row_2 (x : Fin 1 → K) (h0 : (x 0) = 0) (j : Fin 3) :
    (d1 x * primitive_0 x + represent_0 x * project_0 x + correction_0 x * d2 x) 2 j = (1 : Matrix (Fin 3) (Fin 3) K) 2 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_0, represent_0, primitive_0, correction_0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_0 (x : Fin 1 → K) (h0 : (x 0) = 0) :
    d1 x * primitive_0 x + represent_0 x * project_0 x + correction_0 x * d2 x = 1 := by
  ext i j
  fin_cases i
  · exact decompose_0_row_0 x h0 j
  · exact decompose_0_row_1 x h0 j
  · exact decompose_0_row_2 x h0 j

def branch_0 (x : Fin 1 → K) (h0 : (x 0) = 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 3 where
  project := project_0 x
  represent := represent_0 x
  primitive := primitive_0 x
  correction := correction_0 x
  chain := chain_0 x h0
  closed := closed_0 x h0
  boundary := boundary_0 x h0
  retract := retract_0 x h0
  decompose := decompose_0 x h0

def project_1 (x : Fin 1 → K) : Matrix (Fin 2) (Fin 3) K :=
  !![1, 0, 0;
    0, 1, 0]

def represent_1 (x : Fin 1 → K) : Matrix (Fin 3) (Fin 2) K :=
  !![1, 0;
    0, 1;
    0, 0]

def primitive_1 (x : Fin 1 → K) : Matrix (Fin 9) (Fin 3) K :=
  !![0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, ((x 0))⁻¹;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0]

def correction_1 (x : Fin 1 → K) : Matrix (Fin 3) (Fin 0) K :=
  0

theorem chain_1 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) :
    d2 x * d1 x = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem closed_1 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) :
    d2 x * represent_1 x = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem boundary_1 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) :
    project_1 x * d1 x = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem retract_1 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) :
    project_1 x * represent_1 x = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_1_row_0 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) (j : Fin 3) :
    (d1 x * primitive_1 x + represent_1 x * project_1 x + correction_1 x * d2 x) 0 j = (1 : Matrix (Fin 3) (Fin 3) K) 0 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_1_row_1 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) (j : Fin 3) :
    (d1 x * primitive_1 x + represent_1 x * project_1 x + correction_1 x * d2 x) 1 j = (1 : Matrix (Fin 3) (Fin 3) K) 1 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_1_row_2 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) (j : Fin 3) :
    (d1 x * primitive_1 x + represent_1 x * project_1 x + correction_1 x * d2 x) 2 j = (1 : Matrix (Fin 3) (Fin 3) K) 2 j := by
    fin_cases j <;>
      norm_num [d1, d2, project_1, represent_1, primitive_1, correction_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

theorem decompose_1 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) :
    d1 x * primitive_1 x + represent_1 x * project_1 x + correction_1 x * d2 x = 1 := by
  ext i j
  fin_cases i
  · exact decompose_1_row_0 x h0 j
  · exact decompose_1_row_1 x h0 j
  · exact decompose_1_row_2 x h0 j

def branch_1 (x : Fin 1 → K) (h0 : (x 0) ≠ 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 2 where
  project := project_1 x
  represent := represent_1 x
  primitive := primitive_1 x
  correction := correction_1 x
  chain := chain_1 x h0
  closed := closed_1 x h0
  boundary := boundary_1 x h0
  retract := retract_1 x h0
  decompose := decompose_1 x h0

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
end LeanPhy.Generated.HeisenbergThirdParameterThirdCE

namespace LeanPhy.Generated.HeisenbergThirdParameter
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates
open scoped _root_.Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
set_option maxSynthPendingDepth 7
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

abbrev C3 (p : Fin 1 → K) (hp : Conditions p) := LieCochain3 (algebra p hp) (coefficients p hp)

def threeExpr (a : Fin 3 → K) (x y z : (Space K)) : (Coeff K) := ![a 0 * (x 0 * y 1 * z 2 - x 0 * y 2 * z 1 - x 1 * y 0 * z 2 + x 1 * y 2 * z 0 + x 2 * y 0 * z 1 - x 2 * y 1 * z 0), a 1 * (x 0 * y 1 * z 2 - x 0 * y 2 * z 1 - x 1 * y 0 * z 2 + x 1 * y 2 * z 0 + x 2 * y 0 * z 1 - x 2 * y 1 * z 0), a 2 * (x 0 * y 1 * z 2 - x 0 * y 2 * z 1 - x 1 * y 0 * z 2 + x 1 * y 2 * z 0 + x 2 * y 0 * z 1 - x 2 * y 1 * z 0)]

def threeLinear (a : Fin 3 → K) : (Space K) →ₗ[K] (Space K) →ₗ[K] (Space K) →ₗ[K] (Coeff K) where
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

def threeFrom (p : Fin 1 → K) (hp : Conditions p) (a : Fin 3 → K) : (C3 p hp) := ⟨threeLinear a,by
  constructor
  · intro x z; change threeExpr a x x z = 0
    ext r; fin_cases r <;> dsimp [threeExpr] <;> ring
  · intro x y; change threeExpr a x y y = 0
    ext r; fin_cases r <;> dsimp [threeExpr] <;> ring⟩

def threeValues (p : Fin 1 → K) (hp : Conditions p) (t : (C3 p hp)) : Fin 3 → K := readThird t.val

/-- Coordinates cover all alternating three-cochains. -/
noncomputable def threeCoordinates (p : Fin 1 → K) (hp : Conditions p) : (C3 p hp) ≃ₗ[K] (Fin 3 → K) where
  toFun := (threeValues p hp)
  invFun := (threeFrom p hp)
  left_inv t := by
    apply three_ext_increasing
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> fin_cases k <;> norm_num at hjk
    all_goals ext r; fin_cases r <;> simp [threeFrom,threeLinear,threeExpr,threeValues,readThird,e]
  right_inv a := by
    ext r; fin_cases r <;> simp [threeValues,readThird,threeFrom,threeLinear,threeExpr,e]
  map_add' := by intros; ext r; fin_cases r <;> rfl
  map_smul' := by intros; ext r; fin_cases r <;> rfl

def readFourth : ((Space K) →ₗ[K] (Space K) →ₗ[K] (Space K) →ₗ[K] (Space K) →ₗ[K] (Coeff K)) →ₗ[K] (Fin 0 → K) where
  toFun t := ![]
  map_add' := by intros; ext r; fin_cases r <;> rfl
  map_smul' := by intros; ext r; fin_cases r <;> rfl

theorem readFourth_detect (p : Fin 1 → K) (hp : Conditions p) (t : (C3 p hp)) (hz : readFourth (differential3 (coefficients p hp) t) = 0) :
    differential3 (coefficients p hp) t = 0 := by

  apply differential3_eq_zero_of_increasing
  intro i j k l hij hjk hkl
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> fin_cases k <;> norm_num at hjk <;> fin_cases l <;> norm_num at hkl
  all_goals first | omega

theorem differential2_third_coordinates (p : Fin 1 → K) (hp : Conditions p) (ω : (C2 p hp)) :
    (threeCoordinates p hp) (differential2ToThree (coefficients p hp) ω) = (HeisenbergThirdParameterThirdCE.d1 p).toLin' ((twoCoordinates p hp) ω) :=
  (differential2_coordinates p hp ω).symm

theorem differential3_coordinates (p : Fin 1 → K) (hp : Conditions p) (t : (C3 p hp)) :
    (HeisenbergThirdParameterThirdCE.d2 p).toLin' ((threeCoordinates p hp) t) = readFourth (differential3 (coefficients p hp) t) := by
  obtain ⟨a,rfl⟩ := (threeCoordinates p hp).symm.surjective t
  rw [(threeCoordinates p hp).apply_symm_apply]
  change (HeisenbergThirdParameterThirdCE.d2 p).toLin' a = readFourth (differential3 (coefficients p hp) ((threeFrom p hp) a))
  ext r; fin_cases r <;>
    simp [readFourth,differential3_apply,differential3Expr,coefficients,adjointLieModule,action,algebra,
      bracket,threeFrom,threeLinear,threeExpr,e,HeisenbergThirdParameterThirdCE.d2,Matrix.toLin'_apply,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

/-- Both differentials and every parameter branch are checked before this transport. -/
def thirdReduction (p : Fin 1 → K) (hp : Conditions p) :
    ThirdReduction (coefficients p hp) (Fin (HeisenbergThirdParameterThirdCE.dimension p) → K) :=
  (HeisenbergThirdParameterThirdCE.certificate p).toReduction.transport (twoCoordinates p hp) (threeCoordinates p hp) readFourth
    (differential2_third_coordinates p hp) (differential3_coordinates p hp) (readFourth_detect p hp)

def h3Equiv (p : Fin 1 → K) (hp : Conditions p) : H3 (coefficients p hp) ≃ₗ[K] (Fin (HeisenbergThirdParameterThirdCE.dimension p) → K) :=
  (thirdReduction p hp).h3Equiv (coefficients p hp)

theorem h3_finrank (p : Fin 1 → K) (hp : Conditions p) :
    Module.finrank K (H3 (coefficients p hp)) = HeisenbergThirdParameterThirdCE.dimension p := by
  rw [(h3Equiv p hp).finrank_eq]; simp

theorem third_boundary_iff (p : Fin 1 → K) (hp : Conditions p) (t : C3 p hp) (ht : IsThreeCocycle (coefficients p hp) t) :
    IsThreeCoboundary (coefficients p hp) t ↔ (thirdReduction p hp).project t = 0 :=
  (thirdReduction p hp).exact_iff t ht

theorem third_normal_form (p : Fin 1 → K) (hp : Conditions p) (t : C3 p hp) (ht : IsThreeCocycle (coefficients p hp) t) :
    differential2ToThree (coefficients p hp) ((thirdReduction p hp).primitive t) +
      (thirdReduction p hp).represent ((thirdReduction p hp).project t) = t :=
  (thirdReduction p hp).normal_form t ht

/-- Intrinsic H³ coordinates on this parameter fiber. -/
def intrinsicObstruction (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp) :=
  (thirdReduction p hp).project (LieDeformation.obstructionCochain ω)

theorem intrinsicObstruction_class (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp)
    (hω : IsTwoCocycle (coefficients p hp) ω) :
    h3Equiv p hp (LieDeformation.obstructionClass ω hω) = intrinsicObstruction p hp ω := rfl

theorem intrinsic_extension_iff (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp)
    (hω : IsTwoCocycle (coefficients p hp) ω) :
    LieDeformation.SecondExtendable ω ↔ intrinsicObstruction p hp ω = 0 := by
  rw [LieDeformation.secondExtendable_iff_obstructionClass_zero ω hω]
  exact (map_eq_zero_iff (h3Equiv p hp) (h3Equiv p hp).injective).symm

def intrinsicCorrection (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp) : C2 p hp :=
  LieDeformation.ThirdReduction.correction (thirdReduction p hp) ω

theorem intrinsicCorrection_cancels (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp)
    (hω : IsTwoCocycle (coefficients p hp) ω) (h : intrinsicObstruction p hp ω = 0) :
    LieDeformation.secondResidual ω (intrinsicCorrection p hp ω) = 0 :=
  LieDeformation.ThirdReduction.correction_cancels (thirdReduction p hp) ω hω h

def intrinsicModel (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp)
    (hω : IsTwoCocycle (coefficients p hp) ω) (h : intrinsicObstruction p hp ω = 0) :
    LeanPhy.Mathematics.LieAlgebra K (Space K × Space K × Space K) :=
  LieDeformation.ThirdReduction.model (thirdReduction p hp) ω hω h

theorem intrinsicModel_bracket (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp)
    (hω : IsTwoCocycle (coefficients p hp) ω) (h : intrinsicObstruction p hp ω = 0) :
    (intrinsicModel p hp ω hω h).bracket =
      LieDeformation.secondBracket ω (intrinsicCorrection p hp ω) := rfl

/-- Class invariance is checked within the same declared parameter fiber. -/
theorem intrinsicObstruction_equivalence (p : Fin 1 → K) (hp : Conditions p) (ω η : C2 p hp)
    (E : LieDeformation.Equivalence ω η) :
    intrinsicObstruction p hp ω = intrinsicObstruction p hp η :=
  congrArg (h3Equiv p hp) (LieDeformation.obstructionClass_equivalence E)

/-- The source coordinates are the complete H² coordinates of this fiber. -/
def representativeObstruction (p : Fin 1 → K) (hp : Conditions p) (a : Fin (HeisenbergThirdParameterCE.dimension p) → K) :=
  intrinsicObstruction p hp ((reduction p hp).represent a)

theorem representative_extension_iff (p : Fin 1 → K) (hp : Conditions p) (a : Fin (HeisenbergThirdParameterCE.dimension p) → K) :
    LieDeformation.SecondExtendable ((reduction p hp).represent a) ↔
      representativeObstruction p hp a = 0 :=
  intrinsic_extension_iff p hp _ ((reduction p hp).represent_closed a)

theorem normalized_extension_iff (p : Fin 1 → K) (hp : Conditions p) (ω : C2 p hp)
    (hω : IsTwoCocycle (coefficients p hp) ω) :
    LieDeformation.SecondExtendable ω ↔
      representativeObstruction p hp ((reduction p hp).project ω) = 0 :=
  (LieDeformation.Reduction.normalize (reduction p hp) ω hω).secondExtendable_iff.trans
    (representative_extension_iff p hp _)

end
end LeanPhy.Generated.HeisenbergThirdParameter
