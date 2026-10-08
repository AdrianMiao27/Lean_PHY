import LeanPhy.Mathematics.CohomologyReduction
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/- Generated candidate: compile with Lean before using any conclusion.
Input SHA-256: 07242f4ba1430844dce054f391195fc50421f1741ae22c63b5e35ecfb052f802
Parameter order: a, b, t.
The decision tree includes all zero and nonzero branches under the declared
input conditions. No numerical sampling or physical interpretation is assumed. -/
namespace LeanPhy.Generated.SolvableStrata

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
  !![((x 2) + (-1 * (x 0))), 0, 0;
    0, ((x 2) + (-1 * (x 1))), 0;
    0, 0, 0]

def d2 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0;
    0, 0, 0;
    0, 0, ((x 2) + (-1 * (x 0)) + (-1 * (x 1)))]

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

def correction_0 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  0

def branch_0 (x : Fin 3 → K) (h0 : ((x 0) + (-1 * (x 2))) = 0) (h1 : ((x 1) + (-1 * (x 2))) = 0) (h2 : (x 2) = 0) :
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

def project_1 (x : Fin 3 → K) : Matrix (Fin 2) (Fin 3) K :=
  !![1, 0, 0;
    0, 1, 0]

def represent_1 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 2) K :=
  !![1, 0;
    0, 1;
    0, 0]

def primitive_1 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  0

def correction_1 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0;
    0, 0, 0;
    0, 0, (-1 * ((x 2))⁻¹)]

def branch_1 (x : Fin 3 → K) (h0 : ((x 0) + (-1 * (x 2))) = 0) (h1 : ((x 1) + (-1 * (x 2))) = 0) (h2 : (x 2) ≠ 0) :
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

def project_2 (x : Fin 3 → K) : Matrix (Fin 2) (Fin 3) K :=
  !![1, 0, 0;
    0, 0, 1]

def represent_2 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 2) K :=
  !![1, 0;
    0, 0;
    0, 1]

def primitive_2 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0;
    0, ((x 2))⁻¹, 0;
    0, 0, 0]

def correction_2 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  0

def branch_2 (x : Fin 3 → K) (h0 : ((x 0) + (-1 * (x 2))) = 0) (h1 : ((x 1) + (-1 * (x 2))) ≠ 0) (h2 : (x 1) = 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 2 where
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

def project_3 (x : Fin 3 → K) : Matrix (Fin 1) (Fin 3) K :=
  !![1, 0, 0]

def represent_3 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 1) K :=
  !![1;
    0;
    0]

def primitive_3 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0;
    0, (((x 2) + (-1 * (x 1))))⁻¹, 0;
    0, 0, 0]

def correction_3 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0;
    0, 0, 0;
    0, 0, (-1 * ((x 1))⁻¹)]

def branch_3 (x : Fin 3 → K) (h0 : ((x 0) + (-1 * (x 2))) = 0) (h1 : ((x 1) + (-1 * (x 2))) ≠ 0) (h2 : (x 1) ≠ 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 1 where
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

def project_4 (x : Fin 3 → K) : Matrix (Fin 2) (Fin 3) K :=
  !![0, 1, 0;
    0, 0, 1]

def represent_4 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 2) K :=
  !![0, 0;
    1, 0;
    0, 1]

def primitive_4 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![((x 2))⁻¹, 0, 0;
    0, 0, 0;
    0, 0, 0]

def correction_4 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  0

def branch_4 (x : Fin 3 → K) (h0 : ((x 0) + (-1 * (x 2))) ≠ 0) (h1 : ((x 1) + (-1 * (x 2))) = 0) (h2 : (x 0) = 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 2 where
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
  !![0, 1, 0]

def represent_5 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 1) K :=
  !![0;
    1;
    0]

def primitive_5 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![(((x 2) + (-1 * (x 0))))⁻¹, 0, 0;
    0, 0, 0;
    0, 0, 0]

def correction_5 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0;
    0, 0, 0;
    0, 0, (-1 * ((x 0))⁻¹)]

def branch_5 (x : Fin 3 → K) (h0 : ((x 0) + (-1 * (x 2))) ≠ 0) (h1 : ((x 1) + (-1 * (x 2))) = 0) (h2 : (x 0) ≠ 0) :
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
  !![0, 0, 1]

def represent_6 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 1) K :=
  !![0;
    0;
    1]

def primitive_6 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![((x 1))⁻¹, 0, 0;
    0, (((x 2) + (-1 * (x 1))))⁻¹, 0;
    0, 0, 0]

def correction_6 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  0

def branch_6 (x : Fin 3 → K) (h0 : ((x 0) + (-1 * (x 2))) ≠ 0) (h1 : ((x 1) + (-1 * (x 2))) ≠ 0) (h2 : ((x 0) + (x 1) + (-1 * (x 2))) = 0) :
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

def project_7 (x : Fin 3 → K) : Matrix (Fin 0) (Fin 3) K :=
  0

def represent_7 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 0) K :=
  0

def primitive_7 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![(((x 2) + (-1 * (x 0))))⁻¹, 0, 0;
    0, (((x 2) + (-1 * (x 1))))⁻¹, 0;
    0, 0, 0]

def correction_7 (x : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0;
    0, 0, 0;
    0, 0, (((x 2) + (-1 * (x 0)) + (-1 * (x 1))))⁻¹]

def branch_7 (x : Fin 3 → K) (h0 : ((x 0) + (-1 * (x 2))) ≠ 0) (h1 : ((x 1) + (-1 * (x 2))) ≠ 0) (h2 : ((x 0) + (x 1) + (-1 * (x 2))) ≠ 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 0 where
  project := project_7 x
  represent := represent_7 x
  primitive := primitive_7 x
  correction := correction_7 x
  chain := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_7, represent_7, primitive_7, correction_7, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  closed := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_7, represent_7, primitive_7, correction_7, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  boundary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_7, represent_7, primitive_7, correction_7, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  retract := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_7, represent_7, primitive_7, correction_7, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind
  decompose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project_7, represent_7, primitive_7, correction_7, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    <;> (try field_simp)
    <;> grind

def dimension (x : Fin 3 → K) : Nat :=
  (if ((x 0) + (-1 * (x 2))) = 0 then (if ((x 1) + (-1 * (x 2))) = 0 then (if (x 2) = 0 then 3 else 2) else (if (x 1) = 0 then 2 else 1)) else (if ((x 1) + (-1 * (x 2))) = 0 then (if (x 0) = 0 then 2 else 1) else (if ((x 0) + (x 1) + (-1 * (x 2))) = 0 then 1 else 0)))

def certificate (x : Fin 3 → K) :
    MatrixCohomologyReduction (d1 x) (d2 x) (dimension x) := by
  by_cases h0 : ((x 0) + (-1 * (x 2))) = 0
  · by_cases h1 : ((x 1) + (-1 * (x 2))) = 0
    · by_cases h2 : (x 2) = 0
      · unfold dimension
        rw [ite_eq_left h0, ite_eq_left h1, ite_eq_left h2]
        exact branch_0 x h0 h1 h2
      · unfold dimension
        rw [ite_eq_left h0, ite_eq_left h1, ite_eq_right h2]
        exact branch_1 x h0 h1 h2
    · by_cases h2 : (x 1) = 0
      · unfold dimension
        rw [ite_eq_left h0, ite_eq_right h1, ite_eq_left h2]
        exact branch_2 x h0 h1 h2
      · unfold dimension
        rw [ite_eq_left h0, ite_eq_right h1, ite_eq_right h2]
        exact branch_3 x h0 h1 h2
  · by_cases h1 : ((x 1) + (-1 * (x 2))) = 0
    · by_cases h2 : (x 0) = 0
      · unfold dimension
        rw [ite_eq_right h0, ite_eq_left h1, ite_eq_left h2]
        exact branch_4 x h0 h1 h2
      · unfold dimension
        rw [ite_eq_right h0, ite_eq_left h1, ite_eq_right h2]
        exact branch_5 x h0 h1 h2
    · by_cases h2 : ((x 0) + (x 1) + (-1 * (x 2))) = 0
      · unfold dimension
        rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2]
        exact branch_6 x h0 h1 h2
      · unfold dimension
        rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2]
        exact branch_7 x h0 h1 h2

def cohomologyEquiv (x : Fin 3 → K) :
    CohomologyReduction.Cohomology (d1 x).toLin' (d2 x).toLin' ≃ₗ[K] (Fin (dimension x) → K) :=
  (certificate x).toReduction.quotientEquiv

theorem finrank_eq (x : Fin 3 → K) :
    Module.finrank K (CohomologyReduction.Cohomology (d1 x).toLin' (d2 x).toLin') = dimension x := by
  rw [(cohomologyEquiv x).finrank_eq]
  simp

theorem exact_iff (x : Fin 3 → K)
    (ω : Fin 3 → K) (hω : (d2 x).toLin' ω = 0) :
    (∃ φ, (d1 x).toLin' φ = ω) ↔ (certificate x).project.toLin' ω = 0 :=
  (certificate x).toReduction.exact_iff ω hω

theorem normal_form (x : Fin 3 → K)
    (ω : Fin 3 → K) (hω : (d2 x).toLin' ω = 0) :
    (d1 x).toLin' ((certificate x).primitive.toLin' ω) +
      (certificate x).represent.toLin' ((certificate x).project.toLin' ω) = ω :=
  (certificate x).toReduction.normal_form ω hω

end
end LeanPhy.Generated.SolvableStrata
