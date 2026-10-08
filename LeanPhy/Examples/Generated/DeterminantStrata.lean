import LeanPhy.Mathematics.CohomologyReduction
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/- Generated candidate: compile with Lean before using any conclusion.
Input SHA-256: f9c9d5c5b4fb441fc7d401a4cd4e2166b5c7aa8a76748e26a507b63e50b8c77c
Parameter order: s, t.
The decision tree includes all zero and nonzero branches under the declared
input conditions. No numerical sampling or physical interpretation is assumed. -/
namespace LeanPhy.Generated.DeterminantStrata

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

def d1 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  !![(x 0), (x 1);
    (x 1), (x 0)]

def d2 (x : Fin 2 → K) : Matrix (Fin 0) (Fin 2) K :=
  0

def project_0 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  !![1, 0;
    0, 1]

def represent_0 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  !![1, 0;
    0, 1]

def primitive_0 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  0

def correction_0 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 0) K :=
  0

def branch_0 (x : Fin 2 → K) (h0 : (x 0) = 0) (h1 : (x 1) = 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 2 where
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

def project_1 (x : Fin 2 → K) : Matrix (Fin 0) (Fin 2) K :=
  0

def represent_1 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 0) K :=
  0

def primitive_1 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  !![0, ((x 1))⁻¹;
    ((x 1))⁻¹, 0]

def correction_1 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 0) K :=
  0

def branch_1 (x : Fin 2 → K) (h0 : (x 0) = 0) (h1 : (x 1) ≠ 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 0 where
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

def project_2 (x : Fin 2 → K) : Matrix (Fin 1) (Fin 2) K :=
  !![1, -1]

def represent_2 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 1) K :=
  !![1;
    0]

def primitive_2 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  !![0, ((x 1))⁻¹;
    0, 0]

def correction_2 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 0) K :=
  0

def branch_2 (x : Fin 2 → K) (h0 : (x 0) ≠ 0) (h1 : ((x 0) + (-1 * (x 1))) = 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 1 where
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

def project_3 (x : Fin 2 → K) : Matrix (Fin 1) (Fin 2) K :=
  !![1, 1]

def represent_3 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 1) K :=
  !![1;
    0]

def primitive_3 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  !![0, ((x 1))⁻¹;
    0, 0]

def correction_3 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 0) K :=
  0

def branch_3 (x : Fin 2 → K) (h0 : (x 0) ≠ 0) (h1 : ((x 0) + (-1 * (x 1))) ≠ 0) (h2 : ((x 0) + (x 1)) = 0) :
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

def project_4 (x : Fin 2 → K) : Matrix (Fin 0) (Fin 2) K :=
  0

def represent_4 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 0) K :=
  0

def primitive_4 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  !![((x 0) * ((((x 0) ^ 2) + (-1 * ((x 1) ^ 2))))⁻¹), (-1 * (x 1) * ((((x 0) ^ 2) + (-1 * ((x 1) ^ 2))))⁻¹);
    (-1 * (x 1) * ((((x 0) ^ 2) + (-1 * ((x 1) ^ 2))))⁻¹), ((x 0) * ((((x 0) ^ 2) + (-1 * ((x 1) ^ 2))))⁻¹)]

def correction_4 (x : Fin 2 → K) : Matrix (Fin 2) (Fin 0) K :=
  0

def branch_4 (x : Fin 2 → K) (h0 : (x 0) ≠ 0) (h1 : ((x 0) + (-1 * (x 1))) ≠ 0) (h2 : ((x 0) + (x 1)) ≠ 0) :
    MatrixCohomologyReduction (d1 x) (d2 x) 0 where
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

def dimension (x : Fin 2 → K) : Nat :=
  (if (x 0) = 0 then (if (x 1) = 0 then 2 else 0) else (if ((x 0) + (-1 * (x 1))) = 0 then 1 else (if ((x 0) + (x 1)) = 0 then 1 else 0)))

def certificate (x : Fin 2 → K) :
    MatrixCohomologyReduction (d1 x) (d2 x) (dimension x) := by
  by_cases h0 : (x 0) = 0
  · by_cases h1 : (x 1) = 0
    · unfold dimension
      rw [ite_eq_left h0, ite_eq_left h1]
      exact branch_0 x h0 h1
    · unfold dimension
      rw [ite_eq_left h0, ite_eq_right h1]
      exact branch_1 x h0 h1
  · by_cases h1 : ((x 0) + (-1 * (x 1))) = 0
    · unfold dimension
      rw [ite_eq_right h0, ite_eq_left h1]
      exact branch_2 x h0 h1
    · by_cases h2 : ((x 0) + (x 1)) = 0
      · unfold dimension
        rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2]
        exact branch_3 x h0 h1 h2
      · unfold dimension
        rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2]
        exact branch_4 x h0 h1 h2

def cohomologyEquiv (x : Fin 2 → K) :
    CohomologyReduction.Cohomology (d1 x).toLin' (d2 x).toLin' ≃ₗ[K] (Fin (dimension x) → K) :=
  (certificate x).toReduction.quotientEquiv

theorem finrank_eq (x : Fin 2 → K) :
    Module.finrank K (CohomologyReduction.Cohomology (d1 x).toLin' (d2 x).toLin') = dimension x := by
  rw [(cohomologyEquiv x).finrank_eq]
  simp

theorem exact_iff (x : Fin 2 → K)
    (ω : Fin 2 → K) (hω : (d2 x).toLin' ω = 0) :
    (∃ φ, (d1 x).toLin' φ = ω) ↔ (certificate x).project.toLin' ω = 0 :=
  (certificate x).toReduction.exact_iff ω hω

theorem normal_form (x : Fin 2 → K)
    (ω : Fin 2 → K) (hω : (d2 x).toLin' ω = 0) :
    (d1 x).toLin' ((certificate x).primitive.toLin' ω) +
      (certificate x).represent.toLin' ((certificate x).project.toLin' ω) = ω :=
  (certificate x).toReduction.normal_form ω hω

end
end LeanPhy.Generated.DeterminantStrata
