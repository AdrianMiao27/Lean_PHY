import LeanPhy.Mathematics.CohomologyReduction

/- Generated candidate: compile with `lake env lean` before treating it as checked.
Input SHA-256: b8431f67bfb6b5b4d99023cdbe836be9e2d8a0d8c714997f6e73ea9d1c1081fb
The matrices below are the mathematical input; no physical interpretation is inferred. -/
namespace LeanPhy.Generated.Heisenberg

open LeanPhy.Mathematics

def d1 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 0, -1;
    0, 0, 0;
    0, 0, 0]

def d2 : Matrix (Fin 1) (Fin 3) ℚ :=
  0

def project : Matrix (Fin 2) (Fin 3) ℚ :=
  !![0, 1, 0;
    0, 0, 1]

def represent : Matrix (Fin 3) (Fin 2) ℚ :=
  !![0, 0;
    1, 0;
    0, 1]

def primitive : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 0, 0;
    0, 0, 0;
    -1, 0, 0]

def correction : Matrix (Fin 3) (Fin 1) ℚ :=
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

end LeanPhy.Generated.Heisenberg
