import LeanPhy.Quantum.Spin
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# Angular momentum one: the spin-1 representation

The spin-`1/2` representation lives in `LeanPhy.Quantum.Spin` on `2 x 2`
matrices.  This module records the next representation, angular momentum one,
on the `3 x 3` matrices in the Cartesian basis, where the three generators are

    S_1 = [[0,0,0],[0,0,-i],[0,i,0]],
    S_2 = [[0,0,i],[0,0,0],[-i,0,0]],
    S_3 = [[0,-i,0],[i,0,0],[0,0,0]].

The kernel checks the `su(2)` commutation relations `[S_i, S_j] = i eps_{ijk} S_k`
entrywise, so the three matrices really generate a spin-one representation rather
than being an ansatz.  From them it reads off the defining data of the
representation:

* the **Casimir** `S . S = S_1^2 + S_2^2 + S_3^2 = 2 * 1 = l(l+1) 1` with `l = 1`,
the spin-one eigenvalue, exactly `2` and not `3/4`;
* the ladder operators `J_+ = S_1 + i S_2`, `J_- = S_1 - i S_2` raise and lower the
`S_3` eigenvalue, `[S_3, J_+] = J_+`, `[S_3, J_-] = -J_-`;
* the **cubic identities** `S_i^3 = S_i`, the characteristic identity of the
eigenvalues `{-1, 0, 1}`, the spin-one analogue of `S_i^2 = 1/4` for spin `1/2`;
* `J_+ J_- = S_1^2 + S_2^2 + S_3`, the standard `J_+ J_- = J^2 - J_3^2 + J_3` in
the dimensionless normalisation used here.

Everything is checked entrywise on the explicit matrices, so the representation
is exact.  The Clebsch-Gordan decomposition of a product of two spin-one
multiplets and the general spin-`l` representation are out of scope.
-/

namespace LeanPhy.Quantum

open scoped BigOperators Matrix

/-- `3 x 3` complex matrices. -/
abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ

/-- The first Cartesian generator `S_1`. -/
noncomputable def S1 : M3 := !![0, 0, 0; 0, 0, -Complex.I; 0, Complex.I, 0]

/-- The second Cartesian generator `S_2`. -/
noncomputable def S2 : M3 := !![0, 0, Complex.I; 0, 0, 0; -Complex.I, 0, 0]

/-- The third Cartesian generator `S_3`. -/
noncomputable def S3 : M3 := !![0, -Complex.I, 0; Complex.I, 0, 0; 0, 0, 0]

/-- The raising operator `J_+ = S_1 + i S_2`. -/
noncomputable def Jplus : M3 := S1 + Complex.I • S2

/-- The lowering operator `J_- = S_1 - i S_2`. -/
noncomputable def Jminus : M3 := S1 - Complex.I • S2

/-- **su(2) relation** `[S_1, S_2] = i S_3`. -/
theorem S1_commutator_S2 : S1 * S2 - S2 * S1 = Complex.I • S3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [S1, S2, S3, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Complex.I_mul_I] <;> ring)

/-- **su(2) relation** `[S_2, S_3] = i S_1`. -/
theorem S2_commutator_S3 : S2 * S3 - S3 * S2 = Complex.I • S1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [S1, S2, S3, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Complex.I_mul_I] <;> ring)

/-- **su(2) relation** `[S_3, S_1] = i S_2`. -/
theorem S3_commutator_S1 : S3 * S1 - S1 * S3 = Complex.I • S2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [S1, S2, S3, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Complex.I_mul_I] <;> ring)

/-- **The Casimir**: `S . S = 2 * 1 = l(l+1) 1` with `l = 1`. -/
theorem spinOne_casimir : S1 * S1 + S2 * S2 + S3 * S3 = 2 • (1 : M3) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [S1, S2, S3, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.mul_apply, Fin.sum_univ_three, Complex.I_mul_I] <;> ring)

/-- **Cubic identity** `S_1^3 = S_1`. -/
theorem S1_cubed : S1 * S1 * S1 = S1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [S1, Matrix.mul_apply, Fin.sum_univ_three, Complex.I_mul_I] <;> ring)

/-- **Cubic identity** `S_2^3 = S_2`. -/
theorem S2_cubed : S2 * S2 * S2 = S2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [S2, Matrix.mul_apply, Fin.sum_univ_three, Complex.I_mul_I] <;> ring)

/-- **Cubic identity** `S_3^3 = S_3`. -/
theorem S3_cubed : S3 * S3 * S3 = S3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [S3, Matrix.mul_apply, Fin.sum_univ_three, Complex.I_mul_I] <;> ring)

/-- The raising operator raises the `S_3` eigenvalue: `[S_3, J_+] = J_+`. -/
theorem S3_commutator_Jplus : S3 * Jplus - Jplus * S3 = Jplus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [S1, S2, S3, Jplus, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.mul_apply, Fin.sum_univ_three, Complex.I_mul_I] <;> ring)

/-- The lowering operator lowers the `S_3` eigenvalue: `[S_3, J_-] = -J_-`. -/
theorem S3_commutator_Jminus : S3 * Jminus - Jminus * S3 = - Jminus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [S1, S2, S3, Jminus, Matrix.sub_apply, Matrix.neg_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_three, Complex.I_mul_I] <;> ring)

/-- `J_+ J_- = S_1^2 + S_2^2 + S_3`, i.e. `J^2 - S_3^2 + S_3` in this
normalisation. -/
theorem Jplus_mul_Jminus : Jplus * Jminus = S1 * S1 + S2 * S2 + S3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [S1, S2, S3, Jplus, Jminus, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_three, Complex.I_mul_I] <;> ring)

end LeanPhy.Quantum
