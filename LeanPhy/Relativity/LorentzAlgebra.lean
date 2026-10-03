import LeanPhy.Relativity.Minkowski
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# The Lorentz algebra so(3,1)

The one-axis boost matrix is built in `LeanPhy.Relativity.Boost`.  This module
records the full **Lie algebra** that a boost belongs to: the six generators of
the Lorentz group acting on `(t, x, y, z)`, three rotations `R_1, R_2, R_3` and
three boosts `B_1, B_2, B_3`, as explicit `4 x 4` complex matrices.

The kernel checks the commutation relations entrywise:

* the rotations close on themselves, `[R_i, R_j] = eps_{ijk} R_k`, so they span
an `so(3)` subalgebra;
* the rotations act on the boosts as vectors, `[R_i, B_j] = eps_{ijk} B_k`;
* two boosts close into a negative rotation, `[B_i, B_j] = - eps_{ijk} R_k`, the
famous statement that the commutator of two boosts is a rotation (Thomas-Wigner
precession).

It also checks that every generator is **metric-antisymmetric**,
`X^T eta + eta X = 0` with `eta = diag (1, -1, -1, -1)`, i.e.` eta X` is
antisymmetric, the defining property of `so(3,1)`.  So the six matrices are a
faithful representation of the Lorentz Lie algebra rather than an ansatz.

Everything is checked on the explicit matrices over `C`, so no analysis enters.
The exponentiation to finite Lorentz transformations, the spinor (double-valued)
representation and the Poincare group are out of scope.
-/

namespace LeanPhy.Relativity

open scoped BigOperators Matrix

/-- `4 x 4` complex matrices for Minkowski space. -/
abbrev M4L := Matrix (Fin 4) (Fin 4) ℂ

/-- The `(+---)` Minkowski metric as a complex matrix. -/
noncomputable def eta4 : M4L := !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

/-- The rotation generator in the `(x, y)` plane. -/
noncomputable def R1 : M4L := !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

/-- The rotation generator in the `(z, x)` plane. -/
noncomputable def R2 : M4L := !![0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, -1, 0, 0]

/-- The rotation generator in the `(y, z)` plane. -/
noncomputable def R3 : M4L := !![0, 0, 0, 0; 0, 0, -1, 0; 0, 1, 0, 0; 0, 0, 0, 0]

/-- The boost generator in the `t`-`x` plane. -/
noncomputable def B1 : M4L := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

/-- The boost generator in the `t`-`y` plane. -/
noncomputable def B2 : M4L := !![0, 0, 1, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0]

/-- The boost generator in the `t`-`z` plane. -/
noncomputable def B3 : M4L := !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0]

/-! ### Rotations close on so(3) -/

theorem R1_commutator_R2 : R1 * R2 - R2 * R1 = R3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [R1, R2, R3, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four] <;> ring)

theorem R2_commutator_R3 : R2 * R3 - R3 * R2 = R1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [R1, R2, R3, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four] <;> ring)

theorem R3_commutator_R1 : R3 * R1 - R1 * R3 = R2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [R1, R2, R3, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four] <;> ring)

/-! ### Rotations act on boosts as vectors -/

theorem R1_commutator_B2 : R1 * B2 - B2 * R1 = B3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [R1, B2, B3, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four] <;> ring)

theorem R2_commutator_B3 : R2 * B3 - B3 * R2 = B1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [R2, B1, B3, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four] <;> ring)

theorem R3_commutator_B1 : R3 * B1 - B1 * R3 = B2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [R3, B1, B2, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four] <;> ring)

/-! ### Two boosts close into a rotation (Thomas-Wigner) -/

theorem B1_commutator_B2 : B1 * B2 - B2 * B1 = - R3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [R3, B1, B2, Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring)

theorem B2_commutator_B3 : B2 * B3 - B3 * B2 = - R1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [R1, B2, B3, Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring)

theorem B3_commutator_B1 : B3 * B1 - B1 * B3 = - R2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [R2, B1, B3, Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring)

/-! ### Every generator is metric-antisymmetric -/

theorem metric_R1 : R1ᵀ * eta4 + eta4 * R1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [R1, eta4, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_four] <;> ring)

theorem metric_R2 : R2ᵀ * eta4 + eta4 * R2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [R2, eta4, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_four] <;> ring)

theorem metric_R3 : R3ᵀ * eta4 + eta4 * R3 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [R3, eta4, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_four] <;> ring)

theorem metric_B1 : B1ᵀ * eta4 + eta4 * B1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [B1, eta4, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_four] <;> ring)

theorem metric_B2 : B2ᵀ * eta4 + eta4 * B2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [B2, eta4, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_four] <;> ring)

theorem metric_B3 : B3ᵀ * eta4 + eta4 * B3 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [B3, eta4, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_four] <;> ring)

end LeanPhy.Relativity
