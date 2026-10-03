import LeanPhy.Quantum.Pauli
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# The Ising transfer matrix

A classical one-dimensional Ising chain is diagonalised by a `2 x 2` transfer
matrix.  In the symmetric sector the Boltzmann weight is

    T = [[c, s], [s, c]] = c I + s sigma_x,

with `c` the weight for equal spins and `s` for opposite spins.  This module
records the transfer-matrix algebra a statistical-mechanics derivation uses:
the Pauli form, the composition law (two transfer matrices multiply to one whose
parameters add like rapidities), the fact that all such matrices commute, the
characteristic polynomial `T^2 - 2 c T + (c^2 - s^2) I = 0`, and the trace
identities `tr T = 2c` and `tr (T^2) = 2 (c^2 + s^2)`, i.e. the partition
function is the sum of the two eigenvalues `c ± s`.

Everything is exact linear algebra over `C`.  What is not attempted is the
thermodynamic limit: the free energy per site, the `N -> infinity` limit and
the phase-transition analysis belong to the analytic layer and are out of scope,
consistent with the conditional semantics of the library.
-/

namespace LeanPhy.StatMech

open LeanPhy.Quantum
open scoped BigOperators Matrix

/-- The symmetric Ising transfer matrix `T = c I + s sigma_x`, with `c` the
equal-spin Boltzmann weight and `s` the opposite-spin weight. -/
noncomputable def isingTransferMatrix (c s : ℂ) : Operator 2 := !![c, s; s, c]

/-- The transfer matrix is `c I + s sigma_x` in the Pauli basis. -/
theorem isingTransferMatrix_eq_pauli (c s : ℂ) :
    isingTransferMatrix c s = c • (1 : Operator 2) + s • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [isingTransferMatrix, pauliX, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, Matrix.of_apply] <;> norm_num

/-- **Composition law.**  Two transfer matrices multiply to a transfer matrix
whose parameters combine by the addition formulas: the rapidities add. -/
theorem isingTransferMatrix_mul (c s c' s' : ℂ) :
    isingTransferMatrix c s * isingTransferMatrix c' s'
      = isingTransferMatrix (c * c' + s * s') (c * s' + s * c') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [isingTransferMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- All symmetric transfer matrices commute, so the chain can be diagonalised
in one fixed basis regardless of the coupling. -/
theorem isingTransferMatrix_comm (c s c' s' : ℂ) :
    isingTransferMatrix c s * isingTransferMatrix c' s'
      = isingTransferMatrix c' s' * isingTransferMatrix c s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [isingTransferMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Characteristic polynomial.**  The transfer matrix satisfies
`T^2 - 2 c T + (c^2 - s^2) I = 0`, so its spectrum is the pair `c ± s`. -/
theorem isingTransferMatrix_charpoly (c s : ℂ) :
    isingTransferMatrix c s * isingTransferMatrix c s
        - (2 * c) • isingTransferMatrix c s
        + (c * c - s * s) • (1 : Operator 2) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [isingTransferMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Fin.sum_univ_two, Matrix.of_apply] <;>
    ring

/-- The partition function is the trace, `tr T = 2 c`: the sum of eigenvalues. -/
theorem isingTransferMatrix_trace (c s : ℂ) :
    Matrix.trace (isingTransferMatrix c s) = 2 * c := by
  simp [isingTransferMatrix, Matrix.trace, Matrix.diag_apply]
  ring

/-- **Two-site partition function.**  `tr (T^2) = 2 (c^2 + s^2) = (c+s)^2 + (c-s)^2`,
the sum of the squared eigenvalues. -/
theorem isingTransferMatrix_trace_sq (c s : ℂ) :
    Matrix.trace (isingTransferMatrix c s * isingTransferMatrix c s)
      = 2 * (c * c + s * s) := by
  simp [isingTransferMatrix, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.of_apply]
  ring

/-- The determinant is the product of the eigenvalues,
`det T = c^2 - s^2 = (c+s)(c-s)`. -/
theorem isingTransferMatrix_det (c s : ℂ) :
    Matrix.det (isingTransferMatrix c s) = c * c - s * s := by
  simp [isingTransferMatrix, Matrix.det_fin_two, Matrix.of_apply]

/-- A concrete diagonal witness: with `s = 0` the transfer matrix is `c I`,
so the two-site partition function is `2 c^2`.  Evaluated by the kernel. -/
theorem isingTransferMatrix_diagonal_witness :
    Matrix.trace (isingTransferMatrix 3 0 * isingTransferMatrix 3 0) = 18 := by
  rw [isingTransferMatrix_trace_sq]
  norm_num

end LeanPhy.StatMech

