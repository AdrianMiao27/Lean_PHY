import LeanPhy.QuantumInfo.GHZ
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# Three-qubit bit-flip code

The repetition code encodes one logical qubit as

    |0_L> = |000>,       |1_L> = |111>.

The two stabilizers are `Z Z I` and `I Z Z`.  A logical code state is therefore
an eigenvector of both with eigenvalue `+1`.  A bit flip on one physical qubit
changes the two stabilizer eigenvalues to a unique **syndrome**:

    X_1 : (-1, +1),   X_2 : (-1, -1),   X_3 : (+1, -1).

This module checks that statement as an exact matrix identity for arbitrary
complex amplitudes `a`, `b` in `a |000> + b |111>`.  It does not claim that a
real device implements the code or that a noise channel is restricted to bit
flips; those are physical assumptions.  The proved content is the algebraic
stabilizer calculation that makes the error-correction table possible.

The code is deliberately paired with `LeanPhy.QuantumInfo.NoCloning`: the
no-cloning theorem rules out copying an arbitrary unknown state, while the
bit-flip code protects an encoded state by adding a structured redundant
subspace and measuring its syndrome.
-/

namespace LeanPhy.QuantumInfo

open LeanPhy.Quantum
open scoped BigOperators Matrix

/-- The two stabilizers `Z Z I` and `I Z Z`. -/
noncomputable def zz1q : Matrix Idx3 Idx3 Complex := kron3 pauliZ pauliZ (1 : Operator 2)
noncomputable def zz2q : Matrix Idx3 Idx3 Complex := kron3 (1 : Operator 2) pauliZ pauliZ

/-- Bit flips on the first, second and third physical qubits. -/
noncomputable def xx1q : Matrix Idx3 Idx3 Complex := kron3 pauliX (1 : Operator 2) (1 : Operator 2)
noncomputable def xx2q : Matrix Idx3 Idx3 Complex := kron3 (1 : Operator 2) pauliX (1 : Operator 2)
noncomputable def xx3q : Matrix Idx3 Idx3 Complex := kron3 (1 : Operator 2) (1 : Operator 2) pauliX

/-- An arbitrary encoded state `a |000> + b |111>`. -/
noncomputable def codeVec (a b : Complex) : Idx3 → Complex := fun i =>
  if i = ((0, 0), 0) then a else if i = ((1, 1), 1) then b else 0

/-! ### The code subspace is the +1 stabilizer eigenspace -/

/-- `Z Z I` fixes every encoded state. -/
theorem stab1_code (a b : Complex) (j : Idx3) :
    (zz1q *ᵥ codeVec a b) j = codeVec a b j := by
  rw [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  fin_cases j <;>
    simp [zz1q, codeVec, kron3_apply, pauliZ, Matrix.one_apply] <;> ring

/-- `I Z Z` fixes every encoded state. -/
theorem stab2_code (a b : Complex) (j : Idx3) :
    (zz2q *ᵥ codeVec a b) j = codeVec a b j := by
  rw [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  fin_cases j <;>
    simp [zz2q, codeVec, kron3_apply, pauliZ, Matrix.one_apply] <;> ring

/-! ### Stabilizer syndromes -/

/-- `Z Z I` anticommutes with the first bit flip. -/
theorem zz1_xx1_anticomm : zz1q * xx1q = - (xx1q * zz1q) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [zz1q, xx1q, kron3_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      pauliZ, pauliX, Matrix.one_apply] <;> norm_num)

/-- `I Z Z` commutes with the first bit flip. -/
theorem zz2_xx1_comm : zz2q * xx1q = xx1q * zz2q := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [zz2q, xx1q, kron3_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      pauliZ, pauliX, Matrix.one_apply] <;> norm_num)

/-- The first bit flip has syndrome `(-1, +1)`. -/
theorem xx1_syndrome (a b : Complex) :
    zz1q *ᵥ (xx1q *ᵥ codeVec a b) = - (xx1q *ᵥ codeVec a b) := by
  funext j
  rw [Matrix.mulVec_mulVec, zz1_xx1_anticomm, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
  rw [show (zz1q *ᵥ codeVec a b) = codeVec a b by
    funext k; exact stab1_code a b k]

/-- The first bit flip leaves the second stabilizer at `+1`. -/
theorem xx1_syndrome2 (a b : Complex) :
    zz2q *ᵥ (xx1q *ᵥ codeVec a b) = xx1q *ᵥ codeVec a b := by
  funext j
  rw [Matrix.mulVec_mulVec, zz2_xx1_comm, ← Matrix.mulVec_mulVec]
  rw [show (zz2q *ᵥ codeVec a b) = codeVec a b by
    funext k; exact stab2_code a b k]

/-- `Z Z I` anticommutes with the second bit flip. -/
theorem zz1_xx2_anticomm : zz1q * xx2q = - (xx2q * zz1q) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [zz1q, xx2q, kron3_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      pauliZ, pauliX, Matrix.one_apply] <;> norm_num)

/-- `I Z Z` anticommutes with the second bit flip. -/
theorem zz2_xx2_anticomm : zz2q * xx2q = - (xx2q * zz2q) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [zz2q, xx2q, kron3_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      pauliZ, pauliX, Matrix.one_apply] <;> norm_num)

/-- The second bit flip has syndrome `(-1, -1)`. -/
theorem xx2_syndrome1 (a b : Complex) :
    zz1q *ᵥ (xx2q *ᵥ codeVec a b) = - (xx2q *ᵥ codeVec a b) := by
  funext j
  rw [Matrix.mulVec_mulVec, zz1_xx2_anticomm, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
  rw [show (zz1q *ᵥ codeVec a b) = codeVec a b by
    funext k; exact stab1_code a b k]

/-- The second bit flip has syndrome `-1` for the second stabilizer. -/
theorem xx2_syndrome2 (a b : Complex) :
    zz2q *ᵥ (xx2q *ᵥ codeVec a b) = - (xx2q *ᵥ codeVec a b) := by
  funext j
  rw [Matrix.mulVec_mulVec, zz2_xx2_anticomm, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
  rw [show (zz2q *ᵥ codeVec a b) = codeVec a b by
    funext k; exact stab2_code a b k]

/-- `Z Z I` commutes with the third bit flip. -/
theorem zz1_xx3_comm : zz1q * xx3q = xx3q * zz1q := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [zz1q, xx3q, kron3_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      pauliZ, pauliX, Matrix.one_apply] <;> norm_num)

/-- `I Z Z` anticommutes with the third bit flip. -/
theorem zz2_xx3_anticomm : zz2q * xx3q = - (xx3q * zz2q) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [zz2q, xx3q, kron3_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      pauliZ, pauliX, Matrix.one_apply] <;> norm_num)

/-- The third bit flip has syndrome `(+1, -1)`. -/
theorem xx3_syndrome1 (a b : Complex) :
    zz1q *ᵥ (xx3q *ᵥ codeVec a b) = xx3q *ᵥ codeVec a b := by
  funext j
  rw [Matrix.mulVec_mulVec, zz1_xx3_comm, ← Matrix.mulVec_mulVec]
  rw [show (zz1q *ᵥ codeVec a b) = codeVec a b by
    funext k; exact stab1_code a b k]

/-- The third bit flip has syndrome `-1` for the second stabilizer. -/
theorem xx3_syndrome2 (a b : Complex) :
    zz2q *ᵥ (xx3q *ᵥ codeVec a b) = - (xx3q *ᵥ codeVec a b) := by
  funext j
  rw [Matrix.mulVec_mulVec, zz2_xx3_anticomm, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
  rw [show (zz2q *ᵥ codeVec a b) = codeVec a b by
    funext k; exact stab2_code a b k]

end LeanPhy.QuantumInfo
