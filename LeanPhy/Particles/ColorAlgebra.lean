import LeanPhy.Quantum.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# SU(3) colour algebra (Gell-Mann matrices)

Quantum chromodynamics is the strong-interaction gauge theory with colour group
SU(3), and almost every computation in it reduces to the algebra of the eight
Gell-Mann matrices `lam_1 ... lam_8`: the SU(3) generators in the fundamental
`3` of colour.  This module fixes an explicit normalisation (integer entries, with
`1/sqrt 3` in the diagonal `lam_8`) and checks the identities every QCD trace or
Fierz rearrangement uses:

- trace orthonormality `tr (lam_a lam_b) = 2 delta_ab`;
- the fundamental quadratic Casimir `sum_a lam_a lam_a = (16/3) 1`, whose
  normalisation fixes the quark colour factor `C_F = 4/3`;
- the Fierz completeness relation
  `sum_a (lam_a)_{ij} (lam_a)_{kl} = 2 delta_il delta_jk - (2/3) delta_ij delta_kl`,
  which turns a product of colour generators into colour-singlet plus colour-octet
  exchange with the standard weights `2` and `-2/3`.

Everything is checked entrywise on the explicit `3 x 3` complex matrices; the
`sqrt 3` is carried as an explicit algebraic symbol (`sqrt3 * sqrt3 = 3`), never
approximated.  The matrices are Hermitian and traceless, so they lie in the Lie
algebra `su(3)` rather than its complexification.
-/

namespace LeanPhy.Particles

open LeanPhy.Quantum
open scoped BigOperators Matrix

local notation "𝕜" => Complex.I

/-- The explicit algebraic square root of three appearing in `lam_8`. -/
noncomputable def sqrt3 : Complex := (Real.sqrt 3 : Complex)

theorem sqrt3_sq : sqrt3 * sqrt3 = 3 := by
  have h : ((Real.sqrt 3 : Real) * (Real.sqrt 3 : Real)) = (3 : Real) := by
    rw [←sq, Real.sq_sqrt (by norm_num)]
  simp only [sqrt3]
  exact_mod_cast h

theorem inv_sqrt3_sq : (sqrt3 ⁻¹) ^ 2 = (1 / 3 : Complex) := by
  rw [sq, ←mul_inv, sqrt3_sq, inv_eq_one_div]

/-- The Gell-Mann matrices, the eight generators of SU(3) in the colour triplet. -/
noncomputable def gm : Fin 8 → Matrix (Fin 3) (Fin 3) Complex :=
  ![!![0, 1, 0; 1, 0, 0; 0, 0, 0],
    !![0, -𝕜, 0; 𝕜, 0, 0; 0, 0, 0],
    !![1, 0, 0; 0, -1, 0; 0, 0, 0],
    !![0, 0, 1; 0, 0, 0; 1, 0, 0],
    !![0, 0, -𝕜; 0, 0, 0; 𝕜, 0, 0],
    !![0, 0, 0; 0, 0, 1; 0, 1, 0],
    !![0, 0, 0; 0, 0, -𝕜; 0, 𝕜, 0],
    !![sqrt3 ⁻¹, 0, 0; 0, sqrt3 ⁻¹, 0; 0, 0, -2 * sqrt3 ⁻¹]]

/-- The Kronecker delta on the eight colour-generator indices. -/
noncomputable def kdelta (a b : Fin 8) : Complex := if a = b then 1 else 0

/-- Every Gell-Mann matrix is traceless: the generators span SU(3), not U(3). -/
theorem gm_traceless (a : Fin 8) : (gm a).trace = 0 := by
  fin_cases a <;>
    simp [gm, Matrix.trace, Matrix.diag, Fin.sum_univ_three] <;> ring

/-- **Trace orthonormality** `tr (lam_a lam_b) = 2 delta_ab`. -/
theorem gm_trace_orthonormal (a b : Fin 8) :
    (gm a * gm b).trace = 2 * kdelta a b := by
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.sum_univ_eight, gm, kdelta, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Fin.sum_univ_three] <;>
    norm_num <;> ring_nf <;>
    (rw [inv_sqrt3_sq]; norm_num) <;>
    (rw [inv_sqrt3_sq]; norm_num) <;>
    (rw [inv_sqrt3_sq]; norm_num)

/-- **Fundamental quadratic Casimir** `sum_a lam_a lam_a = (16/3) 1`.  With the QCD
normalisation `T_a = lam_a / 2` this becomes `sum_a T_a T_a = (4/3) 1`, whose
coefficient is the quark colour factor `C_F = 4/3`. -/
theorem gm_casimir :
    (∑ a : Fin 8, gm a * gm a)
      = (16 / 3 : Complex) • (1 : Matrix (Fin 3) (Fin 3) Complex) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
    Fin.sum_univ_eight, gm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.of_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    norm_num <;> ring_nf <;>
    (rw [inv_sqrt3_sq]; norm_num) <;>
    (rw [inv_sqrt3_sq]; norm_num) <;>
    (rw [inv_sqrt3_sq]; norm_num) <;>
    (rw [inv_sqrt3_sq]; norm_num)

/-- **Fierz completeness** of the colour generators,
`sum_a (lam_a)_{ij} (lam_a)_{kl} = 2 delta_il delta_jk - (2/3) delta_ij delta_kl`.
This is the SU(3) analogue of the Pauli completeness relation and the identity
that rearranges any four-quark operator into colour-singlet and colour-octet parts. -/
theorem gm_fierz (i j k l : Fin 3) :
    (∑ a : Fin 8, gm a i j * gm a k l)
      = 2 * (if i = l then 1 else 0) * (if j = k then 1 else 0)
        - (2 / 3) * (if i = j then 1 else 0) * (if k = l then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [Fin.sum_univ_eight, gm, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Fin.sum_univ_three] <;>
    norm_num <;> ring_nf <;>
    (rw [inv_sqrt3_sq]; norm_num) <;>
    (rw [inv_sqrt3_sq]; norm_num) <;>
    (rw [inv_sqrt3_sq]; norm_num)

/-- The trace of the Casimir: `sum_a tr (lam_a lam_a) = 16`, the colour-singlet
coefficient of the one-loop gluon vacuum polarisation (with `T_a = lam_a/2` it is
`8 * C_F` through `C_F = 4/3`). -/
theorem gm_casimir_trace :
    (∑ a : Fin 8, (gm a * gm a).trace) = 16 := by
  rw [← Matrix.trace_sum]
  rw [gm_casimir]
  simp [Matrix.trace, Matrix.diag, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three]
  norm_num

end LeanPhy.Particles