import LeanPhy.Quantum.Pauli
import LeanPhy.Quantum.Composite
import LeanPhy.QuantumInfo.Bell
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Prod

/-!
# The CHSH operator and the Bell state

This module turns the CHSH inequality into a matrix identity and evaluates it on
the (unnormalised) Bell state.  Two facts are proved:

* the CHSH operator satisfies the Tsirelson square identity
  S^2 = 4 I + 4 (sigma_y tensor sigma_y);

* the optimal tilted settings give S = sqrt 2 (ZZ + XX), whose Bell expectation
  is 4 sqrt 2, the Tsirelson bound 2 sqrt 2 after normalising.

The normalisation conventions are chosen so every entry is an exact algebraic
real number, the only irrational one being sqrt 2.
-/

namespace LeanPhy.QuantumInfo

open LeanPhy.Quantum
open scoped BigOperators

local notation "𝕚" => Complex.I

abbrev M4 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- Expectation of a two-qubit operator in the Bell state, unnormalised. -/
noncomputable def bellExpect (M : M4) : ℂ :=
  ∑ i, ∑ j, star (bell i) * M i j * bell j

/-- sqrt 2 as a complex number, the coupling of the tilted settings. -/
noncomputable def r2c : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

theorem r2c_mul_self : r2c * r2c = 2 := by
  unfold r2c
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem r2c_ne_zero : r2c ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [r2c] at this

theorem r2c_inv_mul_two : r2c⁻¹ * 2 = r2c := by
  rw [← r2c_mul_self, ← mul_assoc, inv_mul_cancel₀ r2c_ne_zero, one_mul]

/-- Expectation is complex-linear in the operator. -/
theorem bellExpect_smul (c : ℂ) (M : M4) :
    bellExpect (c • M) = c * bellExpect M := by
  simp only [bellExpect, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The four correlation terms of the standard CHSH experiment, written as
A_i tensor B_j with A_0 = Z, A_1 = X, B_0 = Z, B_1 = X. -/
noncomputable def chshOp : M4 :=
  tensorOp pauliZ identity * tensorOp identity pauliZ
    + tensorOp pauliZ identity * tensorOp identity pauliX
    + tensorOp pauliX identity * tensorOp identity pauliZ
    - tensorOp pauliX identity * tensorOp identity pauliX

/-- Tsirelson square identity at the operator level:
S^2 = 4 I + 4 (sigma_y tensor sigma_y). -/
theorem chshOp_sq : chshOp * chshOp
    = (4 : ℂ) • (1 : M4) + (4 : ℂ) • tensorOp pauliY pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chshOp, tensorOp, Matrix.kroneckerMap_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, pauliX, pauliY, pauliZ,
      identity, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Complex.I_mul_I] <;> ring

/-- The optimal Bob settings (Z ± X)/sqrt 2. -/
noncomputable def bobPlus : M4 := (r2c⁻¹) • tensorOp (1 : Operator 2) (pauliZ + pauliX)
noncomputable def bobMinus : M4 := (r2c⁻¹) • tensorOp (1 : Operator 2) (pauliZ - pauliX)

/-- The rotated CHSH operator built from the optimal settings. -/
noncomputable def chshOpt : M4 :=
  tensorOp pauliZ identity * bobPlus + tensorOp pauliZ identity * bobMinus
    + tensorOp pauliX identity * bobPlus - tensorOp pauliX identity * bobMinus

/-- With the optimal settings the CHSH operator collapses to sqrt 2 (ZZ + XX). -/
theorem chshOpt_eq : chshOpt
    = r2c • (tensorOp pauliZ pauliZ + tensorOp pauliX pauliX) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chshOpt, bobPlus, bobMinus, tensorOp, Matrix.kroneckerMap_apply,
      Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      pauliX, pauliZ, identity, Matrix.one_apply, Fintype.sum_prod_type]
  all_goals
    field_simp
    ring_nf
    rw [r2c_inv_mul_two]

/-- Bell-state expectation of ZZ + XX is 4. -/
theorem bellExpect_ZZ_add_XX :
    bellExpect (tensorOp pauliZ pauliZ + tensorOp pauliX pauliX) = 4 := by
  simp [bellExpect, bell, tensorOp, Matrix.kroneckerMap_apply, pauliX, pauliZ,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

/-- The CHSH value on the unnormalised Bell state is 4 sqrt 2, which is the Tsirelson bound 2 sqrt 2 after normalising. -/
theorem bellExpect_chshOpt : bellExpect chshOpt = 4 * r2c := by
  rw [chshOpt_eq, bellExpect_smul, bellExpect_ZZ_add_XX]
  ring

end LeanPhy.QuantumInfo
