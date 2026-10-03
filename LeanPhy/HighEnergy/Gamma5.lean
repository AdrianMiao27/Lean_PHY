import LeanPhy.Quantum.Basic
import LeanPhy.HighEnergy.Gamma
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Gamma matrices, chirality, and the Clifford relation

This extends the explicit chiral-basis gamma matrices with the two objects that
high-energy algebra is written in terms of: the Clifford relation as a single
indexed statement, and the chirality matrix gamma^5 with its chiral projectors.
Everything is checked entrywise on the 4x4 complex representation.
-/

namespace LeanPhy.HighEnergy

open LeanPhy.Quantum

local notation "𝕚" => Complex.I
local notation "M4" => Matrix (Fin 4) (Fin 4) ℂ

/-- gamma^mu as a function of a single index. -/
def gammaFin (mu : Fin 4) : M4 := ![gamma0, gamma1, gamma2, gamma3] mu

/-- The Minkowski metric with signature (+---) as a complex coefficient. -/
def etaFin (mu nu : Fin 4) : ℂ := if mu = nu then (if mu = 0 then 1 else -1) else 0

/-- The Clifford relation {gamma^mu, gamma^nu} = 2 eta^{mu nu} as one statement. -/
theorem gammaFin_clifford (mu nu : Fin 4) :
    gammaFin mu * gammaFin nu + gammaFin nu * gammaFin mu
      = (2 * etaFin mu nu) • (1 : M4) := by
  fin_cases mu <;> fin_cases nu <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gammaFin, etaFin, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_four] <;>
    (try ring_nf) <;> (try (simp only [Complex.I_sq])) <;> (try ring)

/-- The chirality matrix gamma^5 = i gamma^0 gamma^1 gamma^2 gamma^3. -/
def gamma5 : M4 := 𝕚 • (gamma0 * gamma1 * gamma2 * gamma3)

/-- gamma^5 squares to the identity. -/
theorem gamma5_sq : gamma5 * gamma5 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma5, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_four]
  all_goals
    ring_nf
    simp only [Complex.I_sq]
    ring

/-- gamma^0 anticommutes with gamma^5. -/
theorem gamma0_anticommutes_gamma5 : gamma0 * gamma5 + gamma5 * gamma0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma5, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply, Matrix.add_apply,
      Matrix.zero_apply, Fin.sum_univ_four]
  all_goals
    ring_nf
    simp only [Complex.I_sq]
    ring

/-- gamma^1 anticommutes with gamma^5. -/
theorem gamma1_anticommutes_gamma5 : gamma1 * gamma5 + gamma5 * gamma1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma5, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply, Matrix.add_apply,
      Matrix.zero_apply, Fin.sum_univ_four]
  all_goals
    ring_nf
    simp only [Complex.I_sq]
    ring

/-- gamma^2 anticommutes with gamma^5. -/
theorem gamma2_anticommutes_gamma5 : gamma2 * gamma5 + gamma5 * gamma2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma5, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply, Matrix.add_apply,
      Matrix.zero_apply, Fin.sum_univ_four]
  all_goals
    ring_nf
    simp only [Complex.I_sq]
    ring

/-- gamma^3 anticommutes with gamma^5. -/
theorem gamma3_anticommutes_gamma5 : gamma3 * gamma5 + gamma5 * gamma3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma5, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply, Matrix.add_apply,
      Matrix.zero_apply, Fin.sum_univ_four]
  all_goals
    ring_nf
    simp only [Complex.I_sq]
    ring

/-- gamma^5 is Hermitian. -/
theorem gamma5_hermitian : Matrix.conjTranspose gamma5 = gamma5 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma5, gamma0, gamma1, gamma2, gamma3, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_four, Complex.I_sq, Complex.conj_ofReal, map_neg, map_one, map_zero] <;> ring

/-- Left-chirality projector P_+ = (1 + gamma^5)/2. -/
noncomputable def chiralPlus : M4 := ((2 : ℂ)⁻¹) • (1 + gamma5)

/-- Right-chirality projector P_- = (1 - gamma^5)/2. -/
noncomputable def chiralMinus : M4 := ((2 : ℂ)⁻¹) • (1 - gamma5)

/-- The projectors add to the identity. -/
theorem chiralPlus_add_chiralMinus : chiralPlus + chiralMinus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralPlus, chiralMinus, gamma5, gamma0, gamma1, gamma2, gamma3, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Complex.I_sq] <;> ring

/-- P_+ is idempotent. -/
theorem chiralPlus_idempotent : chiralPlus * chiralPlus = chiralPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralPlus, gamma5, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_four, Complex.I_sq] <;> ring

/-- The two projectors are orthogonal: P_+ P_- = 0. -/
theorem chiralPlus_mul_chiralMinus : chiralPlus * chiralMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralPlus, chiralMinus, gamma5, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply,
      Fin.sum_univ_four, Complex.I_sq] <;> ring

end LeanPhy.HighEnergy
