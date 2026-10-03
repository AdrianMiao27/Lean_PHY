import LeanPhy.Quantum.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# Dirac gamma matrices

An explicit four-dimensional Clifford representation, in the chiral basis, so
that the Dirac bilinear identities used in high-energy algebra can be checked
exactly rather than assumed.
-/

namespace LeanPhy.HighEnergy

local notation "𝕚" => Complex.I

/-- The Dirac gamma matrices in the chiral (Weyl) representation. -/
def gamma0 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
def gamma1 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
def gamma2 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, -𝕚; 0, 0, 𝕚, 0; 0, 𝕚, 0, 0; -𝕚, 0, 0, 0]
def gamma3 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]

@[simp] theorem gamma0_sq : gamma0 * gamma0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma0, Matrix.mul_apply, Fin.sum_univ_four]

@[simp] theorem gamma1_sq : gamma1 * gamma1 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma1, Matrix.mul_apply, Fin.sum_univ_four]

@[simp] theorem gamma2_sq : gamma2 * gamma2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma2, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

@[simp] theorem gamma3_sq : gamma3 * gamma3 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma3, Matrix.mul_apply, Fin.sum_univ_four]

/-- `γ⁰` anticommutes with the spatial gamma matrices. -/
theorem gamma0_anticommutes_gamma1 : gamma0 * gamma1 + gamma1 * gamma0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma0, gamma1]

/-- The Clifford relation in the form used for `μ = ν = 1`. -/
theorem clifford_gamma1 : (gamma1 * gamma1 : Matrix (Fin 4) (Fin 4) ℂ) = -1 := gamma1_sq

end LeanPhy.HighEnergy
