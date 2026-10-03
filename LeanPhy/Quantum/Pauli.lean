import LeanPhy.Quantum.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-! Pauli matrices and their first verified identities. -/

namespace LeanPhy.Quantum

local notation "𝕚" => Complex.I

def pauliX : Operator 2 := !![0, 1; 1, 0]
def pauliY : Operator 2 := !![0, -𝕚; 𝕚, 0]
def pauliZ : Operator 2 := !![1, 0; 0, -1]

@[simp] theorem pauliX_sq : pauliX * pauliX = identity := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, identity, Matrix.mul_apply]

@[simp] theorem pauliY_sq : pauliY * pauliY = identity := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, identity, Matrix.mul_apply, Complex.I_mul_I]

@[simp] theorem pauliZ_sq : pauliZ * pauliZ = identity := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, identity, Matrix.mul_apply]

theorem pauliX_pauliY : pauliX * pauliY = 𝕚 • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]

theorem pauliY_pauliX : pauliY * pauliX = -𝕚 • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]

theorem pauliXY_commutator : commutator pauliX pauliY = (2 * 𝕚) • pauliZ := by
  rw [commutator, pauliX_pauliY, pauliY_pauliX]
  rw [show (2 : ℂ) * 𝕚 = 𝕚 + 𝕚 by ring, add_smul, neg_smul, sub_neg_eq_add]

/-! ### Cyclic products and commutators

Together these give the standard relations and the angular-momentum commutator. -/

theorem pauliY_pauliZ : pauliY * pauliZ = 𝕚 • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, pauliZ, pauliX, Matrix.mul_apply]

theorem pauliZ_pauliY : pauliZ * pauliY = -𝕚 • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, pauliZ, pauliX, Matrix.mul_apply]

theorem pauliZ_pauliX : pauliZ * pauliX = 𝕚 • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, pauliX, pauliY, Matrix.mul_apply, Complex.I_mul_I]

theorem pauliX_pauliZ : pauliX * pauliZ = -𝕚 • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, pauliX, pauliY, Matrix.mul_apply, Complex.I_mul_I]

theorem pauliYZ_commutator : commutator pauliY pauliZ = (2 * 𝕚) • pauliX := by
  rw [commutator, pauliY_pauliZ, pauliZ_pauliY]
  rw [show (2 : ℂ) * 𝕚 = 𝕚 + 𝕚 by ring, add_smul, neg_smul, sub_neg_eq_add]

theorem pauliZX_commutator : commutator pauliZ pauliX = (2 * 𝕚) • pauliY := by
  rw [commutator, pauliZ_pauliX, pauliX_pauliZ]
  rw [show (2 : ℂ) * 𝕚 = 𝕚 + 𝕚 by ring, add_smul, neg_smul, sub_neg_eq_add]

/-! ### The spin-1/2 Pauli-vector product

The identity (sigma.a)(sigma.b) = (a.b) I + i sigma.(a cross b) for commuting
scalar components.  This is the workhorse behind Bell/CHSH and spin algebra. -/

def cross3 (a b : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

def dot3 (a b : Fin 3 → ℂ) : ℂ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

/-- The Pauli vector sigma.a as a 2x2 operator. -/
def sigmaDot (a : Fin 3 → ℂ) : Operator 2 :=
  a 0 • pauliX + a 1 • pauliY + a 2 • pauliZ

/-- Main identity: (sigma.a)(sigma.b) = (a.b) I + i sigma.(a cross b). -/
theorem sigmaDot_mul_sigmaDot (a b : Fin 3 → ℂ) :
    sigmaDot a * sigmaDot b
      = dot3 a b • identity + 𝕚 • sigmaDot (cross3 a b) := by
  unfold sigmaDot dot3 cross3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, identity, Matrix.mul_apply, Matrix.add_apply,
      Matrix.smul_apply, Fin.sum_univ_two]
  all_goals
    ring_nf
    simp only [Complex.I_sq]
    ring

end LeanPhy.Quantum
