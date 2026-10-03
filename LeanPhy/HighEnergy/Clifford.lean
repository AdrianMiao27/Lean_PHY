import LeanPhy.Quantum.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

/-! Abstract Clifford generators and consequences used by high-energy models. -/

namespace LeanPhy.HighEnergy

open LeanPhy.Quantum

variable {A : Type} [Ring A]

def cliffordRelation (x y : A) (η : A) : Prop := x * y + y * x = 2 * η

/-- A Clifford generator squares to its metric coefficient. -/
theorem clifford_square (x η : A) (h : cliffordRelation x x η) : 2 * (x * x) = 2 * η := by
  dsimp [cliffordRelation] at h
  rw [← two_mul (x * x)] at h
  exact h

/-- Two generators anticommute when their bilinear form vanishes. -/
def anticommuting (x y : A) : Prop := x * y + y * x = 0

/-- Anticommuting generators turn their commutator into `2 x y`. -/
theorem anticommuting_commutator (x y : A) (h : anticommuting x y) :
    ⟦x, y⟧ = 2 * (x * y) := by
  have h2 : y * x = -(x * y) := eq_neg_of_add_eq_zero_right h
  rw [commutator, h2]
  noncomm_ring

theorem anticommuting_sq (x : A) (h : anticommuting x x) : 2 * (x * x) = 0 := by
  dsimp [anticommuting] at h
  rw [← two_mul (x * x)] at h
  exact h

end LeanPhy.HighEnergy
