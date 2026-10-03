import LeanPhy.Quantum.Basic
import LeanPhy.Quantum.Oscillator
import Mathlib.Tactic.NoncommRing

/-!
# Algebraic canonical commutation relations

All statements here are finite algebraic consequences of the CCR.  They do
not assert existence of unbounded operators on a Hilbert space.
-/

namespace LeanPhy.FieldTheory

open LeanPhy.Quantum

variable {A : Type} [Ring A]

def number (adag a : A) : A := adag * a

theorem number_commutator (a adag : A) (h : ⟦a, adag⟧ = 1) :
    ⟦number adag a, adag⟧ = adag := by
  exact LeanPhy.Quantum.number_commutator a adag h

theorem commutator_a_number (a adag : A) (h : ⟦a, adag⟧ = 1) :
    ⟦a, number adag a⟧ = a := by
  rw [number, commutator_mul_right, h, commutator_self]
  simp

theorem number_commutator_a (a adag : A) (h : ⟦a, adag⟧ = 1) :
    ⟦number adag a, a⟧ = -a := by
  rw [commutator_skew, commutator_a_number a adag h]

theorem commutator_a_number_neg (a adag : A) (h : ⟦a, adag⟧ = 1) :
    ⟦number adag a, a⟧ = -a := number_commutator_a a adag h

theorem annihilation_kills_ground (a adag : A) (h : ⟦a, adag⟧ = 1) :
    ⟦number adag a, adag⟧ - adag = 0 := by
  rw [number_commutator a adag h, sub_self]

end LeanPhy.FieldTheory
