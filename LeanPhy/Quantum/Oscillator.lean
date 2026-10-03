import LeanPhy.Quantum.Basic

/-!
# Algebraic oscillator identities

This module proves the ladder-operator commutator from the CCR as a purely
algebraic theorem.  No analytic claim about unbounded operators is made.
-/

namespace LeanPhy.Quantum

theorem number_commutator {A : Type} [Ring A] (a adag : A)
    (hCCR : ⟦a, adag⟧ = 1) :
    ⟦adag * a, adag⟧ = adag := by
  rw [commutator_mul_left, hCCR, commutator_self]
  simp

theorem number_commutator_explicit {A : Type} [Ring A] (a adag : A)
    (hCCR : a * adag - adag * a = 1) :
    (adag * a) * adag - adag * (adag * a) = adag := by
  exact number_commutator a adag hCCR

end LeanPhy.Quantum
