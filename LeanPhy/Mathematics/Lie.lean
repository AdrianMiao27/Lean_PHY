import LeanPhy.Quantum.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Lie algebra identities from associative operator algebras

The commutator of any associative algebra is a Lie bracket.  These identities
are the common mathematical core of angular momentum, Lorentz and gauge
algebras, creation/annihilation operators, and supersymmetry.  They are proved
once here and reused by domain modules; no structure constants or
representation-specific assumptions are hidden.
-/

namespace LeanPhy.Mathematics

universe u

open LeanPhy.Quantum

theorem commutator_jacobi {A : Type u} [Ring A] (x y z : A) :
    ⟦x, ⟦y, z⟧⟧ + ⟦y, ⟦z, x⟧⟧ + ⟦z, ⟦x, y⟧⟧ = 0 := by
  simp only [commutator, mul_sub, sub_mul]
  noncomm_ring

theorem commutator_adjoint_leibniz {A : Type u} [Ring A] (x y z : A) :
    ⟦x, y * z⟧ = ⟦x, y⟧ * z + y * ⟦x, z⟧ := by
  exact commutator_mul_right x y z

theorem commutator_adjoint_additive {A : Type u} [Ring A] (x y z : A) :
    ⟦x, y + z⟧ = ⟦x, y⟧ + ⟦x, z⟧ := by
  exact commutator_add_right x y z

theorem commutator_center_iff {A : Type u} [Ring A] (c : A) :
    (∀ x, ⟦x, c⟧ = 0) ↔ (∀ x, x * c = c * x) := by
  constructor
  · intro h x
    exact sub_eq_zero.mp (h x)
  · intro h x
    exact sub_eq_zero.mpr (h x)

end LeanPhy.Mathematics
