import LeanPhy.Entry.Physics
import LeanPhy.Tactics
import LeanPhy.Library

/-!
# Cross-domain regression for the `physics` tactic

These tests exercise the public tactic on the algebraic interfaces shared by
different domains.  They are intentionally generic in the coefficient ring or
finite index type; the purpose is to ensure that `physics` is a reusable proof
entry point, rather than a macro that only happens to solve one named example.
Every example still elaborates to an ordinary kernel-checked Lean proof.
-/

namespace LeanPhy.Examples.PhysicsTactic

open LeanPhy.Quantum
open LeanPhy.FieldTheory
open LeanPhy.GaugeTheory
open LeanPhy.IndexCalculus

/-! Quantum and field-theory algebra. -/

example {A : Type} [Ring A] (x y z : A) :
    commutator (x + y) z = commutator x z + commutator y z := by
  physics

example {A : Type} [Ring A] (x y : A) :
    x * (y + y) = x * y + x * y := by
  physics

example : commutator pauliX pauliY = (2 * Complex.I) • pauliZ := by
  rw [LeanPhy.Quantum.commutator, pauliX_pauliY, pauliY_pauliX]
  physics

example {A : Type} [Ring A] (a adag : A) (h : ⟦a, adag⟧ = 1) :
    ⟦adag * a, adag⟧ = adag := by
  rw [commutator_mul_left, h, commutator_self]
  physics

/-! The same normaliser handles the non-abelian gauge curvature skeleton. -/

example {A : Type} [Ring A] (D : Fin 4 → A) (mu nu : Fin 4) :
    fieldStrength D mu nu = -fieldStrength D nu mu := by
  unfold fieldStrength
  physics

/-! Finite index identities use the surface unfolding before arithmetic. -/

example (i : Fin 3) : delta i i = 1 := by
  physics

example (i j k : Fin 3) : epsilon i j k = -epsilon i k j := by
  exact epsilon_antisymm i j k

/-! Discovery and arithmetic facade regressions.  `physics_search` delegates
to Lean's ordinary theorem search, while `physics_norm_num` is a stable name
for numerical normalization; neither tactic adds an untrusted proof path. -/

example (i : Fin 3) : delta i i = 1 := by
  physics_search

example : (7 : ℤ) + 5 = 12 := by
  physics_norm_num

example : (LeanPhy.Library.names (LeanPhy.Library.search "CCR")).length = 1 := by
  decide

end LeanPhy.Examples.PhysicsTactic
