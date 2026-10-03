import LeanPhy.Quantum.Basic
import LeanPhy.FieldTheory.CCR

/-!
# Fock-space algebra in a ring

The Fock space is modelled abstractly by a ring with a distinguished pair of
ladder operators.  This is the algebraic skeleton that the operator-theoretic
version would instantiate; no completeness, convergence, or domain condition is
claimed here.
-/

namespace LeanPhy.FieldTheory

open LeanPhy.Quantum

variable {A : Type} [Ring A]

/-- A structure carrying the algebraic data of a single bosonic mode. -/
structure BosonicMode (A : Type) [Ring A] where
  /-- Annihilation operator. -/
  annihilate : A
  /-- Creation operator. -/
  create : A
  /-- The canonical commutation relation, as an explicit hypothesis. -/
  ccr : ⟦annihilate, create⟧ = 1

namespace BosonicMode

variable (M : BosonicMode A)

/-- The number operator `N = a† a`. -/
def numberOp : A := M.create * M.annihilate

/-- `N` raises/commutes with `a†` in the expected way. -/
theorem number_commutes_create : ⟦M.numberOp, M.create⟧ = M.create := by
  simpa [numberOp] using
    (LeanPhy.Quantum.number_commutator M.annihilate M.create M.ccr)

/-- `[N, a] = -a`: lowering by one unit. -/
theorem number_commutes_annihilate : ⟦M.numberOp, M.annihilate⟧ = -M.annihilate := by
  simpa [numberOp, number, mul_comm] using
    commutator_a_number_neg M.annihilate M.create M.ccr

/-- The number operator commutes with every power of the raising operator up to
the ladder factor, stated one step at a time to keep the arithmetic transparent. -/
theorem number_create_sq :
    ⟦M.numberOp, M.create * M.create⟧ = 2 * (M.create * M.create) := by
  rw [commutator_mul_right, M.number_commutes_create]
  noncomm_ring

end BosonicMode

end LeanPhy.FieldTheory
