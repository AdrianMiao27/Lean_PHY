import LeanPhy.Quantum.Basic
import LeanPhy.FieldTheory.MultiCAR
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# Fermionic algebra: canonical anticommutation relations

One fermionic mode, stated as pure ring algebra with explicit hypotheses,
mirroring the bosonic modules.  From the CAR {c, c†} = 1 and nilpotency
c^2 = (c†)^2 = 0, the number operator N = c† c is a projector and acts as the
ladder c† (raising) and c (lowering).  These are the algebraic ingredients of
Hubbard/BCS-style model identities.
-/

namespace LeanPhy.FieldTheory

open LeanPhy.Quantum

/-- A single fermionic mode in a ring. -/
structure FermionicMode where
  A : Type
  [ringA : Ring A]
  /-- Annihilation operator. -/
  c : A
  /-- Creation operator. -/
  cdag : A
  /-- The canonical anticommutation relation, {c, c†} = 1. -/
  car : c * cdag + cdag * c = 1
  /-- Annihilation is nilpotent. -/
  c_sq : c * c = 0
  /-- Creation is nilpotent. -/
  cdag_sq : cdag * cdag = 0

attribute [instance] FermionicMode.ringA

namespace FermionicMode

variable (M : FermionicMode)

local notation "c" => M.c
local notation "d" => M.cdag

/-- The CAR in subtractive form: c c† = 1 - c† c. -/
theorem car_sub : c * d = 1 - d * c := by
  have h : c * d + d * c = 1 := M.car
  rw [eq_sub_iff_add_eq]
  exact h

/-- The number operator N = c† c. -/
def numberOp : M.A := M.cdag * M.c

/-- The number operator is a projector (Pauli exclusion at the algebra level):
N^2 = N. -/
theorem number_idempotent : M.numberOp * M.numberOp = M.numberOp := by
  have hcd : c * d = 1 - d * c := M.car_sub
  have hdd : d * (d * (c * c)) = 0 := by
    rw [show d * (d * (c * c)) = (d * d) * (c * c) from by noncomm_ring, M.c_sq, mul_zero]
  rw [numberOp, show (d*c) * (d*c) = d * (c*d) * c from by noncomm_ring, hcd]
  rw [show d * (1 - d*c) * c = d*c - d * (d * (c*c)) from by noncomm_ring, hdd, sub_zero]

/-- The number operator raises: [N, c†] = c†. -/
theorem number_commutator_create : ⟦M.numberOp, d⟧ = d := by
  have hcd : c * d = 1 - d * c := M.car_sub
  have hkey : d * (d * c) = 0 := by
    rw [show d * (d * c) = (d * d) * c from by noncomm_ring, M.cdag_sq, zero_mul]
  have hdcd : d * (c * d) = d := by
    rw [show d * (c * d) = d * (c * d) from rfl, hcd]
    rw [show d * (1 - d*c) = d - d*(d*c) from by noncomm_ring, hkey, sub_zero]
  rw [numberOp, commutator, show (d*c)*d = d*(c*d) from by noncomm_ring, hdcd, hkey]
  abel

/-- The number operator lowers: [N, c] = -c. -/
theorem number_commutator_annihilate : ⟦M.numberOp, c⟧ = -c := by
  have hcc : d * (c * c) = 0 := by rw [M.c_sq, mul_zero]
  have hcdc : c * (d * c) = c := by
    rw [show c * (d * c) = (c * d) * c from by noncomm_ring, M.car_sub]
    rw [show (1 - d*c) * c = c - d*(c*c) from by noncomm_ring, hcc, sub_zero]
  rw [numberOp, commutator, show (d*c)*c = d*(c*c) from by noncomm_ring, hcc, hcdc]
  abel

/-- Acting with the raising operator twice kills any state, so N shrinks the
two-particle sector to zero: N (c† c†) = 0. -/
theorem number_create_nilpotent : M.numberOp * (d * d) = 0 := by
  rw [numberOp, show (d*c) * (d*d) = d * (c * (d*d)) from by noncomm_ring, M.cdag_sq, mul_zero,
    mul_zero]

/-! The one-mode condensed-matter object is an instance of the shared finite
    CAR interface.  This lets Hubbard/Kitaev adapters reuse the multi-mode
    number-operator lemmas without duplicating the anticommutator bookkeeping. -/

noncomputable def asMultiCAR : MultiModeCAR PUnit M.A where
  ann := fun _ => M.c
  cre := fun _ => M.cdag
  car_ann_cre := by
    intro i j
    simp [anticommutator, M.car]
  car_ann_ann := by
    intro i j
    simp [anticommutator, M.c_sq]
  car_cre_cre := by
    intro i j
    simp [anticommutator, M.cdag_sq]

theorem asMultiCAR_numberOp : (M.asMultiCAR).numberOp PUnit.unit = M.numberOp := by
  simp [MultiModeCAR.numberOp, asMultiCAR, FermionicMode.numberOp]

theorem asMultiCAR_totalNumber : (M.asMultiCAR).totalNumber = M.numberOp := by
  classical
  change (∑ _ : PUnit, (M.asMultiCAR).numberOp PUnit.unit) = M.numberOp
  simp [asMultiCAR_numberOp]

end FermionicMode

end LeanPhy.FieldTheory
