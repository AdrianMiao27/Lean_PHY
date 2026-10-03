import LeanPhy.QuantumInfo.KrausBundle
import LeanPhy.Quantum.Unitary
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-!
# Closed dynamics as a CPTP channel

A finite unitary is a one-Kraus trace-preserving channel.  This adapter keeps
the closed-system and open-system APIs compatible: a quantum gate can be used
where a `KrausChannel` is expected, while the direct conjugation notation stays
available for physics-facing proofs.
-/

namespace LeanPhy.QuantumInfo

open LeanPhy.Quantum
open scoped BigOperators Matrix

/-- The singleton Kraus presentation of a finite unitary. -/
noncomputable def unitaryChannel {n : Nat}
    (U : UnitaryOperator n) : KrausChannel n PUnit where
  op := fun _ => U.op
  complete := by
    simpa using U.unitary

theorem unitaryChannel_apply {n : Nat}
    (U : UnitaryOperator n) (rho : State n) :
    (unitaryChannel U).toFiniteChannel rho = unitaryConjugate U rho := by
  unfold unitaryChannel KrausChannel.toFiniteChannel fromKraus applyKraus unitaryConjugate
  simp

theorem unitaryChannel_isDensity {n : Nat}
    (U : UnitaryOperator n) (rho : State n) (hrho : IsDensity rho) :
    IsDensity ((unitaryChannel U).toFiniteChannel rho) := by
  rw [unitaryChannel_apply]
  exact unitaryConjugate_isDensity U rho hrho

theorem unitaryChannel_trace_preserving {n : Nat}
    (U : UnitaryOperator n) (rho : State n) :
    Matrix.trace ((unitaryChannel U).toFiniteChannel rho) = Matrix.trace rho := by
  exact (unitaryChannel U).trace_preserving rho

theorem unitaryChannel_compose_apply {n : Nat}
    (after before : UnitaryOperator n) (rho : State n) :
    ((unitaryChannel after).compose (unitaryChannel before)).toFiniteChannel rho =
      (unitaryChannel (after.compose before)).toFiniteChannel rho := by
  rw [KrausChannel.compose_toFiniteChannel_apply]
  rw [unitaryChannel_apply, unitaryChannel_apply, unitaryChannel_apply]
  exact (UnitaryOperator.compose_conjugate after before rho).symm

end LeanPhy.QuantumInfo
