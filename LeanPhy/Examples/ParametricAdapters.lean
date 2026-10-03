import LeanPhy.QuantumInfo.Model
import LeanPhy.StatMech.Model
import Mathlib.Tactic

/-!
# Domain adapter regression for parameterised models

The constructors under `QuantumInfo` and `StatMech` are deliberately tiny:
they expose the existing finite CPTP and Markov-kernel invariants through the
same parameterised model interface.  The examples below check that a client
can recover the original pointwise models without any additional axiom.
-/

namespace LeanPhy.Examples.ParametricAdapters

open LeanPhy.Mathematics
open LeanPhy.QuantumInfo
open LeanPhy.StatMech

theorem quantum_family_at
    {P ι : Type*} [Fintype ι]
    (family : P → FiniteCPTPMap ι ι) (p : P) :
    (FiniteCPTPMap.toParametricModel family).modelAt p =
      (family p).toModel := by
  rfl

theorem stochastic_family_at
    {P ι : Type*} [Fintype ι]
    (family : P → FiniteKernel ι) (p : P) :
    (FiniteKernel.toParametricModel family).modelAt p =
      FiniteKernel.toModel (family p) := by
  rfl

end LeanPhy.Examples.ParametricAdapters
