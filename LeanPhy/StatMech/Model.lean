import LeanPhy.Mathematics.Model
import LeanPhy.Mathematics.ParametricModel
import LeanPhy.StatMech.FiniteKernel

/-! # Finite stochastic models

These adapters retain normalized probability states and expectation readouts.
A channel between models must intertwine the declared evolution steps; merely
preserving probabilities does not imply that two dynamics simulate each other.
-/

namespace LeanPhy.StatMech.FiniteKernel

open LeanPhy.Mathematics

variable {ι : Type*} [Fintype ι]

/-- The existing stochastic kernel as a model with real expectation readouts. -/
noncomputable def toModel (K : FiniteKernel ι) : PhysicalModel ℝ where
  State := FiniteProbability ι
  valid := fun _ => True
  step := K.toStateMap
  Observable := ι → ℝ
  evaluate := fun p f => p.expectation f

/- A temperature, field, or coupling sweep is represented by a parameterised
   family of finite kernels.  Normalisation remains part of each
   `FiniteKernel`; the family constructor adds no hidden stochastic axiom. -/
noncomputable def toParametricModel {P : Type*}
    (family : P → FiniteKernel ι) : ParametricModel P ℝ where
  State := FiniteProbability ι
  valid := fun _ _ => True
  step := fun p => (family p).toStateMap
  Observable := ι → ℝ
  evaluate := fun _ p f => p.expectation f

@[simp] theorem toParametricModel_modelAt {P : Type*}
    (family : P → FiniteKernel ι) (p : P) :
    (toParametricModel family).modelAt p = toModel (family p) := rfl

/-- A stochastic adapter between two dynamics, given the intertwining law.
The observable pullback is computed from the kernel, with its duality proved. -/
noncomputable def modelMap (C K L : FiniteKernel ι)
    (h : ∀ p, C.step (K.step p) = L.step (C.step p)) :
    ModelMap K.toModel L.toModel where
  state := C.toStateMap
  pullback := C.pullback
  step_commutes := fun p _ => h p
  evaluate_commutes := fun p _ f => C.step_expectation p f

/-- One intertwining identity controls every finite-time expectation. -/
theorem modelMap_expectation (C K L : FiniteKernel ι)
    (h : ∀ p, C.step (K.step p) = L.step (C.step p))
    (n : Nat) (p : FiniteProbability ι) (f : ι → ℝ) :
    (Process.iterate L.toStateMap n (C.step p)).expectation f =
      (Process.iterate K.toStateMap n p).expectation (C.pullback f) :=
  (modelMap C K L h).trajectory_evaluate n p trivial f

end LeanPhy.StatMech.FiniteKernel
