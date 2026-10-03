import LeanPhy.Mathematics.Model
import LeanPhy.Mathematics.ParametricModel
import LeanPhy.QuantumInfo.CPTP

/-! # Finite quantum model adapters

Evolution is an arbitrary finite CPTP endomap. A rectangular Kraus map can
connect different state-space sizes after proving the explicit intertwining
law. Observable transport uses the existing trace-pairing theorem; complete
positivity, normalization, and the dynamics proof are never inferred from
names. Complex trace readouts also allow non-Hermitian probes.
-/

namespace LeanPhy.QuantumInfo

open LeanPhy.Mathematics LeanPhy.Quantum

variable {ι κ ξ : Type*} [Fintype ι] [Fintype κ] [Fintype ξ]

def FiniteCPTPMap.toModel (C : FiniteCPTPMap ι ι) : PhysicalModel ℂ where
  State := Matrix ι ι ℂ
  valid := IsFiniteDensity
  step := C.toStateMap
  Observable := Matrix ι ι ℂ
  evaluate := fun rho A => Matrix.trace (rho * A)

/- A parameterised channel family is a first-class model.  This constructor
   is intentionally representation-preserving: every parameter uses the same
   finite matrix state and observable types, while positivity and trace
   preservation are carried by each member of the supplied family. -/
def FiniteCPTPMap.toParametricModel {P : Type*}
    (family : P → FiniteCPTPMap ι ι) : ParametricModel P ℂ where
  State := Matrix ι ι ℂ
  valid := fun _ => IsFiniteDensity
  step := fun p => (family p).toStateMap
  Observable := Matrix ι ι ℂ
  evaluate := fun _ rho A => Matrix.trace (rho * A)

@[simp] theorem FiniteCPTPMap.toParametricModel_modelAt
    {P : Type*} (family : P → FiniteCPTPMap ι ι) (p : P) :
    (FiniteCPTPMap.toParametricModel family).modelAt p =
      (family p).toModel := rfl

/-- A Kraus bridge between different model sizes, with exact dynamics supplied. -/
noncomputable def TypedKrausChannel.modelMap [DecidableEq ι]
    (C : TypedKrausChannel ι κ ξ)
    (K : FiniteCPTPMap ι ι) (L : FiniteCPTPMap κ κ)
    (h : ∀ rho, IsFiniteDensity rho → C.apply (K rho) = L (C.apply rho)) :
    ModelMap K.toModel L.toModel where
  state := C.toStateMap
  pullback := typedAdjointKraus C.op
  step_commutes := h
  evaluate_commutes := fun rho _ A => typedTracePairing C.op rho A

/-- Evolve in either representation and obtain the same pulled-back readout. -/
theorem TypedKrausChannel.modelMap_expectation [DecidableEq ι]
    (C : TypedKrausChannel ι κ ξ)
    (K : FiniteCPTPMap ι ι) (L : FiniteCPTPMap κ κ)
    (h : ∀ rho, IsFiniteDensity rho → C.apply (K rho) = L (C.apply rho))
    (n : Nat) (rho : Matrix ι ι ℂ) (hrho : IsFiniteDensity rho)
    (A : Matrix κ κ ℂ) :
    Matrix.trace (Process.iterate L.toStateMap n (C.apply rho) * A) =
      Matrix.trace (Process.iterate K.toStateMap n rho * typedAdjointKraus C.op A) :=
  (C.modelMap K L h).trajectory_evaluate n rho hrho A

end LeanPhy.QuantumInfo
