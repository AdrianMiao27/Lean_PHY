import LeanPhy.Quantum.DynamicalResponse
import LeanPhy.Mathematics.FiniteFourier

set_option autoImplicit false

/-!
# Finite frequency readout for an actual response

This module is the finite-volume bridge between the already proved
time-domain response and a frequency-labelled data product.  A researcher
supplies a finite Fourier system and a sampling map from Fourier labels to
real times.  The transform is exact on the supplied finite grid: the inverse
reconstructs the sampled response and Parseval keeps the normalization
explicit.  No stationarity, continuum Fourier integral, infinite-time limit,
or spectral convergence is inferred.
-/

namespace LeanPhy.Quantum.Dynamics

open LeanPhy.Mathematics

variable {α : Type} {ι : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype ι] [DecidableEq ι]

/-! ## Sampling the actual finite-time response -/

noncomputable def sampledStepResponse
    (ρ H V O : Matrix ι ι ℂ) (times : α → ℝ) : α → ℂ :=
  fun k => stepResponse ρ H V O (times k)

noncomputable def finiteFrequencyResponse
    (F : FiniteFourierSystem α) (ρ H V O : Matrix ι ι ℂ)
    (times : α → ℝ) : α → ℂ :=
  F.forward (sampledStepResponse ρ H V O times)

theorem finiteFrequencyResponse_inverse
    (F : FiniteFourierSystem α) (ρ H V O : Matrix ι ι ℂ)
    (times : α → ℝ) :
    F.inverse (finiteFrequencyResponse F ρ H V O times) =
      sampledStepResponse ρ H V O times := by
  exact F.inverse_forward _

theorem finiteFrequencyResponse_reconstruct_at
    (F : FiniteFourierSystem α) (ρ H V O : Matrix ι ι ℂ)
    (times : α → ℝ) (k : α) :
    (F.inverse (finiteFrequencyResponse F ρ H V O times)) k =
      stepResponse ρ H V O (times k) := by
  rw [finiteFrequencyResponse_inverse]
  rfl

theorem finiteFrequencyResponse_parseval
    (F : FiniteFourierSystem α) (ρ H V O : Matrix ι ι ℂ)
    (times : α → ℝ) :
    FiniteFourierSystem.finiteInner (finiteFrequencyResponse F ρ H V O times)
      (finiteFrequencyResponse F ρ H V O times) =
      (Fintype.card α : ℂ) *
        FiniteFourierSystem.finiteInner (sampledStepResponse ρ H V O times)
          (sampledStepResponse ρ H V O times) := by
  exact F.parseval _ _

end LeanPhy.Quantum.Dynamics
