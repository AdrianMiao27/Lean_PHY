import LeanPhy.Quantum.ThermalPerturbation
import LeanPhy.Quantum.FiniteFrequencyResponse
import LeanPhy.Quantum.DrivenPulse
import LeanPhy.Quantum.Pauli
import LeanPhy.FieldTheory.FiniteFermion
import LeanPhy.Workflow.Core

set_option autoImplicit false

/-! Public clients consume constructed many-body models; exact counterexamples
protect time signs, noncommutativity, thermal normalization and contact terms. -/

namespace LeanPhy.Examples.DynamicsResearch

open LeanPhy.Quantum LeanPhy.Quantum.Dynamics LeanPhy.Quantum.ThermalPerturbation
open LeanPhy.FieldTheory.FiniteFermion LeanPhy.FieldTheory.FermionBdG
open LeanPhy.Mathematics LeanPhy.Workflow
open scoped Matrix Matrix.Norms.Operator

theorem fermion_response (n : ℕ) (K V : Coefficients (Fin n))
    (O : Matrix (Occupation n) (Occupation n) ℂ) (β t : ℝ) :
    HasDerivAt (fun ε : ℝ => expectation ((modes n).thermalState K β).rho
      ((modes n).hamiltonian K + ε • (modes n).hamiltonian V) O t)
      (∫ s in (0 : ℝ)..t, kernel ((modes n).thermalState K β).rho
        ((modes n).hamiltonian K) ((modes n).hamiltonian V) O t s) 0 :=
  expectation_perturbation_integral _ _ _ _ t

noncomputable def initialState : FiniteDensity (Fin 2) := diagonalDensity
  { weight := fun i => if i = 0 then 1 else 0
    nonneg := by intro i; split_ifs <;> norm_num
    normalised := by norm_num [Fin.sum_univ_two] }

theorem kernel_sign : kernel initialState.rho pauliZ pauliX pauliY 0 0 = -2 := by
  norm_num [kernel, commutatorResponse, heisenberg_zero, initialState, diagonalDensity,
    realDiagonal, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, pauliX, pauliY,
    mul_add, Complex.I_mul_I]

theorem noncommuting_input : ¬ Commute pauliZ pauliX := by
  intro h
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) h.eq
  norm_num [pauliZ, pauliX, Matrix.mul_apply, Fin.sum_univ_two] at he

theorem time_sign : HasDerivAt (heisenberg pauliZ pauliX) ((-2 : ℂ) • pauliY) 0 := by
  have h : Complex.I • (pauliZ * pauliX - pauliX * pauliZ) = (-2 : ℂ) • pauliY := by
    rw [pauliZ_pauliX, pauliX_pauliZ, ← sub_smul, smul_smul]
    congr 1
    norm_num [mul_sub, mul_add, Complex.I_mul_I]
  simpa only [heisenberg_zero, h] using! heisenberg_derivative pauliZ pauliX 0

theorem wrong_time_sign_rejected :
    ¬ HasDerivAt (heisenberg pauliZ pauliX) ((2 : ℂ) • pauliY) 0 := by
  intro h
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 0 1).im) (h.unique time_sign)
  norm_num [pauliY, Matrix.smul_apply] at he

theorem normalization_subtraction :
    response (0 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 0 1 = 0 ∧
      Matrix.trace (weightVariation (0 : Matrix (Fin 2) (Fin 2) ℂ) 1 1) = -2 := by
  constructor
  · exact response_identity _ _ _
  · rw [weightVariation, Duhamel.insertion_of_commute _ _ _ (Commute.zero_left _)]
    norm_num [Duhamel.flow, Matrix.trace_one]

theorem contact_required : response (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 1 1 = 1 := by
  norm_num [response, weight, partition, Duhamel.flow, Matrix.trace_one]

theorem beta_factor : response (0 : Matrix (Fin 2) (Fin 2) ℂ) pauliZ pauliZ 0 2 = -2 := by
  rw [response_of_commute _ _ _ _ _ (Commute.zero_left _)
    (by norm_num [partition, weight, Duhamel.flow, Matrix.trace_one])]
  norm_num [mean, partition, weight, Duhamel.flow, pauliZ_sq, identity, pauliZ,
    Matrix.trace, Fin.sum_univ_two]

/-! A finite Fourier system reconstructs the sampled actual response exactly.
The theorem is deliberately grid-level: it does not introduce stationarity or
an infinite-time/frequency limit. -/
theorem finite_frequency_reconstruction
    (ρ H V O : Matrix (Fin 2) (Fin 2) ℂ) (times : Fin 4 → ℝ) :
    FiniteFourierSystem.inverse FiniteFourierSystem.fourier4
        (finiteFrequencyResponse FiniteFourierSystem.fourier4 ρ H V O times) =
      sampledStepResponse ρ H V O times :=
  finiteFrequencyResponse_inverse FiniteFourierSystem.fourier4 ρ H V O times

/-- Arbitrary finite CAR models and continuous rotating-frame envelopes enter
an explicitly constructed Schrödinger family, not a postulated response. -/
theorem fermion_pulse_response (n : ℕ) (K B : Coefficients (Fin n))
    (O : Matrix (Occupation n) (Occupation n) ℂ) (β a t : ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    let U := TimeDependent.autonomous ((modes n).hamiltonian K)
      ((modes n).hamiltonian_hermitian K) a
    let F := TimeDependent.pulseFamily U ((modes n).hamiltonian B)
      ((modes n).hamiltonian_hermitian B) f hf
    HasDerivAt (fun ε => Matrix.trace (((modes n).thermalState K β).rho *
      (F.evolution ε).observable O t))
      (TimeDependent.pulseArea f a t • (Complex.I * commutatorResponse
        ((modes n).thermalState K β).rho ((modes n).hamiltonian B) (U.observable O t))) 0 := by
  dsimp only
  rw [← TimeDependent.pulseFamily_response]
  exact TimeDependent.DrivenFamily.expectation_derivative _ _ _ _

def package : TheoryPackage :=
  TheoryPackage.empty "finite quantum response" "condensed matter and finite-mode field theory"
    |>.addTheorem "constructed many-body response" "actual CAR Hamiltonians and Gibbs initial states enter finite-time Kubo response"
      "fermion_response" fermion_response
    |>.addTheorem "physical picture equivalence" "the evolved density and Heisenberg probe have identical trace readouts"
      "LeanPhy.Quantum.Dynamics.state_expectation" (@state_expectation.{0})
    |>.addTheorem "noncommuting thermal derivative" "a perturbed Hermitian family differentiates actual normalized Gibbs expectations"
      "LeanPhy.Quantum.ThermalPerturbation.thermal_expectation_perturbation"
      (@thermal_expectation_perturbation.{0})
    |>.addTheorem "moving probe response" "the probe derivative is retained as a contact term"
      "LeanPhy.Quantum.Dynamics.expectation_perturbation" (@expectation_perturbation.{0})
    |>.addTheorem "commuting thermal limit" "the ordinary covariance rule requires commuting H and V and keeps minus beta"
      "LeanPhy.Quantum.ThermalPerturbation.response_of_commute" (@response_of_commute.{0})
    |>.addTheorem "causal switched response" "the actual switched readout has the claimed response derivative"
      "LeanPhy.Quantum.Dynamics.step_response_derivative" (@step_response_derivative.{0})
    |>.addTheorem "noncommuting input" "Pauli perturbations genuinely exercise noncommutative dynamics"
      "noncommuting_input" noncommuting_input
    |>.addTheorem "time convention" "the opposite Heisenberg derivative sign is rejected"
      "wrong_time_sign_rejected" wrong_time_sign_rejected
    |>.addTheorem "normalization subtraction" "the identity response vanishes although its unnormalized insertion does not"
      "normalization_subtraction" normalization_subtraction
    |>.addTheorem "thermal beta" "finite-temperature response retains its beta factor"
      "beta_factor" beta_factor
    |>.addTheorem "finite frequency reconstruction"
      "a supplied finite Fourier grid reconstructs the sampled actual response"
      "finite_frequency_reconstruction" finite_frequency_reconstruction
    |>.addTheorem "constructed continuous many-body pulse"
      "arbitrary CAR models and continuous rotating-frame envelopes have actual response derivatives"
      "fermion_pulse_response" fermion_pulse_response
    |>.addTheorem "unitarity from the driven equation"
      "Hermiticity, the actual differential equation and common preparation imply unitarity"
      "LeanPhy.Quantum.TimeDependent.Evolution.unitary" (@TimeDependent.Evolution.unitary.{0})
    |>.addTheorem "ordered two-time transport"
      "finite transport composes in Schrödinger order and permits a new preparation time"
      "LeanPhy.Quantum.TimeDependent.Evolution.between_comp" (@TimeDependent.Evolution.between_comp.{0})
    |>.addTheorem "general driven response"
      "jointly continuous actual amplitude families yield the two-time Kubo integral"
      "LeanPhy.Quantum.TimeDependent.DrivenFamily.expectation_derivative"
      (@TimeDependent.DrivenFamily.expectation_derivative.{0})
    |>.addTheorem "preparation and probe contacts"
      "amplitude-dependent initial matrices and probes retain both derivative terms"
      "LeanPhy.Quantum.TimeDependent.DrivenFamily.expectation_contacts"
      (@TimeDependent.DrivenFamily.expectation_contacts.{0})
    |>.addTheorem "causal driven derivative"
      "the switched actual driven readout has zero past response"
      "LeanPhy.Quantum.TimeDependent.DrivenFamily.switched_derivative"
      (@TimeDependent.DrivenFamily.switched_derivative.{0})
    |>.addTheorem "observed source interval"
      "changing a source outside the observed interval preserves first response"
      "LeanPhy.Quantum.TimeDependent.DrivenFamily.response_congr"
      (@TimeDependent.DrivenFamily.response_congr.{0})
    |>.addObligationText "general evolution existence and frequency response"
      "construct solutions beyond autonomous and rotating-frame drives and establish continuous frequency representations"
      "general ODE existence and parameter continuity, local or discontinuous envelopes, stationarity and convergence evidence"
    |>.addObligationText "controlled perturbation remainder" "bound the finite-amplitude error of a chosen linear-response approximation"
      "model and parameter dependent norm estimates"
    |>.addObligationText "continuum limits" "justify unbounded, infinite-volume or infinite-time limits for the target theory"
      "operator domains and uniform analytic bounds"

example : package.claimCount = 18 := rfl
example : package.obligationCount = 3 := rfl
example : package.hasErrors = false := by decide

end LeanPhy.Examples.DynamicsResearch
