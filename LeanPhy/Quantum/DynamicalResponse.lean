import LeanPhy.Mathematics.Duhamel
import LeanPhy.Mathematics.FiniteResponse
import LeanPhy.Quantum.FiniteDensity
import LeanPhy.Quantum.HamiltonianFlow
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

/-!
# Actual finite Hamiltonian dynamics and perturbation response

The convention is ℏ = 1, `U(t) = exp(+i t H)`, and the Heisenberg observable
is `U(t) O U(-t)`. The physical density evolves with the opposite sign.
The response below differentiates this actual observable when `H` changes to
`H + ε V`; it does not assume that `H` and `V` commute. Positivity of states
is supplied by the existing finite-density and unitary APIs. No unbounded
operators, time-dependent drive, infinite-time or thermodynamic limit is used.
-/

namespace LeanPhy.Quantum.Dynamics

open LeanPhy.Mathematics
open scoped Matrix Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def propagator (H : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  Duhamel.flow (Complex.I • H) t

theorem propagator_eq_finiteHamiltonianFlow (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    propagator H t = (finiteHamiltonianFlow H hH t).op := by
  simp only [propagator, Duhamel.flow, finiteHamiltonianFlow_op,
    hamiltonianGenerator, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

theorem propagator_neg_eq_adjoint (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (t : ℝ) : propagator H (-t) = (propagator H t)ᴴ := by
  rw [propagator_eq_finiteHamiltonianFlow H hH (-t),
    propagator_eq_finiteHamiltonianFlow H hH t]
  simp only [finiteHamiltonianFlow_op, ← Matrix.exp_conjTranspose]
  congr 1
  simp [hamiltonianGenerator, Matrix.conjTranspose_smul, hH.eq]

noncomputable def heisenberg (H O : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  Duhamel.conjugate (Complex.I • H) O t

theorem heisenberg_eq_conjugate (H O : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    heisenberg H O t = (finiteHamiltonianFlow H hH t).conjugate O := by
  change propagator H t * O * propagator H (-t) = _
  rw [propagator_neg_eq_adjoint H hH, propagator_eq_finiteHamiltonianFlow H hH]
  rfl

@[simp] theorem heisenberg_zero (H O : Matrix ι ι ℂ) : heisenberg H O 0 = O :=
  Duhamel.conjugate_zero _ _

/-- The Heisenberg equation follows from the time derivative of the exponential. -/
theorem heisenberg_derivative (H O : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (heisenberg H O)
      (Complex.I • (H * heisenberg H O t - heisenberg H O t * H)) t := by
  simpa only [heisenberg, smul_mul_assoc, mul_smul_comm, smul_sub] using!
    Duhamel.conjugate_derivative (Complex.I • H) O t

/-- A physical Schrödinger density; the minus sign is part of the construction. -/
noncomputable def state (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (ρ : FiniteDensity ι) (t : ℝ) : FiniteDensity ι :=
  (finiteHamiltonianFlow H hH (-t)).evolveDensity ρ

theorem state_eq_heisenberg (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (ρ : FiniteDensity ι) (t : ℝ) : (state H hH ρ t).rho = heisenberg H ρ.rho (-t) := by
  rw [heisenberg_eq_conjugate H ρ.rho hH]
  rfl

theorem state_derivative (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (ρ : FiniteDensity ι) (t : ℝ) :
    HasDerivAt (fun s => (state H hH ρ s).rho)
      (-Complex.I • (H * (state H hH ρ t).rho - (state H hH ρ t).rho * H)) t := by
  simp only [state_eq_heisenberg]
  simpa only [Function.comp_apply, neg_smul, one_smul] using!
    (heisenberg_derivative H ρ.rho (-t)).scomp t (hasDerivAt_id t).neg

/-- The trace is a continuous real-linear readout on finite matrices. -/
noncomputable def traceMap : Matrix ι ι ℂ →L[ℝ] ℂ :=
  (Matrix.traceLinearMap ι ℝ ℂ).toContinuousLinearMap

@[simp] theorem traceMap_apply (A : Matrix ι ι ℂ) : traceMap A = Matrix.trace A := rfl

theorem hasDerivAt_trace {f : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ} {t : ℝ}
    (hf : HasDerivAt f D t) : HasDerivAt (fun s => Matrix.trace (f s)) (Matrix.trace D) t := by
  convert! (traceMap (ι := ι)).hasFDerivAt.comp_hasDerivAt t hf using 1

noncomputable def expectation (ρ H O : Matrix ι ι ℂ) (t : ℝ) : ℂ :=
  Matrix.trace (ρ * heisenberg H O t)

/-- Schrödinger and Heisenberg pictures give the same physical readout. -/
theorem state_expectation (H O : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (ρ : FiniteDensity ι) (t : ℝ) :
    Matrix.trace ((state H hH ρ t).rho * O) = expectation ρ.rho H O t := by
  rw [state_eq_heisenberg]
  simp only [expectation, heisenberg, Duhamel.conjugate, neg_neg]
  calc
    _ = Matrix.trace (Duhamel.flow (Complex.I • H) (-t) *
        (ρ.rho * (Duhamel.flow (Complex.I • H) t * O))) := by
      congr 1; noncomm_ring
    _ = Matrix.trace ((ρ.rho * (Duhamel.flow (Complex.I • H) t * O)) *
        Duhamel.flow (Complex.I • H) (-t)) := Matrix.trace_mul_comm _ _
    _ = _ := by congr 1; noncomm_ring

theorem expectation_derivative (ρ H O : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (expectation ρ H O)
      (Complex.I * commutatorResponse ρ H (heisenberg H O t)) t := by
  simpa [expectation, commutatorResponse] using!
    hasDerivAt_trace ((heisenberg_derivative H O t).const_mul ρ)

noncomputable def variation (H V O : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  Duhamel.conjugateVariation (Complex.I • H) (Complex.I • V) O t

/-- Vary the Hamiltonian itself, preserving both ordered propagator insertions. -/
theorem heisenberg_perturbation (H V O : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun ε : ℝ => heisenberg (H + ε • V) O t) (variation H V O t) 0 := by
  simpa only [heisenberg, variation, smul_add, smul_comm Complex.I] using!
    Duhamel.hasDerivAt_conjugate_perturbation (Complex.I • H) (Complex.I • V) O t

/-- A parameter-dependent probe contributes its own contact term. -/
theorem expectation_perturbation (ρ H V O O' : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun ε : ℝ => expectation ρ (H + ε • V) (O + ε • O') t)
      (Matrix.trace (ρ * (variation H V O t + heisenberg H O' t))) 0 := by
  have hp := Duhamel.hasDerivAt_perturbation (Complex.I • H) (Complex.I • V) t
  have hn := Duhamel.hasDerivAt_perturbation (Complex.I • H) (Complex.I • V) (-t)
  have hO := (hasDerivAt_const (0 : ℝ) O).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const O')
  have h := hasDerivAt_trace (((hp.fun_mul hO).fun_mul hn).const_mul ρ)
  convert h using 1
  · simp only [expectation, heisenberg, Duhamel.conjugate, smul_add, smul_comm Complex.I,
      Pi.mul_apply, id_eq]
  · simp only [variation, Duhamel.conjugateVariation, heisenberg, Duhamel.conjugate,
      id_eq, zero_smul, add_zero, zero_add, one_smul]
    congr 1
    noncomm_ring

theorem variation_eq_integral (H V O : Matrix ι ι ℂ) (t : ℝ) :
    variation H V O t = ∫ s in (0 : ℝ)..t,
      Complex.I • (heisenberg H V s * heisenberg H O t -
        heisenberg H O t * heisenberg H V s) := by
  rw [variation, Duhamel.conjugateVariation_eq_integral]
  congr 1
  funext s
  simp [heisenberg, Duhamel.conjugate, smul_sub, Matrix.mul_assoc]

/-- The unwindowed kernel for the convention `H + ε V`. Replacing `V` by `-V`
changes the sign. No stationarity assumption reduces its two time arguments. -/
noncomputable def kernel (ρ H V O : Matrix ι ι ℂ) (t s : ℝ) : ℂ :=
  Complex.I * commutatorResponse ρ (heisenberg H V s) (heisenberg H O t)

theorem response_eq_integral (ρ H V O : Matrix ι ι ℂ) (t : ℝ) :
    Matrix.trace (ρ * variation H V O t) = ∫ s in (0 : ℝ)..t, kernel ρ H V O t s := by
  let L := (traceMap (ι := ι)).comp (ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ) ρ)
  have hL (X : Matrix ι ι ℂ) : L X = Matrix.trace (ρ * X) := rfl
  have hc : Continuous (heisenberg H V) :=
    continuous_iff_continuousAt.mpr (fun s => (heisenberg_derivative H V s).continuousAt)
  have hi : Continuous (fun s => Complex.I •
      (heisenberg H V s * heisenberg H O t - heisenberg H O t * heisenberg H V s)) := by
    fun_prop
  have h := L.intervalIntegral_comp_comm (hi.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
  rw [variation_eq_integral]
  simpa only [hL, kernel, commutatorResponse, mul_smul_comm, Matrix.trace_smul,
    smul_eq_mul] using! h.symm

/-- Finite-time Kubo formula as the derivative of the actual perturbed readout. -/
theorem expectation_perturbation_integral (ρ H V O : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun ε : ℝ => expectation ρ (H + ε • V) O t)
      (∫ s in (0 : ℝ)..t, kernel ρ H V O t s) 0 := by
  rw [← response_eq_integral]
  exact hasDerivAt_trace ((heisenberg_perturbation H V O t).const_mul ρ)

/-- A constant perturbation switched on at time zero, from a fixed initial state. -/
noncomputable def stepExpectation (ρ H V O : Matrix ι ι ℂ) (ε t : ℝ) : ℂ :=
  if t ≤ 0 then expectation ρ H O t else expectation ρ (H + ε • V) O t

noncomputable def stepResponse (ρ H V O : Matrix ι ι ℂ) (t : ℝ) : ℂ :=
  if t ≤ 0 then 0 else ∫ s in (0 : ℝ)..t, kernel ρ H V O t s

theorem step_response_derivative (ρ H V O : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun ε => stepExpectation ρ H V O ε t) (stepResponse ρ H V O t) 0 := by
  by_cases ht : t ≤ 0
  · simpa only [stepExpectation, stepResponse, if_pos ht] using
      hasDerivAt_const (0 : ℝ) (expectation ρ H O t)
  · simpa only [stepExpectation, stepResponse, if_neg ht] using
      expectation_perturbation_integral ρ H V O t

theorem step_response_causal (ρ H V O : Matrix ι ι ℂ) (t : ℝ) (ht : t ≤ 0) :
    stepResponse ρ H V O t = 0 := by simp [stepResponse, ht]

end LeanPhy.Quantum.Dynamics
