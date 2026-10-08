import LeanPhy.StatMech.FeedbackCertificate
import LeanPhy.Examples.Generated.BiasedFeedbackCertificate
import LeanPhy.StatMech.MeanFieldFunctional
import LeanPhy.Workflow.Core

set_option autoImplicit false

/-!
# Finite-cluster self-consistency as a research client

The configuration count, internal energy, bias and inter-order-parameter coupling
are inputs. This constructs a finite closure, not an exact solution of the
original interacting thermodynamic model. A small two-state regression then
checks a nonzero residual/readout budget and the retained beta factor.
-/

namespace LeanPhy.Examples.SelfConsistencyResearch

open LeanPhy.StatMech LeanPhy.Mathematics LeanPhy.Workflow SourceFeedback
open scoped BigOperators NNReal Topology

abbrev Configuration (n : ℕ) := Fin n → Bool

def spin {n : ℕ} (a : Fin n) (q : Configuration n) : ℝ := if q a then 1 else -1

theorem spin_abs {n : ℕ} (a : Fin n) (q : Configuration n) : |spin a q| = 1 := by
  simp only [spin]
  split <;> norm_num

/-- An explicit bound from the physical beta-scaled coupling table. Internal
cluster energy and applied bias remain arbitrary. This bound is conservative. -/
noncomputable def clusterEnvelope (n : ℕ) (β : ℝ) (K : Fin n → Fin n → ℝ) :
    Envelope (@spin n) (fun a b => β * K a b) where
  amplitude := 1
  coupling := ∑ b, ∑ a, ‖β * K a b‖₊
  observable_le := by intro a q; simp [spin_abs]
  insertion_le := by
    intro q
    simp only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs, insertion]
    apply Finset.sum_le_sum
    intro b _
    calc
      |∑ a, β * K a b * spin a q| ≤ ∑ a, |β * K a b * spin a q| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a, |β * K a b| := by simp only [abs_mul, spin_abs, mul_one]

/-- The actual finite ensemble uses energy couplings, including beta in both
bias and feedback. No temperature factor is inferred from a string convention. -/
theorem cluster_energy_convention (n : ℕ) (E : Configuration n → ℝ)
    (h : Fin n → ℝ) (K : Fin n → Fin n → ℝ) (β : ℝ) (m : Fin n → ℝ) :
    SourceEnsemble.probability (fun q => β * E q) spin
      (source (fun a => β * h a) (fun a b => β * K a b) m) =
      finiteGibbsProbability β (fun q => E q - ∑ a, source h K m a * spin a q) :=
  probability_energy E spin h K β m

theorem cluster_iteration (n : ℕ) (E : Configuration n → ℝ)
    (h : Fin n → ℝ) (K : Fin n → Fin n → ℝ) (β : ℝ)
    (hsmall : (clusterEnvelope n β K).rate < 1) (m : Fin n → ℝ) :
    Filter.Tendsto (fun k =>
      (feedback (fun q => β * E q) spin (fun a => β * h a) (fun a b => β * K a b))^[k] m)
      Filter.atTop (𝓝 ((clusterEnvelope n β K).solution (fun q => β * E q)
        (fun a => β * h a) hsmall)) :=
  (clusterEnvelope n β K).iterate_converges _ _ hsmall m

theorem cluster_stationarity (n : ℕ) (E : Configuration n → ℝ)
    (h : Fin n → ℝ) (K : Fin n → Fin n → ℝ) (hK : ∀ a b, K a b = K b a)
    (β : ℝ) (m v : Fin n → ℝ)
    (hm : feedback (fun q => β * E q) spin (fun a => β * h a)
      (fun a b => β * K a b) m = m) :
    HasDerivAt (fun s => stationaryFunctional (fun q => β * E q) spin
      (fun a => β * h a) (fun a b => β * K a b) (SourceEnsemble.sourceLine m v s)) 0 0 :=
  stationary_of_selfconsistent _ _ _ _ (by intro a b; rw [hK a b]) m v hm

def binarySpin (i : Fin 2) : ℝ := if i = 0 then 1 else -1

theorem binary_bound (i : Fin 2) : |binarySpin i| ≤ 1 := by
  fin_cases i <;> norm_num [binarySpin]

noncomputable def binaryEnvelope (κ : ℝ) :
    Envelope (fun _ : Unit => binarySpin) (fun _ _ => κ) where
  amplitude := 1
  coupling := ‖κ‖₊
  observable_le := fun _ => binary_bound
  insertion_le := by
    intro i
    fin_cases i <;> simp [insertion, binarySpin, Real.norm_eq_abs]

theorem binary_rate (κ : ℝ) : (binaryEnvelope κ).rate = 2 * |κ| := by
  simp [Envelope.rate, binaryEnvelope, Real.norm_eq_abs]

theorem automatic_binary_rate (κ : ℝ) :
    (Envelope.automatic (fun _ : Unit => binarySpin) (fun _ _ => κ)).rate = 2 * |κ| := by
  simp [Envelope.rate, Envelope.automatic, insertion, Finset.univ_fin2, binarySpin,
    Real.norm_eq_abs]

theorem binary_zero_fixed (κ : ℝ) :
    feedback (fun _ : Fin 2 => 0) (fun _ : Unit => binarySpin)
      (fun _ => 0) (fun _ _ => κ) (fun _ => 0) = fun _ => 0 := by
  funext a
  norm_num [feedback, source, SourceEnsemble.probability, SourceEnsemble.action,
    finiteGibbsProbability, finiteGibbsWeight, finitePartitionFunction,
    FiniteProbability.expectation, Fin.sum_univ_two, binarySpin]

/-- The linearization at the symmetric state retains beta times the coupling. -/
theorem binary_temperature_derivative (β κ : ℝ) :
    HasDerivAt (fun t => feedback (fun _ : Fin 2 => 0) (fun _ : Unit => binarySpin)
      (fun _ => 0) (fun _ _ => β * κ) (fun _ => t) ()) (β * κ) 0 := by
  have hd := feedback_derivative (fun _ : Fin 2 => 0) (fun _ : Unit => binarySpin)
    (fun _ => 0) (fun _ _ => β * κ) (fun _ => 0) (fun _ => 1) ()
  norm_num [feedback, source, SourceEnsemble.sourceLine, SourceEnsemble.probability,
    SourceEnsemble.action, SourceEnsemble.directionObservable, finiteGibbsProbability,
    finiteGibbsWeight, finitePartitionFunction, FiniteProbability.covariance,
    FiniteProbability.expectation, Fin.sum_univ_two, binarySpin] at hd ⊢
  convert! hd using 1; ring

/-- No contraction or uniqueness claim is valid merely because the symmetric
state is a fixed point. Here the certified global rate is already above one. -/
theorem strong_coupling_rejected : ¬ (binaryEnvelope 1).rate < 1 := by
  rw [binary_rate]
  norm_num

theorem biased_update (κ : ℝ) :
    feedback (fun _ : Fin 2 => 0) (fun _ : Unit => binarySpin)
      (fun _ => Real.log 2) (fun _ _ => κ) (fun _ => 0) = fun _ => 3 / 5 := by
  funext a
  norm_num [feedback, source, SourceEnsemble.probability, SourceEnsemble.action,
    finiteGibbsProbability, finiteGibbsWeight, finitePartitionFunction,
    FiniteProbability.expectation, Fin.sum_univ_two, binarySpin,
    Real.exp_neg, Real.exp_log (by norm_num : (2 : ℝ) > 0)]

theorem weak_coupling : (binaryEnvelope (1 / 8)).rate < 1 := by
  rw [binary_rate]
  norm_num

theorem biased_residual : ErrorCertificate (fun _ : Unit => (0 : ℝ))
    (feedback (fun _ : Fin 2 => 0) (fun _ : Unit => binarySpin)
      (fun _ => Real.log 2) (fun _ _ => 1 / 8) (fun _ => 0)) (3 / 5) := by
  rw [biased_update]
  refine ⟨by norm_num, (dist_pi_le_iff (by norm_num)).mpr ?_⟩
  intro a
  norm_num [Real.dist_eq]

theorem biased_solution_error :
    ErrorCertificate (fun _ : Unit => (0 : ℝ))
      ((binaryEnvelope (1 / 8)).solution (fun _ => 0) (fun _ => Real.log 2) weak_coupling)
      (4 / 5) := by
  have he := (binaryEnvelope (1 / 8)).solution_error (fun _ => 0)
    (fun _ => Real.log 2) weak_coupling (fun _ => 0) (3 / 5) biased_residual
  norm_num [binary_rate] at he ⊢
  exact he

theorem biased_readout_error :
    ErrorCertificate (3 / 5 : ℝ)
      ((SourceEnsemble.probability (fun _ : Fin 2 => 0) (fun _ : Unit => binarySpin)
        (source (fun _ => Real.log 2) (fun _ _ => 1 / 8)
          ((binaryEnvelope (1 / 8)).solution (fun _ => 0)
            (fun _ => Real.log 2) weak_coupling))).expectation binarySpin) (1 / 5) := by
  have he := (binaryEnvelope (1 / 8)).observable_error (fun _ => 0)
    (fun _ => Real.log 2) weak_coupling (fun _ => 0) (3 / 5) biased_residual
      binarySpin 1 binary_bound
  have hr := congrFun (biased_update (1 / 8)) ()
  change (SourceEnsemble.probability (fun _ : Fin 2 => 0) (fun _ : Unit => binarySpin)
    (source (fun _ => Real.log 2) (fun _ _ => 1 / 8) (fun _ => 0))).expectation binarySpin = 3 / 5 at hr
  rw [hr] at he
  norm_num [Envelope.rate, binaryEnvelope, Real.norm_eq_abs] at he ⊢
  exact he

/-- With singular (zero) coupling every m is stationary, including a vector
that is not self-consistent. A stationary-functional converse needs more input. -/
theorem stationary_not_selfconsistent :
    (∀ v : Unit → ℝ, HasDerivAt (fun s => stationaryFunctional (fun _ : Fin 2 => 0)
      (fun _ : Unit => binarySpin) (fun _ => 0) (fun _ _ => 0)
      (SourceEnsemble.sourceLine (fun _ => 1) v s)) 0 0) ∧
    feedback (fun _ : Fin 2 => 0) (fun _ : Unit => binarySpin)
      (fun _ => 0) (fun _ _ => 0) (fun _ => 1) ≠ (fun _ => 1) := by
  constructor
  · intro v
    simpa using functional_derivative (fun _ : Fin 2 => 0) (fun _ : Unit => binarySpin)
      (fun _ => 0) (fun _ _ => 0) (fun _ _ => rfl) (fun _ => 1) v
  · intro he
    have hz : feedback (fun _ : Fin 2 => 0) (fun _ : Unit => binarySpin)
        (fun _ => 0) (fun _ _ => 0) (fun _ => 1) = fun _ => 0 := by
      funext a
      norm_num [SourceFeedback.feedback, SourceFeedback.source, SourceEnsemble.probability,
        SourceEnsemble.action, finiteGibbsProbability, finiteGibbsWeight,
        finitePartitionFunction, FiniteProbability.expectation, Fin.sum_univ_two, binarySpin]
    have hc := congrFun (hz.symm.trans he) ()
    norm_num at hc

namespace Numerical

open LeanPhy.Generated.GibbsCertificates.BiasedFeedback

/-- A real exponential source, with a decimal candidate from an external solver.
The generator checks its actual residual; this is not a logarithmic exact-value trick. -/
noncomputable def envelope := Envelope.automatic
  (fun a i => (observables a i : ℝ)) (fun a b => (coupling a b : ℝ))

theorem rate : envelope.rate = 1 / 4 := by
  norm_num [envelope, Envelope.automatic, Envelope.rate, insertion, observables, coupling,
    Finset.univ_fin2, Real.norm_eq_abs]

theorem small : envelope.rate < 1 := by rw [rate]; norm_num

theorem solution_error : ErrorCertificate (fun a => (point a : ℝ))
    (envelope.solution (fun i => (action i : ℝ)) (fun a => (bias a : ℝ)) small)
    (1 / 75000) := by
  have h := solution_bound envelope small
  norm_num only [error, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, rate] at h
  exact h

def readout : Fin 2 → ℚ := ![-1/2, 3/2]

def readoutCandidate : GibbsCertificate.Candidate :=
  ⟨0, 0, 10, 138587 / 1000000, 1 / 100000⟩

set_option maxRecDepth 16384 in
theorem readout_accepted : readoutCandidate.Accepted
    (GibbsCertificate.exponent action observables
      (GibbsCertificate.feedbackSource bias coupling point)) readout := by decide +kernel

theorem readout_error : ErrorCertificate (readoutCandidate.value : ℝ)
    ((SourceEnsemble.probability (fun i => (action i : ℝ)) (fun a i => (observables a i : ℝ))
      (source (fun a => (bias a : ℝ)) (fun a b => (coupling a b : ℝ))
        (envelope.solution (fun i => (action i : ℝ)) (fun a => (bias a : ℝ)) small))).expectation
          (fun i => (readout i : ℝ))) (3 / 200000) := by
  have hO : ∀ i, |(readout i : ℝ)| ≤ (3 / 2 : ℝ≥0) := by
    intro i
    fin_cases i <;> norm_num [readout]
  have h := GibbsCertificate.solution_readout_error action observables bias coupling point
    candidates error error_nonneg values_match errors_fit accepted envelope small readout
    (3 / 2) hO readoutCandidate readout_accepted
  norm_num [readoutCandidate, error, envelope, Envelope.automatic, Envelope.rate,
    insertion, observables, coupling, Finset.univ_fin2, Real.norm_eq_abs] at h ⊢
  exact h

end Numerical

def package : TheoryPackage :=
  TheoryPackage.empty "finite-source self-consistency" "condensed matter and statistical field theory"
    |>.addTheorem "energy source convention" "finite clusters retain beta in bias and feedback coupling"
      "cluster_energy_convention" cluster_energy_convention
    |>.addTheorem "cluster iteration" "input coupling bounds imply convergence of the actual Gibbs closure"
      "cluster_iteration" cluster_iteration
    |>.addTheorem "cluster stationarity" "symmetric energy couplings give directional stationarity"
      "cluster_stationarity" cluster_stationarity
    |>.addTheorem "automatic finite envelope" "finite maxima supply a checked conservative rate"
      "automatic_binary_rate" automatic_binary_rate
    |>.addTheorem "temperature in linearization" "the actual derivative is beta times the coupling"
      "binary_temperature_derivative" binary_temperature_derivative
    |>.addTheorem "nonzero solution error" "the biased interacting closure retains its residual budget"
      "biased_solution_error" biased_solution_error
    |>.addTheorem "actual readout error" "an actual spin expectation gets a residual-derived budget"
      "biased_readout_error" biased_readout_error
    |>.addTheorem "stationarity counterexample" "singular coupling does not allow the stationary converse"
      "stationary_not_selfconsistent" stationary_not_selfconsistent
    |>.addTheorem "certified numerical residual" "kernel-checked rational enclosures bound the actual Gibbs update"
      "LeanPhy.Generated.GibbsCertificates.BiasedFeedback.valid"
      LeanPhy.Generated.GibbsCertificates.BiasedFeedback.valid
    |>.addTheorem "certified numerical solution" "a rounded external point has a bound to the actual unique solution"
      "Numerical.solution_error" Numerical.solution_error
    |>.addTheorem "certified numerical readout" "readout evaluation and residual errors both reach the actual solution"
      "Numerical.readout_error" Numerical.readout_error
    |>.addObligationText "closure error and thermodynamic limit" "compare this defined closure with the original interacting model"
      "prove model-dependent approximation and volume bounds"
    |>.addObligationText "critical and multiple branches" "the conservative global contraction domain excludes critical analysis"
      "derive local domains and track solution branches"
    |>.addObligationText "scalable numerical solvers and input uncertainty" "exact rational finite sums do not certify a general solver or uncertain real inputs"
      "extend input enclosures, certify local solvers and measure larger-system cost"
    |>.addObligationText "noncommuting quantum self-consistency" "finite real source observables do not implement operator-valued closures"
      "connect actual quantum thermal response and quantum closure conditions"

end LeanPhy.Examples.SelfConsistencyResearch
