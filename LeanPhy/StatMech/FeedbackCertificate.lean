import LeanPhy.StatMech.SourceFeedback

set_option autoImplicit false

/-!
# Finite-data certificates for self-consistent sources

An envelope contains bounds on finite input tables, not a Lipschitz or fixed-point
assumption. `automatic` constructs it using finite maxima. Smallness of the
resulting rate certifies a unique actual solution, iteration convergence, and
error propagation from a separately certified approximate update or readout.
Real maxima are exact mathematical operations; no floating-point interval
algorithm is hidden in this construction.
-/

namespace LeanPhy.StatMech.SourceFeedback

open LeanPhy.Mathematics
open scoped BigOperators Topology NNReal

variable {ι σ : Type*} [Fintype ι] [Nonempty ι] [Fintype σ]

/-- Finite observable and coupling-insertion bounds, before any ensemble or bias
is chosen. They can therefore be reused throughout a bias scan. -/
structure Envelope (A : σ → ι → ℝ) (K : σ → σ → ℝ) where
  amplitude : ℝ≥0
  coupling : ℝ≥0
  observable_le : ∀ a i, |A a i| ≤ amplitude
  insertion_le : ∀ i, ∑ b, |insertion A K i b| ≤ coupling

namespace Envelope

variable {A : σ → ι → ℝ} {K : σ → σ → ℝ}

/-- A finite maximum, including the empty order-parameter type. -/
noncomputable def automatic (A : σ → ι → ℝ) (K : σ → σ → ℝ) : Envelope A K where
  amplitude := Finset.univ.sup fun a => Finset.univ.sup fun i => ‖A a i‖₊
  coupling := Finset.univ.sup fun i => ∑ b, ‖insertion A K i b‖₊
  observable_le := by
    intro a i
    have h := (Finset.le_sup (f := fun i => ‖A a i‖₊) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun a => Finset.univ.sup fun i => ‖A a i‖₊) (Finset.mem_univ a))
    simpa only [coe_nnnorm, Real.norm_eq_abs] using (NNReal.coe_le_coe.mpr h)
  insertion_le := by
    intro i
    have h := Finset.le_sup (f := fun i => ∑ b, ‖insertion A K i b‖₊) (Finset.mem_univ i)
    simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using (NNReal.coe_le_coe.mpr h)

/-- Conservative global rate derived from the finite input bounds. -/
noncomputable def rate (e : Envelope A K) : ℝ := 2 * e.amplitude * e.coupling

omit [Fintype ι] [Nonempty ι] in
theorem rate_nonneg (e : Envelope A K) : 0 ≤ e.rate := by
  unfold rate
  positivity

theorem certificate (e : Envelope A K) (S : ι → ℝ) (J : σ → ℝ) (h : e.rate < 1) :
    ContractionCertificate (feedback S A J K) ⟨e.rate, e.rate_nonneg⟩ :=
  contraction S A J K e.amplitude e.coupling e.amplitude.coe_nonneg e.coupling.coe_nonneg
    e.observable_le e.insertion_le h

noncomputable def solution (e : Envelope A K) (S : ι → ℝ) (J : σ → ℝ) (h : e.rate < 1) :
    σ → ℝ := (e.certificate S J h).fixedPoint

theorem solution_isFixedPt (e : Envelope A K) (S : ι → ℝ) (J : σ → ℝ) (h : e.rate < 1) :
    feedback S A J K (e.solution S J h) = e.solution S J h :=
  (e.certificate S J h).fixedPoint_isFixedPt

theorem solution_unique (e : Envelope A K) (S : ι → ℝ) (J : σ → ℝ) (h : e.rate < 1)
    (m : σ → ℝ) (hm : feedback S A J K m = m) : m = e.solution S J h :=
  (e.certificate S J h).fixedPoint_unique hm

theorem solution_bounded (e : Envelope A K) (S : ι → ℝ) (J : σ → ℝ) (h : e.rate < 1)
    (a : σ) : |e.solution S J h a| ≤ e.amplitude := by
  rw [← e.solution_isFixedPt S J h]
  exact feedback_bounded S A J K e.amplitude e.observable_le _ a

theorem iterate_converges (e : Envelope A K) (S : ι → ℝ) (J : σ → ℝ) (h : e.rate < 1)
    (m : σ → ℝ) :
    Filter.Tendsto (fun n => (feedback S A J K)^[n] m) Filter.atTop (𝓝 (e.solution S J h)) :=
  (e.certificate S J h).iterate_tendsto_fixedPoint m

theorem solution_error (e : Envelope A K) (S : ι → ℝ) (J : σ → ℝ) (h : e.rate < 1)
    (m : σ → ℝ) (ε : ℝ) (hr : ErrorCertificate m (feedback S A J K m) ε) :
    ErrorCertificate m (e.solution S J h) (ε / (1 - e.rate)) :=
  fixedPoint_error S A J K e.amplitude e.coupling e.amplitude.coe_nonneg e.coupling.coe_nonneg
    e.observable_le e.insertion_le h m ε hr

/-- An approximate update needs a bound to the actual Gibbs update. The observed
step size by itself is not a certificate of the true residual. -/
theorem solution_error_of_update (e : Envelope A K) (S : ι → ℝ) (J : σ → ℝ)
    (h : e.rate < 1) (m y : σ → ℝ) (δ : ℝ)
    (hy : ErrorCertificate y (feedback S A J K m) δ) :
    ErrorCertificate m (e.solution S J h) ((dist m y + δ) / (1 - e.rate)) :=
  e.solution_error S J h m _ ((show ErrorCertificate m y (dist m y) from
    ⟨dist_nonneg, le_rfl⟩).trans hy)

theorem observable_error (e : Envelope A K) (S : ι → ℝ) (J : σ → ℝ) (h : e.rate < 1)
    (m : σ → ℝ) (ε : ℝ) (hr : ErrorCertificate m (feedback S A J K m) ε)
    (O : ι → ℝ) (N : ℝ≥0) (hO : ∀ i, |O i| ≤ N) :
    ErrorCertificate ((SourceEnsemble.probability S A (source J K m)).expectation O)
      ((SourceEnsemble.probability S A (source J K (e.solution S J h))).expectation O)
      ((2 * N * e.coupling) * (ε / (1 - e.rate))) :=
  readout_error S A J K e.amplitude e.coupling e.amplitude.coe_nonneg e.coupling.coe_nonneg
    e.observable_le e.insertion_le h m ε hr O N N.coe_nonneg hO

/-- Separate evaluation error from the error of the self-consistent order
parameters. Both refer to the same observable and model. -/
theorem evaluated_observable_error (e : Envelope A K) (S : ι → ℝ) (J : σ → ℝ)
    (h : e.rate < 1) (m : σ → ℝ) (ε : ℝ)
    (hr : ErrorCertificate m (feedback S A J K m) ε)
    (O : ι → ℝ) (N : ℝ≥0) (hO : ∀ i, |O i| ≤ N) (value η : ℝ)
    (hv : ErrorCertificate value
      ((SourceEnsemble.probability S A (source J K m)).expectation O) η) :
    ErrorCertificate value
      ((SourceEnsemble.probability S A (source J K (e.solution S J h))).expectation O)
      (η + (2 * N * e.coupling) * (ε / (1 - e.rate))) :=
  hv.trans (e.observable_error S J h m ε hr O N hO)

end Envelope
end LeanPhy.StatMech.SourceFeedback
