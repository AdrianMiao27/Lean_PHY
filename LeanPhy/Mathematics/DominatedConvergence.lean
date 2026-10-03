import LeanPhy.Mathematics.ContinuousAnalysis
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dominated-convergence and normalized-observable certificates

This module exposes the part of a continuum or renormalisation argument that
is legitimately covered by the Bochner dominated-convergence theorem.  The
dominating function, measurability, almost-everywhere bound and pointwise
limit are all fields of a proof record.  In particular, a truncation index
or a regulator cannot be turned into a continuum limit by metadata alone.

The normalized-observable theorem combines two such certificates: one for
the partition-function weights and one for an inserted observable.  The
nonzero limiting partition is an explicit hypothesis.  Existence of a path
measure, reflection positivity and regulator independence remain outside this
module and should be registered as workflow obligations.
-/

namespace LeanPhy.Mathematics

open Filter MeasureTheory
open scoped BigOperators Topology

universe u v w

/-- The hypotheses needed to pass a sequence of Bochner integrals to its
pointwise almost-everywhere limit. -/
structure DominatedConvergenceCertificate {α : Type u} {G : Type v}
    [MeasurableSpace α] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ : Measure α) (F : ℕ → α → G) (f : α → G) (bound : α → ℝ) : Prop where
  measurable : ∀ n, AEStronglyMeasurable (F n) μ
  bound_integrable : Integrable bound μ
  dominated : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a
  pointwise_limit : ∀ᵐ a ∂μ,
    Tendsto (fun n => F n a) atTop (𝓝 (f a))

namespace DominatedConvergenceCertificate

variable {α : Type u} {G : Type v} [MeasurableSpace α]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : Measure α} {F : ℕ → α → G} {f : α → G} {bound : α → ℝ}

/-- The Bochner integrals converge under the recorded domination hypotheses. -/
theorem integral_tendsto (h : DominatedConvergenceCertificate μ F f bound) :
    Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) := by
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    bound h.measurable h.bound_integrable h.dominated h.pointwise_limit

/-- A certificate can be viewed directly as the `LimitCertificate` used by the
rest of the continuous-analysis API. -/
theorem integral_limit_certificate
    (h : DominatedConvergenceCertificate μ F f bound) :
    LimitCertificate atTop (fun n => ∫ a, F n a ∂μ) (∫ a, f a ∂μ) :=
  ⟨h.integral_tendsto⟩

end DominatedConvergenceCertificate

/-- Convergence of a numerator and denominator, with a nonzero limiting
denominator, is sufficient for convergence of their normalized ratio. -/
structure NormalizedRatioCertificate {𝕜 : Type w}
    [NormedField 𝕜] (numerator denominator : ℕ → 𝕜)
    (numeratorLimit denominatorLimit : 𝕜) : Prop where
  numerator_tendsto : Tendsto numerator atTop (𝓝 numeratorLimit)
  denominator_tendsto : Tendsto denominator atTop (𝓝 denominatorLimit)
  denominator_limit_ne_zero : denominatorLimit ≠ 0

namespace NormalizedRatioCertificate

variable {𝕜 : Type w} [NormedField 𝕜]
  {numerator denominator : ℕ → 𝕜}
  {numeratorLimit denominatorLimit : 𝕜}

theorem ratio_tendsto (h : NormalizedRatioCertificate numerator denominator
    numeratorLimit denominatorLimit) :
    Tendsto (fun n => numerator n / denominator n) atTop
      (𝓝 (numeratorLimit / denominatorLimit)) :=
  h.numerator_tendsto.div h.denominator_tendsto h.denominator_limit_ne_zero

end NormalizedRatioCertificate

/-- A path-integral style normalized observable.  `weights` and the inserted
observable both need their own domination proof; domination of the weight by
itself is not enough for an unbounded insertion. -/
structure NormalizedObservableConvergenceCertificate {α : Type u}
    [MeasurableSpace α] (μ : Measure α)
    (weights : ℕ → α → ℂ) (weightLimit : α → ℂ) (observable : α → ℂ)
    (weightBound insertionBound : α → ℝ) : Prop where
  weight_certificate : DominatedConvergenceCertificate μ weights weightLimit weightBound
  insertion_certificate : DominatedConvergenceCertificate μ
    (fun n a => weights n a * observable a)
    (fun a => weightLimit a * observable a) insertionBound
  partition_limit_ne_zero : (∫ a, weightLimit a ∂μ) ≠ 0

namespace NormalizedObservableConvergenceCertificate

variable {α : Type u} [MeasurableSpace α] {μ : Measure α}
  {weights : ℕ → α → ℂ} {weightLimit : α → ℂ} {observable : α → ℂ}
  {weightBound insertionBound : α → ℝ}

/-- The normalized inserted observable converges to the normalized limiting
integral.  This is the checked analytic core of a regulated path-integral
limit; it does not assert that the limiting measure or theory exists. -/
theorem expectation_tendsto
    (h : NormalizedObservableConvergenceCertificate μ weights weightLimit observable
      weightBound insertionBound) :
    Tendsto
      (fun n =>
        (∫ a, weights n a * observable a ∂μ) /
          (∫ a, weights n a ∂μ)) atTop
      (𝓝 ((∫ a, weightLimit a * observable a ∂μ) /
        (∫ a, weightLimit a ∂μ))) := by
  apply NormalizedRatioCertificate.ratio_tendsto
  exact
    { numerator_tendsto := h.insertion_certificate.integral_tendsto
      denominator_tendsto := h.weight_certificate.integral_tendsto
      denominator_limit_ne_zero := h.partition_limit_ne_zero }

end NormalizedObservableConvergenceCertificate

end LeanPhy.Mathematics
