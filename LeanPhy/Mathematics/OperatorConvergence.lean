import LeanPhy.Mathematics.Hilbert
import LeanPhy.Mathematics.ContinuousAnalysis
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Operator-norm and strong-operator convergence certificates

Finite matrices, Galerkin truncations, lattice discretisations and regulated
propagators all produce a sequence of bounded operators.  This file records a
uniform operator-norm error and derives the two consequences that are safe to
reuse in physics proofs: convergence on every state and convergence after any
bounded observable.  No compactness, spectral convergence, or continuum model
existence is inferred from the certificate.
-/

namespace LeanPhy.Mathematics

open Filter
open scoped Topology

universe u v w

structure UniformOperatorApproximationCertificate
    {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (approximants : ℕ → E →L[𝕜] E) (limit : E →L[𝕜] E)
    (radius : ℕ → ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ radius n
  bound : ∀ n, ‖approximants n - limit‖ ≤ radius n
  radius_tendsto_zero : Tendsto radius atTop (𝓝 0)

namespace UniformOperatorApproximationCertificate

variable {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {approximants : ℕ → E →L[𝕜] E} {limit : E →L[𝕜] E}
  {radius : ℕ → ℝ}

private theorem norm_apply_tendsto_zero
    (h : UniformOperatorApproximationCertificate approximants limit radius)
    (x : E) :
    Tendsto (fun n => ‖(approximants n - limit) x‖) atTop (𝓝 0) := by
  have hrad : Tendsto (fun n => radius n * ‖x‖) atTop (𝓝 0) := by
    simpa using h.radius_tendsto_zero.mul_const ‖x‖
  apply squeeze_zero
  · intro n
    exact norm_nonneg _
  · intro n
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (h.bound n) (norm_nonneg x))
  · exact hrad

theorem apply_tendsto
    (h : UniformOperatorApproximationCertificate approximants limit radius)
    (x : E) :
    Tendsto (fun n => approximants n x) atTop (𝓝 (limit x)) := by
  have hdiff : Tendsto (fun n => (approximants n - limit) x) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (h.norm_apply_tendsto_zero x)
  have hadd := hdiff.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => limit x)
    atTop (𝓝 (limit x)))
  simpa [sub_apply] using hadd

theorem apply_limit_certificate
    (h : UniformOperatorApproximationCertificate approximants limit radius)
    (x : E) :
    LimitCertificate atTop (fun n => approximants n x) (limit x) :=
  ⟨h.apply_tendsto x⟩

theorem observable_tendsto
    {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (h : UniformOperatorApproximationCertificate approximants limit radius)
    (observable : E →L[𝕜] F) (x : E) :
    Tendsto (fun n => observable (approximants n x)) atTop
      (𝓝 (observable (limit x))) := by
  exact observable.continuous.continuousAt.tendsto.comp (h.apply_tendsto x)

theorem observable_limit_certificate
    {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (h : UniformOperatorApproximationCertificate approximants limit radius)
    (observable : E →L[𝕜] F) (x : E) :
    LimitCertificate atTop (fun n => observable (approximants n x))
      (observable (limit x)) :=
  ⟨h.observable_tendsto observable x⟩

theorem norm_error_le
    (h : UniformOperatorApproximationCertificate approximants limit radius)
    (n : ℕ) (x : E) :
    ‖approximants n x - limit x‖ ≤ radius n * ‖x‖ := by
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (h.bound n) (norm_nonneg x))

end UniformOperatorApproximationCertificate

/-! Strong convergence is weaker than operator-norm convergence.  It is useful
for unbounded-limit arguments, but must carry its pointwise hypothesis
explicitly because it cannot be recovered from a finite collection of states. -/

structure StrongOperatorConvergenceCertificate
    {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (approximants : ℕ → E →L[𝕜] E) (limit : E →L[𝕜] E) : Prop where
  pointwise : ∀ x : E, Tendsto (fun n => approximants n x) atTop (𝓝 (limit x))

namespace StrongOperatorConvergenceCertificate

variable {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {approximants : ℕ → E →L[𝕜] E} {limit : E →L[𝕜] E}

theorem apply_tendsto
    (h : StrongOperatorConvergenceCertificate approximants limit) (x : E) :
    Tendsto (fun n => approximants n x) atTop (𝓝 (limit x)) :=
  h.pointwise x

theorem observable_tendsto
    {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (h : StrongOperatorConvergenceCertificate approximants limit)
    (observable : E →L[𝕜] F) (x : E) :
    Tendsto (fun n => observable (approximants n x)) atTop
      (𝓝 (observable (limit x))) := by
  exact observable.continuous.continuousAt.tendsto.comp (h.pointwise x)

end StrongOperatorConvergenceCertificate

end LeanPhy.Mathematics
