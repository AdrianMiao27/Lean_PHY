import LeanPhy.Mathematics.InfiniteSpectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Tactic

/-!
# Rayleigh and positivity certificates

This module is the first reusable bridge from quadratic-form estimates to
bounded self-adjoint operator bounds.  It deliberately stays on the bounded
side of the Hilbert-space boundary: domains of unbounded operators,
spectral measures and the spectral theorem remain separate obligations.
-/

namespace LeanPhy.Mathematics

open RCLike

universe u v

/-- A checked interval enclosure for the quadratic form of a bounded operator.

The two inequalities are pointwise hypotheses.  They may come from a finite
matrix calculation, an analytic estimate, or a separately certified numerical
bound; the conclusions below use only these fields and the Hilbert-space
inner-product laws checked by Lean.
-/
structure RayleighIntervalCertificate {𝕜 : Type u} {E : Type v}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (A : E →L[𝕜] E) (lower upper : ℝ) : Prop where
  selfAdjoint : IsSelfAdjoint A
  lower_le : ∀ x : E, lower * ‖x‖ ^ 2 ≤ A.reApplyInnerSelf x
  upper_le : ∀ x : E, A.reApplyInnerSelf x ≤ upper * ‖x‖ ^ 2

namespace RayleighIntervalCertificate

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {A : E →L[𝕜] E} {lower upper : ℝ}

/-- Every nonzero vector has a Rayleigh quotient in the certified interval. -/
theorem rayleigh_mem (h : RayleighIntervalCertificate A lower upper)
    {x : E} (hx : x ≠ 0) :
    lower ≤ A.rayleighQuotient x ∧ A.rayleighQuotient x ≤ upper := by
  have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  constructor
  · exact (le_div_iff₀ hn).2 (by simpa [mul_comm] using h.lower_le x)
  · exact (div_le_iff₀ hn).2 (by simpa [mul_comm] using h.upper_le x)

/-- A self-adjoint operator enclosed by `[lower, upper]` has the corresponding
operator-norm bound. -/
theorem norm_le (h : RayleighIntervalCertificate A lower upper) :
    ‖A‖ ≤ max |lower| |upper| := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient A h.selfAdjoint.isSymmetric]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hq := h.rayleigh_mem hx
  let M : ℝ := max |lower| |upper|
  have hneg : -M ≤ lower := by
    exact neg_le_of_abs_le (le_max_left |lower| |upper|)
  have hpos : upper ≤ M := by
    exact (le_abs_self upper).trans (le_max_right |lower| |upper|)
  exact abs_le.2 ⟨hneg.trans hq.1, hq.2.trans hpos⟩

/-- A Rayleigh lower bound by zero gives mathlib's positive-operator predicate. -/
theorem isPositive_of_lower_zero
    (h : RayleighIntervalCertificate A 0 upper) :
    ContinuousLinearMap.IsPositive A :=
  ContinuousLinearMap.isPositive_def'.2 ⟨h.selfAdjoint, by simpa using h.lower_le⟩

end RayleighIntervalCertificate

/-- A reusable certificate for positivity of a bounded operator. -/
structure PositiveOperatorCertificate {𝕜 : Type u} {E : Type v}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (A : E →L[𝕜] E) : Prop where
  selfAdjoint : IsSelfAdjoint A
  quadratic_nonneg : ∀ x : E, 0 ≤ A.reApplyInnerSelf x

namespace PositiveOperatorCertificate

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {A : E →L[𝕜] E}

theorem toIsPositive (h : PositiveOperatorCertificate A) :
    ContinuousLinearMap.IsPositive A :=
  ContinuousLinearMap.isPositive_def'.2 ⟨h.selfAdjoint, h.quadratic_nonneg⟩

/-! The real-spectrum bridge is stated for complex Hilbert spaces because the
mathlib functional-calculus instance supplies the required `Algebra ℝ` and
scalar-tower structures there.  The positivity certificate itself remains
generic over `RCLike`. -/
theorem spectrumRestricts_complex {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {A : E →L[ℂ] E} (h : PositiveOperatorCertificate A) :
    SpectrumRestricts A ContinuousMap.realToNNReal := by
  exact h.toIsPositive.spectrumRestricts

end PositiveOperatorCertificate

end LeanPhy.Mathematics
