import LeanPhy.Mathematics.FinitePathApproximation
import Mathlib.Tactic

/-!
# Diagnostics for finite RG fixed-point defects

An exact finite fixed point is rarely what a numerical blocking procedure
produces.  This file turns a pointwise mismatch of coarse and fine weights
into a normalized-expectation error certificate.  The denominator lower
bounds and the observable insertion upper bound remain explicit inputs.

This is a finite error ledger, not a claim about a continuum RG fixed point,
critical exponent, universality class, or convergence of repeated blocking.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

universe u

namespace FinitePathIntegral.FiniteRGStep

variable {ι : Type u} [Fintype ι]

/-- A pointwise defect of an endomorphism RG step.  The radius can vary by
configuration, which lets a numerical adapter retain local error information
instead of replacing it by an untracked global estimate. -/
structure FixedPointDefect (R : FinitePathIntegral.FiniteRGStep ι ι) where
  radius : ι → ℝ
  radius_nonneg : ∀ y, 0 ≤ radius y
  error : ∀ y,
    ErrorCertificate (R.coarseWeight y) (R.fineWeight y) (radius y)

/-- The exact fixed point is represented by a zero-radius defect. -/
def FixedPointDefect.exact
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (hR : FinitePathIntegral.FiniteRGStep.IsFixedPoint R) :
    FixedPointDefect R where
  radius := fun _ => 0
  radius_nonneg := fun _ => le_rfl
  error := fun y => ErrorCertificate.of_eq (hR y)

/-! A blocking calculation is commonly executed in several stages.  The
following constructor composes two finite defect ledgers when the second
stage explicitly identifies its fine weights with the first stage's coarse
weights.  That equality is the audit point: without it, two local error
budgets cannot be soundly added. -/

/-- Compose pointwise fixed-point defects for two consecutive endomorphism RG
steps.  The resulting step uses the composite coarse map and has the summed
radius at every final configuration. -/
def FixedPointDefect.compose
    (R S : FinitePathIntegral.FiniteRGStep ι ι)
    (hmiddle : S.fineWeight = R.coarseWeight)
    (first : FixedPointDefect R) (second : FixedPointDefect S) :
    FixedPointDefect (R.coarsen S.coarse) where
  radius := fun y => first.radius y + second.radius y
  radius_nonneg := fun y => add_nonneg (first.radius_nonneg y)
    (second.radius_nonneg y)
  error := by
    have hcoarse : (R.coarsen S.coarse).coarseWeight = S.coarseWeight := by
      funext y
      calc
        (R.coarsen S.coarse).coarseWeight y =
            pushforwardWeight S.coarse R.coarseWeight y :=
          R.coarsen_weight_eq_pushforward_coarseWeight S.coarse y
        _ = pushforwardWeight S.coarse S.fineWeight y := by
          rw [hmiddle]
        _ = S.coarseWeight y := rfl
    intro y
    have hsecond : ErrorCertificate (S.coarseWeight y)
        (R.coarseWeight y) (second.radius y) := by
      simpa [hmiddle] using second.error y
    have hcombined := hsecond.trans (first.error y)
    change ErrorCertificate ((R.coarsen S.coarse).coarseWeight y)
      (R.fineWeight y) (first.radius y + second.radius y)
    rw [hcoarse]
    simpa [add_comm] using hcombined

theorem FixedPointDefect.partition_error
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (C : FixedPointDefect R) :
    ErrorCertificate
      (∑ y, R.coarseWeight y)
      (∑ y, R.fineWeight y)
      (∑ y, C.radius y) := by
  refine ⟨Finset.sum_nonneg (fun y hy => C.radius_nonneg y), ?_⟩
  rw [dist_eq_norm]
  calc
    ‖(∑ y, R.coarseWeight y) - (∑ y, R.fineWeight y)‖ =
        ‖∑ y, (R.coarseWeight y - R.fineWeight y)‖ := by
      rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ y, ‖R.coarseWeight y - R.fineWeight y‖ := by
      simpa using (norm_sum_le Finset.univ
        (fun y => R.coarseWeight y - R.fineWeight y))
    _ ≤ ∑ y, C.radius y := by
      apply Finset.sum_le_sum
      intro y hy
      simpa [dist_eq_norm] using (C.error y).bound

theorem FixedPointDefect.compose_partition_error
    (R S : FinitePathIntegral.FiniteRGStep ι ι)
    (hmiddle : S.fineWeight = R.coarseWeight)
    (first : FixedPointDefect R) (second : FixedPointDefect S) :
    ErrorCertificate
      (∑ y, (R.coarsen S.coarse).coarseWeight y)
      (∑ y, R.fineWeight y)
      (∑ y, (first.radius y + second.radius y)) := by
  have h := (FixedPointDefect.compose R S hmiddle first second).partition_error
  have hfine : (R.coarsen S.coarse).fineWeight = R.fineWeight := rfl
  have hradius :
      (FixedPointDefect.compose R S hmiddle first second).radius =
        (fun y => first.radius y + second.radius y) := rfl
  rw [hfine, hradius] at h
  have hsum :
      (∑ y, (fun y => first.radius y + second.radius y) y) =
        (∑ y, (first.radius y + second.radius y)) := by
    apply Finset.sum_congr rfl
    intro y hy
    rfl
  rw [hsum] at h
  exact h

/-!
The constructor below asks for both denominator bounds explicitly.  Even
though an exact finite push-forward has equal partition sums, retaining both
arguments makes an approximate numerical replacement auditable and prevents a
normalization estimate from silently using an unavailable lower bound.
-/
noncomputable def FixedPointDefect.toApproximation
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (C : FixedPointDefect R) (O : ι → ℂ)
    (coarseLower fineLower : ℝ)
    (hcoarse_pos : 0 < coarseLower)
    (hfine_pos : 0 < fineLower)
    (hcoarse_lower : coarseLower ≤
      ‖(R.coarsePathIntegral h).partition‖)
    (hfine_lower : fineLower ≤
      ‖(R.finePathIntegral h).partition‖)
    (insertionUpper : ℝ) (hinsertionUpper_nonneg : 0 ≤ insertionUpper)
    (hinsertion_upper :
      ‖(R.finePathIntegral h).insertion O‖ ≤ insertionUpper) :
    FinitePathIntegral.ApproximationCertificate
      (R.coarsePathIntegral h) (R.finePathIntegral h) O := by
  exact R.coarse_approximation_certificate h (R.finePathIntegral h) O
    C.radius C.radius_nonneg C.error
    coarseLower fineLower hcoarse_pos hfine_pos hcoarse_lower hfine_lower
    insertionUpper hinsertionUpper_nonneg hinsertion_upper

theorem FixedPointDefect.expectation_error
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (C : FixedPointDefect R) (O : ι → ℂ)
    (coarseLower fineLower : ℝ)
    (hcoarse_pos : 0 < coarseLower)
    (hfine_pos : 0 < fineLower)
    (hcoarse_lower : coarseLower ≤
      ‖(R.coarsePathIntegral h).partition‖)
    (hfine_lower : fineLower ≤
      ‖(R.finePathIntegral h).partition‖)
    (insertionUpper : ℝ) (hinsertionUpper_nonneg : 0 ≤ insertionUpper)
    (hinsertion_upper :
      ‖(R.finePathIntegral h).insertion O‖ ≤ insertionUpper) :
    ErrorCertificate
      ((R.coarsePathIntegral h).expectation O)
      ((R.finePathIntegral h).expectation O)
      ((FixedPointDefect.toApproximation R h C O coarseLower fineLower hcoarse_pos hfine_pos
        hcoarse_lower hfine_lower insertionUpper hinsertionUpper_nonneg
        hinsertion_upper).insertionRadius /
        (FixedPointDefect.toApproximation R h C O coarseLower fineLower hcoarse_pos hfine_pos
          hcoarse_lower hfine_lower insertionUpper hinsertionUpper_nonneg
          hinsertion_upper).exactLower +
        (FixedPointDefect.toApproximation R h C O coarseLower fineLower hcoarse_pos hfine_pos
          hcoarse_lower hfine_lower insertionUpper hinsertionUpper_nonneg
          hinsertion_upper).insertionUpper *
          (FixedPointDefect.toApproximation R h C O coarseLower fineLower hcoarse_pos hfine_pos
            hcoarse_lower hfine_lower insertionUpper hinsertionUpper_nonneg
            hinsertion_upper).partitionRadius /
          ((FixedPointDefect.toApproximation R h C O coarseLower fineLower hcoarse_pos hfine_pos
            hcoarse_lower hfine_lower insertionUpper hinsertionUpper_nonneg
            hinsertion_upper).exactLower *
            (FixedPointDefect.toApproximation R h C O coarseLower fineLower hcoarse_pos hfine_pos
              hcoarse_lower hfine_lower insertionUpper hinsertionUpper_nonneg
              hinsertion_upper).approximateLower) ) := by
  exact (FixedPointDefect.toApproximation R h C O coarseLower fineLower hcoarse_pos hfine_pos
    hcoarse_lower hfine_lower insertionUpper hinsertionUpper_nonneg
    hinsertion_upper).expectation_error

/-- A named normalized expectation certificate is easier for downstream RG
chains to compose than the expanded rational error expression. -/
noncomputable def FixedPointDefect.toExpectationComparison
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (C : FixedPointDefect R) (O : ι → ℂ)
    (coarseLower fineLower : ℝ)
    (hcoarse_pos : 0 < coarseLower)
    (hfine_pos : 0 < fineLower)
    (hcoarse_lower : coarseLower ≤
      ‖(R.coarsePathIntegral h).partition‖)
    (hfine_lower : fineLower ≤
      ‖(R.finePathIntegral h).partition‖)
    (insertionUpper : ℝ) (hinsertionUpper_nonneg : 0 ≤ insertionUpper)
    (hinsertion_upper :
      ‖(R.finePathIntegral h).insertion O‖ ≤ insertionUpper) :
    NormalizedExpectationCertificate
      (R.coarsePathIntegral h) (R.finePathIntegral h) O :=
  NormalizedExpectationCertificate.ofApproximation
    (FixedPointDefect.toApproximation R h C O coarseLower fineLower hcoarse_pos hfine_pos
      hcoarse_lower hfine_lower insertionUpper hinsertionUpper_nonneg
      hinsertion_upper)

end FinitePathIntegral.FiniteRGStep

end LeanPhy.Mathematics
