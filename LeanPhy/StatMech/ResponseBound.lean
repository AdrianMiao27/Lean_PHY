import LeanPhy.StatMech.SourceEnsemble
import LeanPhy.Mathematics.Approximation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

/-!
# Controlled finite source changes

Uniform bounds on a finite observable and the source insertion give a
(non-sharp) uniform covariance bound, hence an explicit bound on the change
of the normalized expectation over a finite source interval. The output is
the existing `ErrorCertificate`, not an assertion that a first derivative
exactly predicts a finite perturbation. No Taylor remainder is discarded.
The source convention remains dimensionless `exp(-S + J·A)`.
-/

namespace LeanPhy.StatMech.FiniteProbability

open scoped BigOperators

variable {ι : Type*} [Fintype ι] (p : FiniteProbability ι)

theorem abs_expectation_le (O : ι → ℝ) (M : ℝ) (hO : ∀ i, |O i| ≤ M) :
    |p.expectation O| ≤ M := by
  calc
    |p.expectation O| ≤ ∑ i, |p.weight i * O i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, p.weight i * |O i| := by simp [abs_mul, abs_of_nonneg (p.nonneg _)]
    _ ≤ ∑ i, p.weight i * M := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hO i) (p.nonneg i))
    _ = M := p.expectation_const M

/-- A robust uniform bound sufficient for finite-parameter error budgets.
It is deliberately not advertised as the sharp covariance bound. -/
theorem abs_covariance_le (O A : ι → ℝ) (M N : ℝ) (hM : 0 ≤ M)
    (hO : ∀ i, |O i| ≤ M) (hA : ∀ i, |A i| ≤ N) :
    |p.covariance O A| ≤ 2 * M * N := by
  have hprod (i : ι) : |O i * A i| ≤ M * N := by
    rw [abs_mul]
    exact mul_le_mul (hO i) (hA i) (abs_nonneg _) hM
  calc
    |p.covariance O A| ≤ |p.expectation (fun i => O i * A i)| +
        |p.expectation O * p.expectation A| := by
      simpa only [covariance, sub_eq_add_neg, abs_neg] using
        (abs_add_le (p.expectation (fun i => O i * A i)) (-(p.expectation O * p.expectation A)))
    _ ≤ M * N + M * N := by
      apply add_le_add (p.abs_expectation_le _ _ hprod)
      rw [abs_mul]
      exact mul_le_mul (p.abs_expectation_le O M hO) (p.abs_expectation_le A N hA)
        (abs_nonneg _) hM
    _ = 2 * M * N := by ring

end LeanPhy.StatMech.FiniteProbability

namespace LeanPhy.StatMech.SourceEnsemble

open LeanPhy.Mathematics

variable {ι σ : Type*} [Fintype ι] [Nonempty ι] [Fintype σ]

/-- All real source values have a normalized state, so the derivative bound
controls every finite segment, not merely a neighborhood of zero. -/
theorem expectation_source_error (S : ι → ℝ) (A : σ → ι → ℝ) (J v : σ → ℝ)
    (O : ι → ℝ) (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hO : ∀ i, |O i| ≤ M) (hA : ∀ i, |directionObservable A v i| ≤ N) (s t : ℝ) :
    ErrorCertificate ((probability S A (sourceLine J v s)).expectation O)
      ((probability S A (sourceLine J v t)).expectation O) (2 * M * N * |s - t|) := by
  have hf (x : ℝ) := hasDerivAt_expectation S A J v O x
  have hd (x : ℝ) : ‖deriv (fun z => (probability S A (sourceLine J v z)).expectation O) x‖
      ≤ 2 * M * N := by
    rw [(hf x).deriv, Real.norm_eq_abs]
    exact (probability S A (sourceLine J v x)).abs_covariance_le O
      (directionObservable A v) M N hM hO hA
  refine ⟨mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM) hN) (abs_nonneg _), ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
    (fun x _ => (hf x).differentiableAt) (fun x _ => hd x)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ t) (Set.mem_univ s)
  simpa [Real.dist_eq, Real.norm_eq_abs] using h

/-- Conjugate observables increase monotonically along their own real source
direction. This follows from a proved variance derivative. -/
theorem conjugate_expectation_monotone (S : ι → ℝ) (A : σ → ι → ℝ) (J v : σ → ℝ) :
    Monotone (fun s => (probability S A (sourceLine J v s)).expectation (directionObservable A v)) := by
  apply monotone_of_deriv_nonneg
  · intro s
    exact (hasDerivAt_expectation S A J v (directionObservable A v) s).differentiableAt
  · intro s
    rw [(hasDerivAt_expectation S A J v (directionObservable A v) s).deriv]
    exact (probability S A (sourceLine J v s)).variance_nonneg _

end LeanPhy.StatMech.SourceEnsemble
