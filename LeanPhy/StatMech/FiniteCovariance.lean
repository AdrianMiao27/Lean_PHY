import LeanPhy.StatMech.FiniteProbability
import LeanPhy.Mathematics.FiniteWeightedResponse
import LeanPhy.Mathematics.FiniteCorrelator

set_option autoImplicit false

/-!
# Connected fluctuations of a finite probability state

The same finite probability state used by Gibbs and Markov models now supplies
covariances, centered fluctuations and positive semidefinite source-response
matrices. Positivity is proved from nonnegative probability weights; it is not
asserted for complex/oscillatory path weights. The explicit complex path-sum
adapter identifies these covariances with the existing connected correlator.
-/

namespace LeanPhy.StatMech.FiniteProbability

open scoped BigOperators
open LeanPhy.Mathematics

variable {ι : Type*} [Fintype ι] (p : FiniteProbability ι)

/-- Connected correlation of real observables in the actual state `p`. -/
def covariance (O A : ι → ℝ) : ℝ :=
  p.expectation (fun i => O i * A i) - p.expectation O * p.expectation A

def variance (O : ι → ℝ) : ℝ := p.covariance O O

theorem expectation_eq_weighted (O : ι → ℝ) :
    p.expectation O = FiniteWeighted.expectation p.weight O := by
  simp [FiniteWeighted.expectation, FiniteWeighted.partition,
    FiniteWeighted.insertion, p.normalised, expectation]

theorem covariance_eq_connected (O A : ι → ℝ) :
    p.covariance O A = FiniteWeighted.connected p.weight O A := by
  simp only [covariance, FiniteWeighted.connected, ← p.expectation_eq_weighted]

theorem covariance_symm (O A : ι → ℝ) : p.covariance O A = p.covariance A O := by
  unfold covariance expectation
  simp_rw [mul_comm (O _) (A _)]
  ring

theorem expectation_sub (O A : ι → ℝ) :
    p.expectation (O - A) = p.expectation O - p.expectation A := by
  simp [expectation, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem expectation_sum {σ : Type*} [Fintype σ] (A : σ → ι → ℝ) :
    p.expectation (fun i => ∑ a, A a i) = ∑ a, p.expectation (A a) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

/-- Centering uses the normalization proof, not a formal cancellation label. -/
theorem covariance_eq_centered (O A : ι → ℝ) :
    p.covariance O A =
      p.expectation (fun i => (O i - p.expectation O) * (A i - p.expectation A)) := by
  have h : (fun i => (O i - p.expectation O) * (A i - p.expectation A)) =
      ((fun i => O i * A i) - p.expectation A • O - p.expectation O • A +
        (fun _ => p.expectation O * p.expectation A)) := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, p.expectation_add, p.expectation_sub, p.expectation_sub,
    p.expectation_smul, p.expectation_smul, p.expectation_const]
  unfold covariance
  ring

theorem variance_nonneg (O : ι → ℝ) : 0 ≤ p.variance O := by
  rw [variance, p.covariance_eq_centered]
  apply p.expectation_nonneg
  intro i
  exact mul_self_nonneg _

theorem covariance_add_left (O Q A : ι → ℝ) :
    p.covariance (O + Q) A = p.covariance O A + p.covariance Q A := by
  unfold covariance expectation
  simp [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem covariance_smul_left (c : ℝ) (O A : ι → ℝ) :
    p.covariance (c • O) A = c * p.covariance O A := by
  unfold covariance
  have h : (fun i => (c • O) i * A i) = c • (fun i => O i * A i) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [h, p.expectation_smul, p.expectation_smul]
  ring

theorem covariance_smul_right (c : ℝ) (O A : ι → ℝ) :
    p.covariance O (c • A) = c * p.covariance O A := by
  rw [p.covariance_symm O (c • A), p.covariance_smul_left, p.covariance_symm A O]

@[simp] theorem covariance_const_left (c : ℝ) (A : ι → ℝ) :
    p.covariance (fun _ => c) A = 0 := by
  unfold covariance
  rw [p.expectation_const]
  have h := p.expectation_smul c A
  change p.expectation (c • A) - c * p.expectation A = 0
  rw [h, sub_self]

theorem covariance_sum_left {σ : Type*} [Fintype σ] (A : σ → ι → ℝ) (O : ι → ℝ) :
    p.covariance (fun i => ∑ a, A a i) O = ∑ a, p.covariance (A a) O := by
  unfold covariance
  have h : (fun i => (∑ a, A a i) * O i) =
      (fun i => ∑ a, A a i * O i) := by
    funext i
    exact Finset.sum_mul _ _ _
  rw [h, p.expectation_sum, p.expectation_sum, Finset.sum_mul, Finset.sum_sub_distrib]

/-- The quadratic form of the covariance matrix is a variance in this state. -/
theorem covariance_quadratic_eq_variance {σ : Type*} [Fintype σ]
    (A : σ → ι → ℝ) (v : σ → ℝ) :
    (∑ a, ∑ b, v a * p.covariance (A a) (A b) * v b) =
      p.variance (fun i => ∑ a, v a * A a i) := by
  unfold variance
  rw [p.covariance_sum_left]
  apply Eq.symm
  apply Finset.sum_congr rfl
  intro a _
  rw [p.covariance_symm, p.covariance_sum_left]
  apply Finset.sum_congr rfl
  intro b _
  change p.covariance (v b • A b) (v a • A a) = _
  rw [p.covariance_smul_left, p.covariance_symm, p.covariance_smul_left]
  ring

theorem covariance_quadratic_nonneg {σ : Type*} [Fintype σ]
    (A : σ → ι → ℝ) (v : σ → ℝ) :
    0 ≤ ∑ a, ∑ b, v a * p.covariance (A a) (A b) * v b := by
  rw [p.covariance_quadratic_eq_variance]
  exact p.variance_nonneg _

/-- Embed the same normalized state into finite complex path sums. -/
noncomputable def toPathIntegral : FinitePathIntegral ι where
  weight := fun i => (p.weight i : ℂ)
  partition_ne_zero := by
    rw [← Complex.ofReal_sum, p.normalised]
    exact one_ne_zero

@[simp] theorem toPathIntegral_expectation (O : ι → ℝ) :
    p.toPathIntegral.expectation (fun i => (O i : ℂ)) = (p.expectation O : ℂ) := by
  simp [toPathIntegral, FinitePathIntegral.expectation, FinitePathIntegral.insertion,
    FinitePathIntegral.partition, ← Complex.ofReal_mul, ← Complex.ofReal_sum,
    p.normalised, expectation]

theorem toPathIntegral_connected (O A : ι → ℝ) :
    p.toPathIntegral.connectedCorrelator (fun i => (O i : ℂ)) (fun i => (A i : ℂ)) =
      (p.covariance O A : ℂ) := by
  simp only [FinitePathIntegral.connectedCorrelator, FinitePathIntegral.correlator,
    ← Complex.ofReal_mul, toPathIntegral_expectation, covariance, Complex.ofReal_sub]

end LeanPhy.StatMech.FiniteProbability
