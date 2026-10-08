import LeanPhy.StatMech.FiniteGibbs
import LeanPhy.StatMech.FiniteCovariance
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false

/-!
# Source-dependent finite Euclidean ensembles and static response

The dimensionless action convention is `exp (-S + Σ_a J_a A_a)`. A real,
nonempty finite configuration space makes the partition positive. Gibbs
weights are recovered by `S = β E`, with an energy-source perturbation
`E - h A` corresponding to `J = β h`; the factor β is not silently absorbed.

Log-partition derivatives and source responses are derived from the actual
finite weights. The same `FiniteProbability` feeds covariance, susceptibility
and the existing complex connected-correlator adapter. These are equilibrium
responses of commuting observables, not real-time quantum Kubo response or a
thermodynamic-limit phase transition.
-/

namespace LeanPhy.StatMech

open LeanPhy.Mathematics
open scoped BigOperators

namespace SourceEnsemble

variable {ι σ : Type*} [Fintype ι] [Nonempty ι] [Fintype σ]

noncomputable def action (S : ι → ℝ) (A : σ → ι → ℝ) (J : σ → ℝ) (i : ι) : ℝ :=
  S i - ∑ a, J a * A a i

noncomputable def probability (S : ι → ℝ) (A : σ → ι → ℝ) (J : σ → ℝ) :
    FiniteProbability ι := finiteGibbsProbability 1 (action S A J)

noncomputable def weight (S : ι → ℝ) (A : σ → ι → ℝ) (J : σ → ℝ) (i : ι) : ℝ :=
  Real.exp (-action S A J i)

noncomputable def partition (S : ι → ℝ) (A : σ → ι → ℝ) (J : σ → ℝ) : ℝ :=
  FiniteWeighted.partition (weight S A J)

noncomputable def logPartition (S : ι → ℝ) (A : σ → ι → ℝ) (J : σ → ℝ) : ℝ :=
  Real.log (partition S A J)

theorem partition_pos (S : ι → ℝ) (A : σ → ι → ℝ) (J : σ → ℝ) :
    0 < partition S A J := by
  simpa [partition, weight, FiniteWeighted.partition, finitePartitionFunction] using
    finitePartitionFunction_pos 1 (action S A J)

theorem expectation_eq_weighted (S : ι → ℝ) (A : σ → ι → ℝ) (J : σ → ℝ) (O : ι → ℝ) :
    (probability S A J).expectation O = FiniteWeighted.expectation (weight S A J) O := by
  simp only [FiniteProbability.expectation, probability, finiteGibbsProbability,
    finiteGibbsWeight, neg_mul, one_mul, FiniteWeighted.expectation,
    FiniteWeighted.insertion, FiniteWeighted.partition, weight, finitePartitionFunction]
  simp_rw [div_mul_eq_mul_div]
  rw [Finset.sum_div]

theorem covariance_eq_connected (S : ι → ℝ) (A : σ → ι → ℝ)
    (J : σ → ℝ) (O Q : ι → ℝ) :
    (probability S A J).covariance O Q = FiniteWeighted.connected (weight S A J) O Q := by
  simp only [FiniteProbability.covariance, FiniteWeighted.connected, ← expectation_eq_weighted]

/-- Real source ensembles and finite Euclidean path sums give the same
normalized observable, despite using normalized versus raw weights internally. -/
theorem fromRealAction_expectation (S : ι → ℝ) (A : σ → ι → ℝ)
    (J : σ → ℝ) (O : ι → ℝ) :
    (FinitePathIntegral.fromRealAction (action S A J)).expectation (fun i => (O i : ℂ)) =
      ((probability S A J).expectation O : ℂ) := by
  rw [expectation_eq_weighted]
  simp only [FinitePathIntegral.expectation, FinitePathIntegral.insertion,
    FinitePathIntegral.partition, FinitePathIntegral.fromRealAction,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_div]
  rfl

theorem fromRealAction_connected (S : ι → ℝ) (A : σ → ι → ℝ)
    (J : σ → ℝ) (O Q : ι → ℝ) :
    (FinitePathIntegral.fromRealAction (action S A J)).connectedCorrelator
      (fun i => (O i : ℂ)) (fun i => (Q i : ℂ)) =
      ((probability S A J).covariance O Q : ℂ) := by
  simp only [FinitePathIntegral.connectedCorrelator, FinitePathIntegral.correlator,
    ← Complex.ofReal_mul, fromRealAction_expectation,
    FiniteProbability.covariance, Complex.ofReal_sub]

/-- A direction in source space inserts the corresponding linear combination
of observables. No particular number of sources is fixed. -/
noncomputable def directionObservable (A : σ → ι → ℝ) (v : σ → ℝ) (i : ι) : ℝ :=
  ∑ a, v a * A a i

def sourceLine (J v : σ → ℝ) (t : ℝ) (a : σ) : ℝ := J a + t * v a

omit [Fintype ι] [Nonempty ι] [Fintype σ] in
@[simp] theorem sourceLine_zero (J v : σ → ℝ) : sourceLine J v 0 = J := by
  funext a
  simp [sourceLine]

omit [Fintype ι] [Nonempty ι] in
@[simp] theorem directionObservable_single [DecidableEq σ]
    (A : σ → ι → ℝ) (b : σ) : directionObservable A (Pi.single b 1) = A b := by
  funext i
  simp [directionObservable, Pi.single_apply, ite_mul]

omit [Fintype ι] [Nonempty ι] in
theorem hasDerivAt_weight (S : ι → ℝ) (A : σ → ι → ℝ) (J v : σ → ℝ)
    (t : ℝ) (i : ι) :
    HasDerivAt (fun s => weight S A (sourceLine J v s) i)
      (weight S A (sourceLine J v t) i * directionObservable A v i) t := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
    (((hasDerivAt_id t).mul_const (v a)).const_add (J a)).mul_const (A a i))
  have hexp := ((hsum.const_sub (S i)).neg).exp
  simpa [weight, action, sourceLine, directionObservable] using hexp

theorem hasDerivAt_partition (S : ι → ℝ) (A : σ → ι → ℝ) (J v : σ → ℝ) (t : ℝ) :
    HasDerivAt (fun s => partition S A (sourceLine J v s))
      (FiniteWeighted.insertion (weight S A (sourceLine J v t)) (directionObservable A v)) t :=
  HasDerivAt.fun_sum (fun i _ => hasDerivAt_weight S A J v t i)

/-- First derivative of log Z is the normalized source insertion. -/
theorem hasDerivAt_logPartition (S : ι → ℝ) (A : σ → ι → ℝ) (J v : σ → ℝ) (t : ℝ) :
    HasDerivAt (fun s => logPartition S A (sourceLine J v s))
      ((probability S A (sourceLine J v t)).expectation (directionObservable A v)) t := by
  rw [expectation_eq_weighted]
  exact (hasDerivAt_partition S A J v t).log (ne_of_gt (partition_pos _ _ _))

/-- Differentiating a normalized expectation gives the connected fluctuation. -/
theorem hasDerivAt_expectation (S : ι → ℝ) (A : σ → ι → ℝ) (J v : σ → ℝ)
    (O : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => (probability S A (sourceLine J v s)).expectation O)
      ((probability S A (sourceLine J v t)).covariance O (directionObservable A v)) t := by
  simp_rw [expectation_eq_weighted, covariance_eq_connected]
  exact FiniteWeighted.hasDerivAt_expectation_fixed _ _ _ t
    (hasDerivAt_weight S A J v t) (ne_of_gt (partition_pos _ _ _))

/-- Parameter-dependent observables retain their explicit derivative term. -/
theorem hasDerivAt_moving_expectation (S : ι → ℝ) (A : σ → ι → ℝ) (J v : σ → ℝ)
    (O : ℝ → ι → ℝ) (O' : ι → ℝ) (t : ℝ)
    (hO : ∀ i, HasDerivAt (fun s => O s i) (O' i) t) :
    HasDerivAt (fun s => (probability S A (sourceLine J v s)).expectation (O s))
      ((probability S A (sourceLine J v t)).expectation O' +
        (probability S A (sourceLine J v t)).covariance (O t) (directionObservable A v)) t := by
  simp_rw [expectation_eq_weighted, covariance_eq_connected]
  exact FiniteWeighted.hasDerivAt_expectation_score _ _ _ _ t
    (hasDerivAt_weight S A J v t) hO (ne_of_gt (partition_pos _ _ _))

/-- Second derivative along an arbitrary source direction is a variance,
proved as a derivative of the actual first derivative of log Z. -/
theorem hasDerivAt_deriv_logPartition (S : ι → ℝ) (A : σ → ι → ℝ)
    (J v : σ → ℝ) (t : ℝ) :
    HasDerivAt (deriv (fun s => logPartition S A (sourceLine J v s)))
      ((probability S A (sourceLine J v t)).variance (directionObservable A v)) t := by
  have hfun : deriv (fun s => logPartition S A (sourceLine J v s)) =
      fun s => (probability S A (sourceLine J v s)).expectation (directionObservable A v) := by
    funext s
    exact (hasDerivAt_logPartition S A J v s).deriv
  rw [hfun]
  exact hasDerivAt_expectation S A J v (directionObservable A v) t

/-- The static response matrix; the next theorem connects each entry to an
actual partial source derivative. -/
noncomputable def susceptibility (S : ι → ℝ) (A : σ → ι → ℝ) (J : σ → ℝ)
    (a b : σ) : ℝ := (probability S A J).covariance (A a) (A b)

theorem susceptibility_is_response [DecidableEq σ]
    (S : ι → ℝ) (A : σ → ι → ℝ) (J : σ → ℝ) (a b : σ) :
    HasDerivAt (fun s => (probability S A (sourceLine J (Pi.single b 1) s)).expectation (A a))
      (susceptibility S A J a b) 0 := by
  simpa only [sourceLine_zero, directionObservable_single, susceptibility] using
    hasDerivAt_expectation S A J (Pi.single b 1) (A a) 0

theorem susceptibility_symm (S : ι → ℝ) (A : σ → ι → ℝ) (J : σ → ℝ) (a b : σ) :
    susceptibility S A J a b = susceptibility S A J b a :=
  (probability S A J).covariance_symm _ _

theorem susceptibility_nonneg (S : ι → ℝ) (A : σ → ι → ℝ) (J v : σ → ℝ) :
    0 ≤ ∑ a, ∑ b, v a * susceptibility S A J a b * v b :=
  (probability S A J).covariance_quadratic_nonneg A v

end SourceEnsemble
end LeanPhy.StatMech
