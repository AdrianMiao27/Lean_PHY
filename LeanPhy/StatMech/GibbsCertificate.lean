import LeanPhy.Mathematics.RationalExp
import LeanPhy.Mathematics.ExternalCertificate
import LeanPhy.StatMech.FeedbackCertificate

set_option autoImplicit false

/-!
# Certified numerical finite Gibbs readouts and feedback residuals

A candidate supplies a rational output, an error budget and exponential enclosure
parameters. Acceptance recomputes the exact rational residual and a strictly
positive partition lower bound. The model's exponent and observable tables are
indices of the checker. A common exponent shift cancels from the normalized
readout and can reduce the size of intermediate rational data.

The soundness theorem bounds the actual normalized exponential sum. The source
and feedback adapters then supply the previously external numerical-error input
of the self-consistency layer. This is not a critical-point or closure-error
certificate and is not a proof about an external floating-point implementation.
-/

namespace LeanPhy.StatMech.GibbsCertificate

open LeanPhy.Mathematics
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

structure Candidate where
  shift : ℚ
  depth : ℕ
  order : ℕ
  value : ℚ
  error : ℚ
  deriving DecidableEq, Repr

namespace Candidate

def weight (c : Candidate) (q : ι → ℚ) (i : ι) : RationalExp.Ball :=
  RationalExp.enclose (q i - c.shift) c.depth c.order

def lowerPartition (c : Candidate) (q : ι → ℚ) : ℚ :=
  ∑ i, ((c.weight q i).center - (c.weight q i).radius)

/-- Residual about the proposed output; signed observables and cancellation are
retained before applying the conservative enclosure error. -/
def residual (c : Candidate) (q O : ι → ℚ) : ℚ :=
  |∑ i, (c.weight q i).center * (O i - c.value)| +
    ∑ i, (c.weight q i).radius * |O i - c.value|

def Accepted (c : Candidate) (q O : ι → ℚ) : Prop :=
  (∀ i, |q i - c.shift| ≤ (2 : ℚ) ^ c.depth) ∧
    0 < c.lowerPartition q ∧ 0 ≤ c.error ∧ c.residual q O ≤ c.error * c.lowerPartition q

instance (c : Candidate) (q O : ι → ℚ) : Decidable (c.Accepted q O) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem weight_contains (c : Candidate) (q O : ι → ℚ) (h : c.Accepted q O) (i : ι) :
    (c.weight q i).Contains (Real.exp ((q i : ℝ) - c.shift)) := by
  simpa only [weight, Rat.cast_sub] using
    RationalExp.enclose_contains (q i - c.shift) c.depth c.order (h.1 i)

theorem partition_lower (c : Candidate) (q O : ι → ℚ) (h : c.Accepted q O) :
    (c.lowerPartition q : ℝ) ≤ ∑ i, Real.exp ((q i : ℝ) - c.shift) := by
  simp only [lowerPartition, Rat.cast_sum, Rat.cast_sub]
  apply Finset.sum_le_sum
  intro i _
  have hw := abs_le.mp (c.weight_contains q O h i)
  linarith [hw.1]

theorem residual_bound (c : Candidate) (q O : ι → ℚ) (h : c.Accepted q O) :
    |∑ i, Real.exp ((q i : ℝ) - c.shift) * ((O i : ℝ) - c.value)| ≤ c.residual q O := by
  let w := fun i => Real.exp ((q i : ℝ) - c.shift)
  have he : (∑ i, w i * ((O i : ℝ) - c.value)) =
      (∑ i, ((c.weight q i).center : ℝ) * ((O i : ℝ) - c.value)) +
      ∑ i, (w i - (c.weight q i).center) * ((O i : ℝ) - c.value) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change |∑ i, w i * ((O i : ℝ) - c.value)| ≤ _
  rw [he]
  simp only [residual, Rat.cast_add, Rat.cast_abs, Rat.cast_sum, Rat.cast_mul, Rat.cast_sub]
  apply (abs_add_le _ _).trans
  apply add_le_add_right
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (c.weight_contains q O h i) (abs_nonneg _)

end Candidate

/-- Actual exponential readout; no approximation appears in this definition. -/
noncomputable def expectation (q O : ι → ℚ) : ℝ :=
  FiniteWeighted.expectation (fun i => Real.exp (q i : ℝ)) (fun i => (O i : ℝ))

theorem expectation_shift (q O : ι → ℚ) (s : ℚ) :
    FiniteWeighted.expectation (fun i => Real.exp ((q i : ℝ) - s)) (fun i => (O i : ℝ)) =
      expectation q O := by
  simp_rw [sub_eq_add_neg, Real.exp_add]
  simpa only [mul_comm, expectation] using FiniteWeighted.expectation_scale
    (fun i => Real.exp (q i : ℝ)) (fun i => (O i : ℝ)) (Real.exp (-(s : ℝ)))
    (Real.exp_ne_zero _)

/-- Kernel-checked rational acceptance gives an error bound for the actual
normalized sum, including the proposed output's rounding error. -/
theorem sound (c : Candidate) (q O : ι → ℚ) (h : c.Accepted q O) :
    ErrorCertificate (c.value : ℝ) (expectation q O) (c.error : ℝ) := by
  have hl : (0 : ℝ) < c.lowerPartition q := by exact_mod_cast h.2.1
  have hz : 0 < ∑ i, Real.exp ((q i : ℝ) - c.shift) :=
    hl.trans_le (c.partition_lower q O h)
  have herr : (0 : ℝ) ≤ c.error := by exact_mod_cast h.2.2.1
  have hbudget : (c.residual q O : ℝ) ≤ (c.error : ℝ) * c.lowerPartition q := by
    exact_mod_cast h.2.2.2
  have he : expectation q O - c.value =
      (∑ i, Real.exp ((q i : ℝ) - c.shift) * ((O i : ℝ) - c.value)) /
        (∑ i, Real.exp ((q i : ℝ) - c.shift)) := by
    rw [← expectation_shift q O c.shift]
    simp only [FiniteWeighted.expectation, FiniteWeighted.insertion, FiniteWeighted.partition,
      mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    field_simp
  refine ⟨herr, ?_⟩
  rw [Real.dist_eq, abs_sub_comm, he, abs_div, abs_of_pos hz]
  apply (div_le_iff₀ hz).mpr
  exact (c.residual_bound q O h).trans (hbudget.trans
    (mul_le_mul_of_nonneg_left (c.partition_lower q O h) herr))

/-- The external-certificate wrapper binds acceptance to both actual tables. -/
def checker (q O : ι → ℚ) (target : Candidate) :
    CertificateChecker
      (ErrorCertificate (target.value : ℝ) (expectation q O) (target.error : ℝ)) Candidate where
  check := fun c => c = target ∧ c.Accepted q O
  sound := by
    rintro c ⟨rfl, h⟩
    exact sound c q O h

section Sources

variable {σ : Type*} [Fintype σ] [Nonempty ι]

def exponent (S : ι → ℚ) (A : σ → ι → ℚ) (J : σ → ℚ) (i : ι) : ℚ :=
  -S i + ∑ a, J a * A a i

theorem source_expectation (S : ι → ℚ) (A : σ → ι → ℚ) (J : σ → ℚ) (O : ι → ℚ) :
    expectation (exponent S A J) O =
      (SourceEnsemble.probability (fun i => (S i : ℝ)) (fun a i => (A a i : ℝ))
        (fun a => (J a : ℝ))).expectation (fun i => (O i : ℝ)) := by
  rw [SourceEnsemble.expectation_eq_weighted]
  unfold expectation
  congr 1
  funext i
  simp only [exponent, Rat.cast_add, Rat.cast_neg, Rat.cast_sum, Rat.cast_mul,
    SourceEnsemble.weight, SourceEnsemble.action, neg_sub]
  congr 1
  ring

theorem source_error (c : Candidate) (S : ι → ℚ) (A : σ → ι → ℚ) (J : σ → ℚ)
    (O : ι → ℚ) (h : c.Accepted (exponent S A J) O) :
    ErrorCertificate (c.value : ℝ)
      ((SourceEnsemble.probability (fun i => (S i : ℝ)) (fun a i => (A a i : ℝ))
        (fun a => (J a : ℝ))).expectation (fun i => (O i : ℝ))) (c.error : ℝ) := by
  rw [← source_expectation]
  exact sound c _ _ h

def feedbackSource (J : σ → ℚ) (K : σ → σ → ℚ) (m : σ → ℚ) (a : σ) : ℚ :=
  J a + ∑ b, K a b * m b

/-- Every component's actual residual is checked; the nonnegative common budget
also handles an empty order-parameter type. -/
theorem feedback_residual (S : ι → ℚ) (A : σ → ι → ℚ) (J : σ → ℚ)
    (K : σ → σ → ℚ) (m : σ → ℚ) (c : σ → Candidate) (ε : ℚ) (hε : 0 ≤ ε)
    (hvalue : ∀ a, (c a).value = m a) (herror : ∀ a, (c a).error ≤ ε)
    (h : ∀ a, (c a).Accepted (exponent S A (feedbackSource J K m)) (A a)) :
    ErrorCertificate (fun a => (m a : ℝ))
      (SourceFeedback.feedback (fun i => (S i : ℝ)) (fun a i => (A a i : ℝ))
        (fun a => (J a : ℝ)) (fun a b => (K a b : ℝ)) (fun a => (m a : ℝ))) (ε : ℝ) := by
  have he : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  refine ⟨he, (dist_pi_le_iff he).mpr ?_⟩
  intro a
  have hd := (source_error (c a) S A (feedbackSource J K m) (A a) (h a)).bound
  simp only [hvalue a, feedbackSource, Rat.cast_add, Rat.cast_sum, Rat.cast_mul] at hd
  exact hd.trans (by exact_mod_cast herror a)

/-- A computable finite-data check supplies the residual premise of the existing
actual fixed-point theorem. The contraction domain remains an independent input. -/
theorem solution_error (S : ι → ℚ) (A : σ → ι → ℚ) (J : σ → ℚ)
    (K : σ → σ → ℚ) (m : σ → ℚ) (c : σ → Candidate) (ε : ℚ) (hε : 0 ≤ ε)
    (hvalue : ∀ a, (c a).value = m a) (herror : ∀ a, (c a).error ≤ ε)
    (h : ∀ a, (c a).Accepted (exponent S A (feedbackSource J K m)) (A a))
    (e : SourceFeedback.Envelope (fun a i => (A a i : ℝ)) (fun a b => (K a b : ℝ)))
    (hsmall : e.rate < 1) :
    ErrorCertificate (fun a => (m a : ℝ))
      (e.solution (fun i => (S i : ℝ)) (fun a => (J a : ℝ)) hsmall)
      ((ε : ℝ) / (1 - e.rate)) :=
  e.solution_error _ _ hsmall _ _ (feedback_residual S A J K m c ε hε hvalue herror h)

/-- Numerical readout error and certified feedback residual are separate inputs
and both survive in the final observable budget at the true closure solution. -/
theorem solution_readout_error (S : ι → ℚ) (A : σ → ι → ℚ) (J : σ → ℚ)
    (K : σ → σ → ℚ) (m : σ → ℚ) (c : σ → Candidate) (ε : ℚ) (hε : 0 ≤ ε)
    (hvalue : ∀ a, (c a).value = m a) (herror : ∀ a, (c a).error ≤ ε)
    (h : ∀ a, (c a).Accepted (exponent S A (feedbackSource J K m)) (A a))
    (e : SourceFeedback.Envelope (fun a i => (A a i : ℝ)) (fun a b => (K a b : ℝ)))
    (hsmall : e.rate < 1) (O : ι → ℚ) (N : ℝ≥0) (hO : ∀ i, |(O i : ℝ)| ≤ N)
    (d : Candidate) (hd : d.Accepted (exponent S A (feedbackSource J K m)) O) :
    ErrorCertificate (d.value : ℝ)
      ((SourceEnsemble.probability (fun i => (S i : ℝ)) (fun a i => (A a i : ℝ))
        (SourceFeedback.source (fun a => (J a : ℝ)) (fun a b => (K a b : ℝ))
          (e.solution (fun i => (S i : ℝ)) (fun a => (J a : ℝ)) hsmall))).expectation
            (fun i => (O i : ℝ)))
      ((d.error : ℝ) + (2 * (N : ℝ) * e.coupling) * ((ε : ℝ) / (1 - e.rate))) := by
  have hnum := source_error d S A (feedbackSource J K m) O hd
  simp only [feedbackSource, Rat.cast_add, Rat.cast_sum, Rat.cast_mul] at hnum
  exact e.evaluated_observable_error (fun i => (S i : ℝ)) (fun a => (J a : ℝ)) hsmall
    (fun a => (m a : ℝ)) (ε : ℝ) (feedback_residual S A J K m c ε hε hvalue herror h)
    (fun i => (O i : ℝ)) N hO (d.value : ℝ) (d.error : ℝ) hnum

end Sources
end LeanPhy.StatMech.GibbsCertificate
