import LeanPhy.StatMech.SourceFeedback

set_option autoImplicit false

/-!
# Stationarity and energy conventions for finite mean-field closures

For symmetric coupling K, the derivative of `m K m / 2 - log Z(J + K m)`
is `(K v) · (m - F(m))`. Self-consistency therefore implies stationarity.
This functional is not claimed to be a variational free-energy minimum;
stationarity alone does not imply self-consistency for singular coupling.
The exact energy-to-source conversion retains beta in both bias and coupling.
-/

namespace LeanPhy.StatMech.SourceFeedback

open SourceEnsemble LeanPhy.Mathematics
open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Nonempty ι] [Fintype σ]

noncomputable def stationaryFunctional (S : ι → ℝ) (A : σ → ι → ℝ)
    (J : σ → ℝ) (K : σ → σ → ℝ) (m : σ → ℝ) : ℝ :=
  (1 / 2) * (∑ a, ∑ b, m a * K a b * m b) - logPartition S A (source J K m)

omit [Fintype ι] [Nonempty ι] in
theorem source_line (J : σ → ℝ) (K : σ → σ → ℝ) (m v : σ → ℝ) (s : ℝ) :
    source J K (sourceLine m v s) =
      sourceLine (source J K m) (fun a => ∑ b, K a b * v b) s := by
  funext a
  simp only [source, sourceLine, mul_add, Finset.sum_add_distrib]
  simp_rw [show ∀ b, K a b * (s * v b) = s * (K a b * v b) by intro b; ring]
  rw [← Finset.mul_sum]
  ring

omit [Fintype ι] [Nonempty ι] in
theorem quadratic_derivative (K : σ → σ → ℝ) (hK : ∀ a b, K a b = K b a)
    (m v : σ → ℝ) :
    HasDerivAt (fun s => (1 / 2 : ℝ) *
      (∑ a, ∑ b, sourceLine m v s a * K a b * sourceLine m v s b))
      (∑ a, (∑ b, K a b * v b) * m a) 0 := by
  have hl (a : σ) : HasDerivAt (fun s => sourceLine m v s a) (v a) 0 := by
    simpa [sourceLine] using ((hasDerivAt_id (0 : ℝ)).mul_const (v a)).const_add (m a)
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun b _ => ((hl a).mul_const (K a b)).mul (hl b)))).const_mul (1 / 2 : ℝ)
  have hc : (∑ a, ∑ b, v a * K a b * m b) = ∑ a, ∑ b, m a * K a b * v b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hK b a]
    ring
  convert! hd using 1
  simp only [sourceLine_zero, Finset.sum_add_distrib]
  rw [hc]
  have ht : (∑ a, ∑ b, m a * K a b * v b) = ∑ a, (∑ b, K a b * v b) * m a := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [ht]
  ring

/-- The actual directional Jacobian of the feedback map is a covariance with
the coupling insertion. No commutativity or Gaussian assumption is added to
these real finite observables. -/
theorem feedback_derivative (S : ι → ℝ) (A : σ → ι → ℝ)
    (J : σ → ℝ) (K : σ → σ → ℝ) (m v : σ → ℝ) (a : σ) :
    HasDerivAt (fun s => feedback S A J K (sourceLine m v s) a)
      ((probability S A (source J K m)).covariance (A a)
        (directionObservable A (fun b => ∑ c, K b c * v c))) 0 := by
  simpa only [feedback, source_line, sourceLine_zero] using
    hasDerivAt_expectation S A (source J K m) (fun b => ∑ c, K b c * v c) (A a) 0

theorem functional_derivative (S : ι → ℝ) (A : σ → ι → ℝ)
    (J : σ → ℝ) (K : σ → σ → ℝ) (hK : ∀ a b, K a b = K b a)
    (m v : σ → ℝ) :
    HasDerivAt (fun s => stationaryFunctional S A J K (sourceLine m v s))
      (∑ a, (∑ b, K a b * v b) * (m a - feedback S A J K m a)) 0 := by
  have hl := hasDerivAt_logPartition S A (source J K m) (fun a => ∑ b, K a b * v b) 0
  have he : (probability S A (source J K m)).expectation
      (directionObservable A (fun a => ∑ b, K a b * v b)) =
      ∑ a, (∑ b, K a b * v b) * feedback S A J K m a := by
    unfold directionObservable
    rw [FiniteProbability.expectation_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact (probability S A (source J K m)).expectation_smul _ _
  have hd := (quadratic_derivative K hK m v).sub hl
  simpa only [stationaryFunctional, source_line, sourceLine_zero, he,
    Finset.sum_sub_distrib, mul_sub] using! hd

theorem stationary_of_selfconsistent (S : ι → ℝ) (A : σ → ι → ℝ)
    (J : σ → ℝ) (K : σ → σ → ℝ) (hK : ∀ a b, K a b = K b a)
    (m v : σ → ℝ) (hm : feedback S A J K m = m) :
    HasDerivAt (fun s => stationaryFunctional S A J K (sourceLine m v s)) 0 0 := by
  simpa only [hm, sub_self, mul_zero, Finset.sum_const_zero] using
    functional_derivative S A J K hK m v

omit [Fintype ι] [Nonempty ι] in
theorem source_energy_scale (h : σ → ℝ) (K : σ → σ → ℝ) (β : ℝ) (m : σ → ℝ) (a : σ) :
    source (fun b => β * h b) (fun b c => β * K b c) m a = β * source h K m a := by
  simp only [source, mul_add, Finset.mul_sum, mul_assoc]

theorem probability_energy (E : ι → ℝ) (A : σ → ι → ℝ)
    (h : σ → ℝ) (K : σ → σ → ℝ) (β : ℝ) (m : σ → ℝ) :
    probability (fun i => β * E i) A
      (source (fun b => β * h b) (fun b c => β * K b c) m) =
      finiteGibbsProbability β (fun i => E i - ∑ a, source h K m a * A a i) := by
  have he : action (fun i => β * E i) A
      (source (fun b => β * h b) (fun b c => β * K b c) m) =
      fun i => β * (E i - ∑ a, source h K m a * A a i) := by
    funext i
    simp only [action, source_energy_scale, mul_assoc, ← Finset.mul_sum, mul_sub]
  unfold probability
  rw [he]
  apply FiniteProbability.ext
  funext i
  simp only [finiteGibbsProbability, finiteGibbsWeight, finitePartitionFunction,
    neg_mul, one_mul]

end LeanPhy.StatMech.SourceFeedback
