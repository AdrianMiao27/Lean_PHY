import LeanPhy.StatMech.ResponseBound
import LeanPhy.Mathematics.Contraction

set_option autoImplicit false

/-!
# Self-consistent sources in an actual finite ensemble

The map sends order parameters `m` to expectations at source `J + K m`.
It is constructed from normalized finite Gibbs weights. Finite bounds on
observables and on their coupling insertions imply a global Lipschitz factor
`2 M B`; strict smallness supplies a contraction, rather than being an assumed
property of the map. Residuals then bound the solution and actual readouts.

These are statements about the specified finite closure. Their conservative
parameter domain is not an exact critical surface, and no approximation to an
underlying interacting thermodynamic system is asserted. Sources are
dimensionless; the energy convention is provided by `MeanFieldFunctional`.
-/

namespace LeanPhy.StatMech.SourceFeedback

open SourceEnsemble LeanPhy.Mathematics
open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Nonempty ι] [Fintype σ]

noncomputable def source (J : σ → ℝ) (K : σ → σ → ℝ) (m : σ → ℝ) (a : σ) : ℝ :=
  J a + ∑ b, K a b * m b

noncomputable def feedback (S : ι → ℝ) (A : σ → ι → ℝ)
    (J : σ → ℝ) (K : σ → σ → ℝ) (m : σ → ℝ) (a : σ) : ℝ :=
  (probability S A (source J K m)).expectation (A a)

noncomputable def insertion (A : σ → ι → ℝ) (K : σ → σ → ℝ)
    (i : ι) (b : σ) : ℝ := ∑ a, K a b * A a i

omit [Fintype ι] [Nonempty ι] in
theorem direction_bound (A : σ → ι → ℝ) (J : σ → ℝ) (K : σ → σ → ℝ)
    (B : ℝ) (hb : ∀ i, ∑ b, |insertion A K i b| ≤ B)
    (m n : σ → ℝ) (i : ι) :
    |directionObservable A (fun a => source J K m a - source J K n a) i|
      ≤ B * dist m n := by
  have he : directionObservable A (fun a => source J K m a - source J K n a) i =
      ∑ b, insertion A K i b * (m b - n b) := by
    simp only [directionObservable, source, add_sub_add_left_eq_sub,
      ← Finset.sum_sub_distrib, ← mul_sub, Finset.sum_mul, insertion]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he]
  calc
    |∑ b, insertion A K i b * (m b - n b)| ≤
        ∑ b, |insertion A K i b * (m b - n b)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b, |insertion A K i b| * |m b - n b| := by simp only [abs_mul]
    _ ≤ ∑ b, |insertion A K i b| * dist m n := by
      apply Finset.sum_le_sum
      intro b _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (Real.dist_eq (m b) (n b)) ▸ dist_le_pi_dist m n b
    _ = (∑ b, |insertion A K i b|) * dist m n := (Finset.sum_mul _ _ _).symm
    _ ≤ B * dist m n := mul_le_mul_of_nonneg_right (hb i) dist_nonneg

theorem feedback_bounded (S : ι → ℝ) (A : σ → ι → ℝ)
    (J : σ → ℝ) (K : σ → σ → ℝ) (M : ℝ)
    (hA : ∀ a i, |A a i| ≤ M) (m : σ → ℝ) (a : σ) :
    |feedback S A J K m a| ≤ M :=
  (probability S A (source J K m)).abs_expectation_le (A a) M (hA a)

theorem feedback_dist_le (S : ι → ℝ) (A : σ → ι → ℝ)
    (J : σ → ℝ) (K : σ → σ → ℝ) (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hA : ∀ a i, |A a i| ≤ M) (hb : ∀ i, ∑ b, |insertion A K i b| ≤ B)
    (m n : σ → ℝ) :
    dist (feedback S A J K m) (feedback S A J K n) ≤ (2 * M * B) * dist m n := by
  apply (dist_pi_le_iff (mul_nonneg (by positivity) dist_nonneg)).mpr
  intro a
  have h := expectation_source_error S A (source J K n)
    (fun b => source J K m b - source J K n b) (A a) M (B * dist m n)
    hM (mul_nonneg hB dist_nonneg) (hA a) (direction_bound A J K B hb m n) 1 0
  have hs : sourceLine (source J K n)
      (fun b => source J K m b - source J K n b) 1 = source J K m := by
    funext b
    simp [sourceLine]
  simpa only [hs, sourceLine_zero, feedback, sub_zero, abs_one, mul_one, mul_assoc] using h.bound

theorem contraction (S : ι → ℝ) (A : σ → ι → ℝ)
    (J : σ → ℝ) (K : σ → σ → ℝ) (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hA : ∀ a i, |A a i| ≤ M) (hb : ∀ i, ∑ b, |insertion A K i b| ≤ B)
    (hsmall : 2 * M * B < 1) :
    ContractionCertificate (feedback S A J K) ⟨2 * M * B, by positivity⟩ := by
  refine ⟨hsmall, LipschitzWith.of_dist_le_mul ?_⟩
  exact feedback_dist_le S A J K M B hM hB hA hb

theorem readout_dist_le (S : ι → ℝ) (A : σ → ι → ℝ)
    (J : σ → ℝ) (K : σ → σ → ℝ) (O : ι → ℝ)
    (N B : ℝ) (hN : 0 ≤ N) (hB : 0 ≤ B)
    (hO : ∀ i, |O i| ≤ N) (hb : ∀ i, ∑ b, |insertion A K i b| ≤ B)
    (m n : σ → ℝ) :
    dist ((probability S A (source J K m)).expectation O)
      ((probability S A (source J K n)).expectation O) ≤ (2 * N * B) * dist m n := by
  have h := expectation_source_error S A (source J K n)
    (fun b => source J K m b - source J K n b) O N (B * dist m n)
    hN (mul_nonneg hB dist_nonneg) hO (direction_bound A J K B hb m n) 1 0
  have hs : sourceLine (source J K n)
      (fun b => source J K m b - source J K n b) 1 = source J K m := by
    funext b
    simp [sourceLine]
  simpa only [hs, sourceLine_zero, sub_zero, abs_one, mul_one, mul_assoc] using h.bound

theorem fixedPoint_error (S : ι → ℝ) (A : σ → ι → ℝ)
    (J : σ → ℝ) (K : σ → σ → ℝ) (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hA : ∀ a i, |A a i| ≤ M) (hb : ∀ i, ∑ b, |insertion A K i b| ≤ B)
    (hsmall : 2 * M * B < 1) (m : σ → ℝ) (ε : ℝ)
    (hres : ErrorCertificate m (feedback S A J K m) ε) :
    ErrorCertificate m (contraction S A J K M B hM hB hA hb hsmall).fixedPoint
      (ε / (1 - 2 * M * B)) := by
  have hd : 0 < 1 - 2 * M * B := sub_pos.mpr hsmall
  refine ⟨div_nonneg hres.nonneg hd.le, ?_⟩
  exact (contraction S A J K M B hM hB hA hb hsmall).fixedPoint_error_of_residual m |>.trans
    (div_le_div_of_nonneg_right hres.bound hd.le)

theorem readout_error (S : ι → ℝ) (A : σ → ι → ℝ)
    (J : σ → ℝ) (K : σ → σ → ℝ) (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hA : ∀ a i, |A a i| ≤ M) (hb : ∀ i, ∑ b, |insertion A K i b| ≤ B)
    (hsmall : 2 * M * B < 1) (m : σ → ℝ) (ε : ℝ)
    (hres : ErrorCertificate m (feedback S A J K m) ε)
    (O : ι → ℝ) (N : ℝ) (hN : 0 ≤ N) (hO : ∀ i, |O i| ≤ N) :
    ErrorCertificate ((probability S A (source J K m)).expectation O)
      ((probability S A (source J K
        (contraction S A J K M B hM hB hA hb hsmall).fixedPoint)).expectation O)
      ((2 * N * B) * (ε / (1 - 2 * M * B))) := by
  exact (fixedPoint_error S A J K M B hM hB hA hb hsmall m ε hres).map
    ⟨by positivity, readout_dist_le S A J K O N B hN hB hO hb⟩

theorem bias_feedback_error (S : ι → ℝ) (A : σ → ι → ℝ)
    (J J' : σ → ℝ) (K : σ → σ → ℝ) (M D : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hA : ∀ a i, |A a i| ≤ M)
    (hsource : ∀ i, |directionObservable A (fun a => J a - J' a) i| ≤ D)
    (m : σ → ℝ) :
    dist (feedback S A J K m) (feedback S A J' K m) ≤ 2 * M * D := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro a
  have h := expectation_source_error S A (source J' K m)
    (fun b => J b - J' b) (A a) M D hM hD (hA a) hsource 1 0
  have hs : sourceLine (source J' K m) (fun b => J b - J' b) 1 = source J K m := by
    funext b
    simp only [sourceLine, source, one_mul]
    ring
  simpa only [hs, sourceLine_zero, feedback, sub_zero, abs_one, mul_one] using h.bound

theorem fixedPoint_bias_error (S : ι → ℝ) (A : σ → ι → ℝ)
    (J J' : σ → ℝ) (K : σ → σ → ℝ) (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hA : ∀ a i, |A a i| ≤ M) (hb : ∀ i, ∑ b, |insertion A K i b| ≤ B)
    (hsmall : 2 * M * B < 1) (D : ℝ) (hD : 0 ≤ D)
    (hsource : ∀ i, |directionObservable A (fun a => J a - J' a) i| ≤ D) :
    ErrorCertificate (contraction S A J K M B hM hB hA hb hsmall).fixedPoint
      (contraction S A J' K M B hM hB hA hb hsmall).fixedPoint
      ((2 * M * D) / (1 - 2 * M * B)) := by
  refine ⟨div_nonneg (by positivity) (sub_pos.mpr hsmall).le, ?_⟩
  exact (contraction S A J K M B hM hB hA hb hsmall).fixedPoint_stable_under_map_error
    (contraction S A J' K M B hM hB hA hb hsmall)
    (bias_feedback_error S A J J' K M D hM hD hA hsource)

end LeanPhy.StatMech.SourceFeedback
