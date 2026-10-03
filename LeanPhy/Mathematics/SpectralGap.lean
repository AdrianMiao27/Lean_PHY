import LeanPhy.Mathematics.Hilbert
import Mathlib.Tactic

/-!
# Spectral-gap contraction certificates

This file packages a proof pattern that occurs in transfer operators, finite
Markov chains, dissipative quantum channels and discretised evolution.  `P`
is the invariant projection and `T` fixes its range.  The one-step estimate is
required explicitly; the kernel then derives the geometric bound for every
iterate and the corresponding convergence of bounded observables.

The certificate is intentionally weaker than a spectral theorem.  It does not
construct an invariant projection from an eigenvalue calculation, prove that a
continuous semigroup has a generator, or infer a thermodynamic-limit gap.  A
researcher must provide those analytic inputs separately.
-/

namespace LeanPhy.Mathematics

universe u v

open Filter
open scoped Topology

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- A projection onto the non-decaying sector of a bounded evolution.

The three composition equations make the decomposition explicit:
`P² = P`, `P T = P`, and `T P = P`.  The final field is a contraction
estimate for the residual in one step. -/
structure SpectralGapCertificate
    (T P : E →L[𝕜] E) (rho : ℝ) : Prop where
  rho_nonneg : 0 ≤ rho
  rho_lt_one : rho < 1
  projection : P * P = P
  left_invariant : P * T = P
  right_invariant : T * P = P
  one_step : ∀ x, ‖T x - P x‖ ≤ rho * ‖x - P x‖

namespace SpectralGapCertificate

variable {T P : E →L[𝕜] E} {rho : ℝ}

private theorem projection_iterate (h : SpectralGapCertificate T P rho)
    (n : ℕ) : P * T ^ n = P := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      calc
        P * (T * T ^ n) = (P * T) * T ^ n := by rw [mul_assoc]
        _ = P * T ^ n := by rw [h.left_invariant]
        _ = P := ih

/-! The estimate is separated from the limit theorem so users can retain a
    quantitative finite-time error budget even when they do not need a limit. -/

theorem iterate_decay (h : SpectralGapCertificate T P rho)
    (n : ℕ) (x : E) :
    ‖(T ^ n) x - P x‖ ≤ rho ^ n * ‖x - P x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      have hproj : P ((T ^ n) x) = P x := by
        have hmap := congrArg (fun L => L x) (projection_iterate h n)
        simpa [mul_apply_eq_comp] using hmap
      calc
        ‖T ((T ^ n) x) - P x‖ =
            ‖T ((T ^ n) x) - P ((T ^ n) x)‖ := by rw [hproj]
        _ ≤ rho * ‖(T ^ n) x - P ((T ^ n) x)‖ := h.one_step _
        _ = rho * ‖(T ^ n) x - P x‖ := by rw [hproj]
        _ ≤ rho * (rho ^ n * ‖x - P x‖) :=
          mul_le_mul_of_nonneg_left ih h.rho_nonneg
        _ = rho ^ (n + 1) * ‖x - P x‖ := by
          rw [pow_succ]
          ring

theorem residual_tendsto_zero (h : SpectralGapCertificate T P rho)
    (x : E) :
    Tendsto (fun n : ℕ => (T ^ n) x - P x) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => rho ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h.rho_nonneg h.rho_lt_one
  have hbound : Tendsto
      (fun n : ℕ => rho ^ n * ‖x - P x‖) atTop (𝓝 0) := by
    simpa using hpow.mul_const ‖x - P x‖
  have hnorm : Tendsto
      (fun n : ℕ => ‖(T ^ n) x - P x‖) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun n => norm_nonneg _)
    · exact Filter.Eventually.of_forall (fun n => h.iterate_decay n x)
    · exact hbound
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

theorem iterate_tendsto_projection (h : SpectralGapCertificate T P rho)
    (x : E) :
    Tendsto (fun n : ℕ => (T ^ n) x) atTop (𝓝 (P x)) := by
  have hres := h.residual_tendsto_zero x
  have hadd := hres.add_const (P x)
  simpa [sub_add_cancel] using hadd

theorem observable_tendsto_projection
    (h : SpectralGapCertificate T P rho) (L : E →L[𝕜] 𝕜) (x : E) :
    Tendsto (fun n : ℕ => L ((T ^ n) x)) atTop (𝓝 (L (P x))) := by
  exact L.continuous.continuousAt.tendsto.comp (h.iterate_tendsto_projection x)

end SpectralGapCertificate

end LeanPhy.Mathematics
