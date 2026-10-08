import LeanPhy.Mathematics.Approximation
import Mathlib.Analysis.Normed.Ring.Basic

set_option autoImplicit false

/-!
# Analytic inverse and elimination errors from actual residuals

Formal retained-order equalities alone give no norm bound. In a normed ring,
a certified inverse instead turns the computable residual `1 - D K` into an
inverse error and hence an effective-operator/readout error. A finite geometric
inverse has an explicitly derived residual `X^N`; its error bound needs no
infinite-series convergence hypothesis. Decay with N additionally requires a
norm below one and a bound on the exact inverse. For matrices, choose a
submultiplicative norm (for example mathlib's operator norm), not an entrywise
norm that lacks the required normed-ring instance.
-/

namespace LeanPhy.Mathematics.EliminationError

open scoped BigOperators

variable {R : Type*} [NormedRing R]

/-- Residual identity keeps multiplication order for noncommuting operators. -/
theorem inverse_error_identity (D : Rˣ) (K : R) :
    (↑(D⁻¹) : R) - K = (↑(D⁻¹) : R) * (1 - (D : R) * K) := by
  simp [mul_sub, ← mul_assoc]

theorem inverse_error (D : Rˣ) (K : R) :
    ErrorCertificate (↑(D⁻¹) : R) K (‖(↑(D⁻¹) : R)‖ * ‖1 - (D : R) * K‖) := by
  refine ⟨mul_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
  rw [dist_eq_norm, inverse_error_identity]
  exact norm_mul_le _ _

/-- Substitute an approximate heavy inverse into the effective operator. -/
theorem effective_error (A B C : R) (D : Rˣ) (K : R) :
    ErrorCertificate (A - B * (↑(D⁻¹) : R) * C) (A - B * K * C)
      (‖B‖ * (‖(↑(D⁻¹) : R)‖ * ‖1 - (D : R) * K‖) * ‖C‖) := by
  refine ⟨mul_nonneg (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
    (norm_nonneg _))) (norm_nonneg _), ?_⟩
  rw [dist_eq_norm]
  have heq : (A - B * (↑(D⁻¹) : R) * C) - (A - B * K * C) =
      -(B * ((↑(D⁻¹) : R) - K) * C) := by noncomm_ring
  rw [heq, norm_neg]
  calc
    _ ≤ ‖B * ((↑(D⁻¹) : R) - K)‖ * ‖C‖ := norm_mul_le _ _
    _ ≤ (‖B‖ * ‖(↑(D⁻¹) : R) - K‖) * ‖C‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using (inverse_error D K).bound)
        (norm_nonneg _)) (norm_nonneg _)

/-- Keep exactly N terms of a geometric inverse. -/
def geometricInverse (X : R) (N : ℕ) : R := ∑ k ∈ Finset.range N, X ^ k

theorem geometric_residual (X : R) (N : ℕ) :
    1 - (1 - X) * geometricInverse X N = X ^ N := by
  induction N with
  | zero => simp [geometricInverse]
  | succ N ih =>
    have hs : geometricInverse X (N + 1) = geometricInverse X N + X ^ N := by
      simp [geometricInverse, Finset.sum_range_succ]
    rw [hs, mul_add]
    rw [pow_succ']
    calc
      _ = (1 - (1 - X) * geometricInverse X N) - X ^ N + X * X ^ N := by noncomm_ring
      _ = _ := by rw [ih]; abel

/-- A finite truncation has a proved error bound once the exact inverse exists. -/
theorem geometric_inverse_error [NormOneClass R]
    (X : R) (D : Rˣ) (hD : (D : R) = 1 - X) (N : ℕ) :
    ErrorCertificate (↑(D⁻¹) : R) (geometricInverse X N)
      (‖(↑(D⁻¹) : R)‖ * ‖X‖ ^ N) := by
  apply (inverse_error D (geometricInverse X N)).weaken
  rw [hD, geometric_residual]
  exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (norm_nonneg _)

end LeanPhy.Mathematics.EliminationError
