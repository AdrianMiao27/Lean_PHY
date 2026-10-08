import LeanPhy.Mathematics.EliminationError
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Algebra.Group.Units.Basic

set_option autoImplicit false

/-!
# A posteriori inverse bounds from a checked approximate inverse

A right residual below one constructs an actual inverse in a normed ring with
summable geometric series and finite direct-inverse property. Finite real and
complex square matrices satisfy these conditions. No exact inverse or inverse
norm bound is an input. The bound also supports a whole norm ball around a
nominal matrix, with the data uncertainty added to the numerical residual.
-/

namespace LeanPhy.Mathematics.ResidualInverse

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
  [IsDedekindFiniteMonoid R]

/-- Construct a two-sided unit from the one-sided, computable right residual. -/
noncomputable def unit (D K : R) (h : ‖1 - D * K‖ < 1) : Rˣ :=
  let U := Units.oneSub (1 - D * K) h
  Units.mkOfMulEqOne D (K * (↑(U⁻¹) : R)) (by
    rw [← mul_assoc]
    have hU : (U : R) = D * K := by simp [U]
    rw [← hU]
    exact U.val_inv)

@[simp] theorem unit_val (D K : R) (h : ‖1 - D * K‖ < 1) :
    (unit D K h : R) = D := rfl

omit [HasSummableGeomSeries R] [IsDedekindFiniteMonoid R] in
/-- The inverse norm is obtained from the residual inequality itself. -/
theorem inverse_norm_bound (D : Rˣ) (K : R) (κ r : ℝ)
    (hK : ‖K‖ ≤ κ) (hR : ‖1 - (D : R) * K‖ ≤ r) (hr : r < 1) :
    ‖(↑(D⁻¹) : R)‖ ≤ κ / (1 - r) := by
  have heq : (↑(D⁻¹) : R) = K + (↑(D⁻¹) : R) * (1 - (D : R) * K) := by
    rw [mul_sub, ← mul_assoc]
    simp
  have hn : ‖(↑(D⁻¹) : R)‖ ≤ κ + ‖(↑(D⁻¹) : R)‖ * r := calc
    _ = ‖K + (↑(D⁻¹) : R) * (1 - (D : R) * K)‖ := congrArg norm heq
    _ ≤ ‖K‖ + ‖(↑(D⁻¹) : R) * (1 - (D : R) * K)‖ := norm_add_le _ _
    _ ≤ κ + ‖(↑(D⁻¹) : R)‖ * r := by
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hR (norm_nonneg _))
  apply (le_div_iff₀ (by linarith : 0 < 1 - r)).mpr
  nlinarith

omit [HasSummableGeomSeries R] [IsDedekindFiniteMonoid R] in
/-- The same verified residual gives a numerical inverse error, not just existence. -/
theorem inverse_error_bound (D : Rˣ) (K : R) (κ r : ℝ)
    (hK : ‖K‖ ≤ κ) (hR : ‖1 - (D : R) * K‖ ≤ r) (hr : r < 1) :
    ErrorCertificate (↑(D⁻¹) : R) K (κ / (1 - r) * r) := by
  apply (EliminationError.inverse_error D K).weaken
  exact mul_le_mul (inverse_norm_bound D K κ r hK hR hr) hR
    (norm_nonneg _) (div_nonneg ((norm_nonneg K).trans hK) (le_of_lt (sub_pos.mpr hr)))

omit [HasSummableGeomSeries R] [IsDedekindFiniteMonoid R] in
/-- Model/rounding uncertainty is propagated before the invertibility test. -/
theorem perturbed_residual (A D K : R) (κ r ε : ℝ)
    (hK : ‖K‖ ≤ κ) (hR : ‖1 - A * K‖ ≤ r) (hD : ‖D - A‖ ≤ ε) :
    ‖1 - D * K‖ ≤ r + ε * κ := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hD
  calc
    _ = ‖(1 - A * K) - (D - A) * K‖ := by congr 1; noncomm_ring
    _ ≤ ‖1 - A * K‖ + ‖(D - A) * K‖ := norm_sub_le _ _
    _ ≤ r + ε * κ := add_le_add hR ((norm_mul_le _ _).trans
      (mul_le_mul hD hK (norm_nonneg _) hε))

/-- One nominal certificate covers a whole model domain inside a proved norm ball. -/
noncomputable def robustUnit (A D K : R) (κ r ε : ℝ)
    (hK : ‖K‖ ≤ κ) (hR : ‖1 - A * K‖ ≤ r) (hD : ‖D - A‖ ≤ ε)
    (hmargin : r + ε * κ < 1) : Rˣ :=
  unit D K ((perturbed_residual A D K κ r ε hK hR hD).trans_lt hmargin)

@[simp] theorem robustUnit_val (A D K : R) (κ r ε : ℝ)
    (hK : ‖K‖ ≤ κ) (hR : ‖1 - A * K‖ ≤ r) (hD : ‖D - A‖ ≤ ε)
    (hmargin : r + ε * κ < 1) :
    (robustUnit A D K κ r ε hK hR hD hmargin : R) = D := rfl

omit [HasSummableGeomSeries R] [IsDedekindFiniteMonoid R] in
/-- Effective operators can use a certified inverse and retain an explicit bound. -/
theorem effective_error_bound (A B C : R) (D : Rˣ) (K : R) (κ r : ℝ)
    (hK : ‖K‖ ≤ κ) (hR : ‖1 - (D : R) * K‖ ≤ r) (hr : r < 1) :
    ErrorCertificate (A - B * (↑(D⁻¹) : R) * C) (A - B * K * C)
      (‖B‖ * (κ / (1 - r) * r) * ‖C‖) := by
  apply (EliminationError.effective_error A B C D K).weaken
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul (inverse_norm_bound D K κ r hK hR hr) hR
      (norm_nonneg _) (div_nonneg ((norm_nonneg K).trans hK) (le_of_lt (sub_pos.mpr hr))))
    (norm_nonneg B)) (norm_nonneg C)

end LeanPhy.Mathematics.ResidualInverse
