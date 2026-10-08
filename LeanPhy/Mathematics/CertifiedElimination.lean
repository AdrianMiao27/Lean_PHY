import LeanPhy.Mathematics.MatrixCertificate
import LeanPhy.Mathematics.BlockElimination

set_option autoImplicit false

/-!
# Certified block elimination with finite-data error bounds

The light, heavy and readout spaces may have different sizes. A checked
approximate inverse constructs the actual heavy unit, then supplies bounds
for the effective operator, heavy reconstruction, source and readout offset.
All norms are L-infinity operator/vector norms. No spectral gap, Hermiticity,
unitary reduction or low-energy truncation is inferred by this interface.
-/

namespace LeanPhy.Mathematics.CertifiedElimination

open MatrixCertificate BlockElimination
open scoped Matrix.Norms.Operator

variable {l n o : ℕ}

/-- A checked nominal matrix and candidate produce a full exact block system. -/
noncomputable def system (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : ‖D - A.realize‖ ≤ (c.modelRadius : ℝ))
    (L : Matrix (Fin l) (Fin l) ℂ) (B : Matrix (Fin l) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin l) ℂ) : System ℂ (Fin l) (Fin n) where
  light := L
  toLight := B
  toHeavy := C
  heavy := c.unit A h D hD

/-- Replacing the inverse preserves a bound for rectangular sandwich operations. -/
theorem sandwich_error {p : ℕ} (U K : Matrix (Fin n) (Fin n) ℂ) (e : ℝ)
    (h : ErrorCertificate U K e) (B : Matrix (Fin o) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin p) ℂ) :
    ErrorCertificate (B * U * C) (B * K * C) (‖B‖ * e * ‖C‖) := by
  refine ⟨mul_nonneg (mul_nonneg (norm_nonneg _) h.nonneg) (norm_nonneg _), ?_⟩
  rw [dist_eq_norm]
  have heq : B * U * C - B * K * C = B * (U - K) * C := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [heq]
  have hb : ‖U - K‖ ≤ e := by simpa [dist_eq_norm] using h.bound
  exact (Matrix.linfty_opNorm_mul _ _).trans
    (mul_le_mul_of_nonneg_right ((Matrix.linfty_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_left hb (norm_nonneg B))) (norm_nonneg C))

theorem applied_error (U K : Matrix (Fin n) (Fin n) ℂ) (e : ℝ)
    (h : ErrorCertificate U K e) (B : Matrix (Fin o) (Fin n) ℂ) (v : Fin n → ℂ) :
    ErrorCertificate ((B * U).mulVec v) ((B * K).mulVec v) (‖B‖ * e * ‖v‖) := by
  refine ⟨mul_nonneg (mul_nonneg (norm_nonneg _) h.nonneg) (norm_nonneg _), ?_⟩
  rw [dist_eq_norm, ← Matrix.sub_mulVec, ← Matrix.mul_sub]
  have hb : ‖U - K‖ ≤ e := by simpa [dist_eq_norm] using h.bound
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right ((Matrix.linfty_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_left hb (norm_nonneg B))) (norm_nonneg v))

theorem vector_error (U K : Matrix (Fin n) (Fin n) ℂ) (e : ℝ)
    (h : ErrorCertificate U K e) (v : Fin n → ℂ) :
    ErrorCertificate (U.mulVec v) (K.mulVec v) (e * ‖v‖) := by
  refine ⟨mul_nonneg h.nonneg (norm_nonneg _), ?_⟩
  rw [dist_eq_norm, ← Matrix.sub_mulVec]
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right (by simpa [dist_eq_norm] using h.bound) (norm_nonneg v))

/-- Actual Schur elimination and the computed approximation differ by this bound. -/
theorem effective_error (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : ‖D - A.realize‖ ≤ (c.modelRadius : ℝ))
    (L : Matrix (Fin l) (Fin l) ℂ) (B : Matrix (Fin l) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin l) ℂ) :
    ErrorCertificate (system A c h D hD L B C).effective
      (L - B * c.inverse.realize * C) (‖B‖ * (c.errorBound : ℝ) * ‖C‖) := by
  have hb := sandwich_error _ _ _ (c.inverse_error A h D hD) B C
  refine ⟨hb.nonneg, ?_⟩
  change dist (L - _) (L - _) ≤ _
  rw [dist_sub_left]
  exact hb.bound

/-- Heavy sources must be retained when certifying an effective equation. -/
theorem source_error (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : ‖D - A.realize‖ ≤ (c.modelRadius : ℝ))
    (L : Matrix (Fin l) (Fin l) ℂ) (B : Matrix (Fin l) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin l) ℂ) (jL : Fin l → ℂ) (jH : Fin n → ℂ) :
    ErrorCertificate ((system A c h D hD L B C).effectiveSource jL jH)
      (jL - (B * c.inverse.realize).mulVec jH) (‖B‖ * (c.errorBound : ℝ) * ‖jH‖) := by
  have hb := applied_error _ _ _ (c.inverse_error A h D hD) B jH
  refine ⟨hb.nonneg, ?_⟩
  change dist (jL - _) (jL - _) ≤ _
  rw [dist_sub_left]
  exact hb.bound

/-- Reconstruction retains the actual heavy source and light configuration. -/
theorem reconstruction_error (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : ‖D - A.realize‖ ≤ (c.modelRadius : ℝ))
    (L : Matrix (Fin l) (Fin l) ℂ) (B : Matrix (Fin l) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin l) ℂ) (x : Fin l → ℂ) (jH : Fin n → ℂ) :
    ErrorCertificate ((system A c h D hD L B C).reconstruct x jH)
      (c.inverse.realize.mulVec (jH - C.mulVec x))
      ((c.errorBound : ℝ) * ‖jH - C.mulVec x‖) :=
  vector_error _ _ _ (c.inverse_error A h D hD) _

/-- Effective probes must be transformed together with the operator. -/
theorem readout_error (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : ‖D - A.realize‖ ≤ (c.modelRadius : ℝ))
    (L : Matrix (Fin l) (Fin l) ℂ) (B : Matrix (Fin l) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin l) ℂ) (OL : Matrix (Fin o) (Fin l) ℂ)
    (OH : Matrix (Fin o) (Fin n) ℂ) :
    ErrorCertificate ((system A c h D hD L B C).effectiveReadout OL OH)
      (OL - OH * c.inverse.realize * C) (‖OH‖ * (c.errorBound : ℝ) * ‖C‖) := by
  have hb := sandwich_error _ _ _ (c.inverse_error A h D hD) OH C
  refine ⟨hb.nonneg, ?_⟩
  change dist (OL - _) (OL - _) ≤ _
  rw [dist_sub_left]
  exact hb.bound

/-- Probe offsets generated by a heavy source have the same certified error. -/
theorem readout_offset_error (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : ‖D - A.realize‖ ≤ (c.modelRadius : ℝ))
    (L : Matrix (Fin l) (Fin l) ℂ) (B : Matrix (Fin l) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin l) ℂ) (OH : Matrix (Fin o) (Fin n) ℂ) (jH : Fin n → ℂ) :
    ErrorCertificate ((system A c h D hD L B C).readoutOffset OH jH)
      ((OH * c.inverse.realize).mulVec jH) (‖OH‖ * (c.errorBound : ℝ) * ‖jH‖) :=
  applied_error _ _ _ (c.inverse_error A h D hD) OH jH

end LeanPhy.Mathematics.CertifiedElimination
