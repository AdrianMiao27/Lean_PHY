import LeanPhy.Minimal
import Mathlib.Tactic

namespace LeanPhy.HighEnergy

open scoped BigOperators
open LeanPhy.Mathematics

/-- A dimensionless low-energy expansion parameter.  The inequalities are
stored in the type so power-counting theorems cannot silently use an invalid
energy hierarchy. -/
structure ExpansionParameter where
  value : ℝ
  nonneg : 0 ≤ value
  le_one : value ≤ 1

/-- A finite effective field-theory expansion.  `dimension` is the relative
power of the expansion parameter and `coefficientBound` is a uniform bound on
Wilson coefficients.  This is an algebraic/truncated object; it does not
assert existence of a continuum EFT or a UV completion. -/
structure FiniteEFT (ι : Type*) [Fintype ι] where
  order : ι → ℕ
  coefficient : ι → ℝ
  coefficientBound : ℝ
  coefficientBound_nonneg : 0 ≤ coefficientBound
  coefficient_abs_le : ∀ i, |coefficient i| ≤ coefficientBound

namespace FiniteEFT

variable {ι : Type*} [Fintype ι]

/-- The contribution of one Wilson operator at expansion parameter `ε`. -/
def contribution (E : ExpansionParameter) (T : FiniteEFT ι) (i : ι) : ℝ :=
  T.coefficient i * E.value ^ T.order i

/-- The complete finite expansion at `ε`.  The index type is finite by design;
    no infinite series or convergence statement is hidden in this definition. -/
def amplitude (E : ExpansionParameter) (T : FiniteEFT ι) : ℝ :=
  ∑ i, T.contribution E i

/-- The part retained by a chosen truncation set. -/
def retainedAmplitude (E : ExpansionParameter) (T : FiniteEFT ι)
    (S : Finset ι) : ℝ :=
  ∑ i ∈ S, T.contribution E i

/-- The finite sum of terms selected as a truncation tail.  In a complete
    truncation certificate this is normally `Finset.univ \ S`, but keeping the
    set explicit also supports sector-by-sector estimates. -/
def tailAmplitude (E : ExpansionParameter) (T : FiniteEFT ι)
    (S : Finset ι) : ℝ :=
  ∑ i ∈ S, T.contribution E i

theorem amplitude_decomposition (E : ExpansionParameter) (T : FiniteEFT ι)
    [DecidableEq ι]
    (S : Finset ι) :
    T.amplitude E = T.tailAmplitude E (Finset.univ \ S) +
      T.retainedAmplitude E S := by
  classical
  have h := Finset.sum_sdiff (s₁ := S) (s₂ := Finset.univ)
    (f := fun i => T.contribution E i) (Finset.subset_univ S)
  simpa [amplitude, retainedAmplitude, tailAmplitude, add_comm] using h

/-- One operator above a cutoff is suppressed by the cutoff power. -/
theorem contribution_abs_bound (E : ExpansionParameter) (T : FiniteEFT ι)
    (cutoff : ℕ) (i : ι) (horder : cutoff ≤ T.order i) :
    |T.contribution E i| ≤ T.coefficientBound * E.value ^ cutoff := by
  rw [contribution, abs_mul, abs_of_nonneg (pow_nonneg E.nonneg _)]
  calc
    |T.coefficient i| * E.value ^ T.order i ≤
        T.coefficientBound * E.value ^ T.order i :=
      mul_le_mul_of_nonneg_right (T.coefficient_abs_le i)
        (pow_nonneg E.nonneg _)
    _ ≤ T.coefficientBound * E.value ^ cutoff := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one E.nonneg E.le_one horder)
        T.coefficientBound_nonneg

/-- A finite EFT tail has an explicit, kernel-checked power-counting bound. -/
theorem tail_bound (E : ExpansionParameter) (T : FiniteEFT ι)
    (S : Finset ι) (cutoff : ℕ)
    (horder : ∀ i ∈ S, cutoff ≤ T.order i) :
    |T.tailAmplitude E S| ≤
      (S.card : ℝ) * T.coefficientBound * E.value ^ cutoff := by
  classical
  calc
    |T.tailAmplitude E S| ≤
        ∑ i ∈ S, |T.contribution E i| := by
      simpa [tailAmplitude] using
        (Finset.abs_sum_le_sum_abs (fun i => T.contribution E i) S)
    _ ≤ ∑ _i ∈ S, T.coefficientBound * E.value ^ cutoff := by
      apply Finset.sum_le_sum
      intro i hi
      exact T.contribution_abs_bound E cutoff i (horder i hi)
    _ = S.card • (T.coefficientBound * E.value ^ cutoff) := by
      rw [Finset.sum_const]
    _ = (S.card : ℝ) * T.coefficientBound * E.value ^ cutoff := by
      simp [nsmul_eq_mul]
      ring

/-- A truncation estimate in the common error-certificate interface.  The
    omitted set is explicit, so this theorem does not assert that a finite
    expansion approximates an infinite or continuum object. -/
theorem truncation_error_certificate (E : ExpansionParameter) (T : FiniteEFT ι)
    [DecidableEq ι]
    (S : Finset ι) (cutoff : ℕ)
    (horder : ∀ i ∈ Finset.univ \ S, cutoff ≤ T.order i) :
    ErrorCertificate (T.amplitude E) (T.retainedAmplitude E S)
      (((Finset.univ \ S).card : ℝ) * T.coefficientBound * E.value ^ cutoff) := by
  classical
  refine ⟨?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) T.coefficientBound_nonneg)
      (pow_nonneg E.nonneg _)
  rw [dist_eq_norm]
  rw [T.amplitude_decomposition E S]
  simpa [add_sub_cancel_right, Real.norm_eq_abs] using
    T.tail_bound E (Finset.univ \ S) cutoff horder

/-- A uniform coefficient-matching certificate for a finite operator basis. -/
structure MatchingCertificate (ι : Type*) [Fintype ι] where
  uvCoefficient : ι → ℝ
  irCoefficient : ι → ℝ
  uniformError : ℝ
  uniformError_nonneg : 0 ≤ uniformError
  coefficient_error : ∀ i, |uvCoefficient i - irCoefficient i| ≤ uniformError

namespace MatchingCertificate

variable {ι : Type*} [Fintype ι]

/-- An observable obtained by weighting the coefficients in a finite basis. -/
def observable (coeff weights : ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ i ∈ S, weights i * coeff i

/-- The observable error induced by matching coefficients is bounded by the
basis size, the observable weights, and the uniform matching error. -/
theorem weighted_error_bound (M : MatchingCertificate ι)
    (weights : ι → ℝ) (S : Finset ι) (weightBound : ℝ)
    (weightBound_nonneg : 0 ≤ weightBound)
    (weight_abs_le : ∀ i ∈ S, |weights i| ≤ weightBound) :
    |∑ i ∈ S, weights i * (M.uvCoefficient i - M.irCoefficient i)| ≤
      (S.card : ℝ) * weightBound * M.uniformError := by
  classical
  calc
    |∑ i ∈ S, weights i * (M.uvCoefficient i - M.irCoefficient i)| ≤
        ∑ i ∈ S, |weights i * (M.uvCoefficient i - M.irCoefficient i)| := by
      simpa using (Finset.abs_sum_le_sum_abs
        (fun i => weights i * (M.uvCoefficient i - M.irCoefficient i)) S)
    _ ≤ ∑ _i ∈ S, weightBound * M.uniformError := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      calc
        |weights i| * |M.uvCoefficient i - M.irCoefficient i| ≤
            weightBound * |M.uvCoefficient i - M.irCoefficient i| :=
          mul_le_mul_of_nonneg_right (weight_abs_le i hi) (abs_nonneg _)
        _ ≤ weightBound * M.uniformError :=
          mul_le_mul_of_nonneg_left (M.coefficient_error i) weightBound_nonneg
    _ = S.card • (weightBound * M.uniformError) := by
      rw [Finset.sum_const]
    _ = (S.card : ℝ) * weightBound * M.uniformError := by
      simp [nsmul_eq_mul]
      ring

/-- The coefficient matching bound as a reusable approximation certificate. -/
theorem error_certificate (M : MatchingCertificate ι)
    (weights : ι → ℝ) (S : Finset ι) (weightBound : ℝ)
    (weightBound_nonneg : 0 ≤ weightBound)
    (weight_abs_le : ∀ i ∈ S, |weights i| ≤ weightBound) :
    ErrorCertificate (observable M.uvCoefficient weights S)
      (observable M.irCoefficient weights S)
      ((S.card : ℝ) * weightBound * M.uniformError) := by
  classical
  refine ⟨?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) weightBound_nonneg)
      M.uniformError_nonneg
  rw [dist_eq_norm]
  change |observable M.uvCoefficient weights S -
    observable M.irCoefficient weights S| ≤ _
  rw [observable, observable, ← Finset.sum_sub_distrib]
  simpa [mul_sub] using M.weighted_error_bound weights S weightBound
    weightBound_nonneg weight_abs_le

end MatchingCertificate
end FiniteEFT
end LeanPhy.HighEnergy
