import LeanPhy.FieldTheory.EnergyMomentum
import LeanPhy.Mathematics.Approximation

/-!
# Quantitative local current defects from action and equation residuals

A candidate field need not satisfy the Euler equations exactly. Its local
current divergence is controlled by the evaluated Euler residuals, the size of
the symmetry variation, and any explicit symmetry-breaking defect. The output
uses the existing `ErrorCertificate` type, so later approximation stages can
compose the resulting bound. Input bounds must be proved; sampling alone is
not a bound on a whole spacetime region.

This controls a local polynomial expression. Integrated charge drift still
requires an integration theorem, boundary flux control, and a consistent
interpretation of the jet assignment as derivatives of a field.
-/

namespace LeanPhy.FieldTheory.FirstOrderLagrangian

open JetPolynomial LeanPhy.Mathematics
open scoped BigOperators

variable {Field Direction : Type*} [Fintype Field] [Fintype Direction]

/-- Keep the symmetry-breaking defect as well as all equation residuals. -/
theorem noether_balance (L : FirstOrderLagrangian ℝ Field Direction)
    (η : Field → JetPolynomial ℝ Field Direction)
    (B : Direction → JetPolynomial ℝ Field Direction) :
    divergence (noetherCurrent L η B) =
      (firstVariation L η - divergence B) - ∑ a, eulerLagrange L a * η a := by
  have h := first_variation L η
  simp only [divergence, noetherCurrent, map_sub, Finset.sum_sub_distrib]
  unfold divergence at h
  linear_combination -h

/-- Equation and symmetry-breaking residuals propagate into the local current
budget. This does not replace a residual bound with an exact conservation law. -/
theorem noether_residual_certificate
    (L : FirstOrderLagrangian ℝ Field Direction)
    (η : Field → JetPolynomial ℝ Field Direction)
    (B : Direction → JetPolynomial ℝ Field Direction)
    (ev : JetPolynomial ℝ Field Direction →+* ℝ)
    (ε M : Field → ℝ) (δ : ℝ)
    (hE : ∀ a, ErrorCertificate (ev (eulerLagrange L a)) 0 (ε a))
    (hη : ∀ a, |ev (η a)| ≤ M a)
    (hBreaking : ErrorCertificate (ev (firstVariation L η - divergence B)) 0 δ) :
    ErrorCertificate (ev (divergence (noetherCurrent L η B))) 0
      (δ + ∑ a, ε a * M a) := by
  have hM (a : Field) : 0 ≤ M a := (abs_nonneg _).trans (hη a)
  have he (a : Field) : |ev (eulerLagrange L a)| ≤ ε a := by
    simpa [Real.dist_eq] using (hE a).bound
  have hb : |ev (firstVariation L η - divergence B)| ≤ δ := by
    simpa [Real.dist_eq] using hBreaking.bound
  refine ⟨add_nonneg hBreaking.nonneg (Finset.sum_nonneg (fun a _ =>
    mul_nonneg (hE a).nonneg (hM a))), ?_⟩
  rw [Real.dist_eq, sub_zero, noether_balance, map_sub, map_sum]
  calc
    |ev (firstVariation L η - divergence B) - ∑ a, ev (eulerLagrange L a * η a)|
        ≤ |ev (firstVariation L η - divergence B)| + |∑ a, ev (eulerLagrange L a * η a)| :=
      by simpa only [sub_eq_add_neg, abs_neg] using
           (abs_add_le (ev (firstVariation L η - divergence B))
             (-∑ a, ev (eulerLagrange L a * η a)))
    _ ≤ δ + ∑ a, |ev (eulerLagrange L a * η a)| :=
      add_le_add hb (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ δ + ∑ a, ε a * M a := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro a _
      rw [map_mul, abs_mul]
      exact mul_le_mul (he a) (hη a) (abs_nonneg _) (hE a).nonneg

/-- Exact symmetry is the zero-breaking special case; the equations may still
have nonzero certified residuals. -/
theorem noether_residual_of_symmetry
    (L : FirstOrderLagrangian ℝ Field Direction)
    (η : Field → JetPolynomial ℝ Field Direction)
    (B : Direction → JetPolynomial ℝ Field Direction)
    (hSymmetry : firstVariation L η = divergence B)
    (ev : JetPolynomial ℝ Field Direction →+* ℝ) (ε M : Field → ℝ)
    (hE : ∀ a, ErrorCertificate (ev (eulerLagrange L a)) 0 (ε a))
    (hη : ∀ a, |ev (η a)| ≤ M a) :
    ErrorCertificate (ev (divergence (noetherCurrent L η B))) 0
      (∑ a, ε a * M a) := by
  have hBreaking : ErrorCertificate (ev (firstVariation L η - divergence B)) 0 0 := by
    apply ErrorCertificate.of_eq
    simp [hSymmetry]
  simpa using noether_residual_certificate L η B ev ε M 0 hE hη hBreaking

/-- A bound on equation residuals and field gradients controls the local
stress divergence, uniformly for any chosen translation direction. -/
theorem canonicalStressTensor_residual
    (L : FirstOrderLagrangian ℝ Field Direction) (ν : Direction)
    (ev : JetPolynomial ℝ Field Direction →+* ℝ) (ε M : Field → ℝ)
    (hE : ∀ a, ErrorCertificate (ev (eulerLagrange L a)) 0 (ε a))
    (hGradient : ∀ a, |ev (jet a (Finsupp.single ν 1))| ≤ M a) :
    ErrorCertificate (ev (divergence (fun μ => canonicalStressTensor L μ ν))) 0
      (∑ a, ε a * M a) := by
  apply noether_residual_of_symmetry L (translationVariation ν) (translationBoundary L ν)
    _ ev ε M hE hGradient
  rw [firstVariation_translation, divergence_translationBoundary]

end LeanPhy.FieldTheory.FirstOrderLagrangian
