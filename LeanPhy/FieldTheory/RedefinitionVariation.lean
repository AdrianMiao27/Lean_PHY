import LeanPhy.FieldTheory.TransformationEvaluation

/-!
# Field redefinitions, Euler terms and endpoint flux

For a point change `phi -> phi + s P(phi)`, differentiate the actual pulled-back
interval action. The result contains the Euler bulk integral and both endpoint
fluxes. On-shell stationarity requires their equality. This is a derivative at
zero, not equality at finite s, an all-order EFT redundancy, or an S-matrix theorem.
-/

set_option autoImplicit false

namespace LeanPhy.FieldTheory.PointTransformation

open FirstOrderLagrangian
open LeanPhy.Mathematics.PolynomialEvaluation
open scoped BigOperators ContDiff

variable {Old New Dir E : Type*} [Fintype Old] [Fintype New] [Fintype Dir]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def infinitesimal (P : New → MvPolynomial New ℝ) (s : ℝ) (b : New) :
    MvPolynomial New ℝ := MvPolynomial.X b + MvPolynomial.C s * P b

omit [Fintype Old] [Fintype Dir] [Fintype New] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem transformed_infinitesimal (P : New → MvPolynomial New ℝ) (s : ℝ)
    (ψ : New → E → ℝ) :
    transformed (infinitesimal P s) ψ = FieldEvaluation.perturb ψ (transformed P ψ) s := by
  funext b x
  simp [transformed, infinitesimal, FieldEvaluation.perturb]

omit [Fintype Old] [Fintype Dir] in
theorem action_infinitesimal (P : New → MvPolynomial New ℝ) (s : ℝ)
    (L : FirstOrderLagrangian ℝ New Unit) (ψ : New → ℝ → ℝ)
    (hψ : ∀ b x, DifferentiableAt ℝ (ψ b) x) (a b : ℝ) :
    IntervalAction.action (pullback (infinitesimal P s) L) ψ a b =
      IntervalAction.action L (FieldEvaluation.perturb ψ (transformed P ψ) s) a b := by
  rw [action_pullback (infinitesimal P s) L ψ hψ a b, transformed_infinitesimal]

omit [Fintype Old] [Fintype Dir] in
theorem action_infinitesimal_derivative (P : New → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ New Unit) (ψ : New → ℝ → ℝ)
    (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (a b : ℝ) :
    HasDerivAt (fun s => IntervalAction.action (pullback (infinitesimal P s) L) ψ a b)
      ((∫ t in a..b, IntervalAction.bulk L ψ (transformed P ψ) t) +
        (IntervalAction.endpoint L ψ (transformed P ψ) b -
          IntervalAction.endpoint L ψ (transformed P ψ) a)) 0 := by
  have hdiff (j : New) (x : ℝ) : DifferentiableAt ℝ (ψ j) x :=
    (hψ j).differentiable (by norm_num) |>.differentiableAt
  simp_rw [action_infinitesimal P _ L ψ hdiff]
  simpa only [add_sub_assoc] using
    IntervalAction.hasDerivAt_action_boundary L ψ (transformed P ψ) hψ
      (fun j => transformed_contDiff P ψ 1 (fun k => (hψ k).of_le (by norm_num)) j) a b

omit [Fintype Old] [Fintype Dir] in
theorem action_infinitesimal_on_shell (P : New → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ New Unit) (ψ : New → ℝ → ℝ)
    (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (a b : ℝ)
    (hboundary : IntervalAction.endpoint L ψ (transformed P ψ) b =
      IntervalAction.endpoint L ψ (transformed P ψ) a)
    (hE : ∀ t ∈ Set.uIcc a b, ∀ i,
      FieldEvaluation.euler L IntervalAction.direction ψ i t = 0) :
    HasDerivAt (fun s => IntervalAction.action (pullback (infinitesimal P s) L) ψ a b) 0 0 := by
  have hz : (∫ t in a..b, IntervalAction.bulk L ψ (transformed P ψ) t) = 0 := by
    calc
      _ = ∫ t in a..b, (0 : ℝ) := intervalIntegral.integral_congr
        (fun t ht => by simp [IntervalAction.bulk, hE t ht])
      _ = 0 := by simp
  simpa only [hz, hboundary, sub_self, add_zero] using
    action_infinitesimal_derivative P L ψ hψ a b

end LeanPhy.FieldTheory.PointTransformation
