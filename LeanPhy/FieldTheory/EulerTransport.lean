import LeanPhy.FieldTheory.TransformationEvaluation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

/-!
# Euler equations and variational currents under point field changes

For real commuting fields and a polynomial point map `phi = F(psi)`, the
Euler residual transforms by the transpose Jacobian. The Hessian terms in
the transformed force cancel the derivatives of the Jacobian in the momentum.
Currents retain the pushed-forward variation. Smoothness is input; neither
field equations nor their transformation law are assumed.

Forward solution transport allows rectangular and singular Jacobians. The
converse requires a pointwise right inverse, so a singular map cannot silently
erase an equation. This is an exact first-order-density statement, not a
derivative-dependent EFT redefinition or a quantum measure equivalence.
-/

namespace LeanPhy.FieldTheory.PointTransformation

open FirstOrderLagrangian
open scoped BigOperators ContDiff

variable {Old New Dir E : Type*} [Fintype Old] [Fintype New] [Fintype Dir]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype Old] [Fintype New] [Fintype Dir] in
theorem pderiv_potential_field (P : MvPolynomial New ℝ) (b : New) :
    MvPolynomial.pderiv (b, none) (potential P : FirstOrderLagrangian ℝ New Dir) =
      potential (MvPolynomial.pderiv b P) := by
  exact MvPolynomial.pderiv_rename
    (f := fun c : New => (c, (none : Option Dir)))
    (fun _ _ h => congrArg Prod.fst h) b P

omit [Fintype Old] [Fintype New] [Fintype Dir] in
theorem pderiv_potential_gradient (P : MvPolynomial New ℝ) (b : New) (μ : Dir) :
    MvPolynomial.pderiv (b, some μ) (potential P : FirstOrderLagrangian ℝ New Dir) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [potential]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P a hP =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, hP, mul_zero, add_zero]
    simp [potential]

omit [Fintype Old] [Fintype New] [Fintype Dir] in
theorem pderiv_swap (P : MvPolynomial New ℝ) (b c : New) :
    MvPolynomial.pderiv b (MvPolynomial.pderiv c P) =
      MvPolynomial.pderiv c (MvPolynomial.pderiv b P) := by
  classical
  have h : ⁅(MvPolynomial.pderiv b : Derivation ℝ (MvPolynomial New ℝ) (MvPolynomial New ℝ)),
      MvPolynomial.pderiv c⁆ =
      (0 : Derivation ℝ (MvPolynomial New ℝ) (MvPolynomial New ℝ)) := by
    apply MvPolynomial.derivation_ext
    intro i
    simp [Derivation.commutator_apply, MvPolynomial.pderiv_X, Pi.single_apply,
      apply_ite]
  have he := congrArg (fun D : Derivation ℝ (MvPolynomial New ℝ) (MvPolynomial New ℝ) => D P) h
  simpa only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] using he

omit [Fintype Old] [Fintype Dir] in
theorem pderiv_coordinate_gradient [DecidableEq Dir] (F : Old → MvPolynomial New ℝ)
    (a : Old) (b : New) (μ ν : Dir) :
    MvPolynomial.pderiv (b, some ν) (coordinate F (a, some μ)) =
      if μ = ν then potential (MvPolynomial.pderiv b (F a)) else 0 := by
  classical
  by_cases h : μ = ν <;>
    simp [coordinate, pderiv_potential_gradient, gradient,
      MvPolynomial.pderiv_X, Pi.single_apply, Prod.mk.injEq, h]

omit [Fintype Old] [Fintype Dir] in
theorem pderiv_coordinate_field (F : Old → MvPolynomial New ℝ)
    (a : Old) (b : New) (μ : Dir) :
    MvPolynomial.pderiv (b, none) (coordinate F (a, some μ)) =
      ∑ c, potential (MvPolynomial.pderiv c (MvPolynomial.pderiv b (F a))) *
        gradient c μ := by
  classical
  simp [coordinate, pderiv_potential_field, gradient, pderiv_swap (F a) b, mul_comm]

/-- The evaluated Jacobian, with rows labelled by old fields. -/
noncomputable def jacobian (F : Old → MvPolynomial New ℝ) (ψ : New → E → ℝ)
    (a : Old) (b : New) : E → ℝ :=
  fun x => MvPolynomial.eval (fun c => ψ c x) (MvPolynomial.pderiv b (F a))

/-- Variations are transported with the same Jacobian as the gradients. -/
noncomputable def pushVariation (F : Old → MvPolynomial New ℝ)
    (ψ η : New → E → ℝ) (a : Old) : E → ℝ :=
  fun x => ∑ b, jacobian F ψ a b x * η b x

theorem pderiv_pullback (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Dir) (p : New × Option Dir) :
    MvPolynomial.pderiv p (pullback F L) =
      ∑ q, pullback F (MvPolynomial.pderiv q L) * MvPolynomial.pderiv p (coordinate F q) :=
  pderiv_substitution (coordinate F) L p

theorem value_pderiv_pullback (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Dir) (e : Dir → E)
    (ψ : New → E → ℝ) (x : E) (hψ : ∀ b, DifferentiableAt ℝ (ψ b) x)
    (p : New × Option Dir) :
    FieldEvaluation.value (MvPolynomial.pderiv p (pullback F L)) e ψ x =
      ∑ q, FieldEvaluation.value (MvPolynomial.pderiv q L) e (transformed F ψ) x *
        FieldEvaluation.value (MvPolynomial.pderiv p (coordinate F q)) e ψ x := by
  rw [pderiv_pullback]
  simp only [FieldEvaluation.value, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro q _
  exact congrArg (fun z : ℝ => z * _) (value_pullback F (MvPolynomial.pderiv q L) e ψ x hψ)

omit [Fintype Old] [Fintype Dir] in
theorem jacobian_directional (F : Old → MvPolynomial New ℝ)
    (ψ : New → E → ℝ) (x : E) (hψ : ∀ b, DifferentiableAt ℝ (ψ b) x)
    (a : Old) (b : New) (v : E) :
    FieldEvaluation.directional v (jacobian F ψ a b) x =
      ∑ c, MvPolynomial.eval (fun d => ψ d x)
        (MvPolynomial.pderiv c (MvPolynomial.pderiv b (F a))) *
        FieldEvaluation.directional v (ψ c) x :=
  transformed_derivative (fun _ : Unit => MvPolynomial.pderiv b (F a)) ψ x hψ () v

omit [Fintype Old] [Fintype Dir] in
theorem value_coordinate_field (F : Old → MvPolynomial New ℝ)
    (e : Dir → E) (ψ : New → E → ℝ) (x : E)
    (hψ : ∀ b, DifferentiableAt ℝ (ψ b) x) (a : Old) (b : New) (μ : Dir) :
    FieldEvaluation.value (MvPolynomial.pderiv (b, none) (coordinate F (a, some μ))) e ψ x =
      FieldEvaluation.directional (e μ) (jacobian F ψ a b) x := by
  rw [pderiv_coordinate_field, jacobian_directional F ψ x hψ]
  simp [FieldEvaluation.value, potential, MvPolynomial.eval_rename, gradient,
    FieldEvaluation.coordinates, Function.comp_def]

/-- Momentum covectors pull back with the field Jacobian. -/
theorem momentum_pullback (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Dir) (e : Dir → E)
    (ψ : New → E → ℝ) (x : E) (hψ : ∀ b, DifferentiableAt ℝ (ψ b) x)
    (b : New) (ν : Dir) :
    FieldEvaluation.momentum (pullback F L) e ψ b ν x =
      ∑ a, FieldEvaluation.momentum L e (transformed F ψ) a ν x * jacobian F ψ a b x := by
  classical
  unfold FieldEvaluation.momentum
  rw [value_pderiv_pullback F L e ψ x hψ]
  simp only [Fintype.sum_prod_type, Fintype.sum_option, pderiv_coordinate_gradient]
  simp only [coordinate, Option.elim_none, pderiv_potential_gradient]
  simp [FieldEvaluation.value, apply_ite, potential,
    MvPolynomial.eval_rename, FieldEvaluation.coordinates, jacobian, Function.comp_def]

/-- The transformed force includes Hessian terms; they must not be discarded. -/
theorem force_pullback (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Dir) (e : Dir → E)
    (ψ : New → E → ℝ) (x : E) (hψ : ∀ b, DifferentiableAt ℝ (ψ b) x) (b : New) :
    FieldEvaluation.force (pullback F L) e ψ b x =
      (∑ a, FieldEvaluation.force L e (transformed F ψ) a x * jacobian F ψ a b x) +
      ∑ a, ∑ μ, FieldEvaluation.momentum L e (transformed F ψ) a μ x *
        FieldEvaluation.directional (e μ) (jacobian F ψ a b) x := by
  unfold FieldEvaluation.force
  rw [value_pderiv_pullback F L e ψ x hψ]
  simp only [Fintype.sum_prod_type, Fintype.sum_option,
    value_coordinate_field F e ψ x hψ, Finset.sum_add_distrib]
  simp only [coordinate, Option.elim_none, pderiv_potential_field]
  simp [FieldEvaluation.value, potential,
    MvPolynomial.eval_rename, FieldEvaluation.coordinates, jacobian, Function.comp_def,
    FieldEvaluation.momentum]

omit [Fintype Old] [Fintype New] [Fintype Dir] in
theorem jacobian_contDiff (F : Old → MvPolynomial New ℝ)
    (ψ : New → E → ℝ) (n : ℕ∞ω) (hψ : ∀ b, ContDiff ℝ n (ψ b)) (a : Old) (b : New) :
    ContDiff ℝ n (jacobian F ψ a b) :=
  LeanPhy.Mathematics.PolynomialEvaluation.contDiff_eval _ ψ n hψ

theorem directional_momentum_pullback (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Dir) (e : Dir → E)
    (ψ : New → E → ℝ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b))
    (x : E) (b : New) (μ : Dir) (v : E) :
    FieldEvaluation.directional v (FieldEvaluation.momentum (pullback F L) e ψ b μ) x =
      ∑ a, (FieldEvaluation.momentum L e (transformed F ψ) a μ x *
          FieldEvaluation.directional v (jacobian F ψ a b) x +
        FieldEvaluation.directional v (FieldEvaluation.momentum L e (transformed F ψ) a μ) x *
          jacobian F ψ a b x) := by
  have hdiff (c : New) (y : E) : DifferentiableAt ℝ (ψ c) y :=
    (hψ c).differentiable (by norm_num) y
  have hmomentum : FieldEvaluation.momentum (pullback F L) e ψ b μ =
      fun y => ∑ a, FieldEvaluation.momentum L e (transformed F ψ) a μ y * jacobian F ψ a b y :=
    funext (fun y => momentum_pullback F L e ψ y (fun c => hdiff c y) b μ)
  rw [hmomentum]
  have hp (a : Old) : DifferentiableAt ℝ (FieldEvaluation.momentum L e (transformed F ψ) a μ) x :=
    (FieldEvaluation.contDiff_value _ e (transformed F ψ) (n := 1)
      (transformed_contDiff F ψ 2 hψ)).differentiable (by norm_num) x
  have hj (a : Old) : DifferentiableAt ℝ (jacobian F ψ a b) x :=
    (jacobian_contDiff F ψ 2 hψ a b).differentiable (by norm_num) x
  have h := (HasFDerivAt.fun_sum (u := Finset.univ)
    (fun a _ => (hp a).hasFDerivAt.mul (hj a).hasFDerivAt)).fderiv
  have he := congrArg (fun A : E →L[ℝ] ℝ => A v) h
  simpa [FieldEvaluation.directional, mul_comm, add_comm] using! he

/-- Exact Euler covariance, derived from the density and actual derivatives.
No invertibility or field equation is required for this direction. -/
theorem euler_pullback (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Dir) (e : Dir → E)
    (ψ : New → E → ℝ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (x : E) (b : New) :
    FieldEvaluation.euler (pullback F L) e ψ b x =
      ∑ a, FieldEvaluation.euler L e (transformed F ψ) a x * jacobian F ψ a b x := by
  have hdiff (c : New) : DifferentiableAt ℝ (ψ c) x :=
    (hψ c).differentiable (by norm_num) x
  simp only [FieldEvaluation.euler, force_pullback F L e ψ x hdiff,
    directional_momentum_pullback F L e ψ hψ,
    Finset.sum_add_distrib, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun μ a =>
    FieldEvaluation.momentum L e (transformed F ψ) a μ x *
      FieldEvaluation.directional (e μ) (jacobian F ψ a b) x),
    Finset.sum_comm (f := fun μ a =>
      FieldEvaluation.directional (e μ) (FieldEvaluation.momentum L e (transformed F ψ) a μ) x *
        jacobian F ψ a b x)]
  ring

/-- The full variational boundary current transports with the variation. -/
theorem boundary_pullback (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Dir) (e : Dir → E)
    (ψ η : New → E → ℝ) (x : E) (hψ : ∀ b, DifferentiableAt ℝ (ψ b) x) (μ : Dir) :
    FieldEvaluation.boundary (pullback F L) e ψ η μ x =
      FieldEvaluation.boundary L e (transformed F ψ) (pushVariation F ψ η) μ x := by
  unfold FieldEvaluation.boundary pushVariation
  simp_rw [momentum_pullback F L e ψ x hψ]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [Fintype Old] [Fintype Dir] in
theorem pushVariation_differentiableAt (F : Old → MvPolynomial New ℝ)
    (ψ η : New → E → ℝ) (x : E)
    (hψ : ∀ b, DifferentiableAt ℝ (ψ b) x)
    (hη : ∀ b, DifferentiableAt ℝ (η b) x) (a : Old) :
    DifferentiableAt ℝ (pushVariation F ψ η a) x := by
  apply DifferentiableAt.fun_sum
  intro b _
  apply DifferentiableAt.mul _ (hη b)
  exact (LeanPhy.Mathematics.PolynomialEvaluation.hasFDerivAt_eval
    (MvPolynomial.pderiv b (F a)) ψ (fun c => fderiv ℝ (ψ c) x) x
    (fun c => (hψ c).hasFDerivAt)).differentiableAt

/-- The actual first variation agrees after pushing forward the variation. -/
theorem variation_pullback (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Dir) (e : Dir → E)
    (ψ η : New → E → ℝ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (x : E)
    (hη : ∀ b, DifferentiableAt ℝ (η b) x) :
    FieldEvaluation.variation (pullback F L) e ψ η x =
      FieldEvaluation.variation L e (transformed F ψ) (pushVariation F ψ η) x := by
  have hdiff (b : New) (y : E) : DifferentiableAt ℝ (ψ b) y :=
    (hψ b).differentiable (by norm_num) y
  have hb : FieldEvaluation.boundary (pullback F L) e ψ η =
      FieldEvaluation.boundary L e (transformed F ψ) (pushVariation F ψ η) := by
    funext μ y
    exact boundary_pullback F L e ψ η y (fun b => hdiff b y) μ
  rw [FieldEvaluation.first_variation _ e ψ η x hψ hη,
    FieldEvaluation.first_variation _ e (transformed F ψ) (pushVariation F ψ η) x
      (transformed_contDiff F ψ 2 hψ)
      (pushVariation_differentiableAt F ψ η x (fun b => hdiff b x) hη), hb]
  congr 1
  simp_rw [euler_pullback F L e ψ hψ x]
  simp only [pushVariation, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- A transformed actual solution gives a solution of the pulled-back density,
even when the point map is singular or changes the number of fields. -/
theorem euler_zero_pullback (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Dir) (e : Dir → E)
    (ψ : New → E → ℝ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (x : E)
    (hE : ∀ a, FieldEvaluation.euler L e (transformed F ψ) a x = 0) :
    ∀ b, FieldEvaluation.euler (pullback F L) e ψ b x = 0 := by
  intro b
  simp [euler_pullback F L e ψ hψ x b, hE]

/-- Recover every original equation from the new residuals using a certified
right inverse of the rectangular field Jacobian at the evaluation point. -/
theorem euler_recover [DecidableEq Old] (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Dir) (e : Dir → E)
    (ψ : New → E → ℝ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (x : E)
    (K : New → Old → ℝ)
    (hK : ∀ a c, ∑ b, jacobian F ψ a b x * K b c = if a = c then 1 else 0) (c : Old) :
    FieldEvaluation.euler L e (transformed F ψ) c x =
      ∑ b, FieldEvaluation.euler (pullback F L) e ψ b x * K b c := by
  symm
  simp_rw [euler_pullback F L e ψ hψ x]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, hK]
  simp

theorem euler_zero_iff_of_rightInverse [DecidableEq Old] (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Dir) (e : Dir → E)
    (ψ : New → E → ℝ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (x : E)
    (K : New → Old → ℝ)
    (hK : ∀ a c, ∑ b, jacobian F ψ a b x * K b c = if a = c then 1 else 0) :
    (∀ b, FieldEvaluation.euler (pullback F L) e ψ b x = 0) ↔
      (∀ a, FieldEvaluation.euler L e (transformed F ψ) a x = 0) := by
  constructor
  · intro hE a
    rw [euler_recover F L e ψ hψ x K hK a]
    simp [hE]
  · exact euler_zero_pullback F L e ψ hψ x

/-- Spatial or parameter-dependent solution domains retain the pointwise
right-inverse condition at every point where equivalence is claimed. -/
theorem euler_zero_iff_on_of_rightInverse [DecidableEq Old]
    (F : Old → MvPolynomial New ℝ) (L : FirstOrderLagrangian ℝ Old Dir) (e : Dir → E)
    (ψ : New → E → ℝ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (S : Set E)
    (K : E → New → Old → ℝ)
    (hK : ∀ x ∈ S, ∀ a c, ∑ b, jacobian F ψ a b x * K x b c = if a = c then 1 else 0) :
    (∀ x ∈ S, ∀ b, FieldEvaluation.euler (pullback F L) e ψ b x = 0) ↔
      (∀ x ∈ S, ∀ a, FieldEvaluation.euler L e (transformed F ψ) a x = 0) := by
  constructor <;> intro h x hx
  · exact (euler_zero_iff_of_rightInverse F L e ψ hψ x (K x) (hK x hx)).mp (h x hx)
  · exact (euler_zero_iff_of_rightInverse F L e ψ hψ x (K x) (hK x hx)).mpr (h x hx)

/-- Square-Jacobian data allow the library to construct the right inverse. -/
noncomputable def jacobianMatrix (F : Old → MvPolynomial New ℝ)
    (ψ : New → E → ℝ) (x : E) : Matrix Old New ℝ := fun a b => jacobian F ψ a b x

omit [Fintype Old] in
theorem euler_zero_iff_of_det_ne_zero [DecidableEq New]
    (F : New → MvPolynomial New ℝ) (L : FirstOrderLagrangian ℝ New Dir) (e : Dir → E)
    (ψ : New → E → ℝ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (x : E)
    (hdet : (jacobianMatrix F ψ x).det ≠ 0) :
    (∀ b, FieldEvaluation.euler (pullback F L) e ψ b x = 0) ↔
      (∀ a, FieldEvaluation.euler L e (transformed F ψ) a x = 0) := by
  let K : Matrix New New ℝ := (jacobianMatrix F ψ x)⁻¹
  apply euler_zero_iff_of_rightInverse F L e ψ hψ x K
  intro a c
  have h := congrArg (fun M : Matrix New New ℝ => M a c)
    (Matrix.mul_nonsing_inv (jacobianMatrix F ψ x) (isUnit_iff_ne_zero.mpr hdet))
  simpa [Matrix.mul_apply, Matrix.one_apply, jacobianMatrix, K] using h

omit [Fintype Old] in
theorem euler_zero_iff_on_of_det_ne_zero [DecidableEq New]
    (F : New → MvPolynomial New ℝ) (L : FirstOrderLagrangian ℝ New Dir) (e : Dir → E)
    (ψ : New → E → ℝ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (S : Set E)
    (hdet : ∀ x ∈ S, (jacobianMatrix F ψ x).det ≠ 0) :
    (∀ x ∈ S, ∀ b, FieldEvaluation.euler (pullback F L) e ψ b x = 0) ↔
      (∀ x ∈ S, ∀ a, FieldEvaluation.euler L e (transformed F ψ) a x = 0) := by
  constructor <;> intro h x hx
  · exact (euler_zero_iff_of_det_ne_zero F L e ψ hψ x (hdet x hx)).mp (h x hx)
  · exact (euler_zero_iff_of_det_ne_zero F L e ψ hψ x (hdet x hx)).mpr (h x hx)

omit [Fintype Dir] in
theorem bulk_pullback (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Unit) (ψ η : New → ℝ → ℝ)
    (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (t : ℝ) :
    IntervalAction.bulk (pullback F L) ψ η t =
      IntervalAction.bulk L (transformed F ψ) (pushVariation F ψ η) t := by
  unfold IntervalAction.bulk
  simp_rw [euler_pullback F L IntervalAction.direction ψ hψ t]
  simp only [pushVariation, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [Fintype Dir] in
theorem endpoint_pullback (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Unit) (ψ η : New → ℝ → ℝ)
    (t : ℝ) (hψ : ∀ b, DifferentiableAt ℝ (ψ b) t) :
    IntervalAction.endpoint (pullback F L) ψ η t =
      IntervalAction.endpoint L (transformed F ψ) (pushVariation F ψ η) t :=
  boundary_pullback F L IntervalAction.direction ψ η t hψ ()

omit [Fintype Dir] in
/-- Differentiate the actual pulled-back action and express both bulk and
endpoint terms in the original fields. Finite variations still have higher orders. -/
theorem action_derivative_pullback (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Unit) (ψ η : New → ℝ → ℝ)
    (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (hη : ∀ b, ContDiff ℝ 1 (η b)) (a b : ℝ) :
    HasDerivAt (fun s => IntervalAction.action (pullback F L) (FieldEvaluation.perturb ψ η s) a b)
      ((∫ t in a..b, IntervalAction.bulk L (transformed F ψ) (pushVariation F ψ η) t) +
        IntervalAction.endpoint L (transformed F ψ) (pushVariation F ψ η) b -
        IntervalAction.endpoint L (transformed F ψ) (pushVariation F ψ η) a) 0 := by
  have hdiff (c : New) (t : ℝ) : DifferentiableAt ℝ (ψ c) t :=
    (hψ c).differentiable (by norm_num) t
  have h := IntervalAction.hasDerivAt_action_boundary (pullback F L) ψ η hψ hη a b
  simp_rw [bulk_pullback F L ψ η hψ, endpoint_pullback F L ψ η _ (fun c => hdiff c _)] at h
  exact h

end LeanPhy.FieldTheory.PointTransformation
