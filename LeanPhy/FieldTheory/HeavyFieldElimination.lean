import LeanPhy.FieldTheory.PolynomialAction
import LeanPhy.FieldTheory.FiniteActionResponse

set_option autoImplicit false

/-!
# Algebraic heavy-field elimination in polynomial actions

A heavy auxiliary field χ has action `V(φ) + m χ²/2 + χ J(φ)` with nonzero m.
V and J are arbitrary polynomials in any light-field type. Substitution of
the solved heavy equation gives the effective action `V - J²/(2m)` and induces
operators from every inserted polynomial. This is tree-level elimination of
an algebraic field: propagating heavy fields require a derivative expansion,
and a Gaussian functional integral also requires its determinant and measure.
No such omitted contribution is silently asserted to vanish.
-/

namespace LeanPhy.FieldTheory.HeavyFieldElimination

open MvPolynomial

variable {Field : Type*}

noncomputable def liftLight : MvPolynomial Field ℝ →ₐ[ℝ] MvPolynomial (Option Field) ℝ :=
  rename some

noncomputable def action (m : ℝ) (V J : MvPolynomial Field ℝ) :
    MvPolynomial (Option Field) ℝ :=
  liftLight V + C (m / 2) * X none ^ 2 + X none * liftLight J

noncomputable def effective (m : ℝ) (V J : MvPolynomial Field ℝ) :
    MvPolynomial Field ℝ := V - C ((2 * m)⁻¹) * J ^ 2

/-- The same algebra homomorphism acts on the action and every observable. -/
noncomputable def eliminate (m : ℝ) (J : MvPolynomial Field ℝ) :
    MvPolynomial (Option Field) ℝ →ₐ[ℝ] MvPolynomial Field ℝ :=
  aeval (fun i => match i with | none => -C m⁻¹ * J | some a => X a)

@[simp] theorem eliminate_liftLight (m : ℝ) (J P : MvPolynomial Field ℝ) :
    eliminate m J (liftLight P) = P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [eliminate, liftLight]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [liftLight, eliminate] at hp ⊢; rw [hp]

@[simp] theorem heavy_derivative_liftLight (P : MvPolynomial Field ℝ) :
    pderiv none (liftLight P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [liftLight]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [liftLight, Derivation.leibniz, hp, smul_eq_mul] at hp ⊢

theorem heavy_equation (m : ℝ) (V J : MvPolynomial Field ℝ) :
    pderiv none (action m V J) = C m * X none + liftLight J := by
  have hc : (C (m / 2) : MvPolynomial (Option Field) ℝ) * 2 = C m := by
    rw [← map_ofNat C, ← C_mul]
    congr 1
    ring
  simp [action, Derivation.leibniz, smul_eq_mul, pow_two]
  linear_combination X (none : Option Field) * hc

theorem eliminated_heavy_equation (m : ℝ) (hm : m ≠ 0) (V J : MvPolynomial Field ℝ) :
    eliminate m J (pderiv none (action m V J)) = 0 := by
  rw [heavy_equation]
  simp only [map_add, map_mul, eliminate_liftLight]
  simp only [eliminate, aeval_C, aeval_X]
  change C m * (-C m⁻¹ * J) + J = 0
  rw [← mul_assoc, mul_neg, ← C_mul, mul_inv_cancel₀ hm]
  simp

theorem action_eliminated (m : ℝ) (hm : m ≠ 0) (V J : MvPolynomial Field ℝ) :
    eliminate m J (action m V J) = effective m V J := by
  simp only [action, map_add, map_mul, map_pow, eliminate_liftLight]
  simp only [eliminate, aeval_C, aeval_X]
  unfold effective
  change V + C (m / 2) * (-C m⁻¹ * J) ^ 2 + (-C m⁻¹ * J) * J = _
  have hc : C (m / 2) * C m⁻¹ ^ 2 - C m⁻¹ =
      -(C ((2 * m)⁻¹) : MvPolynomial Field ℝ) := by
    rw [← map_pow, ← C_mul, ← C_sub, ← C_neg]
    congr 1
    field_simp
    ring
  linear_combination J ^ 2 * hc

/-- The retained source generates an induced interaction, including its
quadratic contact term; this identity is exact for an algebraic heavy field. -/
theorem effective_source_shift (m h : ℝ) (V J Q : MvPolynomial Field ℝ) :
    effective m V (J + C h * Q) = effective m V J -
      C ((2 * m)⁻¹) * (2 * C h * J * Q + C h ^ 2 * Q ^ 2) := by
  unfold effective
  ring

/-- Effective light equations include the derivative of the induced interaction. -/
theorem effective_derivative (m : ℝ) (V J : MvPolynomial Field ℝ) (a : Field) :
    pderiv a (effective m V J) = pderiv a V - C m⁻¹ * J * pderiv a J := by
  have hc : (C ((2 * m)⁻¹) : MvPolynomial Field ℝ) * 2 = C m⁻¹ := by
    rw [← map_ofNat C, ← C_mul]
    congr 1
    simp [mul_inv_rev]
  simp only [effective, map_sub, Derivation.leibniz, smul_eq_mul, pow_two,
    pderiv_C, mul_zero, zero_mul, zero_add]
  linear_combination -(J * pderiv a J) * hc

/-- The already implemented variational layer consumes the induced action. -/
theorem eulerLagrange_effective {Direction : Type*} [Fintype Direction]
    (m : ℝ) (V J : MvPolynomial Field ℝ) (a : Field) :
    FirstOrderLagrangian.eulerLagrange
      (FirstOrderLagrangian.potential (effective m V J) : FirstOrderLagrangian ℝ Field Direction) a =
      FirstOrderLagrangian.lift (FirstOrderLagrangian.potential
        (pderiv a V - C m⁻¹ * J * pderiv a J)) := by
  rw [FirstOrderLagrangian.eulerLagrange_potential, effective_derivative]

/-- Evaluate any effective observable by evaluating its original expression
on the reconstructed heavy field and the unchanged light fields. -/
theorem eval_eliminate (m : ℝ) (J : MvPolynomial Field ℝ)
    (O : MvPolynomial (Option Field) ℝ) (φ : Field → ℝ) :
    eval φ (eliminate m J O) =
      eval (fun i => match i with | none => -m⁻¹ * eval φ J | some a => φ a) O := by
  induction O using MvPolynomial.induction_on with
  | C r => simp [eliminate]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul]
    rw [hp]
    cases i <;> simp [eliminate]

end LeanPhy.FieldTheory.HeavyFieldElimination
