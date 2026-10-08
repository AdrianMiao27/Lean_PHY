import LeanPhy.FieldTheory.HeavyFieldMatching
import LeanPhy.FieldTheory.IntervalAction
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false

/-!
# Propagating-heavy matching on actual smooth profiles

The differential expressions are evaluated on the same smooth light profiles
and integrated over an actual interval. The matching identity retains endpoint
flux and the finite-order equation residual. Stationarity of the heavy action
follows from its derived first variation, with boundary conditions explicit.
No actual Green function, boundary-value solution or loop determinant is assumed
to have been constructed by a formal inverse expansion.
-/

namespace LeanPhy.FieldTheory.PropagatingHeavy.Interval

open LeanPhy.Mathematics
open scoped BigOperators ContDiff

variable {Field H : Type*} [Fintype H] [DecidableEq H]

abbrev ProfilePolynomial (Field : Type*) := JetPolynomial ℝ Field Unit

variable (φ : Field → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))

@[simp] theorem evaluate_smul (s t : ℝ) (P : ProfilePolynomial Field) :
    CurveJet.evaluate φ t (s • P) = s * CurveJet.evaluate φ t P := by
  simp [CurveJet.evaluate]

include hφ in
theorem continuous_evaluate (P : ProfilePolynomial Field) :
    Continuous (fun t => CurveJet.evaluate φ t P) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (CurveJet.hasDerivAt_evaluate φ hφ P t).continuousAt)

/-- Integration is a proved real-linear operation on the evaluated jet algebra. -/
noncomputable def integral (a b : ℝ) : ProfilePolynomial Field →ₗ[ℝ] ℝ where
  toFun P := ∫ t in a..b, CurveJet.evaluate φ t P
  map_add' P Q := by
    simp only [map_add]
    exact intervalIntegral.integral_add
      ((continuous_evaluate φ hφ P).intervalIntegrable a b)
      ((continuous_evaluate φ hφ Q).intervalIntegrable a b)
  map_smul' s P := by
    simp only [RingHom.id_apply, evaluate_smul, smul_eq_mul]
    exact intervalIntegral.integral_const_mul s _

theorem integral_derivative (a b : ℝ) (P : ProfilePolynomial Field) :
    integral φ hφ a b (JetPolynomial.totalDerivative () P) =
      CurveJet.evaluate φ b P - CurveJet.evaluate φ a P :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => CurveJet.hasDerivAt_evaluate φ hφ P t)
    ((continuous_evaluate φ hφ _).intervalIntegrable a b)

variable (M : Model (ProfilePolynomial Field) H Unit)
variable (hδ : M.derivative () = JetPolynomial.totalDerivative ())

include hφ hδ

theorem integral_divergence (a b : ℝ) (B : Unit → ProfilePolynomial Field) :
    integral φ hφ a b (M.divergence B) =
      CurveJet.evaluate φ b (B ()) - CurveJet.evaluate φ a (B ()) := by
  simp only [Model.divergence, Fintype.sum_unique, hδ]
  exact integral_derivative φ hφ a b (B ())

noncomputable def action (ε a b : ℝ) (V : ProfilePolynomial Field)
    (J χ : H → ProfilePolynomial Field) : ℝ :=
  integral φ hφ a b (M.density ε V J χ)

noncomputable def effectiveAction (ε : ℝ) (N : ℕ) (a b : ℝ)
    (V : ProfilePolynomial Field) (J : H → ProfilePolynomial Field) : ℝ :=
  integral φ hφ a b (M.effective ε N V J)

/-- The actual local density equals the explicitly differentiated kinetic energy. -/
theorem evaluate_density (ε : ℝ) (V : ProfilePolynomial Field)
    (J χ : H → ProfilePolynomial Field) (t : ℝ) :
    CurveJet.evaluate φ t (M.density ε V J χ) = CurveJet.evaluate φ t V +
      (1 / 2 : ℝ) * ((∑ i, ∑ j,
        (M.mass : Matrix H H ℝ) i j * CurveJet.evaluate φ t (χ i) * CurveJet.evaluate φ t (χ j)) +
        ε * (∑ i, ∑ j, CurveJet.evaluate φ t (M.coupling i j () ()) *
          deriv (fun x => CurveJet.evaluate φ x (χ i)) t *
          deriv (fun x => CurveJet.evaluate φ x (χ j)) t)) +
      ∑ i, CurveJet.evaluate φ t (χ i) * CurveJet.evaluate φ t (J i) := by
  simp only [Model.density, Model.gradientPair, pair, Model.massOperator, massUnit_val,
    massMap_apply, gradientFlux, Fintype.sum_unique, hδ, map_add, evaluate_smul,
    map_sum, map_mul, CurveJet.evaluate_totalDerivative φ hφ,
    Finset.mul_sum]
  simp only [mul_assoc, mul_left_comm, mul_comm]

/-- The constructed kinetic operator really is the derivative of its flux. -/
theorem evaluate_residual (ε : ℝ) (J χ : H → ProfilePolynomial Field) (i : H) (t : ℝ) :
    CurveJet.evaluate φ t (M.residual ε J χ i) =
      (∑ j, (M.mass : Matrix H H ℝ) i j * CurveJet.evaluate φ t (χ j)) -
      ε * deriv (fun x => ∑ j, CurveJet.evaluate φ x (M.coupling i j () ()) *
        deriv (fun y => CurveJet.evaluate φ y (χ j)) x) t + CurveJet.evaluate φ t (J i) := by
  simp only [Model.residual, equation, operator, LinearMap.sub_apply,
    LinearMap.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Model.massOperator, massUnit_val, massMap_apply, Model.kineticOperator,
    kinetic_apply, Fintype.sum_unique, hδ, map_add, map_sub, evaluate_smul, map_sum,
    CurveJet.evaluate_totalDerivative φ hφ]
  congr 2
  apply congrArg (fun f : ℝ → ℝ => ε * deriv f t)
  funext x
  simp only [gradientFlux, Fintype.sum_unique, map_sum, map_mul, hδ,
    CurveJet.evaluate_totalDerivative φ hφ]

theorem action_matching (ε : ℝ) (N : ℕ) (a b : ℝ) (V : ProfilePolynomial Field)
    (J : H → ProfilePolynomial Field) :
    action φ hφ M ε a b V J (M.field ε N J) = effectiveAction φ hφ M ε N a b V J +
      (1 / 2 : ℝ) * integral φ hφ a b (pair (M.field ε N J) (M.residual ε J (M.field ε N J))) +
      (ε / 2) * (CurveJet.evaluate φ b (M.flux (M.field ε N J) (M.field ε N J) ()) -
        CurveJet.evaluate φ a (M.flux (M.field ε N J) (M.field ε N J) ())) := by
  unfold action effectiveAction
  rw [M.density_matching]
  simp only [map_add, map_smul, smul_eq_mul, integral_divergence φ hφ M hδ]

omit hδ in
/-- Source matching keeps both mixed terms and the quadratic source contact term. -/
theorem effectiveAction_source_shift (ε s : ℝ) (N : ℕ) (a b : ℝ)
    (V : ProfilePolynomial Field) (J Q : H → ProfilePolynomial Field) :
    effectiveAction φ hφ M ε N a b V (J + s • Q) =
      effectiveAction φ hφ M ε N a b V J +
      (s / 2) * integral φ hφ a b (pair (M.field ε N J) Q + pair (M.field ε N Q) J) +
      (s ^ 2 / 2) * integral φ hφ a b (pair (M.field ε N Q) Q) := by
  unfold effectiveAction
  rw [M.effective_source_shift]
  simp only [map_add, map_smul, smul_eq_mul]

/-- A uniform bound on the computed residual pairing and a separate endpoint
budget control the difference between substituted and matched actions. This
does not assert proximity to an unsupplied exact boundary-value solution. -/
theorem action_error (ε : ℝ) (N : ℕ) (a b : ℝ) (V : ProfilePolynomial Field)
    (J : H → ProfilePolynomial Field) (ρ β : ℝ)
    (hR : ∀ t ∈ Set.uIcc a b, ErrorCertificate
      (CurveJet.evaluate φ t (pair (M.field ε N J) (M.residual ε J (M.field ε N J)))) 0 ρ)
    (hB : ErrorCertificate
      (CurveJet.evaluate φ b (M.flux (M.field ε N J) (M.field ε N J) ()))
      (CurveJet.evaluate φ a (M.flux (M.field ε N J) (M.field ε N J) ())) β) :
    ErrorCertificate (action φ hφ M ε a b V J (M.field ε N J))
      (effectiveAction φ hφ M ε N a b V J) ((ρ * |b - a| + |ε| * β) / 2) := by
  have hρ := (hR a Set.left_mem_uIcc).nonneg
  have hβ := hB.nonneg
  have hi : |integral φ hφ a b (pair (M.field ε N J) (M.residual ε J (M.field ε N J)))| ≤
      ρ * |b - a| := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := ρ)
      (f := fun t => CurveJet.evaluate φ t
        (pair (M.field ε N J) (M.residual ε J (M.field ε N J)))) (fun t ht => by
          simpa only [Real.norm_eq_abs, Real.dist_eq, sub_zero] using
            (hR t (Set.uIoc_subset_uIcc ht)).bound)
    simpa only [integral, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs] using h
  refine ⟨by positivity, ?_⟩
  rw [Real.dist_eq, action_matching φ hφ M hδ]
  have hb := hB.bound
  rw [Real.dist_eq] at hb
  rw [show effectiveAction φ hφ M ε N a b V J +
      (1 / 2 : ℝ) * integral φ hφ a b (pair (M.field ε N J) (M.residual ε J (M.field ε N J))) +
      (ε / 2) * (CurveJet.evaluate φ b (M.flux (M.field ε N J) (M.field ε N J) ()) -
        CurveJet.evaluate φ a (M.flux (M.field ε N J) (M.field ε N J) ())) -
      effectiveAction φ hφ M ε N a b V J =
      (1 / 2 : ℝ) * integral φ hφ a b (pair (M.field ε N J) (M.residual ε J (M.field ε N J))) +
      (ε / 2) * (CurveJet.evaluate φ b (M.flux (M.field ε N J) (M.field ε N J) ()) -
        CurveJet.evaluate φ a (M.flux (M.field ε N J) (M.field ε N J) ())) by ring]
  calc
    _ ≤ |(1 / 2 : ℝ) * integral φ hφ a b
          (pair (M.field ε N J) (M.residual ε J (M.field ε N J)))| +
        |(ε / 2) * (CurveJet.evaluate φ b (M.flux (M.field ε N J) (M.field ε N J) ()) -
          CurveJet.evaluate φ a (M.flux (M.field ε N J) (M.field ε N J) ()))| := abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) * (ρ * |b - a|) + (|ε| / 2) * β := by
      norm_num only [abs_mul, abs_div, abs_one, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left hi (by norm_num))
        (mul_le_mul_of_nonneg_left hb (by positivity))
    _ = _ := by ring

/-- Actual derivative with respect to a heavy-field variation parameter. -/
theorem hasDerivAt_action (ε a b : ℝ) (V : ProfilePolynomial Field)
    (J χ η : H → ProfilePolynomial Field) :
    HasDerivAt (fun s : ℝ => action φ hφ M ε a b V J (χ + s • η))
      (integral φ hφ a b (pair η (M.residual ε J χ)) +
        ε * (CurveJet.evaluate φ b (M.flux η χ ()) - CurveJet.evaluate φ a (M.flux η χ ()))) 0 := by
  have hexp (s : ℝ) : action φ hφ M ε a b V J (χ + s • η) =
      action φ hφ M ε a b V J χ + s *
        (integral φ hφ a b (pair η (M.residual ε J χ)) +
          ε * (CurveJet.evaluate φ b (M.flux η χ ()) - CurveJet.evaluate φ a (M.flux η χ ()))) +
        (s ^ 2 / 2) * integral φ hφ a b
          (pair η ((M.massOperator : Module.End ℝ (H → ProfilePolynomial Field)) η) +
            ε • M.gradientPair η η) := by
    unfold action
    rw [M.density_perturb]
    simp only [map_add, map_smul, smul_eq_mul, integral_divergence φ hφ M hδ]
  simp_rw [hexp]
  convert! (((hasDerivAt_id (0 : ℝ)).mul_const _).const_add _).add
    ((((hasDerivAt_id (0 : ℝ)).pow 2).div_const 2).mul_const _) using 1
  simp

/-- A derived heavy equation implies stationarity only with matching endpoint flux. -/
theorem stationary_of_equation (ε a b : ℝ) (V : ProfilePolynomial Field)
    (J χ η : H → ProfilePolynomial Field)
    (hE : ∀ t ∈ Set.uIcc a b, ∀ i, CurveJet.evaluate φ t (M.residual ε J χ i) = 0)
    (hboundary : CurveJet.evaluate φ b (M.flux η χ ()) = CurveJet.evaluate φ a (M.flux η χ ())) :
    HasDerivAt (fun s : ℝ => action φ hφ M ε a b V J (χ + s • η)) 0 0 := by
  have hz : integral φ hφ a b (pair η (M.residual ε J χ)) = 0 := by
    change (∫ t in a..b, CurveJet.evaluate φ t (pair η (M.residual ε J χ))) = 0
    calc
      _ = ∫ _ in a..b, (0 : ℝ) := intervalIntegral.integral_congr (fun t ht => by
        simp [pair, hE t ht])
      _ = 0 := by simp
  simpa [hz, hboundary] using hasDerivAt_action φ hφ M hδ ε a b V J χ η

end LeanPhy.FieldTheory.PropagatingHeavy.Interval
