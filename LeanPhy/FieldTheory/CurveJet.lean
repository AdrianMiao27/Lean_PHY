import LeanPhy.FieldTheory.FieldEvaluation
import LeanPhy.FieldTheory.EnergyMomentum
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option autoImplicit false

/-!
# Formal jets interpreted as derivatives of actual profiles

For one coordinate, every formal jet is evaluated at an actual iterated
derivative of the same field. Smooth profiles prove compatibility with total
differentiation for all polynomial jets. This is suitable for time-dependent
finite modes and one-dimensional field profiles. It neither constructs a
solution of the field equations nor discards transverse boundary fluxes.
-/

namespace LeanPhy.FieldTheory.CurveJet

open JetPolynomial
open scoped BigOperators ContDiff

variable {Field : Type*}

noncomputable def evaluate (φ : Field → ℝ → ℝ) (t : ℝ) :
    JetPolynomial ℝ Field Unit →+* ℝ :=
  MvPolynomial.eval (fun p => iteratedDeriv (p.2 ()) (φ p.1) t)

@[simp] theorem evaluate_jet (φ : Field → ℝ → ℝ) (t : ℝ) (a : Field)
    (α : Unit →₀ ℕ) : evaluate φ t (jet a α) = iteratedDeriv (α ()) (φ a) t := by
  simp [evaluate, jet]

/-- Actual smoothness proves the full differential-algebra interpretation. -/
theorem hasDerivAt_evaluate (φ : Field → ℝ → ℝ)
    (hφ : ∀ a, ContDiff ℝ ∞ (φ a)) (P : JetPolynomial ℝ Field Unit) (t : ℝ) :
    HasDerivAt (fun s => evaluate φ s P) (evaluate φ t (totalDerivative () P)) t := by
  induction P using MvPolynomial.induction_on with
  | C r => simpa [evaluate] using (hasDerivAt_const t r)
  | add P Q hP hQ => simpa using! hP.add hQ
  | mul_X P p hP =>
      have hj := ((hφ p.1).differentiable_iteratedDeriv (p.2 ()) (by
        exact_mod_cast (ENat.natCast_lt_top (p.2 ()))) t).hasDerivAt
      have hX : HasDerivAt (fun s => evaluate φ s (MvPolynomial.X p))
          (evaluate φ t (totalDerivative () (MvPolynomial.X p))) t := by
        simpa [evaluate, totalDerivative, jet, iteratedDeriv_succ] using! hj
      simpa [Derivation.leibniz, smul_eq_mul, mul_comm, add_comm] using! hP.mul hX

theorem evaluate_totalDerivative (φ : Field → ℝ → ℝ)
    (hφ : ∀ a, ContDiff ℝ ∞ (φ a)) (P : JetPolynomial ℝ Field Unit) (t : ℝ) :
    evaluate φ t (totalDerivative () P) = deriv (fun s => evaluate φ s P) t :=
  (hasDerivAt_evaluate φ hφ P t).deriv.symm

@[simp] theorem evaluate_lift (L : FirstOrderLagrangian ℝ Field Unit)
    (φ : Field → ℝ → ℝ) (t : ℝ) :
    evaluate φ t (FirstOrderLagrangian.lift L) =
      FieldEvaluation.value L (fun _ => (1 : ℝ)) φ t := by
  simp only [evaluate, FirstOrderLagrangian.lift, MvPolynomial.eval_rename]
  apply congrArg (fun f => MvPolynomial.eval f L)
  funext p
  rcases p with ⟨a, _ | μ⟩
  · simp [FirstOrderLagrangian.jetIndex, FieldEvaluation.coordinates]
  · simp [FirstOrderLagrangian.jetIndex, FieldEvaluation.coordinates,
      FieldEvaluation.directional]

variable [Fintype Field]

omit [Fintype Field] in
/-- The symbolic Euler residual agrees with the analytic Euler residual of
the same action and actual fields; no field equation is assumed. -/
theorem evaluate_eulerLagrange (L : FirstOrderLagrangian ℝ Field Unit)
    (φ : Field → ℝ → ℝ) (hφ : ∀ a, ContDiff ℝ ∞ (φ a)) (a : Field) (t : ℝ) :
    evaluate φ t (FirstOrderLagrangian.eulerLagrange L a) =
      FieldEvaluation.euler L (fun _ => (1 : ℝ)) φ a t := by
  simp only [FirstOrderLagrangian.eulerLagrange, FirstOrderLagrangian.fieldPartial,
    FirstOrderLagrangian.momentum, map_sub, Fintype.sum_unique,
    evaluate_lift, evaluate_totalDerivative φ hφ, FieldEvaluation.euler,
    FieldEvaluation.force, FieldEvaluation.momentum, FieldEvaluation.directional,
    fderiv_apply_one_eq_deriv, evaluate_lift]

/-- A formal Noether symmetry and actual Euler equations imply an actual
zero derivative of the evaluated current, not just a formal divergence. -/
theorem noether_hasDerivAt_zero (L : FirstOrderLagrangian ℝ Field Unit)
    (η : Field → JetPolynomial ℝ Field Unit) (B : Unit → JetPolynomial ℝ Field Unit)
    (hSymmetry : FirstOrderLagrangian.firstVariation L η = FirstOrderLagrangian.divergence B)
    (φ : Field → ℝ → ℝ) (hφ : ∀ a, ContDiff ℝ ∞ (φ a)) (t : ℝ)
    (hE : ∀ a, FieldEvaluation.euler L (fun _ => (1 : ℝ)) φ a t = 0) :
    HasDerivAt (fun s => evaluate φ s (FirstOrderLagrangian.noetherCurrent L η B ())) 0 t := by
  have hj := hasDerivAt_evaluate φ hφ (FirstOrderLagrangian.noetherCurrent L η B ()) t
  have he := FirstOrderLagrangian.noether_on_shell L η B hSymmetry (evaluate φ t)
    (fun a => (evaluate_eulerLagrange L φ hφ a t).trans (hE a))
  simp only [FirstOrderLagrangian.divergence, Fintype.sum_unique] at he
  exact he ▸ hj

end LeanPhy.FieldTheory.CurveJet
