import LeanPhy.FieldTheory.IntervalAction
import LeanPhy.Examples.VariationalResearch
import LeanPhy.Workflow.Exploration

set_option autoImplicit false

/-!
# Actual coupled profiles, action variations and boundary counterexamples

The public operations accept arbitrary polynomial densities and finite field
sets. This client uses mixed finite-mode kinetics and interacting scalar
profiles. Analytic regularity and equations of motion remain explicit;
stationarity is not a minimization or a solution-existence claim.
-/

namespace LeanPhy.Examples.ActionEvaluationResearch

open LeanPhy.FieldTheory LeanPhy.Workflow
open scoped BigOperators ContDiff


/-- The former formal cross-acceleration term is an actual second derivative. -/
theorem mixed_profile_equation (g : ℝ) (φ : Fin 2 → ℝ → ℝ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (t : ℝ) :
    FieldEvaluation.euler (VariationalResearch.kineticMixing g) IntervalAction.direction φ 0 t =
      -g * iteratedDeriv 2 (φ 1) t := by
  unfold IntervalAction.direction
  rw [← CurveJet.evaluate_eulerLagrange _ φ hφ]
  rw [VariationalResearch.kineticMixing_first]
  simp [CurveJet.evaluate, JetPolynomial.jet]

/-- Coupled real order-parameter profiles keep every kinetic-mixing term.
The signs of the coefficients encode the chosen time or static convention. -/
theorem interacting_profile_equation {Field : Type*} [Fintype Field]
    (K : (Field × Unit) → (Field × Unit) → ℝ) (hK : ∀ i j, K i j = K j i)
    (V : MvPolynomial Field ℝ) (φ : Field → ℝ → ℝ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (i : Field) (t : ℝ) :
    FieldEvaluation.euler (FirstOrderLagrangian.quadraticAction K V) IntervalAction.direction φ i t =
      -MvPolynomial.eval (fun j => φ j t) (MvPolynomial.pderiv i V) -
      ∑ j, K (i, ()) (j, ()) * iteratedDeriv 2 (φ j) t := by
  unfold IntervalAction.direction
  rw [← CurveJet.evaluate_eulerLagrange _ φ hφ]
  rw [FirstOrderLagrangian.eulerLagrange_quadraticAction K hK]
  simp [CurveJet.evaluate, FirstOrderLagrangian.lift, FirstOrderLagrangian.potential, JetPolynomial.jet,
    MvPolynomial.eval_rename, Fintype.sum_prod_type]
  congr 1

theorem arbitrary_action_stationarity {Field : Type*} [Fintype Field]
    (L : FirstOrderLagrangian ℝ Field Unit) (φ η : Field → ℝ → ℝ)
    (hφ : ∀ i, ContDiff ℝ 2 (φ i)) (hη : ∀ i, ContDiff ℝ 1 (η i)) (a b : ℝ)
    (ha : ∀ i, η i a = 0) (hb : ∀ i, η i b = 0)
    (hE : ∀ t ∈ Set.uIcc a b, ∀ i, FieldEvaluation.euler L IntervalAction.direction φ i t = 0) :
    HasDerivAt (fun s => IntervalAction.action L (FieldEvaluation.perturb φ η s) a b) 0 0 :=
  IntervalAction.stationary_of_euler L φ η hφ hη a b ha hb hE

/-- A polynomial interacting shift symmetry produces an actual conserved
profile current, conditional on the actual differential equations. -/
theorem interacting_shift_current
    (K : (Fin 2 × Unit) → (Fin 2 × Unit) → ℝ) (coupling : ℝ)
    (φ : Fin 2 → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (a b : ℝ)
    (hE : ∀ t ∈ Set.uIcc a b, ∀ i,
      FieldEvaluation.euler (FirstOrderLagrangian.quadraticAction K (VariationalResearch.relativePotential coupling))
        IntervalAction.direction φ i t = 0) :
    CurveJet.evaluate φ b (FirstOrderLagrangian.noetherCurrent
      (FirstOrderLagrangian.quadraticAction K (VariationalResearch.relativePotential coupling))
      (fun _ => 1) (fun _ => 0) ()) =
    CurveJet.evaluate φ a (FirstOrderLagrangian.noetherCurrent
      (FirstOrderLagrangian.quadraticAction K (VariationalResearch.relativePotential coupling))
      (fun _ => 1) (fun _ => 0) ()) := by
  apply IntervalAction.noether_conserved _ _ _ _ φ hφ a b hE
  simpa [FirstOrderLagrangian.divergence] using VariationalResearch.relativePotential_shift K coupling

noncomputable def freeDensity : FirstOrderLagrangian ℝ Unit Unit :=
  (1 / 2 : ℝ) • FirstOrderLagrangian.gradient () () ^ 2

def straight : Unit → ℝ → ℝ := fun _ t => t

theorem straight_smooth (i : Unit) : ContDiff ℝ ∞ (straight i) := contDiff_id

@[simp] theorem straight_deriv (i : Unit) : deriv (straight i) = fun _ => 1 := by
  change deriv (fun t : ℝ => t) = _
  simp

theorem free_symbolic_equation : FirstOrderLagrangian.eulerLagrange freeDensity () =
    -JetPolynomial.jet () (Finsupp.single () 2) := by
  have heq : freeDensity = FirstOrderLagrangian.quadraticAction (fun _ _ : Unit × Unit => 1) 0 := by
    simp [freeDensity, FirstOrderLagrangian.quadraticAction, FirstOrderLagrangian.quadraticKinetic,
      pow_two, Fintype.sum_prod_type]
  rw [heq, FirstOrderLagrangian.eulerLagrange_quadraticAction _ (fun _ _ => rfl)]
  simp [← Finsupp.single_add, Fintype.sum_prod_type]

/-- This profile satisfies the bulk field equation everywhere. -/
theorem straight_on_shell (t : ℝ) : FieldEvaluation.euler freeDensity IntervalAction.direction straight () t = 0 := by
  unfold IntervalAction.direction
  rw [← CurveJet.evaluate_eulerLagrange _ straight straight_smooth, free_symbolic_equation]
  simp [CurveJet.evaluate, JetPolynomial.jet, iteratedDeriv_succ]

/-- Varying an endpoint of an on-shell profile changes the action. -/
theorem nonzero_boundary_variation :
    HasDerivAt (fun s => IntervalAction.action freeDensity (FieldEvaluation.perturb straight straight s) 0 1) 1 0 := by
  have h := IntervalAction.hasDerivAt_action_boundary freeDensity straight straight
    (fun i => (straight_smooth i).of_le (by simp))
    (fun i => (straight_smooth i).of_le (by simp)) 0 1
  have hE (i : Unit) (t : ℝ) : FieldEvaluation.euler freeDensity IntervalAction.direction straight i t = 0 := by
    cases i
    exact straight_on_shell t
  simp only [IntervalAction.bulk, hE, zero_mul, Finset.sum_const_zero, intervalIntegral.integral_zero,
    zero_add] at h
  simpa [IntervalAction.endpoint, FieldEvaluation.boundary, FieldEvaluation.momentum, FieldEvaluation.value,
    FieldEvaluation.coordinates, FieldEvaluation.directional, freeDensity, FirstOrderLagrangian.gradient, IntervalAction.direction, straight,
    Derivation.leibniz, smul_eq_mul, straight_deriv] using! h

theorem endpoint_cannot_be_discarded :
    ¬ HasDerivAt (fun s => IntervalAction.action freeDensity (FieldEvaluation.perturb straight straight s) 0 1) 0 0 := by
  intro h
  have := nonzero_boundary_variation.unique h
  norm_num at this

def curved : Unit → ℝ → ℝ := fun _ t => t ^ 2

theorem curved_smooth (i : Unit) : ContDiff ℝ ∞ (curved i) := contDiff_id.pow 2

@[simp] theorem curved_second_derivative (i : Unit) : iteratedDeriv 2 (curved i) = fun _ => 2 := by
  change iteratedDeriv 2 (fun t : ℝ => t ^ 2) = _
  have hd : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
    funext t
    simp [pow_two, two_mul]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, hd]
  funext t
  simpa only [mul_one, id_eq] using! ((hasDerivAt_id t).const_mul 2).deriv

theorem curved_residual (t : ℝ) : FieldEvaluation.euler freeDensity IntervalAction.direction curved () t = -2 := by
  unfold IntervalAction.direction
  rw [← CurveJet.evaluate_eulerLagrange _ curved curved_smooth, free_symbolic_equation]
  simp [CurveJet.evaluate, JetPolynomial.jet]

/-- Uniform off-shell equation residuals produce a nonzero integrated budget. -/
theorem off_shell_drift : LeanPhy.Mathematics.ErrorCertificate
    (CurveJet.evaluate curved 1 (FirstOrderLagrangian.noetherCurrent freeDensity
      (fun _ => 1) (fun _ => 0) ()))
    (CurveJet.evaluate curved 0 (FirstOrderLagrangian.noetherCurrent freeDensity
      (fun _ => 1) (fun _ => 0) ())) 2 := by
  have hE (t : ℝ) (_ : t ∈ Set.uIcc (0 : ℝ) 1) (i : Unit) :
      LeanPhy.Mathematics.ErrorCertificate
        (FieldEvaluation.euler freeDensity IntervalAction.direction curved i t) 0 2 := by
    cases i
    rw [curved_residual]
    exact ⟨by norm_num, by norm_num [Real.dist_eq]⟩
  have hη (t : ℝ) (_ : t ∈ Set.uIcc (0 : ℝ) 1) (i : Unit) :
      |CurveJet.evaluate curved t (1 : JetPolynomial ℝ Unit Unit)| ≤ (1 : ℝ) := by simp
  have hBreaking (t : ℝ) (_ : t ∈ Set.uIcc (0 : ℝ) 1) :
      LeanPhy.Mathematics.ErrorCertificate
        (CurveJet.evaluate curved t (FirstOrderLagrangian.firstVariation freeDensity (fun _ => 1) -
          FirstOrderLagrangian.divergence (fun _ => 0))) 0 0 := by
    apply LeanPhy.Mathematics.ErrorCertificate.of_eq
    simp [FirstOrderLagrangian.firstVariation, FirstOrderLagrangian.fieldPartial,
      FirstOrderLagrangian.divergence, freeDensity, FirstOrderLagrangian.gradient]
  simpa using IntervalAction.noether_drift_certificate freeDensity (fun _ => 1) (fun _ => 0)
    curved curved_smooth 0 1 (fun _ => 2) (fun _ => 1) 0 hE hη hBreaking

def boundaryQuestion : Exploration.Question ℝ where
  name := "on-shell stationarity without boundary conditions"
  revision := "unrestricted-endpoints-v1"
  statement := "the free on-shell profile is stationary for the moving-endpoint variation"
  domainDescription := "intervals [0,b] with b nonnegative"
  source := "LeanPhy.Examples.ActionEvaluationResearch.endpoint_cannot_be_discarded"
  domain := fun b => 0 ≤ b
  target := fun b => HasDerivAt
    (fun s => IntervalAction.action freeDensity (FieldEvaluation.perturb straight straight s) 0 b) 0 0

def boundaryCounterexample : Exploration.Counterexample (Exploration.Branch.root boundaryQuestion) where
  input := 1
  inDomain := by norm_num [boundaryQuestion]
  inBranch := Exploration.Condition.holds_nil _
  violates := endpoint_cannot_be_discarded

def boundaryNotebook : Exploration.Notebook boundaryQuestion :=
  ⟨[(Exploration.Candidate.propose (Exploration.Branch.root boundaryQuestion)).refute
    boundaryCounterexample], []⟩

def package : TheoryPackage :=
  boundaryNotebook.toPackage "actual field and action evaluation" "condensed matter and scalar field theory"
    |>.addTheorem "local analytic variation" "C² fields yield the actual first-variation identity"
      "LeanPhy.FieldTheory.FieldEvaluation.first_variation" (@FieldEvaluation.first_variation.{0,0,0})
    |>.addTheorem "integrated action derivative" "polynomial action differentiation retains endpoint flux"
      "LeanPhy.FieldTheory.IntervalAction.hasDerivAt_action_boundary" (@IntervalAction.hasDerivAt_action_boundary.{0})
    |>.addTheorem "mixed profile equation" "formal cross accelerations become actual second derivatives"
      "LeanPhy.Examples.ActionEvaluationResearch.mixed_profile_equation" mixed_profile_equation
    |>.addTheorem "interacting profile equation" "arbitrary polynomial potentials and kinetic mixing"
      "LeanPhy.Examples.ActionEvaluationResearch.interacting_profile_equation" (@interacting_profile_equation.{0})
    |>.addTheorem "fixed endpoint stationarity" "actual Euler equations and fixed endpoints imply stationarity"
      "LeanPhy.Examples.ActionEvaluationResearch.arbitrary_action_stationarity" (@arbitrary_action_stationarity.{0})
    |>.addTheorem "interacting shift current" "smooth on-shell profiles have equal Noether endpoint currents"
      "LeanPhy.Examples.ActionEvaluationResearch.interacting_shift_current" interacting_shift_current
    |>.addTheorem "boundary counterexample" "an on-shell profile with moving endpoints is not stationary"
      "LeanPhy.Examples.ActionEvaluationResearch.endpoint_cannot_be_discarded" endpoint_cannot_be_discarded
    |>.addTheorem "off-shell current drift" "uniform equation residuals give a nonzero integrated current budget"
      "LeanPhy.Examples.ActionEvaluationResearch.off_shell_drift" off_shell_drift
    |>.addObligationText "solution existence and stability"
      "construct solutions for the chosen model and prove any minimization or stability claim"
      "model analysis"
    |>.addObligationText "spacetime boundary and charges"
      "extend finite-interval balance to the chosen spacetime region with all boundary fluxes"
      "multidimensional integration"
    |>.addObligationText "covariant and graded fields"
      "supply the derivative algebra and analytic interpretation for gauge and fermionic fields"
      "field representation"

example : package.claimCount = 9 := rfl
example : package.obligationCount = 4 := rfl
example : package.hasErrors = false := by decide

end LeanPhy.Examples.ActionEvaluationResearch
