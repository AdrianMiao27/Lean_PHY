import LeanPhy.FieldTheory.RedefinitionVariation
import LeanPhy.FieldTheory.EulerTransport
import LeanPhy.Workflow.Core

set_option autoImplicit false

/-!
# Reusable field changes with physical sources and boundary checks

Polynomial field maps, densities, sources and profiles are variable inputs.
The concrete nonlinear kinetic and boundary examples exercise the shared maps;
they do not replace the public proofs with manually asserted model identities.
-/

namespace LeanPhy.Examples.FieldRedefinitionResearch

open LeanPhy.FieldTheory FirstOrderLagrangian PointTransformation
open LeanPhy.Workflow MvPolynomial
open scoped ContDiff BigOperators

noncomputable def cubicChange (g : ℝ) (_ : Unit) : MvPolynomial Unit ℝ :=
  X () + C g * X () ^ 3

theorem nonlinear_kinetic (g : ℝ) :
    pullback (cubicChange g) ((gradient () () : FirstOrderLagrangian ℝ Unit Unit) ^ 2) =
      (1 + 3 * C g * field () ^ 2) ^ 2 * gradient () () ^ 2 := by
  simp [pullback, coordinate, cubicChange, potential, gradient, field]
  simp only [map_ofNat]
  ring

/-- A linear source becomes a nonlinear insertion when the field changes. -/
theorem nonlinear_source (g J : ℝ) :
    pullback (cubicChange g) (C J * (field () : FirstOrderLagrangian ℝ Unit Unit)) =
      C J * (field () + C g * field () ^ 3) := by
  simp [pullback, coordinate, cubicChange, potential, field]

noncomputable def shear (g : ℝ) : Fin 2 → MvPolynomial (Fin 2) ℝ :=
  ![X 0 + C g * X 1 ^ 2, X 1]

/-- A two-field nonlinear shear has an explicit polynomial inverse. -/
theorem shear_inverse (g : ℝ) (a : Fin 2) :
    aeval (shear (-g)) (shear g a) = X a := by
  fin_cases a <;> simp [shear]

theorem shear_density_roundtrip (g : ℝ) {Dir : Type*}
    (L : FirstOrderLagrangian ℝ (Fin 2) Dir) :
    pullback (shear (-g)) (pullback (shear g) L) = L :=
  pullback_inverse (shear g) (shear (-g)) (shear_inverse g) L

/-- Same construction for different field counts, potentials and time profiles. -/
theorem arbitrary_action_transport {Old New : Type*} [Fintype New]
    (F : Old → MvPolynomial New ℝ) (L : FirstOrderLagrangian ℝ Old Unit)
    (ψ : New → ℝ → ℝ) (hψ : ∀ a t, DifferentiableAt ℝ (ψ a) t) (a b : ℝ) :
    IntervalAction.action (pullback F L) ψ a b =
      IntervalAction.action L (transformed F ψ) a b :=
  action_pullback F L ψ hψ a b

/-- The same cell/configuration labels and observable are retained. No change
of a continuous integration measure is being claimed. -/
theorem finite_readout_transport {Old New Dir Config Cell : Type*}
    [Fintype New] [Fintype Cell] [Fintype Config] [Nonempty Config]
    (F : Old → MvPolynomial New ℝ) (L : FirstOrderLagrangian ℝ Old Dir)
    (volume : Cell → ℝ) (v : Config → Cell → New × Option Dir → ℝ) (O : Config → ℝ) :
    (finiteProbability (pullback F L) volume v).expectation O =
      (finiteProbability L volume
        (fun c x p => MvPolynomial.eval (v c x) (coordinate F p))).expectation O := by
  rw [finiteProbability_pullback]

noncomputable def kinetic : FirstOrderLagrangian ℝ Unit Unit := (gradient () ()) ^ 2

def straight (_ : Unit) (t : ℝ) : ℝ := t

/-- The nonzero boundary variation below occurs on a solution of the bulk
equation, so using that equation alone cannot remove it. -/
theorem straight_on_shell (t : ℝ) :
    FieldEvaluation.euler kinetic IntervalAction.direction straight () t = 0 := by
  have hm : FieldEvaluation.momentum kinetic IntervalAction.direction straight () () =
      fun _ => 2 := by
    funext x
    unfold FieldEvaluation.momentum FieldEvaluation.value
    simp [kinetic, gradient, FieldEvaluation.coordinates, FieldEvaluation.directional,
      IntervalAction.direction]
    change deriv (fun t : ℝ => t) x = 1
    simp
  simp only [FieldEvaluation.euler, Fintype.sum_unique, hm]
  simp [FieldEvaluation.force, FieldEvaluation.value,
    FieldEvaluation.directional, kinetic, gradient]

/-- Exact finite field change, retaining the quadratic parameter correction. -/
theorem scaled_action (s : ℝ) :
    IntervalAction.action (pullback (infinitesimal (fun _ : Unit => X ()) s) kinetic)
      straight 0 1 = (1 + s) ^ 2 := by
  have hd (t : ℝ) : FieldEvaluation.directional (1 : ℝ) (straight ()) t = 1 := by
    change fderiv ℝ (fun t : ℝ => t) t 1 = 1
    simp
  unfold IntervalAction.action FieldEvaluation.value
  simp [pullback, coordinate, infinitesimal, kinetic, potential, gradient,
    MvPolynomial.pderiv_X, FieldEvaluation.coordinates,
    IntervalAction.direction, hd]

theorem boundary_variation_nonzero :
    HasDerivAt (fun s => IntervalAction.action
      (pullback (infinitesimal (fun _ : Unit => X ()) s) kinetic) straight 0 1) 2 0 := by
  simp_rw [scaled_action]
  convert! (((hasDerivAt_id (0 : ℝ)).const_add 1).pow 2) using 1; norm_num

/-- First-order reasoning cannot erase the second-order finite difference. -/
theorem finite_change_keeps_higher_order :
    IntervalAction.action (pullback (infinitesimal (fun _ : Unit => X ()) 1) kinetic)
      straight 0 1 ≠ IntervalAction.action kinetic straight 0 1 + 2 := by
  have hz : pullback (infinitesimal (fun _ : Unit => X ()) 0) kinetic = kinetic := by
    have hi : infinitesimal (fun _ : Unit => X ()) 0 = fun a => X a := by
      funext a
      simp [infinitesimal]
    rw [hi, pullback_identity]
  have hbase := scaled_action 0
  rw [hz] at hbase
  rw [scaled_action, hbase]
  norm_num

/-- Arbitrary nonlinear point directions use actual Euler equations and
matching endpoint flux; no boundary premise is silently discarded. -/
theorem on_shell_with_boundary {Field : Type*} [Fintype Field]
    (P : Field → MvPolynomial Field ℝ) (L : FirstOrderLagrangian ℝ Field Unit)
    (ψ : Field → ℝ → ℝ) (hψ : ∀ a, ContDiff ℝ 2 (ψ a)) (a b : ℝ)
    (hboundary : IntervalAction.endpoint L ψ (transformed P ψ) b =
      IntervalAction.endpoint L ψ (transformed P ψ) a)
    (hE : ∀ t ∈ Set.uIcc a b, ∀ i,
      FieldEvaluation.euler L IntervalAction.direction ψ i t = 0) :
    HasDerivAt (fun s => IntervalAction.action (pullback (infinitesimal P s) L) ψ a b) 0 0 :=
  action_infinitesimal_on_shell P L ψ hψ a b hboundary hE

/-- The existing nonlinear shear preserves every coupled Euler equation on
any chosen spacetime domain; the density and source coefficients remain inputs. -/
theorem shear_equation_domain (g : ℝ) {Dir E : Type*} [Fintype Dir]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : FirstOrderLagrangian ℝ (Fin 2) Dir) (e : Dir → E)
    (ψ : Fin 2 → E → ℝ) (hψ : ∀ i, ContDiff ℝ 2 (ψ i)) (S : Set E) :
    (∀ x ∈ S, ∀ b, FieldEvaluation.euler (pullback (shear g) L) e ψ b x = 0) ↔
      (∀ x ∈ S, ∀ a, FieldEvaluation.euler L e (transformed (shear g) ψ) a x = 0) := by
  apply euler_zero_iff_on_of_det_ne_zero (shear g) L e ψ hψ S
  intro x _
  simp [jacobianMatrix, jacobian, shear, Matrix.det_fin_two]

/-- A singular coordinate change creates a spurious stationary profile for
a linear source. This is an actual Euler counterexample, not a failed search. -/
theorem singular_map_loses_equation :
    (∀ b : Unit, FieldEvaluation.euler
      (pullback (fun _ : Unit => X () ^ 2) (field () : FirstOrderLagrangian ℝ Unit Unit))
      IntervalAction.direction (fun _ _ => 0) b 0 = 0) ∧
    FieldEvaluation.euler (field () : FirstOrderLagrangian ℝ Unit Unit)
      IntervalAction.direction
      (transformed (fun _ : Unit => X () ^ 2) (fun (_ : Unit) (_ : ℝ) => 0)) () 0 = 1 := by
  have hz (φ : Unit → ℝ → ℝ) :
      FieldEvaluation.value (0 : FirstOrderLagrangian ℝ Unit Unit) IntervalAction.direction φ =
        fun _ => 0 := by
    funext t
    simp [FieldEvaluation.value]
  simp [FieldEvaluation.euler, FieldEvaluation.force, FieldEvaluation.momentum,
    FieldEvaluation.value, FieldEvaluation.coordinates, FieldEvaluation.directional,
    pullback, coordinate, potential, field, hz]

def package : TheoryPackage :=
  TheoryPackage.empty "field transformations and first-order redundancy" "effective field theory and continuum models"
    |>.addTheorem "nonlinear kinetic factor" "gradient slots retain the field Jacobian"
      "nonlinear_kinetic" nonlinear_kinetic
    |>.addTheorem "physical source transport" "sources change with the field variables"
      "nonlinear_source" nonlinear_source
    |>.addTheorem "nonlinear inverse" "an explicit inverse returns arbitrary densities to the original form"
      "shear_density_roundtrip" (@shear_density_roundtrip.{0})
    |>.addTheorem "actual action transport" "the polynomial pullback matches actual interval actions"
      "arbitrary_action_transport" (@arbitrary_action_transport Unit Unit inferInstance)
    |>.addTheorem "finite physical readout" "the same finite configuration table and probe give the same readout"
      "finite_readout_transport" (@finite_readout_transport Unit Unit Unit (Fin 2) Unit
        inferInstance inferInstance inferInstance inferInstance)
    |>.addTheorem "retained boundary variation" "a scaling field change has nonzero actual action derivative"
      "boundary_variation_nonzero" boundary_variation_nonzero
    |>.addTheorem "finite order distinction" "a finite field change retains terms beyond its first variation"
      "finite_change_keeps_higher_order" finite_change_keeps_higher_order
    |>.addTheorem "conditional on-shell redundancy" "Euler equations and matched flux imply first-order stationarity"
      "on_shell_with_boundary" (@on_shell_with_boundary Unit inferInstance)
    |>.addTheorem "Jacobian-transpose Euler transport"
      "actual coupled Euler residuals transform with the full Jacobian, including cancellation of Hessian terms"
      "euler_pullback" (@euler_pullback.{0,0,0,0})
    |>.addTheorem "variational current transport"
      "the boundary current uses the Jacobian-pushed variation"
      "boundary_pullback" (@boundary_pullback.{0,0,0,0})
    |>.addTheorem "actual transformed action derivative"
      "the derivative of the pulled-back action retains original-field bulk and endpoint contributions"
      "action_derivative_pullback" (@action_derivative_pullback.{0,0})
    |>.addTheorem "nonlinear shear equation domain"
      "a proved unit Jacobian determinant transports all coupled equations on an arbitrary domain"
      "shear_equation_domain" (@shear_equation_domain.{0,0})
    |>.addTheorem "singular-map equation loss"
      "a squared field coordinate can satisfy the new equation while the original linear-source equation fails"
      "singular_map_loses_equation" singular_map_loses_equation
    |>.addObligationText "global inverse field charts"
      "pointwise Jacobian regularity does not prove a globally bijective field map or construct inverse chart domains"
      "construct model-specific inverse charts, their ranges and boundary data"
    |>.addObligationText "higher-order and derivative-dependent changes" "the derivative at zero does not establish higher-order EFT redundancy"
      "track higher orders, derivative jets and induced source operators"
    |>.addObligationText "multidimensional boundaries and graded fields" "interval and commuting polynomial results do not include spacetime charges or fermionic fields"
      "construct region-boundary and covariant/graded adapters"
    |>.addObligationText "quantum measure and scattering" "fixed finite labels do not supply a path-integral measure change or S-matrix theorem"
      "prove Jacobian, regularization and physical matching conditions"

end LeanPhy.Examples.FieldRedefinitionResearch
