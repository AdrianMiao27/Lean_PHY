import LeanPhy.FieldTheory.PointTransformation
import LeanPhy.FieldTheory.FieldEvaluation
import LeanPhy.FieldTheory.IntervalAction
import LeanPhy.FieldTheory.FiniteActionResponse

/-!
# Actual fields and finite action tables under point transformations

The formal pullback agrees with the density evaluated on actual transformed
fields and with the interval action. Finite tables retain their original
configuration labels and transform their field/gradient slots. This does not
change an integration measure or assert a quantum path-integral Jacobian formula.
-/

set_option autoImplicit false

namespace LeanPhy.FieldTheory.PointTransformation

open FirstOrderLagrangian
open LeanPhy.Mathematics.PolynomialEvaluation
open scoped BigOperators ContDiff

variable {Old New Dir E : Type*} [Fintype Old] [Fintype New] [Fintype Dir]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def transformed (F : Old → MvPolynomial New ℝ) (ψ : New → E → ℝ) : Old → E → ℝ :=
  fun a x => MvPolynomial.eval (fun b => ψ b x) (F a)

omit [Fintype Old] in
theorem transformed_derivative (F : Old → MvPolynomial New ℝ) (ψ : New → E → ℝ)
    (x : E) (hψ : ∀ b, DifferentiableAt ℝ (ψ b) x) (a : Old) (v : E) :
    FieldEvaluation.directional v (transformed F ψ a) x =
      ∑ b, MvPolynomial.eval (fun c => ψ c x) (MvPolynomial.pderiv b (F a)) *
        FieldEvaluation.directional v (ψ b) x := by
  have hd := hasFDerivAt_eval (F a) ψ (fun b => fderiv ℝ (ψ b) x) x
    (fun b => (hψ b).hasFDerivAt)
  unfold FieldEvaluation.directional transformed
  rw [hd.fderiv]
  simp

omit [Fintype Old] [Fintype Dir] in
theorem eval_coordinate (F : Old → MvPolynomial New ℝ) (e : Dir → E)
    (ψ : New → E → ℝ) (x : E) (hψ : ∀ b, DifferentiableAt ℝ (ψ b) x)
    (p : Old × Option Dir) :
    MvPolynomial.eval (FieldEvaluation.coordinates e ψ x) (coordinate F p) =
      FieldEvaluation.coordinates e (transformed F ψ) x p := by
  obtain ⟨a, μ⟩ := p
  cases μ with
  | none => simp [coordinate, potential, MvPolynomial.eval_rename, FieldEvaluation.coordinates, transformed, Function.comp_def]
  | some μ =>
    simpa [coordinate, potential, MvPolynomial.eval_rename, gradient, FieldEvaluation.coordinates, Function.comp_def] using
      (transformed_derivative F ψ x hψ a (e μ)).symm

omit [Fintype Old] [Fintype Dir] in
theorem value_pullback (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Dir) (e : Dir → E)
    (ψ : New → E → ℝ) (x : E) (hψ : ∀ b, DifferentiableAt ℝ (ψ b) x) :
    FieldEvaluation.value (pullback F L) e ψ x =
      FieldEvaluation.value L e (transformed F ψ) x := by
  unfold FieldEvaluation.value pullback
  induction L using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P a hP =>
    simpa [eval_coordinate F e ψ x hψ a] using
      congrArg₂ (· * ·) hP (eval_coordinate F e ψ x hψ a)

omit [Fintype Old] [Fintype New] in
theorem transformed_contDiff (F : Old → MvPolynomial New ℝ) (ψ : New → E → ℝ)
    (n : ℕ∞ω) (hψ : ∀ b, ContDiff ℝ n (ψ b)) (a : Old) :
    ContDiff ℝ n (transformed F ψ a) :=
  contDiff_eval (F a) ψ n hψ

omit [Fintype Old] [Fintype Dir] in
theorem action_pullback (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Unit) (ψ : New → ℝ → ℝ)
    (hψ : ∀ b x, DifferentiableAt ℝ (ψ b) x) (a b : ℝ) :
    IntervalAction.action (pullback F L) ψ a b =
      IntervalAction.action L (transformed F ψ) a b := by
  unfold IntervalAction.action
  apply intervalIntegral.integral_congr
  intro x _
  exact value_pullback F L IntervalAction.direction ψ x (fun j => hψ j x)

omit [Fintype Old] [Fintype Dir] in
theorem eval_pullback (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Dir) (v : New × Option Dir → ℝ) :
    MvPolynomial.eval v (pullback F L) =
      MvPolynomial.eval (fun p => MvPolynomial.eval v (coordinate F p)) L := by
  induction L using MvPolynomial.induction_on with
  | C r => simp [pullback]
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P a hP =>
      simpa [pullback] using congrArg₂ (· * ·) hP (rfl : MvPolynomial.eval v (coordinate F a) = _)

omit [Fintype Old] [Fintype Dir] in
theorem finiteAction_pullback {Config Cell : Type*} [Fintype Cell]
    (F : Old → MvPolynomial New ℝ) (L : FirstOrderLagrangian ℝ Old Dir)
    (volume : Cell → ℝ) (v : Config → Cell → New × Option Dir → ℝ) (c : Config) :
    finiteAction (pullback F L) volume v c =
      finiteAction L volume (fun c x p => MvPolynomial.eval (v c x) (coordinate F p)) c := by
  simp only [finiteAction, eval_pullback]

omit [Fintype Old] [Fintype Dir] in
theorem finiteProbability_pullback {Config Cell : Type*} [Fintype Cell]
    [Fintype Config] [Nonempty Config]
    (F : Old → MvPolynomial New ℝ) (L : FirstOrderLagrangian ℝ Old Dir)
    (volume : Cell → ℝ) (v : Config → Cell → New × Option Dir → ℝ) :
    finiteProbability (pullback F L) volume v =
      finiteProbability L volume (fun c x p => MvPolynomial.eval (v c x) (coordinate F p)) := by
  unfold finiteProbability
  congr 1
  funext c
  exact finiteAction_pullback F L volume v c

end LeanPhy.FieldTheory.PointTransformation
