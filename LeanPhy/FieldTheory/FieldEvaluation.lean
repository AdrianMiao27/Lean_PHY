import LeanPhy.FieldTheory.Variational
import LeanPhy.Mathematics.PolynomialEvaluation
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false

/-!
# First-order actions on actual differentiable fields

A field is a real function on a normed real space. The explicit constant
vectors `e μ` specify the coordinate directions; no metric, signature or basis
is inferred. Polynomial densities, their partials and momenta are evaluated
on the actual fields and their Frechet derivatives. For C² fields the Euler
residual and boundary divergence are analytic derivatives, with a proved
first-variation identity. Smoothness is input; field equations are not.
-/

namespace LeanPhy.FieldTheory.FieldEvaluation

open LeanPhy.Mathematics.PolynomialEvaluation
open scoped BigOperators ContDiff

variable {Field Direction E : Type*} [Fintype Field] [Fintype Direction]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def directional (v : E) (f : E → ℝ) (x : E) : ℝ := fderiv ℝ f x v

noncomputable def coordinates (e : Direction → E) (φ : Field → E → ℝ) (x : E)
    (p : Field × Option Direction) : ℝ :=
  p.2.elim (φ p.1 x) (fun μ => directional (e μ) (φ p.1) x)

noncomputable def value (L : FirstOrderLagrangian ℝ Field Direction)
    (e : Direction → E) (φ : Field → E → ℝ) (x : E) : ℝ :=
  MvPolynomial.eval (coordinates e φ x) L

noncomputable def force (L : FirstOrderLagrangian ℝ Field Direction)
    (e : Direction → E) (φ : Field → E → ℝ) (a : Field) : E → ℝ :=
  value (MvPolynomial.pderiv (a, none) L) e φ

noncomputable def momentum (L : FirstOrderLagrangian ℝ Field Direction)
    (e : Direction → E) (φ : Field → E → ℝ) (a : Field) (μ : Direction) : E → ℝ :=
  value (MvPolynomial.pderiv (a, some μ) L) e φ

noncomputable def euler (L : FirstOrderLagrangian ℝ Field Direction)
    (e : Direction → E) (φ : Field → E → ℝ) (a : Field) (x : E) : ℝ :=
  force L e φ a x - ∑ μ, directional (e μ) (momentum L e φ a μ) x

noncomputable def variation (L : FirstOrderLagrangian ℝ Field Direction)
    (e : Direction → E) (φ η : Field → E → ℝ) (x : E) : ℝ :=
  (∑ a, force L e φ a x * η a x) +
    ∑ a, ∑ μ, momentum L e φ a μ x * directional (e μ) (η a) x

noncomputable def boundary (L : FirstOrderLagrangian ℝ Field Direction)
    (e : Direction → E) (φ η : Field → E → ℝ) (μ : Direction) (x : E) : ℝ :=
  ∑ a, momentum L e φ a μ x * η a x

noncomputable def divergence (e : Direction → E) (J : Direction → E → ℝ) (x : E) : ℝ :=
  ∑ μ, directional (e μ) (J μ) x

def perturb (φ η : Field → E → ℝ) (s : ℝ) : Field → E → ℝ :=
  fun a x => φ a x + s * η a x

omit [Fintype Field] [Fintype Direction] in
@[simp] theorem value_field (e : Direction → E) (φ : Field → E → ℝ) (a : Field) (x : E) :
    value (FirstOrderLagrangian.field a) e φ x = φ a x := by
  simp [value, FirstOrderLagrangian.field, coordinates]

omit [Fintype Field] [Fintype Direction] in
@[simp] theorem value_gradient (e : Direction → E) (φ : Field → E → ℝ)
    (a : Field) (μ : Direction) (x : E) :
    value (FirstOrderLagrangian.gradient a μ) e φ x = directional (e μ) (φ a) x := by
  simp [value, FirstOrderLagrangian.gradient, coordinates]

theorem contDiff_directional (v : E) (f : E → ℝ) {n : ℕ∞ω}
    (hf : ContDiff ℝ (n + 1) f) : ContDiff ℝ n (directional v f) :=
  (hf.fderiv_right le_rfl).clm_apply contDiff_const

omit [Fintype Field] [Fintype Direction] in
theorem contDiff_value (L : FirstOrderLagrangian ℝ Field Direction)
    (e : Direction → E) (φ : Field → E → ℝ) {n : ℕ∞ω}
    (hφ : ∀ a, ContDiff ℝ (n + 1) (φ a)) : ContDiff ℝ n (value L e φ) := by
  apply contDiff_eval
  rintro ⟨a, _ | μ⟩
  · exact (hφ a).of_le (by simp)
  · exact contDiff_directional _ _ (hφ a)

omit [Fintype Field] [Fintype Direction] in
theorem coordinates_perturb (e : Direction → E) (φ η : Field → E → ℝ) (x : E)
    (hφ : ∀ a, DifferentiableAt ℝ (φ a) x) (hη : ∀ a, DifferentiableAt ℝ (η a) x)
    (s : ℝ) (p : Field × Option Direction) :
    coordinates e (perturb φ η s) x p =
      coordinates e φ x p + s * coordinates e η x p := by
  rcases p with ⟨a, _ | μ⟩
  · rfl
  · change fderiv ℝ (fun y => φ a y + s * η a y) x (e μ) = _
    rw [fderiv_fun_add (hφ a) ((hη a).const_mul s), fderiv_const_mul (hη a)]
    rfl

/-- The local variation is the actual derivative of the perturbed density. -/
theorem hasDerivAt_value_perturb (L : FirstOrderLagrangian ℝ Field Direction)
    (e : Direction → E) (φ η : Field → E → ℝ) (x : E)
    (hφ : ∀ a, DifferentiableAt ℝ (φ a) x) (hη : ∀ a, DifferentiableAt ℝ (η a) x) :
    HasDerivAt (fun s => value L e (perturb φ η s) x) (variation L e φ η x) 0 := by
  have hc : (fun s => value L e (perturb φ η s) x) =
      fun s => MvPolynomial.eval (fun p => coordinates e φ x p + s * coordinates e η x p) L := by
    funext s
    have hp : coordinates e (perturb φ η s) x =
        fun p => coordinates e φ x p + s * coordinates e η x p :=
      funext (coordinates_perturb e φ η x hφ hη s)
    unfold value
    rw [hp]
  rw [hc]
  have h := hasDerivAt_eval L
    (fun p s => coordinates e φ x p + s * coordinates e η x p)
    (coordinates e η x) 0 (fun p => by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (coordinates e η x p)).const_add
        (coordinates e φ x p))
  simpa [variation, force, momentum, value, coordinates,
    Fintype.sum_prod_type, Fintype.sum_option, Finset.sum_add_distrib] using! h

omit [Fintype Direction] in
theorem directional_boundary (L : FirstOrderLagrangian ℝ Field Direction)
    (e : Direction → E) (φ η : Field → E → ℝ) (x : E) (μ : Direction)
    (hφ : ∀ a, ContDiff ℝ 2 (φ a)) (hη : ∀ a, DifferentiableAt ℝ (η a) x) :
    directional (e μ) (boundary L e φ η μ) x =
      ∑ a, (momentum L e φ a μ x * directional (e μ) (η a) x +
        directional (e μ) (momentum L e φ a μ) x * η a x) := by
  have hp (a : Field) : DifferentiableAt ℝ (momentum L e φ a μ) x :=
    (contDiff_value _ e φ (n := 1) hφ).differentiable (by norm_num) x
  have h := (HasFDerivAt.fun_sum (u := Finset.univ)
    (fun a _ => (hp a).hasFDerivAt.mul (hη a).hasFDerivAt)).fderiv
  have he := congrArg (fun A : E →L[ℝ] ℝ => A (e μ)) h
  change (fderiv ℝ (fun y => ∑ a, momentum L e φ a μ y * η a y) x) (e μ) = _
  simpa [directional, mul_comm, add_comm] using! he

/-- Integration by parts before integration: all derivatives belong to the
actual fields. C² regularity proves differentiability of the momenta. -/
theorem first_variation (L : FirstOrderLagrangian ℝ Field Direction)
    (e : Direction → E) (φ η : Field → E → ℝ) (x : E)
    (hφ : ∀ a, ContDiff ℝ 2 (φ a)) (hη : ∀ a, DifferentiableAt ℝ (η a) x) :
    variation L e φ η x = (∑ a, euler L e φ a x * η a x) +
      divergence e (boundary L e φ η) x := by
  unfold divergence
  simp_rw [directional_boundary L e φ η x _ hφ hη]
  simp only [variation, euler, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun μ a => momentum L e φ a μ x * directional (e μ) (η a) x),
    Finset.sum_comm (f := fun μ a => directional (e μ) (momentum L e φ a μ) x * η a x)]
  ring

end LeanPhy.FieldTheory.FieldEvaluation
