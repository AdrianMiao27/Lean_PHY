import LeanPhy.FieldTheory.Variational
import LeanPhy.StatMech.GibbsResponse

set_option autoImplicit false

/-!
# From a polynomial density to finite Euclidean source response

Evaluate a first-order density on an explicit finite table of field/gradient
values and cell weights. The resulting real action defines a finite positive
Gibbs measure. Varying a coupling `L + h V` inserts the evaluated `V`, with the
minus covariance sign dictated by `exp(-S)`. The formula is proved through
polynomial linearity and the shared normalized derivative theorem.

The table is a declared finite model, not an automatically verified continuum
discretization. It does not assert that its gradient slots are actual finite
differences, that cell weights approximate a volume integral, or that a finite
configuration set approximates an unrestricted scalar-field path measure.
Such consistency and limit claims remain independent research obligations.
-/

namespace LeanPhy.FieldTheory.FirstOrderLagrangian

open LeanPhy.StatMech
open scoped BigOperators

variable {Field Direction Config Cell : Type*} [Fintype Cell]

/-- Explicit finite action from cell coefficients and field/gradient tables.
Use Euclidean sign conventions when interpreting its exponential as a Gibbs
weight; no Wick rotation is performed by this operation. -/
noncomputable def finiteAction (L : FirstOrderLagrangian ℝ Field Direction)
    (volume : Cell → ℝ) (values : Config → Cell → Field × Option Direction → ℝ)
    (c : Config) : ℝ := ∑ x, volume x * MvPolynomial.eval (values c x) L

@[simp] theorem finiteAction_add (L V : FirstOrderLagrangian ℝ Field Direction)
    (volume : Cell → ℝ) (values : Config → Cell → Field × Option Direction → ℝ) (c : Config) :
    finiteAction (L + V) volume values c =
      finiteAction L volume values c + finiteAction V volume values c := by
  simp [finiteAction, mul_add, Finset.sum_add_distrib]

@[simp] theorem finiteAction_smul (L : FirstOrderLagrangian ℝ Field Direction) (h : ℝ)
    (volume : Cell → ℝ) (values : Config → Cell → Field × Option Direction → ℝ) (c : Config) :
    finiteAction (h • L) volume values c = h * finiteAction L volume values c := by
  simp only [finiteAction, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem hasDerivAt_finiteAction_coupling (L V : FirstOrderLagrangian ℝ Field Direction)
    (volume : Cell → ℝ) (values : Config → Cell → Field × Option Direction → ℝ)
    (h : ℝ) (c : Config) :
    HasDerivAt (fun t => finiteAction (L + t • V) volume values c)
      (finiteAction V volume values c) h := by
  simp_rw [finiteAction_add, finiteAction_smul]
  simpa using ((hasDerivAt_id h).mul_const (finiteAction V volume values c)).const_add
    (finiteAction L volume values c)

variable [Fintype Config] [Nonempty Config]

/-- The existing finite Gibbs probability, built from the actual action table. -/
noncomputable def finiteProbability (L : FirstOrderLagrangian ℝ Field Direction)
    (volume : Cell → ℝ) (values : Config → Cell → Field × Option Direction → ℝ) :
    FiniteProbability Config := finiteGibbsProbability 1 (finiteAction L volume values)

/-- Coupling differentiation of the action produces a connected insertion
with the action sign. The observable is fixed in this theorem. -/
theorem hasDerivAt_finiteAction_expectation (L V : FirstOrderLagrangian ℝ Field Direction)
    (volume : Cell → ℝ) (values : Config → Cell → Field × Option Direction → ℝ)
    (O : Config → ℝ) (h : ℝ) :
    HasDerivAt (fun t => (finiteProbability (L + t • V) volume values).expectation O)
      (-(finiteProbability (L + h • V) volume values).covariance O
        (finiteAction V volume values)) h := by
  have hp := hasDerivAt_finiteGibbs_parameter 1
    (fun t => finiteAction (L + t • V) volume values) (fun _ => O)
    (finiteAction V volume values) (fun _ => 0) h
    (hasDerivAt_finiteAction_coupling L V volume values h)
    (fun c => hasDerivAt_const h (O c))
  simpa only [finiteProbability, FiniteProbability.expectation_const, one_mul, zero_sub] using hp

end LeanPhy.FieldTheory.FirstOrderLagrangian
