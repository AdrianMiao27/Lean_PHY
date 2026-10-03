import Mathlib.Tactic
import LeanPhy.Mathematics.FiniteProcess

/-!
# Finite positive and parabolic steps

Many numerical PDE, master-equation and lattice-diffusion updates have a
common algebraic core: a nonnegative row-stochastic matrix maps a field to a
convex combination of its old values.  This file records that core as an
explicit certificate.  The kernel proves preservation of constants,
nonnegativity and pointwise lower/upper bounds for every finite step and for
any finite iterate.  Conservation of the unweighted total is kept separate:
it requires an explicit column-sum certificate and is never inferred from
row-stochasticity.

No CFL condition, mesh stability, maximum-principle theorem for a continuum
operator or convergence statement is hidden in these definitions.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

universe u

/-- A finite positive row-stochastic update.  The row sum is the algebraic
condition needed for a discrete maximum principle. -/
structure FinitePositiveStep (ι : Type u) [Fintype ι] where
  kernel : Matrix ι ι ℝ
  nonneg : ∀ i j, 0 ≤ kernel i j
  row_sum : ∀ i, ∑ j, kernel i j = 1

namespace FinitePositiveStep

variable {ι : Type u} [Fintype ι]

/-- The admissible states for a positive finite step: componentwise
    nonnegative fields.  It is reusable by Markov, diffusion and lattice
    adapters without choosing a norm or a mesh interpretation. -/
def NonnegativeField (u : ι → ℝ) : Prop := ∀ i, 0 ≤ u i

/-- One finite parabolic/Markov update. -/
def step (K : FinitePositiveStep ι) (u : ι → ℝ) : ι → ℝ :=
  K.kernel.mulVec u

@[simp] theorem step_apply (K : FinitePositiveStep ι) (u : ι → ℝ) (i : ι) :
    K.step u i = ∑ j, K.kernel i j * u j := rfl

/-- A finite iterate of the same update. -/
def iterate (K : FinitePositiveStep ι) : ℕ → (ι → ℝ) → (ι → ℝ)
  | 0, u => u
  | n + 1, u => K.step (K.iterate n u)

@[simp] theorem iterate_zero (K : FinitePositiveStep ι) (u : ι → ℝ) :
    K.iterate 0 u = u := rfl

@[simp] theorem iterate_succ (K : FinitePositiveStep ι) (n : ℕ)
    (u : ι → ℝ) :
    K.iterate (n + 1) u = K.step (K.iterate n u) := rfl

theorem step_const (K : FinitePositiveStep ι) (c : ℝ) :
    K.step (fun _ => c) = fun _ => c := by
  funext i
  rw [step_apply, ← Finset.sum_mul, K.row_sum i]
  simp

theorem step_nonneg (K : FinitePositiveStep ι) {u : ι → ℝ}
    (hu : ∀ j, 0 ≤ u j) :
    ∀ i, 0 ≤ K.step u i := by
  intro i
  rw [step_apply]
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (K.nonneg i j) (hu j)

def toStateMap (K : FinitePositiveStep ι) :
    StateMap (ι → ℝ) (ι → ℝ) NonnegativeField NonnegativeField where
  toFun := K.step
  preserves := by
    intro u hu
    exact K.step_nonneg hu

theorem step_bounds (K : FinitePositiveStep ι) (u : ι → ℝ)
    (lower upper : ℝ) (hlo : ∀ j, lower ≤ u j)
    (hhi : ∀ j, u j ≤ upper) :
    ∀ i, lower ≤ K.step u i ∧ K.step u i ≤ upper := by
  intro i
  constructor
  · rw [step_apply]
    have hleft : ∑ j, K.kernel i j * lower = lower := by
      rw [← Finset.sum_mul, K.row_sum i]
      simp
    rw [← hleft]
    exact Finset.sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_left (hlo j) (K.nonneg i j))
  · rw [step_apply]
    have hright : upper = ∑ j, K.kernel i j * upper := by
      rw [← Finset.sum_mul, K.row_sum i]
      simp
    rw [hright]
    exact Finset.sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_left (hhi j) (K.nonneg i j))

theorem iterate_nonneg (K : FinitePositiveStep ι) {u : ι → ℝ}
    (hu : ∀ j, 0 ≤ u j) :
    ∀ n i, 0 ≤ K.iterate n u i := by
  intro n
  induction n with
  | zero =>
      intro i
      exact hu i
  | succ n ih =>
      exact K.step_nonneg (fun j => ih j)

theorem iterate_bounds (K : FinitePositiveStep ι) (u : ι → ℝ)
    (lower upper : ℝ) (hlo : ∀ j, lower ≤ u j)
    (hhi : ∀ j, u j ≤ upper) :
    ∀ n i, lower ≤ K.iterate n u i ∧ K.iterate n u i ≤ upper := by
  intro n
  induction n with
  | zero =>
      intro i
      exact ⟨hlo i, hhi i⟩
  | succ n ih =>
      have hprevlo : ∀ j, lower ≤ K.iterate n u j := fun j => (ih j).1
      have hprevhi : ∀ j, K.iterate n u j ≤ upper := fun j => (ih j).2
      simpa only [iterate_succ] using K.step_bounds
        (K.iterate n u) lower upper hprevlo hprevhi

/-- A separate certificate for conservation of the unweighted finite sum.
Row stochasticity alone preserves constants but does not preserve total mass;
the column sum is therefore an explicit additional hypothesis. -/
structure MassConservationCertificate (K : FinitePositiveStep ι) : Prop where
  column_sum : ∀ j, ∑ i, K.kernel i j = 1

theorem sum_preserved (K : FinitePositiveStep ι)
    (C : MassConservationCertificate K) (u : ι → ℝ) :
    ∑ i, K.step u i = ∑ i, u i := by
  calc
    (∑ i, K.step u i) = ∑ i, ∑ j, K.kernel i j * u j := by
      apply Finset.sum_congr rfl
      intro i hi
      rfl
    _ = ∑ j, ∑ i, K.kernel i j * u j := by
      rw [Finset.sum_comm]
    _ = ∑ j, u j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_mul, C.column_sum j]
      simp

theorem iterate_sum_preserved (K : FinitePositiveStep ι)
    (C : MassConservationCertificate K) (u : ι → ℝ) :
    ∀ n, ∑ i, K.iterate n u i = ∑ i, u i := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate_succ, K.sum_preserved C]
      exact ih

/-! A concrete pointwise error metric for finite fields.  It is deliberately
independent of a choice of norm on the function space, so a PDE adapter can
report a componentwise residual without silently importing a mesh norm. -/

structure UniformError (u v : ι → ℝ) (radius : ℝ) : Prop where
  radius_nonneg : 0 ≤ radius
  bound : ∀ i, |u i - v i| ≤ radius

namespace UniformError

theorem of_eq {u v : ι → ℝ} (h : u = v) : UniformError u v 0 := by
  subst v
  exact ⟨le_rfl, by intro i; simp⟩

theorem trans {u v w : ι → ℝ} {r s : ℝ}
    (huv : UniformError u v r) (hvw : UniformError v w s) :
    UniformError u w (r + s) := by
  refine { radius_nonneg := add_nonneg huv.radius_nonneg hvw.radius_nonneg, bound := ?_ }
  intro i
  calc
    |u i - w i| ≤ |u i - v i| + |v i - w i| := by
      have hsum := abs_add_le (u i - v i) (v i - w i)
      simpa [sub_eq_add_neg, add_assoc] using hsum
    _ ≤ r + s := add_le_add (huv.bound i) (hvw.bound i)

end UniformError

theorem step_uniformError (K : FinitePositiveStep ι)
    {u v : ι → ℝ} {radius : ℝ}
    (h : UniformError u v radius) :
    UniformError (K.step u) (K.step v) radius := by
  refine ⟨h.radius_nonneg, ?_⟩
  intro i
  rw [step_apply, step_apply]
  have hdiff :
      (∑ j, K.kernel i j * u j) - ∑ j, K.kernel i j * v j =
        ∑ j, K.kernel i j * (u j - v j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hdiff]
  calc
    |∑ j, K.kernel i j * (u j - v j)| ≤
        ∑ j, |K.kernel i j * (u j - v j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, K.kernel i j * |u j - v j| := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_mul, abs_of_nonneg (K.nonneg i j)]
    _ ≤ ∑ j, K.kernel i j * radius := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (h.bound j) (K.nonneg i j)
    _ = radius := by
      rw [← Finset.sum_mul, K.row_sum i]
      simp

/-- The componentwise error budget for a finite positive trajectory. -/
def propagatedRadius (initial : ℝ) (stepRadius : ℕ → ℝ) : ℕ → ℝ
  | 0 => initial
  | n + 1 => propagatedRadius initial stepRadius n + stepRadius n

@[simp] theorem propagatedRadius_zero (initial : ℝ) (stepRadius : ℕ → ℝ) :
    propagatedRadius initial stepRadius 0 = initial := rfl

@[simp] theorem propagatedRadius_succ (initial : ℝ) (stepRadius : ℕ → ℝ)
    (n : ℕ) :
    propagatedRadius initial stepRadius (n + 1) =
      propagatedRadius initial stepRadius n + stepRadius n := rfl

theorem propagatedRadius_nonneg {initial : ℝ} {stepRadius : ℕ → ℝ}
    (hi : 0 ≤ initial) (hs : ∀ n, 0 ≤ stepRadius n) :
    ∀ n, 0 ≤ propagatedRadius initial stepRadius n := by
  intro n
  induction n with
  | zero => exact hi
  | succ n ih =>
      simp only [propagatedRadius_succ]
      exact add_nonneg ih (hs n)

/-- Exact and approximate finite parabolic trajectories with local residuals.
The exact recurrence, initial error and every one-step residual are all fields,
so a later bound cannot be produced by omitting one of them. -/
structure TrajectoryCertificate
    (K : FinitePositiveStep ι)
    (exact approximate : ℕ → (ι → ℝ))
    (initialRadius : ℝ) (stepRadius : ℕ → ℝ) : Prop where
  initial_nonneg : 0 ≤ initialRadius
  step_nonneg : ∀ n, 0 ≤ stepRadius n
  initial : UniformError (exact 0) (approximate 0) initialRadius
  exact_step : ∀ n, exact (n + 1) = K.step (exact n)
  step : ∀ n, UniformError (K.step (approximate n))
    (approximate (n + 1)) (stepRadius n)

theorem TrajectoryCertificate.bound
    {K : FinitePositiveStep ι}
    {exact approximate : ℕ → (ι → ℝ)}
    {initialRadius : ℝ} {stepRadius : ℕ → ℝ}
    (C : TrajectoryCertificate K exact approximate initialRadius stepRadius)
    (n : ℕ) :
    UniformError (exact n) (approximate n)
      (propagatedRadius initialRadius stepRadius n) := by
  induction n with
  | zero => simpa using C.initial
  | succ n ih =>
      have hprop := K.step_uniformError ih
      have hnext := UniformError.trans hprop (C.step n)
      rw [C.exact_step n]
      simpa [propagatedRadius_succ] using hnext

end FinitePositiveStep

/-! Physics-facing names retain the same explicit finite certificate. -/

abbrev FiniteParabolicStep := FinitePositiveStep
abbrev FiniteHeatStep := FinitePositiveStep
abbrev FiniteDiffusionStep := FinitePositiveStep
abbrev FiniteMarkovStep := FinitePositiveStep
abbrev FiniteMasterEquationStep := FinitePositiveStep

end LeanPhy.Mathematics
