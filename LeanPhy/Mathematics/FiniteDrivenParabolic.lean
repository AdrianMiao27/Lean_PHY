import LeanPhy.Mathematics.FiniteParabolic
import Mathlib.Tactic

/-!
# Finite driven parabolic steps

The homogeneous positive step in `FiniteParabolic` is enough for heat and
Markov updates without a source.  Physical discretisations also contain
forcing, a current, a measurement source, or an inhomogeneous boundary
contribution.  This file records the finite algebraic contract for

    u_(n+1) = K u_n + f_n.

The source is an explicit input.  The kernel proves the corresponding bound
and error propagation, but it does not infer a CFL condition, a continuum
maximum principle, or a stability estimate for a PDE solver.
-/

namespace LeanPhy.Mathematics

universe u

namespace FinitePositiveStep

open scoped BigOperators

variable {ι : Type u} [Fintype ι]

/-- One finite update with an explicit additive source/forcing field. -/
def drivenStep (K : FinitePositiveStep ι) (u f : ι → ℝ) : ι → ℝ :=
  fun i => K.step u i + f i

@[simp] theorem drivenStep_apply (K : FinitePositiveStep ι)
    (u f : ι → ℝ) (i : ι) :
    K.drivenStep u f i = K.step u i + f i := rfl

/-- A common source cancels from a pointwise error comparison. -/
theorem drivenStep_uniformError (K : FinitePositiveStep ι)
    {u v f : ι → ℝ} {radius : ℝ}
    (h : UniformError (K.step u) (K.step v) radius) :
    UniformError (K.drivenStep u f) (K.drivenStep v f) radius := by
  refine ⟨h.radius_nonneg, ?_⟩
  intro i
  simpa [drivenStep, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using h.bound i

/-- A source/forcing perturbation propagates directly through an additive
source term.  This is kept separate from `drivenStep_uniformError` so a
numerical adapter must account for both state error and source error. -/
theorem drivenStep_source_uniformError (K : FinitePositiveStep ι)
    {u : ι → ℝ} {f g : ι → ℝ} {radius : ℝ}
    (h : UniformError f g radius) :
    UniformError (K.drivenStep u f) (K.drivenStep u g) radius := by
  refine ⟨h.radius_nonneg, ?_⟩
  intro i
  simpa [drivenStep, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using h.bound i

/-- A discrete maximum-principle bound with a separately certified source. -/
theorem drivenStep_bounds (K : FinitePositiveStep ι) (u f : ι → ℝ)
    (lower upper sourceLower sourceUpper : ℝ)
    (hlo : ∀ j, lower ≤ u j) (hhi : ∀ j, u j ≤ upper)
    (hslo : ∀ i, sourceLower ≤ f i)
    (hshi : ∀ i, f i ≤ sourceUpper) :
    ∀ i, lower + sourceLower ≤ K.drivenStep u f i ∧
      K.drivenStep u f i ≤ upper + sourceUpper := by
  intro i
  have hstep := K.step_bounds u lower upper hlo hhi i
  change lower + sourceLower ≤ K.step u i + f i ∧
    K.step u i + f i ≤ upper + sourceUpper
  constructor <;> linarith [hstep.1, hstep.2, hslo i, hshi i]

/-- A finite trajectory certificate for an inhomogeneous update.

The exact source recurrence and every approximate one-step residual are
stored separately.  Consequently a later error bound cannot be constructed
without naming the forcing term and every local residual. -/
structure DrivenTrajectoryCertificate
    (K : FinitePositiveStep ι)
    (source : ℕ → (ι → ℝ))
    (exact approximate : ℕ → (ι → ℝ))
    (initialRadius : ℝ) (stepRadius : ℕ → ℝ) : Prop where
  initial_nonneg : 0 ≤ initialRadius
  step_nonneg : ∀ n, 0 ≤ stepRadius n
  initial : UniformError (exact 0) (approximate 0) initialRadius
  exact_step : ∀ n,
    exact (n + 1) = K.drivenStep (exact n) (source n)
  step : ∀ n,
    UniformError (K.drivenStep (approximate n) (source n))
      (approximate (n + 1)) (stepRadius n)

theorem DrivenTrajectoryCertificate.bound
    {K : FinitePositiveStep ι}
    {source : ℕ → (ι → ℝ)}
    {exact approximate : ℕ → (ι → ℝ)}
    {initialRadius : ℝ} {stepRadius : ℕ → ℝ}
    (C : DrivenTrajectoryCertificate K source exact approximate
      initialRadius stepRadius) (n : ℕ) :
    UniformError (exact n) (approximate n)
      (propagatedRadius initialRadius stepRadius n) := by
  induction n with
  | zero => simpa using C.initial
  | succ n ih =>
      have hprop := K.drivenStep_uniformError (f := source n)
        (K.step_uniformError ih)
      have hnext := UniformError.trans hprop (C.step n)
      rw [C.exact_step n]
      simpa [propagatedRadius_succ] using hnext

/-! A forcing term is often discretized independently of the state.  The
following certificate records that second error source explicitly. -/

/-- Exact and approximate driven trajectories with independently approximated
source/forcing fields.  `source_error` and `step` are both required at every
time step, so a bound cannot silently discard forcing discretisation error. -/
structure SourceDrivenTrajectoryCertificate
    (K : FinitePositiveStep ι)
    (exactSource approximateSource : ℕ → (ι → ℝ))
    (exact approximate : ℕ → (ι → ℝ))
    (initialRadius : ℝ) (sourceRadius stepRadius : ℕ → ℝ) : Prop where
  initial_nonneg : 0 ≤ initialRadius
  source_nonneg : ∀ n, 0 ≤ sourceRadius n
  step_nonneg : ∀ n, 0 ≤ stepRadius n
  initial : UniformError (exact 0) (approximate 0) initialRadius
  exact_step : ∀ n,
    exact (n + 1) = K.drivenStep (exact n) (exactSource n)
  source_error : ∀ n,
    UniformError (exactSource n) (approximateSource n) (sourceRadius n)
  step : ∀ n,
    UniformError (K.drivenStep (approximate n) (approximateSource n))
      (approximate (n + 1)) (stepRadius n)

/-- Radius propagated by a trajectory with a separately approximated source. -/
def sourcePropagatedRadius (initial : ℝ)
    (sourceRadius stepRadius : ℕ → ℝ) : ℕ → ℝ
  | 0 => initial
  | n + 1 =>
      sourcePropagatedRadius initial sourceRadius stepRadius n +
        sourceRadius n + stepRadius n

@[simp] theorem sourcePropagatedRadius_zero (initial : ℝ)
    (sourceRadius stepRadius : ℕ → ℝ) :
    sourcePropagatedRadius initial sourceRadius stepRadius 0 = initial := rfl

@[simp] theorem sourcePropagatedRadius_succ (initial : ℝ)
    (sourceRadius stepRadius : ℕ → ℝ) (n : ℕ) :
    sourcePropagatedRadius initial sourceRadius stepRadius (n + 1) =
      sourcePropagatedRadius initial sourceRadius stepRadius n +
        sourceRadius n + stepRadius n := rfl

theorem sourcePropagatedRadius_nonneg {initial : ℝ}
    {sourceRadius stepRadius : ℕ → ℝ}
    (hi : 0 ≤ initial) (hs : ∀ n, 0 ≤ sourceRadius n)
    (ht : ∀ n, 0 ≤ stepRadius n) :
    ∀ n, 0 ≤ sourcePropagatedRadius initial sourceRadius stepRadius n := by
  intro n
  induction n with
  | zero => exact hi
  | succ n ih =>
      simp only [sourcePropagatedRadius_succ]
      exact add_nonneg (add_nonneg ih (hs n)) (ht n)

theorem SourceDrivenTrajectoryCertificate.bound
    {K : FinitePositiveStep ι}
    {exactSource approximateSource : ℕ → (ι → ℝ)}
    {exact approximate : ℕ → (ι → ℝ)}
    {initialRadius : ℝ} {sourceRadius stepRadius : ℕ → ℝ}
    (C : SourceDrivenTrajectoryCertificate K exactSource approximateSource
      exact approximate initialRadius sourceRadius stepRadius) (n : ℕ) :
    UniformError (exact n) (approximate n)
      (sourcePropagatedRadius initialRadius sourceRadius stepRadius n) := by
  induction n with
  | zero => simpa using C.initial
  | succ n ih =>
      have hstate := K.drivenStep_uniformError (f := exactSource n)
        (K.step_uniformError ih)
      have hsource := K.drivenStep_source_uniformError
        (u := approximate n) (C.source_error n)
      have hlocal := UniformError.trans hsource (C.step n)
      have hnext := UniformError.trans hstate hlocal
      rw [C.exact_step n]
      simpa [sourcePropagatedRadius_succ, add_assoc] using hnext

/-! Physics-facing names make the same certificate discoverable in domain
documentation and diagnostics while preserving one checked implementation. -/

abbrev FiniteDrivenParabolicStep := FinitePositiveStep
abbrev FiniteForcedHeatStep := FinitePositiveStep
abbrev FiniteForcedDiffusionStep := FinitePositiveStep
abbrev FiniteInhomogeneousMarkovStep := FinitePositiveStep
abbrev FiniteForcedMasterEquationStep := FinitePositiveStep

end FinitePositiveStep

end LeanPhy.Mathematics
