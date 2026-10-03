import LeanPhy.Mathematics.Hilbert
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Weak variational solutions on Hilbert spaces

Many continuum physics calculations reduce first to a coercive weak problem:
elliptic PDE, Euclidean free fields, linear response and finite-element
discretisations all use the same step.  This module exposes the Lax--Milgram
theorem with a physics-facing certificate.  It proves existence, a checked
variational identity and uniqueness from an explicit coercivity witness.

The result is intentionally conditional.  A user still has to prove that the
chosen bilinear form is continuous and coercive, and to prove that the model's
boundary conditions really induce that form.  The certificate does not claim
regularity, a continuum limit, nonlinear well-posedness or a Navier--Stokes
theorem.
-/

namespace LeanPhy.Mathematics

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

/-- A coercive variational form, separated as a named LeanPhy assumption so it
can be recorded in a theory package or consumed by a downstream model. -/
structure LaxMilgramCertificate (B : V →L[ℝ] V →L[ℝ] ℝ) : Prop where
  coercive : IsCoercive B

namespace LaxMilgramCertificate

variable {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- The Riesz-represented weak solution for a right-hand side `f`. -/
noncomputable def solution (h : LaxMilgramCertificate B) (f : V) : V :=
  h.coercive.continuousLinearEquivOfBilin.symm f

/-- The variational equation solved by `solution`. -/
theorem solution_spec (h : LaxMilgramCertificate B) (f w : V) :
    B (h.solution f) w = inner ℝ f w := by
  have hs := h.coercive.continuousLinearEquivOfBilin_apply
    (h.coercive.continuousLinearEquivOfBilin.symm f) w
  rw [ContinuousLinearEquiv.apply_symm_apply] at hs
  exact hs.symm

/-- The weak solution is unique among vectors satisfying the variational
equation. -/
theorem solution_unique (h : LaxMilgramCertificate B) (f u : V)
    (hu : ∀ w, B u w = inner ℝ f w) :
    u = h.solution f := by
  have hT : Function.Injective (InnerProductSpace.continuousLinearMapOfBilin B) :=
    LinearMap.ker_eq_bot.mp h.coercive.ker_eq_bot
  apply hT
  apply ext_inner_right ℝ
  intro w
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  exact (hu w).trans (h.solution_spec f w).symm

/-- A coercive form has no nontrivial homogeneous weak solution. -/
theorem homogeneous_unique (h : LaxMilgramCertificate B) {u : V}
    (hu : ∀ w, B u w = 0) : u = 0 := by
  have hu' : ∀ w, B u w = inner ℝ (0 : V) w := by
    intro w
    rw [hu w]
    simp
  simpa [solution] using h.solution_unique 0 u hu'

end LaxMilgramCertificate

end LeanPhy.Mathematics
