import LeanPhy.Classical.Symplectic
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# A small Hamiltonian interface

This file is the first classical-mechanics layer above the symplectic matrix
API.  It deliberately stays in the finite, algebraic fragment: affine phase
space observables have an exact Poisson bracket, and the dimensionless harmonic
oscillator flow is represented by a rotation.  No derivative, limit or
existence theorem is hidden here.  A future calculus layer can map concrete
functions and their gradients into this interface.
-/

namespace LeanPhy.Classical

open scoped Matrix

/-- A dimensionless point `(q,p)` in a one-degree-of-freedom phase space. -/
abbrev PhasePoint := Fin 2 → ℝ

/-- An affine observable `a q + b p + c`.

The coefficients are stored explicitly so the canonical Poisson bracket is
decidable by ring normalization. -/
structure AffineObservable where
  qCoeff : ℝ
  pCoeff : ℝ
  constant : ℝ

instance : Add AffineObservable where
  add f g :=
    { qCoeff := f.qCoeff + g.qCoeff
      pCoeff := f.pCoeff + g.pCoeff
      constant := f.constant + g.constant }

instance : Zero AffineObservable where
  zero := { qCoeff := 0, pCoeff := 0, constant := 0 }

/-- Evaluate an affine observable at a phase-space point. -/
def AffineObservable.eval (f : AffineObservable) (z : PhasePoint) : ℝ :=
  f.qCoeff * z 0 + f.pCoeff * z 1 + f.constant

/-- The canonical Poisson bracket of two affine observables. -/
def poisson (f g : AffineObservable) : ℝ :=
  f.qCoeff * g.pCoeff - f.pCoeff * g.qCoeff

/-- The canonical coordinate observables `q` and `p`. -/
def qObservable : AffineObservable := { qCoeff := 1, pCoeff := 0, constant := 0 }
def pObservable : AffineObservable := { qCoeff := 0, pCoeff := 1, constant := 0 }

theorem eval_qObservable (z : PhasePoint) : qObservable.eval z = z 0 := by
  simp [AffineObservable.eval, qObservable]

theorem eval_pObservable (z : PhasePoint) : pObservable.eval z = z 1 := by
  simp [AffineObservable.eval, pObservable]

theorem poisson_q_p : poisson qObservable pObservable = 1 := by
  simp [poisson, qObservable, pObservable]

theorem poisson_p_q : poisson pObservable qObservable = -1 := by
  simp [poisson, qObservable, pObservable]

theorem poisson_antisymm (f g : AffineObservable) :
    poisson f g = -poisson g f := by
  simp [poisson]
  ring

theorem poisson_add_left (f g h : AffineObservable) :
    poisson (f + g) h = poisson f h + poisson g h := by
  change (f.qCoeff + g.qCoeff) * h.pCoeff - (f.pCoeff + g.pCoeff) * h.qCoeff =
    f.qCoeff * h.pCoeff - f.pCoeff * h.qCoeff +
      (g.qCoeff * h.pCoeff - g.pCoeff * h.qCoeff)
  ring

theorem poisson_add_right (f g h : AffineObservable) :
    poisson f (g + h) = poisson f g + poisson f h := by
  change f.qCoeff * (g.pCoeff + h.pCoeff) - f.pCoeff * (g.qCoeff + h.qCoeff) =
    (f.qCoeff * g.pCoeff - f.pCoeff * g.qCoeff) +
      (f.qCoeff * h.pCoeff - f.pCoeff * h.qCoeff)
  ring

/-- The oscillator flow in normalized units, `(q,p) ↦ R θ (q,p)`. -/
noncomputable def oscillatorFlow (theta : ℝ) : PhasePoint → PhasePoint :=
  fun z =>
    (!![Real.cos theta, -Real.sin theta; Real.sin theta, Real.cos theta] : M2R) *ᵥ z

/-- The quadratic oscillator energy in normalized units. -/
def oscillatorEnergy (z : PhasePoint) : ℝ := z 0 * z 0 + z 1 * z 1

theorem oscillatorFlow_q (theta : ℝ) (z : PhasePoint) :
    oscillatorFlow theta z 0 = Real.cos theta * z 0 - Real.sin theta * z 1 := by
  simp [oscillatorFlow, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem oscillatorFlow_p (theta : ℝ) (z : PhasePoint) :
    oscillatorFlow theta z 1 = Real.sin theta * z 0 + Real.cos theta * z 1 := by
  simp [oscillatorFlow, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Harmonic oscillator evolution preserves its quadratic energy. -/
theorem oscillatorFlow_energy (theta : ℝ) (z : PhasePoint) :
    oscillatorEnergy (oscillatorFlow theta z) = oscillatorEnergy z := by
  rw [oscillatorEnergy, oscillatorFlow_q, oscillatorFlow_p, oscillatorEnergy]
  nlinarith [Real.sin_sq_add_cos_sq theta]

/-- Every oscillator flow is a canonical (symplectic) transformation. -/
theorem oscillatorFlow_symplectic (theta : ℝ) :
    (!![Real.cos theta, -Real.sin theta; Real.sin theta, Real.cos theta] : M2R)ᵀ
        * symplecticJ
        * !![Real.cos theta, -Real.sin theta; Real.sin theta, Real.cos theta]
      = symplecticJ :=
  rotation_symplectic theta

end LeanPhy.Classical
