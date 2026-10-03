import LeanPhy.Quantum.NamedFinite
import LeanPhy.StatMech.FiniteKernel

/-!
# Classical finite dynamics in a named diagonal quantum basis

This adapter makes the shared finite-label boundary explicit: a Markov kernel
acts on a `FiniteProbability`, and the resulting state is embedded as a
diagonal density matrix.  The expectation theorem exposes the observable-side
pullback, so statistical-mechanics, lattice and measurement post-processing
calculations can reuse the same finite quantum matrix API.  No claim about
continuous-time Markov processes or quantum channels is made here.
-/

namespace LeanPhy.Quantum

open LeanPhy.StatMech
open scoped BigOperators Matrix ComplexOrder

noncomputable def namedDiagonalStep {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : FiniteKernel ι) (p : FiniteProbability ι) : NamedState ι :=
  diagonalNamedState (K.step p)

theorem namedDiagonalStep_isDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : FiniteKernel ι) (p : FiniteProbability ι) :
    IsNamedDensity (namedDiagonalStep K p) := by
  exact diagonalNamedState_isDensity (K.step p)

theorem namedDiagonalStep_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : FiniteKernel ι) (p : FiniteProbability ι) (f : ι → ℝ) :
    namedTrace (namedDiagonalStep K p * diagonalNamedObservable f) =
      ((p.expectation (K.pullback f) : ℝ) : ℂ) := by
  unfold namedDiagonalStep
  rw [diagonalNamed_expectation_eq, K.step_expectation]

theorem namedDiagonalStep_purity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : FiniteKernel ι) (p : FiniteProbability ι) :
    namedMatrixPurity (namedDiagonalStep K p) =
      ((K.step p).collisionProbability : ℂ) := by
  exact diagonalNamed_purity_eq_collision (K.step p)

end LeanPhy.Quantum
