import LeanPhy.Quantum.Density
import LeanPhy.StatMech.Entropy
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

/-!
# Classical distributions as diagonal quantum states

This finite adapter is a deliberately small interoperability layer.  A
classical distribution on `Fin n` is embedded as a diagonal density matrix.
The bridge identifies its matrix purity with the classical collision
probability, so statistical-mechanics and quantum-information statements can
reuse the same second-moment API.

No spectral theorem, measure theory, or infinite-dimensional Hilbert space is
used here.
-/

namespace LeanPhy.Quantum

open LeanPhy.StatMech
open scoped BigOperators Matrix ComplexOrder

/-- The diagonal density matrix associated with a finite distribution. -/
noncomputable def diagonalState {n : Nat} (p : FiniteDistribution n) : State n :=
  Matrix.diagonal (fun i => (p.weight i : ℂ))

theorem diagonalState_isHermitian {n : Nat} (p : FiniteDistribution n) :
    (diagonalState p).IsHermitian := by
  unfold diagonalState
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  rw [isSelfAdjoint_iff]
  simp

theorem diagonalState_posSemidef {n : Nat} (p : FiniteDistribution n) :
    (diagonalState p).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  exact Complex.nonneg_iff.mpr ⟨p.nonneg i, by simp⟩

theorem diagonalState_trace {n : Nat} (p : FiniteDistribution n) :
    trace (diagonalState p) = (1 : ℂ) := by
  unfold trace diagonalState
  rw [Matrix.trace_diagonal]
  rw [← Complex.ofReal_sum]
  rw [p.normalised]
  simp

theorem diagonalState_isDensity {n : Nat} (p : FiniteDistribution n) :
    IsDensity (diagonalState p) := by
  exact ⟨diagonalState_isHermitian p, diagonalState_posSemidef p,
    diagonalState_trace p⟩

/-- A real finite observable embedded as a diagonal quantum observable. -/
noncomputable def diagonalObservable {n : Nat} (f : Fin n → ℝ) : Observable n :=
  Matrix.diagonal (fun i => (f i : ℂ))

theorem diagonal_expectation_eq {n : Nat} (p : FiniteDistribution n)
    (f : Fin n → ℝ) :
    expectation (diagonalState p) (diagonalObservable f) =
      (p.expectation f : ℂ) := by
  unfold expectation trace diagonalState diagonalObservable
  unfold FiniteDistribution.expectation
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  norm_num [Complex.ofReal_sum, mul_comm]

/-- Matrix purity, kept at the finite algebraic boundary. -/
noncomputable def matrixPurity {n : Nat} (rho : State n) : ℂ :=
  trace (rho * rho)

theorem diagonalState_purity {n : Nat} (p : FiniteDistribution n) :
    matrixPurity (diagonalState p) = (p.collisionProbability : ℂ) := by
  unfold matrixPurity diagonalState trace FiniteDistribution.collisionProbability
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  norm_num [Complex.ofReal_sum, pow_two]

end LeanPhy.Quantum
