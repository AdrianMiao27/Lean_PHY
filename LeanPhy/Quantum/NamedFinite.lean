import LeanPhy.StatMech.FiniteProbability
import LeanPhy.StatMech.FiniteGibbs
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

/-!
# Finite quantum states with named basis labels

Most matrix APIs in LeanPhy use `Fin n` because it makes dimensions explicit.
Many physical models, however, have a useful finite label type: lattice sites,
spin projections, bands, colours, or polarization modes.  This adapter keeps
those labels while reusing the same Hermitian, positivity, trace and diagonal
probability proofs.  It is a finite matrix layer and makes no claim about
continuous or infinite-dimensional bases.
-/

namespace LeanPhy.Quantum

open LeanPhy.StatMech
open scoped BigOperators Matrix ComplexOrder

abbrev NamedState (ι : Type*) [Fintype ι] := Matrix ι ι ℂ

def namedTrace {ι : Type*} [Fintype ι] (rho : NamedState ι) : ℂ :=
  Matrix.trace rho

def IsNamedDensity {ι : Type*} [Fintype ι] (rho : NamedState ι) : Prop :=
  rho.IsHermitian ∧ rho.PosSemidef ∧ namedTrace rho = 1

noncomputable def diagonalNamedState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : FiniteProbability ι) : NamedState ι :=
  Matrix.diagonal (fun i => (p.weight i : ℂ))

theorem diagonalNamedState_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : FiniteProbability ι) :
    (diagonalNamedState p).IsHermitian := by
  classical
  unfold diagonalNamedState
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  rw [isSelfAdjoint_iff]
  simp

theorem diagonalNamedState_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : FiniteProbability ι) :
    (diagonalNamedState p).PosSemidef := by
  classical
  apply Matrix.PosSemidef.diagonal
  intro i
  exact Complex.nonneg_iff.mpr ⟨p.nonneg i, by simp⟩

theorem diagonalNamedState_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : FiniteProbability ι) :
    namedTrace (diagonalNamedState p) = (1 : ℂ) := by
  classical
  unfold namedTrace diagonalNamedState
  rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, p.normalised]
  simp

theorem diagonalNamedState_isDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : FiniteProbability ι) :
    IsNamedDensity (diagonalNamedState p) := by
  exact ⟨diagonalNamedState_isHermitian p, diagonalNamedState_posSemidef p,
    diagonalNamedState_trace p⟩

noncomputable def namedMatrixPurity {ι : Type*} [Fintype ι]
    (rho : NamedState ι) : ℂ :=
  namedTrace (rho * rho)

noncomputable def diagonalNamedObservable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) : NamedState ι :=
  Matrix.diagonal (fun i => (f i : ℂ))

theorem diagonalNamed_expectation_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : FiniteProbability ι) (f : ι → ℝ) :
    namedTrace (diagonalNamedState p * diagonalNamedObservable f) =
      (p.expectation f : ℂ) := by
  classical
  unfold namedTrace diagonalNamedState diagonalNamedObservable
    FiniteProbability.expectation
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  norm_num [Complex.ofReal_sum, mul_comm]

theorem diagonalNamed_purity_eq_collision {ι : Type*} [Fintype ι]
    [DecidableEq ι] (p : FiniteProbability ι) :
    namedMatrixPurity (diagonalNamedState p) =
      (p.collisionProbability : ℂ) := by
  classical
  unfold namedMatrixPurity namedTrace diagonalNamedState
    FiniteProbability.collisionProbability
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  norm_num [Complex.ofReal_sum, pow_two]

/-- The finite Gibbs state in a named basis. -/
noncomputable def diagonalGibbsState {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (β : ℝ) (E : ι → ℝ) : NamedState ι :=
  diagonalNamedState (finiteGibbsProbability β E)

theorem diagonalGibbsState_isDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (β : ℝ) (E : ι → ℝ) :
    IsNamedDensity (diagonalGibbsState β E) := by
  exact diagonalNamedState_isDensity (finiteGibbsProbability β E)

theorem diagonalGibbs_expectation_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (β : ℝ) (E f : ι → ℝ) :
    namedTrace (diagonalGibbsState β E * diagonalNamedObservable f) =
      ((finiteGibbsProbability β E).expectation f : ℂ) := by
  exact diagonalNamed_expectation_eq (finiteGibbsProbability β E) f

theorem diagonalGibbs_purity_eq_collision {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (β : ℝ) (E : ι → ℝ) :
    namedMatrixPurity (diagonalGibbsState β E) =
      ((finiteGibbsProbability β E).collisionProbability : ℂ) := by
  exact diagonalNamed_purity_eq_collision (finiteGibbsProbability β E)

end LeanPhy.Quantum
