import LeanPhy.Quantum.DiagonalState
import LeanPhy.StatMech.FiniteProbability
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# Spectral bridge for finite Hermitian operators

The finite matrix layer should not reimplement spectral theory.  Mathlib
already proves the Hermitian matrix spectral theorem; this module gives it a
physics-facing adapter for density matrices and observables.  The resulting
statements are useful for finite quantum systems, band/BdG Hamiltonians,
finite-volume field models, and Gibbs calculations.  Infinite-dimensional
spectral measures and continuous spectra remain outside this adapter.
-/

namespace LeanPhy.Quantum

open scoped BigOperators Matrix

theorem hermitian_spectral_theorem {n : Nat} (A : Operator n)
    (hA : A.IsHermitian) :
    A = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) :=
  hA.spectral_theorem

theorem density_eigenvalue_nonneg {n : Nat} (rho : State n)
    (hrho : IsDensity rho) (i : Fin n) :
    0 ≤ hrho.1.eigenvalues i :=
  hrho.2.1.eigenvalues_nonneg i

theorem density_eigenvalue_sum {n : Nat} (rho : State n)
    (hrho : IsDensity rho) :
    ∑ i, (hrho.1.eigenvalues i : ℂ) = 1 := by
  calc
    (∑ i, (hrho.1.eigenvalues i : ℂ)) = Matrix.trace rho := by
      symm
      exact hrho.1.trace_eq_sum_eigenvalues
    _ = 1 := hrho.2.2

theorem density_spectral_theorem {n : Nat} (rho : State n)
    (hrho : IsDensity rho) :
    rho = Unitary.conjStarAlgAut ℂ _ hrho.1.eigenvectorUnitary
      (Matrix.diagonal (fun i => (hrho.1.eigenvalues i : ℂ))) :=
  hrho.1.spectral_theorem

theorem hermitian_matrixPurity_eq_eigenvalue_secondMoment {n : Nat}
    (A : Operator n) (hA : A.IsHermitian) :
    matrixPurity A = ∑ i, (hA.eigenvalues i : ℂ) ^ 2 := by
  unfold matrixPurity
  conv_lhs => rw [hA.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  let U : Matrix (Fin n) (Fin n) ℂ := hA.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hU : star U * U = 1 := by
    exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hU' : Matrix.conjTranspose U * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hU
  change Matrix.trace ((U * D * Matrix.conjTranspose U) *
      (U * D * Matrix.conjTranspose U)) = _
  have hprod : (U * D * Matrix.conjTranspose U) *
      (U * D * Matrix.conjTranspose U) = U * (D * D) * Matrix.conjTranspose U := by
    calc
      (U * D * Matrix.conjTranspose U) *
          (U * D * Matrix.conjTranspose U) =
          U * D * (Matrix.conjTranspose U * U) * D * Matrix.conjTranspose U := by
            noncomm_ring
      _ = U * (D * D) * Matrix.conjTranspose U := by rw [hU']; noncomm_ring
  rw [hprod, Matrix.trace_mul_cycle, hU', Matrix.one_mul]
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp [pow_two]

/-- The spectrum of a finite density matrix is itself a classical finite
probability distribution on its (multiplicity-indexed) eigenvalue labels. -/
noncomputable def densitySpectrumProbability {n : Nat}
    (rho : State n) (hrho : IsDensity rho) :
    LeanPhy.StatMech.FiniteProbability (Fin n) where
  weight := hrho.1.eigenvalues
  nonneg := density_eigenvalue_nonneg rho hrho
  normalised := by
    have h := congrArg Complex.re (density_eigenvalue_sum rho hrho)
    simpa using h

theorem density_matrixPurity_eq_spectrum_collision {n : Nat}
    (rho : State n) (hrho : IsDensity rho) :
    matrixPurity rho =
      (densitySpectrumProbability rho hrho).collisionProbability := by
  rw [hermitian_matrixPurity_eq_eigenvalue_secondMoment rho hrho.1]
  unfold LeanPhy.StatMech.FiniteProbability.collisionProbability
    densitySpectrumProbability
  change (∑ i, (hrho.1.eigenvalues i : ℂ) ^ 2) =
    (∑ i, (hrho.1.eigenvalues i ^ 2) : ℝ)
  norm_num [Complex.ofReal_sum]

end LeanPhy.Quantum
