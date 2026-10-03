import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# Two-dimensional symplectic linear algebra

A linear canonical transformation of one classical degree of freedom preserves
the symplectic form

    J = [[0, 1], [-1, 0]],       A^T J A = J.

This same condition appears in Hamiltonian mechanics, paraxial optics,
accelerator lattices and bosonic Gaussian quantum mechanics.  In two dimensions
it is especially useful that the condition is exactly `det A = 1`.  The kernel
checks that equivalence, closure under composition, and the canonical rotation
and shear families.  The result is a small reusable algebraic layer: a proposed
phase-space update can be checked by one determinant or one matrix identity.

Only finite-dimensional linear algebra is used.  Hamiltonian flows, generating
functions, Poisson brackets and the nonlinear symplectic group are future layers;
no differentiability or dynamical claim is hidden in this module.
-/

namespace LeanPhy.Classical

open scoped Matrix

/-- Two-dimensional real phase-space matrices. -/
abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The standard symplectic form `dq ∧ dp`. -/
noncomputable def symplecticJ : M2R := !![0, 1; -1, 0]

/-- A generic `2 x 2` real matrix. -/
noncomputable def phaseMatrix (a b c d : ℝ) : M2R := !![a, b; c, d]

/-- In one degree of freedom, symplectic is exactly determinant one. -/
theorem symplectic_iff_det (A : M2R) :
    Aᵀ * symplecticJ * A = symplecticJ ↔ A.det = 1 := by
  constructor
  · intro h
    have h01 := congrArg (fun M : M2R => M 0 1) h
    simp [symplecticJ, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] at h01
    have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      linarith [h01]
    simpa [Matrix.det_fin_two] using hdet
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symplecticJ, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two, Matrix.det_fin_two] at h ⊢ <;>
      linarith

/-- Products of symplectic transformations are symplectic. -/
theorem symplectic_mul (A B : M2R)
    (hA : Aᵀ * symplecticJ * A = symplecticJ)
    (hB : Bᵀ * symplecticJ * B = symplecticJ) :
    (A * B)ᵀ * symplecticJ * (A * B) = symplecticJ := by
  calc
    (A * B)ᵀ * symplecticJ * (A * B) = Bᵀ * (Aᵀ * symplecticJ * A) * B := by
      rw [Matrix.transpose_mul]
      noncomm_ring
    _ = Bᵀ * symplecticJ * B := by rw [hA]
    _ = symplecticJ := hB

/-- A phase-space rotation is symplectic. -/
theorem rotation_symplectic (theta : ℝ) :
    (!![Real.cos theta, -Real.sin theta; Real.sin theta, Real.cos theta] : M2R)ᵀ
        * symplecticJ
        * !![Real.cos theta, -Real.sin theta; Real.sin theta, Real.cos theta]
      = symplecticJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticJ, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  all_goals nlinarith [Real.sin_sq_add_cos_sq theta]

/-- A free-particle shear `(q,p) ↦ (q + t p,p)` is symplectic. -/
theorem shear_symplectic (t : ℝ) :
    (!![1, t; 0, 1] : M2R)ᵀ * symplecticJ * !![1, t; 0, 1] = symplecticJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticJ, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  all_goals ring

/-- The determinant form of the canonical condition for a concrete matrix. -/
theorem phaseMatrix_symplectic_iff (a b c d : ℝ) :
    (phaseMatrix a b c d)ᵀ * symplecticJ * phaseMatrix a b c d = symplecticJ ↔
      a * d - b * c = 1 := by
  rw [symplectic_iff_det]
  simp [phaseMatrix, Matrix.det_fin_two]

end LeanPhy.Classical
