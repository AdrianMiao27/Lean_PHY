import LeanPhy.Quantum.Unitary
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option autoImplicit false

/-!
# Finite fermionic Nambu coefficient matrices

Mode labels include sites, orbitals and spin. The full Nambu order is `(c,c†)`.
Hermitian normal coefficients and antisymmetric pairing coefficients determine
`[[h, Δ], [Δ†, -hᵀ]]`. Particle-hole conjugation swaps the two sectors AND
conjugates coefficients; it is antilinear, not unitary matrix conjugation alone.
These are coefficient matrices, not many-body density matrices.
-/

namespace LeanPhy.FieldTheory.FermionBdG

open LeanPhy.Quantum
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure Coefficients (ι : Type*) where
  normal : Matrix ι ι ℂ
  pairing : Matrix ι ι ℂ
  normal_hermitian : normal.IsHermitian
  pairing_skew : pairing.transpose = -pairing

namespace Coefficients

variable (K : Coefficients ι)

def matrix : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks K.normal K.pairing K.pairingᴴ (-K.normal.transpose)

theorem matrix_hermitian : K.matrix.IsHermitian :=
  K.normal_hermitian.fromBlocks rfl K.normal_hermitian.transpose.neg

theorem pairing_skew_apply (i j : ι) : K.pairing j i = -K.pairing i j :=
  congrArg (fun A : Matrix ι ι ℂ => A i j) K.pairing_skew

theorem normal_hermitian_apply (i j : ι) : star (K.normal j i) = K.normal i j :=
  congrArg (fun A : Matrix ι ι ℂ => A i j) K.normal_hermitian

/-- Spinless on-site pairing is forbidden by fermionic antisymmetry. -/
theorem pairing_diagonal (i : ι) : K.pairing i i = 0 := by
  have h := K.pairing_skew_apply i i
  linear_combination (1 / 2 : ℂ) * h

end Coefficients

/-- Full particle-hole action on a Nambu vector, with complex conjugation. -/
def particleHole (v : ι ⊕ ι → ℂ) : ι ⊕ ι → ℂ := fun i => star (v i.swap)

@[simp] theorem particleHole_zero : particleHole (0 : ι ⊕ ι → ℂ) = 0 := by
  ext i
  simp [particleHole]

@[simp] theorem particleHole_involution (v : ι ⊕ ι → ℂ) :
    particleHole (particleHole v) = v := by ext i; simp [particleHole]

theorem particleHole_smul (c : ℂ) (v : ι ⊕ ι → ℂ) :
    particleHole (c • v) = star c • particleHole v := by
  ext i
  simp [particleHole, star_mul, mul_comm]

/-- The associated matrix operation is conjugate-linear as well. -/
def holeMatrix (A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  fun i j => star (A i.swap j.swap)

theorem Coefficients.particle_hole (K : Coefficients ι) : holeMatrix K.matrix = -K.matrix := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp only [holeMatrix, Coefficients.matrix, Matrix.fromBlocks, Matrix.of_apply,
    Sum.elim_inl, Sum.elim_inr,
    Sum.swap_inl, Sum.swap_inr, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    Matrix.neg_apply, star_neg, star_star, neg_neg]
  · rw [K.normal_hermitian_apply]
  · exact K.pairing_skew_apply i j
  · rw [K.pairing_skew_apply i j, star_neg, neg_neg]
  · exact K.normal_hermitian_apply j i

theorem particleHole_mulVec (A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (v : ι ⊕ ι → ℂ) :
    particleHole (A.mulVec v) = (holeMatrix A).mulVec (particleHole v) := by
  ext i
  simp [particleHole, holeMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    star_sum, star_mul, mul_comm, add_comm]

/-- An eigen-equation maps to the opposite conjugate energy. -/
theorem Coefficients.partner_equation (K : Coefficients ι) (v : ι ⊕ ι → ℂ)
    (z : ℂ) (hv : K.matrix.mulVec v = z • v) :
    K.matrix.mulVec (particleHole v) = (-star z) • particleHole v := by
  have h := congrArg particleHole hv
  rw [particleHole_mulVec, K.particle_hole, Matrix.neg_mulVec, particleHole_smul] at h
  simpa using congrArg Neg.neg h

theorem particleHole_ne_zero_iff (v : ι ⊕ ι → ℂ) : particleHole v ≠ 0 ↔ v ≠ 0 := by
  constructor
  · intro h hv
    subst hv
    exact h (by ext i; simp [particleHole])
  · intro h hv
    apply h
    have hh := congrArg particleHole hv
    simpa only [particleHole_involution, particleHole_zero] using hh

/-- Reindex modes without conflating orbital labels with Nambu sectors. -/
def Coefficients.relabel {κ : Type*} (K : Coefficients ι) (e : κ ≃ ι) : Coefficients κ where
  normal := K.normal.submatrix e e
  pairing := K.pairing.submatrix e e
  normal_hermitian := by
    ext i j
    exact K.normal_hermitian_apply (e i) (e j)
  pairing_skew := by
    ext i j
    exact K.pairing_skew_apply (e i) (e j)

theorem Coefficients.relabel_matrix {κ : Type*} (K : Coefficients ι) (e : κ ≃ ι) :
    (K.relabel e).matrix = K.matrix.submatrix (Equiv.sumCongr e e) (Equiv.sumCongr e e) := by
  ext i j
  cases i <;> cases j <;> rfl

/-- Orbital basis changes use a transpose, not an adjoint, on the pairing leg. -/
def Coefficients.rotate (K : Coefficients ι) (U : FiniteUnitary ι) : Coefficients ι where
  normal := U.op * K.normal * U.opᴴ
  pairing := U.op * K.pairing * U.op.transpose
  normal_hermitian := Matrix.isHermitian_mul_mul_conjTranspose U.op K.normal_hermitian
  pairing_skew := by
    simp [Matrix.transpose_mul, K.pairing_skew, Matrix.mul_assoc]

end LeanPhy.FieldTheory.FermionBdG
