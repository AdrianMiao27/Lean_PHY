import LeanPhy.FieldTheory.FermionBdG
import LeanPhy.FieldTheory.FermionLinear
import LeanPhy.Quantum.SpectralGap

set_option autoImplicit false

/-! Orbital basis changes act on particles by U and holes by conjugate U.
Pairing therefore transforms with U Δ Uᵀ. The induced Nambu unitary preserves
the finite spectral-gap predicate, and transformed CAR generators preserve the
actual many-body quadratic operator when coefficients are transported too. -/

namespace LeanPhy.FieldTheory.FermionBdG

open LeanPhy.Quantum
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bar (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := A.map (starRingEnd ℂ)

theorem bar_mul (A B : Matrix ι ι ℂ) : bar (A * B) = bar A * bar B :=
  Matrix.map_mul

@[simp] theorem bar_one : bar (1 : Matrix ι ι ℂ) = 1 := by
  ext i j
  simp [bar, Matrix.one_apply]

@[simp] theorem bar_adjoint (A : Matrix ι ι ℂ) : bar Aᴴ = (bar A)ᴴ := by
  ext i j
  simp [bar, Matrix.conjTranspose_apply]

@[simp] theorem bar_adjoint_eq_transpose (A : Matrix ι ι ℂ) : (bar A)ᴴ = A.transpose := by
  ext i j
  simp [bar, Matrix.conjTranspose_apply]

@[simp] theorem transpose_adjoint_eq_bar (A : Matrix ι ι ℂ) : Aᴴ.transpose = bar A := by
  ext i j
  rfl

@[simp] theorem adjoint_transpose_eq_bar (A : Matrix ι ι ℂ) : A.transposeᴴ = bar A := by
  ext i j
  rfl

def conjugateUnitary (U : FiniteUnitary ι) : FiniteUnitary ι where
  op := bar U.op
  unitary := by
    rw [← bar_adjoint, ← bar_mul, U.unitary, bar_one]

/-- Full Nambu lift of an orbital unitary. -/
def nambuUnitary (U : FiniteUnitary ι) : FiniteUnitary (ι ⊕ ι) where
  op := Matrix.fromBlocks U.op 0 0 (bar U.op)
  unitary := by
    have hu : (bar U.op)ᴴ * bar U.op = 1 := (conjugateUnitary U).unitary
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      U.unitary, hu]
    rw [Matrix.fromBlocks_one]

theorem Coefficients.rotate_matrix (K : Coefficients ι) (U : FiniteUnitary ι) :
    (K.rotate U).matrix = (nambuUnitary U).conjugate K.matrix := by
  simp [Coefficients.matrix, Coefficients.rotate, FiniteUnitary.conjugate, nambuUnitary,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.transpose_mul, Matrix.mul_assoc]

theorem Coefficients.rotate_gap_iff (K : Coefficients ι) (U : FiniteUnitary ι)
    (center radius : ℝ) :
    IsFiniteSpectralGap (K.rotate U).matrix center radius ↔
      IsFiniteSpectralGap K.matrix center radius := by
  rw [K.rotate_matrix]
  exact (nambuUnitary U).conjugate_isFiniteSpectralGap_iff K.matrix center radius

section Operators

variable {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A]
variable [StarRing A] [StarModule ℂ A]

/-- Rotate both generators and coefficient tables; the many-body operator is unchanged. -/
theorem quadratic_rotate (M : MultiModeCAR ι A) (K : Coefficients ι) (U : FiniteUnitary ι) :
    (M.rotate U).quadratic (K.rotate U).normal (K.rotate U).pairing =
      M.quadratic K.normal K.pairing := by
  have hn : U.opᴴ * (U.op * K.normal * U.opᴴ) * U.op = K.normal := by
    simp [← Matrix.mul_assoc, U.unitary]
    rw [Matrix.mul_assoc, U.unitary, Matrix.mul_one]
  have hp : U.opᴴ * (U.op * K.pairing * U.op.transpose) * bar U.op = K.pairing := by
    have hh : U.op.transpose * bar U.op = 1 := by
      simpa only [conjugateUnitary, bar_adjoint_eq_transpose] using (conjugateUnitary U).unitary
    calc
      _ = (U.opᴴ * U.op) * K.pairing * (U.op.transpose * bar U.op) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [U.unitary, hh]; simp
  simp only [MultiModeCAR.quadratic, MultiModeCAR.rotate, Coefficients.rotate,
    M.normal_mix, M.creationPair_mix, hn]
  change M.normal K.normal + (1 / 2 : ℂ) •
    (M.creationPair (U.opᴴ * (U.op * K.pairing * U.op.transpose) * bar U.op) +
      star (M.creationPair (U.opᴴ * (U.op * K.pairing * U.op.transpose) * bar U.op))) = _
  rw [hp]

end Operators
end LeanPhy.FieldTheory.FermionBdG
