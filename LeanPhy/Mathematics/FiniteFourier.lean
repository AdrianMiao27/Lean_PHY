import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import LeanPhy.Quantum.Unitary
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LeanPhy.Mathematics

open scoped Matrix
open LeanPhy.Quantum

/-- A finite Fourier system is a square complex kernel whose two orthogonality
relations are supplied explicitly.  Concrete roots-of-unity constructions,
normalisation conventions and physical boundary conditions can instantiate it
without weakening the kernel-checked inverse theorem. -/
structure FiniteFourierSystem (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] where
  kernel : Matrix α α ℂ
  left_orthogonal : Matrix.conjTranspose kernel * kernel =
    (Fintype.card α : ℂ) • (1 : Matrix α α ℂ)
  right_orthogonal : kernel * Matrix.conjTranspose kernel =
    (Fintype.card α : ℂ) • (1 : Matrix α α ℂ)

namespace FiniteFourierSystem

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] (F : FiniteFourierSystem α)

noncomputable def forward (x : α → ℂ) : α → ℂ := F.kernel.mulVec x

noncomputable def inverse (y : α → ℂ) : α → ℂ :=
  ((Fintype.card α : ℂ)⁻¹ • Matrix.conjTranspose F.kernel).mulVec y

omit [DecidableEq α] in
private theorem card_scalar_ne_zero : (Fintype.card α : ℂ) ≠ 0 := by
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)

theorem inverse_forward (x : α → ℂ) : F.inverse (F.forward x) = x := by
  unfold inverse forward
  rw [Matrix.smul_mulVec]
  rw [Matrix.mulVec_mulVec]
  rw [F.left_orthogonal]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  simp [smul_smul, card_scalar_ne_zero]

theorem forward_inverse (y : α → ℂ) : F.forward (F.inverse y) = y := by
  unfold inverse forward
  rw [Matrix.smul_mulVec]
  rw [Matrix.mulVec_smul]
  rw [Matrix.mulVec_mulVec]
  rw [F.right_orthogonal]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  simp [smul_smul, card_scalar_ne_zero]

/-! ## Finite Parseval identity

The transform interface also exposes the sesquilinear norm bookkeeping used
by finite-volume Hamiltonians and lattice response calculations.  The result
is stated with the unnormalised kernel convention used above; a normalized
unitary transform is obtained by the explicit factor `card⁻¹/²` at the model
layer.
-/

noncomputable def finiteInner {β : Type} [Fintype β]
    (x y : β → ℂ) : ℂ := dotProduct (star x) y

private theorem finiteInner_mulVec {β γ : Type} [Fintype β] [Fintype γ]
    (M : Matrix β γ ℂ) (x y : γ → ℂ) :
    finiteInner (M.mulVec x) (M.mulVec y) =
      finiteInner x ((Matrix.conjTranspose M * M).mulVec y) := by
  unfold finiteInner
  rw [Matrix.star_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_vecMul]
  rw [← Matrix.dotProduct_mulVec]

theorem parseval (x y : α → ℂ) :
    finiteInner (F.forward x) (F.forward y) =
      (Fintype.card α : ℂ) * finiteInner x y := by
  unfold forward
  rw [finiteInner_mulVec, F.left_orthogonal]
  simp [finiteInner, Matrix.smul_mulVec]

/-! ## Normalized Fourier transforms as finite unitaries

The orthogonality field is enough to construct a unitary matrix once a model
chooses its normalization factor.  Keeping the factor as an explicit
hypothesis avoids hiding convention choices (`1 / sqrt N`, `1 / N`, etc.) in
the kernel and lets lattice, optical and finite-volume models share the same
unitary dynamics API.
-/

noncomputable def normalizedUnitary (c : ℂ)
    (hc : star c * c * (Fintype.card α : ℂ) = 1) : FiniteUnitary α where
  op := c • F.kernel
  unitary := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    rw [F.left_orthogonal]
    simp only [smul_smul]
    rw [← mul_assoc, hc]
    simp


/-- The two-point Fourier/Hadamard kernel, a concrete finite witness used by
qubit circuits and one-cell lattice transforms. -/
noncomputable def hadamardFourier : FiniteFourierSystem (Fin 2) where
  kernel := !![1, 1; 1, -1]
  left_orthogonal := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        Matrix.of_apply, Matrix.one_apply] <;> norm_num
  right_orthogonal := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        Matrix.of_apply, Matrix.one_apply] <;> norm_num

theorem hadamard_inverse_forward (x : Fin 2 → ℂ) :
    hadamardFourier.inverse (hadamardFourier.forward x) = x :=
  hadamardFourier.inverse_forward x

/-! ## A four-site lattice/optics transform

The first nontrivial periodic transform is useful for four-site tight-binding
models, a four-point finite-volume calculation, and small optical mode
networks.  The orthogonality equations are checked entrywise, so the inverse
formula does not rely on an unrecorded convention about normalisation.
-/

noncomputable def fourier4 : FiniteFourierSystem (Fin 4) where
  kernel := !![1, 1, 1, 1;
               1, Complex.I, -1, -Complex.I;
               1, -1, 1, -1;
               1, -Complex.I, -1, Complex.I]
  left_orthogonal := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
        Matrix.of_apply, Complex.star_def] <;>
      norm_num [Complex.I_mul_I]
  right_orthogonal := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
        Matrix.of_apply, Complex.star_def] <;>
      norm_num [Complex.I_mul_I]

theorem fourier4_inverse_forward (x : Fin 4 → ℂ) :
    fourier4.inverse (fourier4.forward x) = x :=
  fourier4.inverse_forward x

theorem fourier4_forward_inverse (x : Fin 4 → ℂ) :
    fourier4.forward (fourier4.inverse x) = x :=
  fourier4.forward_inverse x

/-- The normalized four-point periodic transform is a finite unitary. -/
noncomputable def fourier4Unitary : FiniteUnitary (Fin 4) :=
  fourier4.normalizedUnitary (1 / 2 : ℂ) (by norm_num)

end FiniteFourierSystem

end LeanPhy.Mathematics
