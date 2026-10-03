import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing

/-!
# Finite bilinear-form isometries

The same matrix equation appears in several physical domains: symplectic maps
preserve `J`, Lorentz maps preserve `eta`, and lattice or material symmetries
preserve other finite bilinear forms.  The form is an explicit parameter so a
model must state its convention; the kernel then supplies composition closure.
-/

namespace LeanPhy.Mathematics

open scoped Matrix

structure BilinearIsometry {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (form : Matrix ι ι R) where
  op : Matrix ι ι R
  preserve : opᵀ * form * op = form

def BilinearIsometry.identity {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (form : Matrix ι ι R) : BilinearIsometry form where
  op := 1
  preserve := by simp

def BilinearIsometry.compose {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] {form : Matrix ι ι R}
    (after before : BilinearIsometry form) : BilinearIsometry form where
  op := after.op * before.op
  preserve := by
    calc
      (after.op * before.op)ᵀ * form * (after.op * before.op) =
          before.opᵀ * (after.opᵀ * form * after.op) * before.op := by
            rw [Matrix.transpose_mul]
            noncomm_ring
      _ = before.opᵀ * form * before.op := by rw [after.preserve]
      _ = form := before.preserve

theorem BilinearIsometry.compose_op {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] {form : Matrix ι ι R}
    (after before : BilinearIsometry form) :
    (after.compose before).op = after.op * before.op := rfl

end LeanPhy.Mathematics
