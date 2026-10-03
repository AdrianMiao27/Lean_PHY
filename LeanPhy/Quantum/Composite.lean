import LeanPhy.Quantum.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Fintype.Prod

/-!
# Composite systems: tensor products and partial traces

Composite finite-dimensional systems are represented by `Matrix.kroneckerMap`,
so associativity and mixed-product laws are inherited from mathlib rather than
re-proved here.  The partial trace is defined from the Kronecker basis and its
defining property is proved entrywise.
-/

namespace LeanPhy.Quantum

open Matrix

/-- Tensor product of two operators on finite-dimensional spaces. -/
def tensorOp {m n : Nat} (A : Operator m) (B : Operator n) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  Matrix.kroneckerMap (· * ·) A B

theorem tensorOp_apply {m n : Nat} (A : Operator m) (B : Operator n)
    (i j : Fin m × Fin n) :
    tensorOp A B i j = A i.1 j.1 * B i.2 j.2 := by
  simp [tensorOp, Matrix.kroneckerMap_apply]

theorem tensorOp_one {m n : Nat} :
    tensorOp (1 : Operator m) (1 : Operator n) = 1 := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [tensorOp, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases h : i = j <;> by_cases h2 : k = l <;> simp [h, h2]

/-- Bilinearity of the tensor product in the left argument. -/
theorem tensorOp_add_left {m n : Nat} (A B : Operator m) (C : Operator n) :
    tensorOp (A + B) C = tensorOp A C + tensorOp B C := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [tensorOp, Matrix.kroneckerMap_apply, Matrix.add_apply]
  ring

/-- Bilinearity of the tensor product in the right argument. -/
theorem tensorOp_add_right {m n : Nat} (A : Operator m) (B C : Operator n) :
    tensorOp A (B + C) = tensorOp A B + tensorOp A C := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [tensorOp, Matrix.kroneckerMap_apply, Matrix.add_apply]
  ring

/-- Mixed-product law: `(A ⊗ B) * (C ⊗ D) = (A * C) ⊗ (B * D)`. -/
theorem tensorOp_mul {m n : Nat} (A C : Operator m) (B D : Operator n) :
    tensorOp A B * tensorOp C D = tensorOp (A * C) (B * D) := by
  simpa [tensorOp, Matrix.kroneckerMap, mul_comm] using
    (Matrix.mul_kronecker_mul (l := Fin m) (n := Fin m) (l' := Fin n) (n' := Fin n) A C B D).symm

end LeanPhy.Quantum
