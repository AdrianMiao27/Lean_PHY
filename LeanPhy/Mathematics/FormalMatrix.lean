import LeanPhy.Mathematics.FormalExpansion
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

set_option autoImplicit false

/-!
# Operator series as matrices of formal coefficients

Power series with matrix coefficients describe noncommuting perturbation
theory; block equations consume matrices whose entries are series. This ring
homomorphism checks that the two descriptions have the same ordered products.
An invertible constant matrix then supplies an actual unit formal matrix for
the shared block-elimination interface, rather than an assumed inverse series.
-/

namespace LeanPhy.Mathematics.FormalExpansion

open PowerSeries
open scoped BigOperators Matrix

variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

/-- Interchange the matrix labels and the formal-series coefficient label. -/
noncomputable def matrix (f : PowerSeries (Matrix ι ι R)) : Matrix ι ι (PowerSeries R) :=
  fun i j => mk (fun k => coeff k f i j)

@[simp] theorem coeff_matrix (f : PowerSeries (Matrix ι ι R)) (k : ℕ) (i j : ι) :
    coeff k (matrix f i j) = coeff k f i j := coeff_mk _ _

theorem matrix_one : matrix (1 : PowerSeries (Matrix ι ι R)) = 1 := by
  ext i j k
  by_cases hij : i = j <;> by_cases hk : k = 0 <;>
    simp [matrix, coeff_one, Matrix.one_apply, hij, hk]

theorem matrix_add (f g : PowerSeries (Matrix ι ι R)) :
    matrix (f + g) = matrix f + matrix g := by
  ext i j k
  simp

theorem matrix_mul (f g : PowerSeries (Matrix ι ι R)) :
    matrix (f * g) = matrix f * matrix g := by
  ext i j k
  simp only [coeff_matrix, coeff_mul, Matrix.sum_apply, Matrix.mul_apply, map_sum]
  exact Finset.sum_comm

noncomputable def matrixHom : PowerSeries (Matrix ι ι R) →+* Matrix ι ι (PowerSeries R) where
  toFun := matrix
  map_zero' := by
    ext i j k
    simp
  map_one' := matrix_one
  map_add' := matrix_add
  map_mul' := matrix_mul

/-- A certified constant inverse creates the full formal inverse. -/
noncomputable def matrixUnit (f : PowerSeries (Matrix ι ι R))
    (u : (Matrix ι ι R)ˣ) (hf : constantCoeff f = u) :
    (Matrix ι ι (PowerSeries R))ˣ :=
  Units.map matrixHom.toMonoidHom
    ⟨f, invOfUnit f u, mul_invOfUnit f u hf, invOfUnit_mul f u hf⟩

@[simp] theorem matrixUnit_val (f : PowerSeries (Matrix ι ι R))
    (u : (Matrix ι ι R)ˣ) (hf : constantCoeff f = u) :
    (↑(matrixUnit f u hf) : Matrix ι ι (PowerSeries R)) = matrix f := rfl

@[simp] theorem matrixUnit_inv_val (f : PowerSeries (Matrix ι ι R))
    (u : (Matrix ι ι R)ˣ) (hf : constantCoeff f = u) :
    (↑((matrixUnit f u hf)⁻¹) : Matrix ι ι (PowerSeries R)) = matrix (invOfUnit f u) := rfl

end LeanPhy.Mathematics.FormalExpansion
