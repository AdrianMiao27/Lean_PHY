import LeanPhy.Quantum.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Dirac notation

The inner product and rank-one operators that physics proofs actually use.
Keeping this layer thin means a proof reads like the derivation on paper
(`|u⟩⟨v| w = ⟨v|w⟩ |u⟩`) without committing to a bespoke parser.
-/

namespace LeanPhy.Quantum

open scoped BigOperators

/-- The Dirac bracket `⟨u|v⟩`, conjugate-linear in `u` and linear in `v`. -/
noncomputable def braket {n : Nat} (u v : Ket n) : ℂ := ∑ i, star (u i) * v i

/-- The rank-one operator `|u⟩⟨v|`. -/
noncomputable def ketbra {n : Nat} (u v : Ket n) : Operator n :=
  fun i j => u i * star (v j)

theorem braket_add_right {n : Nat} (u v w : Ket n) :
    braket u (v + w) = braket u v + braket u w := by
  simp [braket, mul_add, Finset.sum_add_distrib]

theorem braket_smul_right {n : Nat} (u v : Ket n) (c : ℂ) :
    braket u (c • v) = c * braket u v := by
  simp only [braket, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem braket_conj_symm {n : Nat} (u v : Ket n) :
    star (braket u v) = braket v u := by
  simp only [braket, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul, star_star, mul_comm]

/-- The composition law for rank-one operators. -/
theorem ketbra_mul_ketbra {n : Nat} (u v w x : Ket n) :
    ketbra u v * ketbra w x = braket v w • ketbra u x := by
  ext i j
  simp only [ketbra, braket, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

@[simp] theorem trace_ketbra {n : Nat} (u v : Ket n) :
    Matrix.trace (ketbra u v) = braket v u := by
  simp [ketbra, braket, Matrix.trace, mul_comm]

end LeanPhy.Quantum
