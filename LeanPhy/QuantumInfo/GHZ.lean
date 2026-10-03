import LeanPhy.QuantumInfo.CHSH
import Mathlib.Tactic

/-!
# Three-qubit GHZ nonlocality: the Mermin operator

The two-qubit CHSH experiment is the smallest Bell test.  Its multipartite
generalisation, the three-qubit **Mermin operator**

`M = X Y Y + Y X Y + Y Y X - X X X`  (each letter a Pauli matrix on one qubit)

exposes a stronger form of nonlocality: the **GHZ state**
`|GHZ> = (|000> + |111>) / sqrt 2` is an eigenvector of `M` with eigenvalue `-4`,
so the Bell combination of local correlations reaches `4`, while any classical
(local hidden-variable) model is bounded by `2`.  This is the Mermin-GHZ
argument against local realism, and it is the canonical illustration of why three
qubits beat two.

Everything is checked by the kernel on the explicit `8 x 8` Pauli matrices built from
the `2 x 2` blocks by Kronecker product: the Mermin operator is symmetric, it maps
the (unnormalised) GHZ vector `|000> + |111>` to `-4` times itself, and its GHZ
expectation is `-8` (i.e. `-4` on the normalised state).  As with the rest of the
library, this is a statement about the algebra of the operators, verified against
the stated state, not a claim about nature.
-/

namespace LeanPhy.QuantumInfo

open LeanPhy.Quantum
open scoped BigOperators

/-- The eight-dimensional three-qubit index. -/
abbrev Idx3 := (Fin 2 × Fin 2) × Fin 2

/-- Kronecker product of two complex matrices over arbitrary finite index types. -/
noncomputable def kron2 {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b Complex) (B : Matrix c d Complex) : Matrix (a × c) (b × d) Complex :=
  Matrix.kroneckerMap (fun x y => x * y) A B

/-- Three-fold Kronecker product of one-qubit operators. -/
noncomputable def kron3 (A B C : Operator 2) : Matrix Idx3 Idx3 Complex :=
  kron2 (kron2 A B) C

/-- The entrywise form: `(A ⊗ B ⊗ C)_{(i1,i2,i3),(j1,j2,j3)} = A_{i1 j1} B_{i2 j2} C_{i3 j3}`. -/
theorem kron3_apply (A B C : Operator 2) (i j : Idx3) :
    kron3 A B C i j = A i.1.1 j.1.1 * B i.1.2 j.1.2 * C i.2 j.2 := by
  simp [kron3, kron2, Matrix.kroneckerMap_apply]

/-- The unnormalised GHZ vector `|000> + |111>` in the three-qubit basis. -/
noncomputable def ghzVec : Idx3 → Complex :=
  fun i => if i = ((0, 0), 0) then 1 else if i = ((1, 1), 1) then 1 else 0

/-- The Mermin operator `X Y Y + Y X Y + Y Y X - X X X`. -/
noncomputable def mermin : Matrix Idx3 Idx3 Complex :=
  kron3 pauliX pauliY pauliY + kron3 pauliY pauliX pauliY
    + kron3 pauliY pauliY pauliX - kron3 pauliX pauliX pauliX

/-- The GHZ expectation functional `<GHZ| M |GHZ>` (unnormalised in the vector). -/
noncomputable def ghzExpect (M : Matrix Idx3 Idx3 Complex) : Complex :=
  ∑ i : Idx3, ∑ j : Idx3, star (ghzVec i) * M i j * ghzVec j

/-- The Mermin operator is symmetric. -/
theorem mermin_symm (i j : Idx3) : mermin i j = mermin j i := by
  fin_cases i <;> fin_cases j <;>
    simp [mermin, kron3_apply, Matrix.add_apply, Matrix.sub_apply, pauliX, pauliY]

/-- **The Mermin-GHZ eigenvalue relation**: `M (|000> + |111>) = -4 (|000> + |111>)`, stated as
the row sum against the GHZ vector. -/
theorem mermin_ghz_eigen (j : Idx3) :
    (∑ i : Idx3, mermin i j * ghzVec i) = -4 * ghzVec j := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  fin_cases j <;>
    simp [mermin, kron3, kron2, ghzVec, Matrix.kroneckerMap_apply, Matrix.add_apply,
      Matrix.sub_apply, pauliX, pauliY, Fin.sum_univ_two] <;>
    norm_num

/-- **The Mermin-GHZ value**: the expectation of the Mermin operator in the GHZ vector is
`-8`, i.e. `-4` on the normalised state.  This is the Bell combination that
separates quantum mechanics (`4`) from local hidden variables (`<= 2`). -/
theorem ghzExpect_mermin : ghzExpect mermin = -8 := by
  rw [ghzExpect]
  simp [mermin, kron3, kron2, ghzVec, Matrix.kroneckerMap_apply, Matrix.add_apply,
    Matrix.sub_apply, pauliX, pauliY, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.cons_val_zero];
  norm_num

end LeanPhy.QuantumInfo
