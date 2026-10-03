import LeanPhy.Condensed.Fermion
import LeanPhy.Quantum.Composite
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# Jordan-Wigner transformation: a two-site fermion chain as matrices

A many-body fermion problem is written with creation and annihilation operators
satisfying the canonical anticommutation relations (CAR)

    {c_j, c_k} = 0,   {c_j, c_k^dag} = delta_{jk}.

The Jordan-Wigner transformation realises these operators on a qubit register.
On two sites the recipe is

    c_0 = sigma^- (x) 1,        c_1 = sigma^z (x) sigma^-,

where `sigma^-` is the fermionic lowering matrix and the string of `sigma^z`
factors encodes the fermionic sign that distinguishes fermions from hard-core
bosons.  This module builds those two matrices explicitly as `4 x 4` complex
matrices and checks, entrywise and by the kernel, the full two-site CAR:

    {c_0, c_0^dag} = 1,  {c_1, c_1^dag} = 1,  {c_0, c_1^dag} = 0,  {c_1, c_0^dag} = 0,
    c_0^2 = 0,  c_1^2 = 0,  {c_0, c_1} = 0.

The string is what makes the cross-site relations work: the module also proves
that the stringless candidate `sigma^- (x) 1`, `1 (x) sigma^-` gives a nonzero
anticommutator, so the `sigma^z` string is not decoration.  On top of the CAR the
module proves that each number operator `n_j = cdag_j c_j` is a projector, that the
two-site hopping term conserves the total particle number `n_0 + n_1`, and that
the hopping term equals `(1/2)(sigma^x (x) sigma^x + sigma^y (x) sigma^y)`, the
standard map between the fermion chain and the XY spin chain.

Everything is checked entrywise on the explicit matrices, so the transform is a
kernel-verified identity, not a convention.  The general `N`-site string, the
momentum-space transform, and the interacting (Hubbard) chain are out of scope.
-/

namespace LeanPhy.Condensed

open scoped BigOperators Matrix

/-- The two-site register index: one `Fin 2` per site. -/
abbrev Idx2q := Fin 2 × Fin 2

/-- The Kronecker product of two `2 x 2` matrices, as a `4 x 4` matrix. -/
noncomputable def kron (A Bm : Matrix (Fin 2) (Fin 2) ℂ) : Matrix Idx2q Idx2q ℂ :=
  Matrix.kroneckerMap (· * ·) A Bm

/-- The fermionic lowering matrix `sigma^- = |0><1|`. -/
noncomputable def smMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The fermionic raising matrix `sigma^+ = |1><0|`. -/
noncomputable def spMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- The Pauli `sigma^z` matrix, the Jordan-Wigner string. -/
noncomputable def zMat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Pauli `sigma^x` matrix. -/
noncomputable def xMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `sigma^y` matrix. -/
noncomputable def yMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The site-0 annihilation operator `c_0 = sigma^- (x) 1`. -/
noncomputable def jwC0 : Matrix Idx2q Idx2q ℂ := kron smMat 1

/-- The site-1 annihilation operator `c_1 = sigma^z (x) sigma^-`. -/
noncomputable def jwC1 : Matrix Idx2q Idx2q ℂ := kron zMat smMat

/-- The site-0 creation operator `c_0^dag = sigma^+ (x) 1`. -/
noncomputable def jwC0dag : Matrix Idx2q Idx2q ℂ := kron spMat 1

/-- The site-1 creation operator `c_1^dag = sigma^z (x) sigma^+`. -/
noncomputable def jwC1dag : Matrix Idx2q Idx2q ℂ := kron zMat spMat

/-- The number operator `n_0 = c_0^dag c_0`. -/
noncomputable def jwN0 : Matrix Idx2q Idx2q ℂ := jwC0dag * jwC0

/-- The number operator `n_1 = c_1^dag c_1`. -/
noncomputable def jwN1 : Matrix Idx2q Idx2q ℂ := jwC1dag * jwC1

/-- The two-site hopping term `c_0^dag c_1 + c_1^dag c_0`. -/
noncomputable def jwHop : Matrix Idx2q Idx2q ℂ := jwC0dag * jwC1 + jwC1dag * jwC0

/-! ### The Kronecker-product calculus -/

/-- **Mixed-product law**: `(A (x) B)(C (x) D) = (AC) (x) (BD)`. -/
theorem kron2_mul (A Bm C D : Matrix (Fin 2) (Fin 2) ℂ) :
    kron A Bm * kron C D = kron (A * C) (Bm * D) := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  simp [kron, Matrix.kroneckerMap, Matrix.mul_apply, Fintype.sum_prod_type]
  ring

/-- The Kronecker product is additive in its first argument. -/
theorem kron2_add_left (A Bm C : Matrix (Fin 2) (Fin 2) ℂ) :
    kron A C + kron Bm C = kron (A + Bm) C := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  simp [kron, Matrix.kroneckerMap, Matrix.add_apply]
  ring

/-- The Kronecker product of zero matrices is zero. -/
theorem kron2_zero_left (Bm : Matrix (Fin 2) (Fin 2) ℂ) :
    kron (0 : Matrix (Fin 2) (Fin 2) ℂ) Bm = 0 := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  simp [kron, Matrix.kroneckerMap]

/-- `1 (x) 1 = 1`. -/
theorem kron2_one_one :
    kron (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 = 1 := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  simp only [kron, Matrix.kroneckerMap, Matrix.one_apply]
  by_cases h1 : i1 = j1 <;> by_cases h2 : i2 = j2 <;> simp [h1, h2]

/-! ### Single-site block identities -/

theorem sm_sp_sum : smMat * spMat + spMat * smMat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [smMat, spMat, Matrix.mul_apply]

theorem sm_sm_zero : smMat * smMat = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [smMat, Matrix.mul_apply]

theorem sp_sp_zero : spMat * spMat = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [spMat, Matrix.mul_apply]

theorem sz_sm_anticomm : zMat * smMat + smMat * zMat = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [zMat, smMat, Matrix.mul_apply]

theorem sp_sz_anticomm : spMat * zMat + zMat * spMat = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [zMat, spMat, Matrix.mul_apply]

theorem sz_sz_one : zMat * zMat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [zMat, Matrix.mul_apply]

/-! ### The canonical anticommutation relations -/

/-- `{c_0, c_0^dag} = 1`. -/
theorem car_zero : jwC0 * jwC0dag + jwC0dag * jwC0 = 1 := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  simp only [jwC0, jwC0dag, kron, Matrix.kroneckerMap, Matrix.add_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, smMat, spMat]
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> norm_num

/-- `{c_1, c_1^dag} = 1`. -/
theorem car_one : jwC1 * jwC1dag + jwC1dag * jwC1 = 1 := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  simp only [jwC1, jwC1dag, kron, Matrix.kroneckerMap, Matrix.add_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, smMat, spMat, zMat]
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> norm_num

/-- `{c_0, c_1^dag} = 0`: the cross-site relation the string fixes. -/
theorem car_zero_one : jwC0 * jwC1dag + jwC1dag * jwC0 = 0 := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  simp only [jwC0, jwC1dag, kron, Matrix.kroneckerMap, Matrix.add_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, smMat, spMat, zMat]
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> norm_num

/-- `{c_1, c_0^dag} = 0`. -/
theorem car_one_zero : jwC1 * jwC0dag + jwC0dag * jwC1 = 0 := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  simp only [jwC1, jwC0dag, kron, Matrix.kroneckerMap, Matrix.add_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, smMat, spMat, zMat]
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> norm_num

/-- `c_0^2 = 0`. -/
theorem cc_zero : jwC0 * jwC0 = 0 := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  simp only [jwC0, kron, Matrix.kroneckerMap, Matrix.mul_apply,
    Fintype.sum_prod_type, smMat]
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> norm_num

/-- `c_1^2 = 0`. -/
theorem cc_one : jwC1 * jwC1 = 0 := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  simp only [jwC1, kron, Matrix.kroneckerMap, Matrix.mul_apply,
    Fintype.sum_prod_type, smMat, zMat]
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> norm_num

/-- `{c_0, c_1} = 0`. -/
theorem cc_zero_one : jwC0 * jwC1 + jwC1 * jwC0 = 0 := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  simp only [jwC0, jwC1, kron, Matrix.kroneckerMap, Matrix.add_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, smMat, zMat]
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> norm_num

/-! ### The string is not decoration -/

/-- Without the `sigma^z` string the cross-site anticommutator does not vanish:
the stringless candidates give `{sigma^- (x) 1, 1 (x) sigma^+} = 2 (sigma^- (x) sigma^+)`. -/
theorem naive_anticommutator :
    (kron smMat 1) * (kron 1 spMat) + (kron 1 spMat) * (kron smMat 1)
      = kron (2 • smMat) spMat := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    (simp [kron, Matrix.kroneckerMap, Matrix.add_apply, Matrix.smul_apply,
      Matrix.mul_apply, Fintype.sum_prod_type, smMat, spMat] <;> ring)

/-- That stringless anticommutator is a nonzero matrix, so the string is needed. -/
theorem naive_anticommutator_ne_zero :
    (kron (2 • smMat) spMat : Matrix Idx2q Idx2q ℂ) ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h (0,1)) (1,0)
  simp [kron, Matrix.kroneckerMap, smMat, spMat] at h01

/-! ### Number conservation and the spin-chain map -/

/-- Each number operator is a projector, `n_j^2 = n_j`. -/
theorem jwN0_projector : jwN0 * jwN0 = jwN0 := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    (simp [jwN0, jwC0, jwC0dag, kron, Matrix.kroneckerMap, Matrix.mul_apply,
      Fintype.sum_prod_type, smMat, spMat] <;> norm_num)

/-- `n_1` is a projector. -/
theorem jwN1_projector : jwN1 * jwN1 = jwN1 := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    (simp [jwN1, jwC1, jwC1dag, kron, Matrix.kroneckerMap, Matrix.mul_apply,
      Fintype.sum_prod_type, smMat, spMat, zMat] <;> norm_num)

/-- The number operators commute, `n_0 n_1 = n_1 n_0`. -/
theorem jwN0_comm_jwN1 : jwN0 * jwN1 = jwN1 * jwN0 := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    (simp [jwN0, jwN1, jwC0, jwC0dag, jwC1, jwC1dag, kron, Matrix.kroneckerMap,
      Matrix.mul_apply, Fintype.sum_prod_type, smMat, spMat, zMat] <;> norm_num)

/-- **Number conservation**: the hopping term commutes with the total number
`n_0 + n_1`, so hopping preserves particle number. -/
theorem jwHop_num_comm :
    (jwN0 + jwN1) * jwHop = jwHop * (jwN0 + jwN1) := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    (simp [jwHop, jwN0, jwN1, jwC0, jwC0dag, jwC1, jwC1dag, kron,
      Matrix.kroneckerMap, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      smMat, spMat, zMat] <;> norm_num)

/-- **Spin-chain map**: the hopping term equals
`(1/2)(sigma^x (x) sigma^x + sigma^y (x) sigma^y)`, the XY spin-chain hopping. -/
theorem jwHop_eq_xy :
    jwHop = (1 / 2 : ℂ) • (kron xMat xMat + kron yMat yMat) := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    (simp [jwHop, jwC0, jwC0dag, jwC1, jwC1dag, kron, Matrix.kroneckerMap,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      smMat, spMat, zMat, xMat, yMat, Complex.I_mul_I] <;> ring)

/-- `c_0^dag` is the conjugate transpose of `c_0`. -/
theorem jwC0dag_conjTranspose : jwC0dag = Matrix.conjTranspose jwC0 := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    (simp [jwC0, jwC0dag, kron, Matrix.kroneckerMap, Matrix.conjTranspose,
      smMat, spMat] <;> norm_num)

/-- `c_1^dag` is the conjugate transpose of `c_1`. -/
theorem jwC1dag_conjTranspose : jwC1dag = Matrix.conjTranspose jwC1 := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    (simp [jwC1, jwC1dag, kron, Matrix.kroneckerMap, Matrix.conjTranspose,
      smMat, spMat, zMat] <;> norm_num)

end LeanPhy.Condensed
