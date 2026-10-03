import LeanPhy.Quantum.Spin
import LeanPhy.Quantum.Composite
import Mathlib.Tactic.Module

set_option maxHeartbeats 800000

open scoped BigOperators

/-!
# Coupling two spin-1/2 systems

Two spin-1/2 representations couple into a singlet (j = 0) and a triplet
(j = 1), the Clebsch-Gordan decomposition `1/2 ⊗ 1/2 = 0 ⊕ 1`.  This file
builds the total angular-momentum operators on the four-dimensional
tensor-product space and proves the algebraic content of that decomposition:

- the total generators again satisfy the su(2) relations;
- the singlet state `|01> - |10>` is annihilated by every total generator
  (it is the spin-0 state);
- the total Casimir `J^2` satisfies the characteristic identity
  `(J^2)(J^2 - 2) = 0`, i.e. its spectrum is `{0, 2}` = `{0, 1(1+1)}`,
  the singlet and triplet values.

The su(2) relations are proved through the mixed-product law for the Kronecker
product, the way the derivation is written by hand, rather than by expanding
4x4 matrices entrywise.  Everything is checked by the Lean kernel; there is no
sorry and no axiom.
-/

namespace LeanPhy.Quantum

local notation "𝕚" => Complex.I

/-! ## Bilinearity helpers for the Kronecker product -/

theorem tensorOp_sub_left {m n : Nat} (A B : Operator m) (C : Operator n) :
    tensorOp (A - B) C = tensorOp A C - tensorOp B C := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [tensorOp, Matrix.kroneckerMap_apply, Matrix.sub_apply]
  ring

theorem tensorOp_sub_right {m n : Nat} (A : Operator m) (B C : Operator n) :
    tensorOp A (B - C) = tensorOp A B - tensorOp A C := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [tensorOp, Matrix.kroneckerMap_apply, Matrix.sub_apply]
  ring

theorem tensorOp_smul_left {m n : Nat} (c : ℂ) (A : Operator m) (B : Operator n) :
    tensorOp (c • A) B = c • tensorOp A B := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [tensorOp, Matrix.kroneckerMap_apply, Matrix.smul_apply]
  ring

theorem tensorOp_smul_right {m n : Nat} (c : ℂ) (A : Operator m) (B : Operator n) :
    tensorOp A (c • B) = c • tensorOp A B := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [tensorOp, Matrix.kroneckerMap_apply, Matrix.smul_apply]
  ring

/-! ## Total angular momentum on the coupled system -/

/-- Total spin-x, `Jx ⊗ 1 + 1 ⊗ Jx`. -/
noncomputable def JtotX : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  tensorOp Jx (1 : Operator 2) + tensorOp (1 : Operator 2) Jx

/-- Total spin-y. -/
noncomputable def JtotY : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  tensorOp Jy (1 : Operator 2) + tensorOp (1 : Operator 2) Jy

/-- Total spin-z. -/
noncomputable def JtotZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  tensorOp Jz (1 : Operator 2) + tensorOp (1 : Operator 2) Jz

/-- The total quadratic Casimir `J^2 = Jx^2 + Jy^2 + Jz^2`. -/
noncomputable def JtotSq : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  JtotX * JtotX + JtotY * JtotY + JtotZ * JtotZ

/-! ## Commutator bookkeeping via the mixed-product law -/

theorem tot_comm_left (A B : Operator 2) :
    commutator (tensorOp A (1 : Operator 2)) (tensorOp B (1 : Operator 2))
      = tensorOp (commutator A B) (1 : Operator 2) := by
  unfold commutator
  rw [tensorOp_mul, tensorOp_mul, ← tensorOp_sub_left]
  simp

theorem tot_comm_right (A B : Operator 2) :
    commutator (tensorOp (1 : Operator 2) A) (tensorOp (1 : Operator 2) B)
      = tensorOp (1 : Operator 2) (commutator A B) := by
  unfold commutator
  rw [tensorOp_mul, tensorOp_mul, ← tensorOp_sub_right]
  simp

theorem tot_comm_mixed (A B : Operator 2) :
    commutator (tensorOp A (1 : Operator 2)) (tensorOp (1 : Operator 2) B) = 0 := by
  unfold commutator
  rw [tensorOp_mul, tensorOp_mul]; simp

theorem tot_comm_mixed' (A B : Operator 2) :
    commutator (tensorOp (1 : Operator 2) A) (tensorOp B (1 : Operator 2)) = 0 := by
  unfold commutator
  rw [tensorOp_mul, tensorOp_mul]; simp

/-- The total generators are again a representation of su(2):
`[JtotX, JtotY] = i JtotZ`. -/
theorem JtotX_commutator_JtotY : commutator JtotX JtotY = 𝕚 • JtotZ := by
  rw [JtotX, JtotY, JtotZ]
  simp only [commutator_add_left, commutator_add_right, tot_comm_left, tot_comm_right,
    tot_comm_mixed, tot_comm_mixed', Jx_commutator_Jy, tensorOp_smul_left,
    tensorOp_smul_right, smul_add, add_zero, zero_add]

/-- The cyclic partner `[JtotY, JtotZ] = i JtotX`. -/
theorem JtotY_commutator_JtotZ : commutator JtotY JtotZ = 𝕚 • JtotX := by
  rw [JtotX, JtotY, JtotZ]
  simp only [commutator_add_left, commutator_add_right, tot_comm_left, tot_comm_right,
    tot_comm_mixed, tot_comm_mixed', Jy_commutator_Jz, tensorOp_smul_left,
    tensorOp_smul_right, smul_add, add_zero, zero_add]

/-- The cyclic partner `[JtotZ, JtotX] = i JtotY`. -/
theorem JtotZ_commutator_JtotX : commutator JtotZ JtotX = 𝕚 • JtotY := by
  rw [JtotX, JtotY, JtotZ]
  simp only [commutator_add_left, commutator_add_right, tot_comm_left, tot_comm_right,
    tot_comm_mixed, tot_comm_mixed', Jz_commutator_Jx, tensorOp_smul_left,
    tensorOp_smul_right, smul_add, add_zero, zero_add]

/-! ## The singlet -/

/-- The (unnormalised) singlet state `|01> - |10>`, the spin-0 state of the
Clebsch-Gordan decomposition. -/
noncomputable def singletVec : Fin 2 × Fin 2 → ℂ :=
  fun p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0

/-- The singlet is annihilated by `JtotX`. -/
theorem singlet_JtotX : JtotX.mulVec singletVec = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, JtotX, tensorOp, Matrix.kroneckerMap_apply, singletVec,
      Jx, pauliX, Prod.mk.injEq, Fin.sum_univ_two, Fintype.sum_prod_type]

/-- The singlet is annihilated by `JtotY`. -/
theorem singlet_JtotY : JtotY.mulVec singletVec = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, JtotY, tensorOp, Matrix.kroneckerMap_apply, singletVec,
      Jy, pauliY, Prod.mk.injEq, Fin.sum_univ_two, Fintype.sum_prod_type]

/-- The singlet is annihilated by `JtotZ`. -/
theorem singlet_JtotZ : JtotZ.mulVec singletVec = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, JtotZ, tensorOp, Matrix.kroneckerMap_apply, singletVec,
      Jz, pauliZ, Prod.mk.injEq, Fin.sum_univ_two, Fintype.sum_prod_type]

/-- The total Casimir kills the singlet, as a spin-0 state must. -/
theorem singlet_JtotSq : JtotSq.mulVec singletVec = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, JtotSq, JtotX, JtotY, JtotZ, tensorOp,
      Matrix.kroneckerMap_apply, Matrix.mul_apply, Matrix.add_apply, singletVec, Jx, Jy, Jz,
      pauliX, pauliY, pauliZ, Prod.mk.injEq, Fin.sum_univ_two, Fintype.sum_prod_type] <;> ring

/-! ## The Casimir spectrum -/

/-- The total Casimir satisfies `J^4 = 2 J^2`, the characteristic identity of
a spectrum equal to `{0, 2}`; `0 = 0(0+1)` is the singlet and
`2 = 1(1+1)` is the triplet.  This is the algebraic statement of the
Clebsch-Gordan decomposition `1/2 ⊗ 1/2 = 0 ⊕ 1`. -/
theorem JtotSq_char : JtotSq * JtotSq = (2 : ℂ) • JtotSq := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [JtotSq, JtotX, JtotY, JtotZ, tensorOp, Matrix.kroneckerMap_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.smul_apply, Jx, Jy, Jz,
      pauliX, pauliY, pauliZ, Fin.sum_univ_two, Fintype.sum_prod_type]
  all_goals
    ring_nf
    simp only [Complex.I_pow_four, Complex.I_sq]
    ring

end LeanPhy.Quantum
