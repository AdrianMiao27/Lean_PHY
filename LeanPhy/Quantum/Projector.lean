import LeanPhy.Quantum.Dirac
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-!
# Finite-dimensional projectors and spectral modes

Rank-one projectors are the common language of finite-dimensional measurement,
spectral bands, spin states, variational ansätze and truncated Fock spaces.
This file proves their algebraic properties from the Dirac `ketbra` definition.
The normalization `⟨v|v⟩ = 1` is an explicit hypothesis; no spectral theorem or
claim that an eigenbasis exists is hidden here.
-/

namespace LeanPhy.Quantum

open scoped BigOperators Matrix ComplexOrder

/-- The rank-one operator `|v⟩⟨v|`. -/
noncomputable def rankOneProjector {n : Nat} (v : Ket n) : Operator n := ketbra v v

/-- Rank-one operators act by the Dirac rule
`|u⟩⟨v| w = ⟨v|w⟩ |u⟩`. -/
theorem ketbra_apply {n : Nat} (u v w : Ket n) :
    (ketbra u v).mulVec w = braket v w • u := by
  ext i
  simp [ketbra, braket, Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

@[simp] theorem rankOneProjector_apply {n : Nat} (v w : Ket n) :
    (rankOneProjector v).mulVec w = braket v w • v :=
  ketbra_apply v v w

/-- A normalized rank-one mode is fixed by its projector. -/
theorem rankOneProjector_project_v {n : Nat} (v : Ket n)
    (h : braket v v = 1) :
    (rankOneProjector v).mulVec v = v := by
  rw [rankOneProjector_apply, h, one_smul]

/-- A mode orthogonal to `v` is killed by the rank-one projector. -/
theorem rankOneProjector_annihilate {n : Nat} (v w : Ket n)
    (h : braket v w = 0) :
    (rankOneProjector v).mulVec w = 0 := by
  rw [rankOneProjector_apply, h, zero_smul]

/-- Normalization makes the rank-one operator idempotent. -/
theorem rankOneProjector_mul_self {n : Nat} (v : Ket n)
    (h : braket v v = 1) :
    rankOneProjector v * rankOneProjector v = rankOneProjector v := by
  simp [rankOneProjector, ketbra_mul_ketbra, h]

/-- A rank-one projector is Hermitian. -/
theorem rankOneProjector_conjTranspose {n : Nat} (v : Ket n) :
    Matrix.conjTranspose (rankOneProjector v) = rankOneProjector v := by
  ext i j
  simp [rankOneProjector, ketbra, Matrix.conjTranspose]
  ring

/-- Every rank-one ket-bra is positive semidefinite. -/
theorem rankOneProjector_posSemidef {n : Nat} (v : Ket n) :
    (rankOneProjector v).PosSemidef := by
  have h : rankOneProjector v = Matrix.vecMulVec v (star v) := by
    ext i j
    rfl
  rw [h]
  exact Matrix.posSemidef_vecMulVec_self_star v

@[simp] theorem rankOneProjector_trace {n : Nat} (v : Ket n) :
    Matrix.trace (rankOneProjector v) = braket v v :=
  trace_ketbra v v

theorem normalized_rankOneProjector_trace {n : Nat} (v : Ket n)
    (h : braket v v = 1) :
    Matrix.trace (rankOneProjector v) = 1 := by
  rw [rankOneProjector_trace, h]

end LeanPhy.Quantum
