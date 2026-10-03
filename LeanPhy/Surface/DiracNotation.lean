import LeanPhy.Quantum.Dirac
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

open scoped BigOperators

/-!
# Dirac notation as a real elaborator

This file upgrades the Dirac-notation surface from plain `scoped notation` into a
genuine term elaborator.  The gain is type inference that a plain notation cannot
give: writing

    |k>,   <u|,   <u|v>,   <u|A|v>,   |u><v|

lets the elaborator infer the Hilbert-space dimension `n` from whichever argument
is already typed and then check the rest against it, so a bra, a ket and an
operator that do not share one dimension `n` are rejected with a physics-facing
Chinese message instead of silently elaborating to a wrong type.

Semantics are unchanged: every form lowers to the thin definitions in
`LeanPhy.Quantum.Dirac` (`braket`, `ketbra`, ...), which are ordinary mathlib
objects, so the kernel checks every statement.  This is not a new logic; it is a
stricter, friendlier front end for the same kernel-checked objects.  The Chinese
diagnostics at the end of the file are pinned as build-time regression tests.
-/

namespace LeanPhy.Quantum

/-- The basis ket `|k⟩`, i.e. the k-th computational basis vector. -/
noncomputable def basisKet {n : Nat} (k : Fin n) : Ket n := fun j => if j = k then 1 else 0

/-- The bra `⟨u|` dual to a ket `|u⟩`, conjugate-linear by construction. -/
noncomputable def braOf {n : Nat} (u : Ket n) : Bra n := fun i => star (u i)

/-- The Dirac bracket `⟨u|v⟩`. -/
noncomputable def bracket {n : Nat} (u v : Ket n) : ℂ := braket u v

/-- The matrix element `⟨u|A|v⟩`. -/
noncomputable def bracketOp {n : Nat} (u v : Ket n) (op : Operator n) : ℂ :=
  braket u (op.mulVec v)

/-- The bra `⟨u|A` obtained by letting an operator act on a bra. -/
noncomputable def braMulOp {n : Nat} (u : Ket n) (op : Operator n) : Bra n :=
  fun j => ∑ i, star (u i) * op i j

/-! ## Basic facts about the computational basis -/

theorem basisKet_of_ne {n : Nat} {k b : Fin n} (h : b ≠ k) : basisKet k b = 0 := by
  simp [basisKet, h]

@[simp] theorem basisKet_self {n : Nat} (k : Fin n) : basisKet k k = 1 := by
  simp [basisKet]

/-- The computational basis is orthonormal: `⟨i|j⟩ = δ_ij`. -/
theorem basisKet_orthonormal {n : Nat} (i j : Fin n) :
    braket (basisKet i) (basisKet j) = if i = j then 1 else 0 := by
  simp only [braket]
  rw [Finset.sum_eq_single i]
  · simp [basisKet]
  · intro b _ hb; rw [basisKet_of_ne hb, star_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Completeness, i.e. the resolution of the identity `∑_k |k⟩⟨k| = 1`. -/
theorem completeness (n : Nat) :
    (∑ k : Fin n, ketbra (basisKet k) (basisKet k)) = 1 := by
  ext i j
  simp only [Matrix.sum_apply, ketbra, Matrix.one_apply]
  rw [Finset.sum_eq_single i]
  · simp [basisKet, eq_comm]
  · intro b _ hb; rw [basisKet_of_ne (Ne.symm hb), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The resolution of the identity reproduces any state, `(∑_k |k⟩⟨k|) |v⟩ = |v⟩`. -/
theorem resolution (n : Nat) (v : Ket n) :
    (∑ k : Fin n, ketbra (basisKet k) (basisKet k)).mulVec v = v := by
  rw [completeness, Matrix.one_mulVec]

/-! ## Brackets and outer products -/

theorem braket_add_left {n : Nat} (u v w : Ket n) :
    braket (u + v) w = braket u w + braket v w := by
  simp only [braket, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem braket_smul_left {n : Nat} (c : ℂ) (u v : Ket n) :
    braket (c • u) v = star c * braket u v := by
  simp only [braket, Pi.smul_apply, smul_eq_mul, star_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `⟨u|u⟩` is real: the norm squared. -/
theorem braket_self_conj {n : Nat} (u : Ket n) : star (braket u u) = braket u u :=
  braket_conj_symm u u

/-- The composition rule that makes Dirac algebra mechanical:
`|u⟩⟨v|` acting on `|w⟩` gives `⟨v|w⟩ |u⟩`. -/
theorem ketbra_mulVec {n : Nat} (u v w : Ket n) :
    (ketbra u v).mulVec w = braket v w • u := by
  funext i
  simp only [Matrix.mulVec, dotProduct, ketbra, Pi.smul_apply, smul_eq_mul, braket]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- The bra is the conjugate-linear functional pairing with `⟨u|`. -/
theorem bra_apply {n : Nat} (u v : Ket n) : (braOf u) ⬝ᵥ v = braket u v := rfl

end LeanPhy.Quantum

namespace LeanPhy.Dirac

open Lean Meta Elab Term
open LeanPhy.Quantum

/-! ## Surface syntax -/

scoped syntax (name := diracKet) "|" term:max "⟩" : term
scoped syntax (name := diracBra) "⟨" term:max "|" : term
scoped syntax (name := diracBracket) "⟨" term:max "|" term:max "⟩" : term
scoped syntax (name := diracOp) "⟨" term:max "|" term:max "|" term:max "⟩" : term
scoped syntax (name := diracBraMul) "⟨" term:max "|" term:max : term
scoped syntax (name := diracOuter) "|" term:max "⟩" "⟨" term:max "|" : term

open scoped LeanPhy.Dirac

/-! ## The elaborators

Each one allocates a single dimension metavariable and elaborates every slot
against `Ket ?n` / `Operator ?n`, so one shared `?n` ties the pieces together.
A slot whose type does not match is reported with a Chinese message. -/

private def dimMVar : TermElabM Expr := mkFreshExprMVar (mkConst ``Nat)
private def ketTy (n : Expr) : Expr := mkApp (mkConst ``LeanPhy.Quantum.Ket) n
private def opTy (n : Expr) : Expr := mkApp (mkConst ``LeanPhy.Quantum.Operator) n

/-- Elaborate a term at a physics-facing slot; on a type clash report the
dimension disagreement in Chinese rather than the raw `type mismatch`. -/
private def elabSlot (stx : Syntax) (ty : Expr) (what : String) : TermElabM Expr := do
  let e ← elabTerm stx none
  let e ← instantiateMVars e
  let t ← inferType e
  unless (← isDefEq t ty) do
    throwError m!"狄拉克记号：{what} 与同一括号内其余张量的希尔伯特空间维数不一致"
  return e

@[term_elab diracKet] def elabDiracKet : TermElab := fun stx _ => do
  let n ← dimMVar
  let kE ← elabTermEnsuringType stx[1] (mkApp (mkConst ``Fin) n)
  mkAppM ``LeanPhy.Quantum.basisKet #[← instantiateMVars kE]

@[term_elab diracBra] def elabDiracBra : TermElab := fun stx _ => do
  let n ← dimMVar
  let uE ← elabSlot stx[1] (ketTy n) "向量"
  mkAppM ``LeanPhy.Quantum.braOf #[uE]

@[term_elab diracBracket] def elabDiracBracket : TermElab := fun stx _ => do
  let n ← dimMVar
  let uE ← elabSlot stx[1] (ketTy n) "左向量"
  let vE ← elabSlot stx[3] (ketTy n) "右向量"
  mkAppM ``LeanPhy.Quantum.bracket #[uE, vE]

@[term_elab diracOp] def elabDiracOp : TermElab := fun stx _ => do
  let n ← dimMVar
  let uE ← elabSlot stx[1] (ketTy n) "左向量"
  let aE ← elabSlot stx[3] (opTy n) "算符"
  let vE ← elabSlot stx[5] (ketTy n) "右向量"
  mkAppM ``LeanPhy.Quantum.bracketOp #[uE, vE, aE]

@[term_elab diracBraMul] def elabDiracBraMul : TermElab := fun stx _ => do
  let n ← dimMVar
  let uE ← elabSlot stx[1] (ketTy n) "向量"
  let aE ← elabSlot stx[3] (opTy n) "算符"
  mkAppM ``LeanPhy.Quantum.braMulOp #[uE, aE]

@[term_elab diracOuter] def elabDiracOuter : TermElab := fun stx _ => do
  let n ← dimMVar
  let uE ← elabSlot stx[1] (ketTy n) "外积左侧向量"
  let vE ← elabSlot stx[4] (ketTy n) "外积右侧向量"
  mkAppM ``LeanPhy.Quantum.ketbra #[uE, vE]

/-! ## Regression tests

The positive cases are ordinary theorems; the negative cases pin the Chinese
diagnostics so a change in the elaborator is caught at build time. -/

-- all slots share one inferred dimension; the result is the thin definition
example (u v : Ket 2) (A : Operator 2) :
    (⟨u|A|v⟩ : ℂ) = LeanPhy.Quantum.braket u (A.mulVec v) := rfl

-- the bra-mul form is the thin definition too, and shares the dimension
example (u : Ket 2) (A : Operator 2) : (⟨u|A : Bra 2) = LeanPhy.Quantum.braMulOp u A := rfl

-- the bra and the outer product are the thin definitions, no new logic
example (u : Ket 2) : (⟨u| : Bra 2) = LeanPhy.Quantum.braOf u := rfl
example (u v : Ket 2) : (|u⟩⟨v| : Operator 2) = LeanPhy.Quantum.ketbra u v := rfl

-- a basis ket infers its dimension from the surrounding bracket
example : (⟨(|(0 : Fin 2)⟩ : Ket 2)|(|(1 : Fin 2)⟩ : Ket 2)⟩ : ℂ) = 0 := by
  rw [LeanPhy.Quantum.bracket, LeanPhy.Quantum.basisKet_orthonormal]
  simp

-- the outer product acting on a ket is the composition rule, in surface syntax
example (u v w : Ket 2) : (|u⟩⟨v| : Operator 2).mulVec w = (⟨v|w⟩ : ℂ) • u :=
  LeanPhy.Quantum.ketbra_mulVec u v w

/-- error: 狄拉克记号：右向量 与同一括号内其余张量的希尔伯特空间维数不一致 -/
#guard_msgs (error) in
example (u : Ket 2) (v : Ket 3) : (⟨u|v⟩ : ℂ) = 0 := rfl

/-- error: 狄拉克记号：算符 与同一括号内其余张量的希尔伯特空间维数不一致 -/
#guard_msgs (error) in
example (u v : Ket 2) (A : Operator 3) : (⟨u|A|v⟩ : ℂ) = 0 := rfl

/-- error: 狄拉克记号：外积右侧向量 与同一括号内其余张量的希尔伯特空间维数不一致 -/
#guard_msgs (error) in
example (u w : Ket 2) (z : Ket 3) : (|u⟩⟨z| : Operator 2) = 1 := rfl

end LeanPhy.Dirac
