import LeanPhy.Quantum.Basic
import LeanPhy.FieldTheory.CCR
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NoncommRing

/-!
# Multi-mode canonical commutation relations

A finite collection of bosonic modes, each carrying its own ladder operators.
The algebra is stated as explicit hypotheses in a ring, exactly as in the
single-mode file, so nothing analytic (domains, unbounded operators,
completeness) is assumed.  What is proved is the finite algebraic content of
the CCR: number operators act diagonally on modes and the total number operator
raises or lowers by one unit.
-/

namespace LeanPhy.FieldTheory

open LeanPhy.Quantum
open scoped BigOperators

variable {ι : Type} [DecidableEq ι] [Fintype ι]
variable {A : Type} [Ring A]

/-- The algebraic data of a finite set of bosonic modes. -/
structure MultiModeCCR (ι : Type) [DecidableEq ι] [Fintype ι] (A : Type) [Ring A] where
  /-- Annihilation operator of each mode. -/
  ann : ι → A
  /-- Creation operator of each mode. -/
  cre : ι → A
  /-- Different modes commute; the same-mode pair gives the canonical relation. -/
  ccr_ann_cre : ∀ i j, ⟦ann i, cre j⟧ = if i = j then 1 else 0
  /-- Annihilation operators mutually commute. -/
  ccr_ann_ann : ∀ i j, ⟦ann i, ann j⟧ = 0
  /-- Creation operators mutually commute. -/
  ccr_cre_cre : ∀ i j, ⟦cre i, cre j⟧ = 0

/-- The commutator distributes over a finite sum in its first argument. -/
theorem commutator_sum_left {ι : Type} [Fintype ι] {A : Type} [Ring A]
    (f : ι → A) (y : A) :
    ⟦∑ i, f i, y⟧ = ∑ i, ⟦f i, y⟧ := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction with
  | empty => simp [commutator]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, commutator_add_left, ih]

namespace MultiModeCCR

variable (M : MultiModeCCR ι A)

/-- Number operator of a single mode. -/
def numberOp (i : ι) : A := M.cre i * M.ann i

/-- The total number operator. -/
noncomputable def totalNumber : A := ∑ i, M.numberOp i

/-- Creation and annihilation of different modes commute. -/
theorem cre_commutator_ann (i j : ι) :
    ⟦M.cre i, M.ann j⟧ = if i = j then -1 else 0 := by
  rw [commutator_skew, M.ccr_ann_cre j i]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

/-- A single number operator raises its own mode. -/
theorem number_commutator_cre (i j : ι) :
    ⟦M.numberOp i, M.cre j⟧ = if i = j then M.cre i else 0 := by
  rw [numberOp, commutator_mul_left, M.ccr_ann_cre i j, M.ccr_cre_cre i j]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- A single number operator lowers its own mode. -/
theorem number_commutator_ann (i j : ι) :
    ⟦M.numberOp i, M.ann j⟧ = if i = j then -M.ann i else 0 := by
  rw [numberOp, commutator_mul_left, M.ccr_ann_ann i j, M.cre_commutator_ann i j]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- The total number operator raises every mode: [N, cre j] = cre j. -/
theorem totalNumber_commutator_cre (j : ι) :
    ⟦M.totalNumber, M.cre j⟧ = M.cre j := by
  classical
  rw [totalNumber, commutator_sum_left]
  rw [Finset.sum_eq_single j]
  · simp [M.number_commutator_cre]
  · intro i _ hij; simp [M.number_commutator_cre, hij]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- The total number operator lowers every mode: [N, ann j] = -ann j. -/
theorem totalNumber_commutator_ann (j : ι) :
    ⟦M.totalNumber, M.ann j⟧ = -M.ann j := by
  classical
  rw [totalNumber, commutator_sum_left]
  rw [Finset.sum_eq_single j]
  · simp [M.number_commutator_ann]
  · intro i _ hij; simp [M.number_commutator_ann, hij]
  · intro hj; exact absurd (Finset.mem_univ j) hj

end MultiModeCCR

end LeanPhy.FieldTheory
