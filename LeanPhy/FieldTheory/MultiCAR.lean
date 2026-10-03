import LeanPhy.FieldTheory.MultiMode
import Mathlib.Tactic.NoncommRing

/-!
# Multi-mode canonical anticommutation relations

This is the fermionic companion to `MultiModeCCR`.  It packages a finite family
of creation/annihilation generators and proves the number-operator identities
used in lattice fermions, Hubbard/Kitaev models and finite-mode QFT:

`[c†_i c_i, c†_j] = δᵢⱼ c†_i`,
`[c†_i c_i, c_j] = -δᵢⱼ c_i`, and therefore
`[∑ᵢ c†_i c_i, c†_j] = c†_j`.

Only the finite CAR algebra is present.  Fock-space completion, domains of
unbounded operators and continuum anticommutator distributions remain explicit
higher-layer assumptions.
-/

namespace LeanPhy.FieldTheory

open LeanPhy.Quantum
open scoped BigOperators

variable {ι : Type} [DecidableEq ι] [Fintype ι]
variable {A : Type} [Ring A]

structure MultiModeCAR (ι : Type) [DecidableEq ι] [Fintype ι]
    (A : Type) [Ring A] where
  ann : ι → A
  cre : ι → A
  car_ann_cre : ∀ i j, ⟪ann i, cre j⟫ = if i = j then 1 else 0
  car_ann_ann : ∀ i j, ⟪ann i, ann j⟫ = 0
  car_cre_cre : ∀ i j, ⟪cre i, cre j⟫ = 0

namespace MultiModeCAR

variable (M : MultiModeCAR ι A)

def numberOp (i : ι) : A := M.cre i * M.ann i

noncomputable def totalNumber : A := ∑ i, M.numberOp i

theorem ann_cre_rewrite (i j : ι) :
    M.ann i * M.cre j = (if i = j then 1 else 0) - M.cre j * M.ann i := by
  have h := M.car_ann_cre i j
  simpa [anticommutator, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using congrArg (fun x : A => x - M.cre j * M.ann i) h

theorem cre_cre_rewrite (i j : ι) :
    M.cre j * M.cre i = -(M.cre i * M.cre j) := by
  have h := M.car_cre_cre i j
  exact eq_neg_of_add_eq_zero_right (show M.cre i * M.cre j + M.cre j * M.cre i = 0 by
      simpa [anticommutator] using h)

theorem ann_ann_rewrite (i j : ι) :
    M.ann i * M.ann j = -(M.ann j * M.ann i) := by
  have h := M.car_ann_ann i j
  exact eq_neg_of_add_eq_zero_left (show M.ann i * M.ann j + M.ann j * M.ann i = 0 by
    simpa [anticommutator] using h)

theorem number_commutator_cre (i j : ι) :
    ⟦M.numberOp i, M.cre j⟧ = if i = j then M.cre i else 0 := by
  unfold numberOp commutator
  calc
    M.cre i * M.ann i * M.cre j - M.cre j * (M.cre i * M.ann i) =
        M.cre i * (M.ann i * M.cre j) - (M.cre j * M.cre i) * M.ann i := by
          noncomm_ring
    _ = M.cre i * ((if i = j then 1 else 0) - M.cre j * M.ann i) -
        (-M.cre i * M.cre j) * M.ann i := by
          rw [ann_cre_rewrite M i j, cre_cre_rewrite M i j]
          noncomm_ring
  by_cases h : i = j
  · subst h
    simp
    noncomm_ring
  · simp [h]
    noncomm_ring

theorem number_commutator_ann (i j : ι) :
    ⟦M.numberOp i, M.ann j⟧ = if i = j then -M.ann i else 0 := by
  unfold numberOp commutator
  calc
    M.cre i * M.ann i * M.ann j - M.ann j * (M.cre i * M.ann i) =
        M.cre i * (M.ann i * M.ann j) - (M.ann j * M.cre i) * M.ann i := by
          noncomm_ring
    _ = M.cre i * (-M.ann j * M.ann i) -
        ((if j = i then 1 else 0) - M.cre i * M.ann j) * M.ann i := by
          rw [ann_ann_rewrite M i j, ann_cre_rewrite M j i]
          noncomm_ring
  by_cases h : i = j
  · subst h
    simp
    noncomm_ring
  · simp [h]
    have h' : j ≠ i := Ne.symm h
    simp [h']
    noncomm_ring

theorem totalNumber_commutator_cre (j : ι) :
    ⟦M.totalNumber, M.cre j⟧ = M.cre j := by
  classical
  rw [totalNumber, commutator_sum_left]
  rw [Finset.sum_eq_single j]
  · simp [M.number_commutator_cre]
  · intro i _ hij
    simp [M.number_commutator_cre, hij]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem totalNumber_commutator_ann (j : ι) :
    ⟦M.totalNumber, M.ann j⟧ = -M.ann j := by
  classical
  rw [totalNumber, commutator_sum_left]
  rw [Finset.sum_eq_single j]
  · simp [M.number_commutator_ann]
  · intro i _ hij
    simp [M.number_commutator_ann, hij]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

end MultiModeCAR

end LeanPhy.FieldTheory
