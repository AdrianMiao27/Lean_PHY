import LeanPhy.StatMech.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Gibbs ensembles on arbitrary finite state types

This is the generic-label version of `StatMech.Gibbs`.  It supplies the finite
algebraic thermal layer used by lattice models, spin systems, bands and finite
internal-state models without requiring an artificial `Fin n` encoding.
-/

namespace LeanPhy.StatMech

open scoped BigOperators

noncomputable def finitePartitionFunction {ι : Type*} [Fintype ι]
    (β : ℝ) (E : ι → ℝ) : ℝ :=
  ∑ i, Real.exp (-β * E i)

theorem finitePartitionFunction_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (E : ι → ℝ) :
    0 < finitePartitionFunction β E := by
  classical
  unfold finitePartitionFunction
  apply Finset.sum_pos'
  · intro i hi
    exact le_of_lt (Real.exp_pos _)
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, Finset.mem_univ i, Real.exp_pos _⟩

noncomputable def finiteGibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (E : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (-β * E i) / finitePartitionFunction β E

theorem finiteGibbsWeight_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (E : ι → ℝ) (i : ι) :
    0 ≤ finiteGibbsWeight β E i := by
  unfold finiteGibbsWeight
  exact le_of_lt (div_pos (Real.exp_pos _)
    (finitePartitionFunction_pos β E))

theorem finiteGibbsWeight_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (E : ι → ℝ) :
    ∑ i, finiteGibbsWeight β E i = 1 := by
  unfold finiteGibbsWeight
  rw [← Finset.sum_div]
  rw [show (∑ i, Real.exp (-β * E i)) = finitePartitionFunction β E from rfl]
  exact div_self (ne_of_gt (finitePartitionFunction_pos β E))

noncomputable def finiteGibbsProbability {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (E : ι → ℝ) : FiniteProbability ι where
  weight := finiteGibbsWeight β E
  nonneg := finiteGibbsWeight_nonneg β E
  normalised := finiteGibbsWeight_sum β E

theorem finiteGibbsWeight_shift {ι : Type*} [Fintype ι] [Nonempty ι]
    (β c : ℝ) (E : ι → ℝ) (i : ι) :
    finiteGibbsWeight β (fun j => E j + c) i = finiteGibbsWeight β E i := by
  classical
  unfold finiteGibbsWeight finitePartitionFunction
  have hterm (x : ι) :
      Real.exp (-β * (E x + c)) =
        Real.exp (-β * c) * Real.exp (-β * E x) := by
    rw [show -β * (E x + c) = (-β * c) + (-β * E x) by ring]
    rw [Real.exp_add]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  field_simp [ne_of_gt (Real.exp_pos (-β * c)),
    ne_of_gt (finitePartitionFunction_pos β E)]

end LeanPhy.StatMech
