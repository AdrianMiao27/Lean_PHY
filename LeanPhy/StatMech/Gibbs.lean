import LeanPhy.StatMech.Probability
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
namespace LeanPhy.StatMech
open scoped BigOperators

noncomputable def partitionFunction {n : Nat} (β : ℝ) (E : Fin n → ℝ) : ℝ :=
  ∑ i, Real.exp (-β * E i)

 theorem partitionFunction_pos {n : Nat} [NeZero n] (β : ℝ) (E : Fin n → ℝ) :
    0 < partitionFunction β E := by
  unfold partitionFunction
  apply Finset.sum_pos'
  · intro i hi
    exact le_of_lt (Real.exp_pos _)
  · exact ⟨0, Finset.mem_univ 0, Real.exp_pos _⟩

noncomputable def gibbsWeight {n : Nat} [NeZero n] (β : ℝ) (E : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (-β * E i) / partitionFunction β E

theorem gibbsWeight_nonneg {n : Nat} [NeZero n] (β : ℝ) (E : Fin n → ℝ) (i : Fin n) :
    0 ≤ gibbsWeight β E i := by
  unfold gibbsWeight
  exact le_of_lt (div_pos (Real.exp_pos _) (partitionFunction_pos β E))

theorem gibbsWeight_sum {n : Nat} [NeZero n] (β : ℝ) (E : Fin n → ℝ) :
    ∑ i, gibbsWeight β E i = 1 := by
  unfold gibbsWeight
  rw [← Finset.sum_div]
  rw [show (∑ i, Real.exp (-β * E i)) = partitionFunction β E from rfl]
  exact div_self (ne_of_gt (partitionFunction_pos β E))

noncomputable def gibbsDistribution {n : Nat} [NeZero n] (β : ℝ) (E : Fin n → ℝ) : FiniteDistribution n where
  weight := gibbsWeight β E
  nonneg := gibbsWeight_nonneg β E
  normalised := gibbsWeight_sum β E

theorem gibbsWeight_shift {n : Nat} [NeZero n] (β c : ℝ) (E : Fin n → ℝ) (i : Fin n) :
    gibbsWeight β (fun j => E j + c) i = gibbsWeight β E i := by
  unfold gibbsWeight partitionFunction
  have hterm (x : Fin n) :
      Real.exp (-β * (E x + c)) = Real.exp (-β * c) * Real.exp (-β * E x) := by
    rw [show -β * (E x + c) = (-β * c) + (-β * E x) by ring]
    rw [Real.exp_add]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  field_simp [ne_of_gt (Real.exp_pos (-β * c)), ne_of_gt (partitionFunction_pos β E)]
end LeanPhy.StatMech

