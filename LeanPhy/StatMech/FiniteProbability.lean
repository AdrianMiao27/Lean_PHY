import Mathlib.Tactic

/-!
# Finite probabilities on arbitrary finite outcome types

`FiniteDistribution` is convenient for matrix APIs indexed by `Fin n`, but
physical outcome spaces often have meaningful finite labels: spin projections,
lattice sites, bands, colours, or measurement outcomes.  This module keeps
the same finite, algebraic semantics while allowing any `Fintype` as the
outcome type.  It is deliberately independent of measure theory.
-/

namespace LeanPhy.StatMech

open scoped BigOperators

/-- A normalized nonnegative probability mass function on a finite type. -/
structure FiniteProbability (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  normalised : ∑ i, weight i = 1

namespace FiniteProbability

variable {ι : Type*} [Fintype ι] (p : FiniteProbability ι)

/-- Probability structures are determined by their mass functions; proof
fields carry no additional computational data. -/
theorem ext {p q : FiniteProbability ι} (h : p.weight = q.weight) : p = q := by
  cases p
  cases q
  cases h
  rfl

/-- Expectation of a real-valued observable on a finite outcome space. -/
def expectation (f : ι → ℝ) : ℝ := ∑ i, p.weight i * f i

@[simp] theorem expectation_const (c : ℝ) : p.expectation (fun _ => c) = c := by
  classical
  unfold expectation
  rw [← Finset.sum_mul, p.normalised]
  ring

theorem expectation_add (f g : ι → ℝ) :
    p.expectation (f + g) = p.expectation f + p.expectation g := by
  classical
  unfold expectation
  simp only [Pi.add_apply]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

theorem expectation_smul (c : ℝ) (f : ι → ℝ) :
    p.expectation (c • f) = c * p.expectation f := by
  classical
  unfold expectation
  simp only [Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem expectation_nonneg {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    0 ≤ p.expectation f := by
  classical
  unfold expectation
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (p.nonneg i) (hf i)

/-- The second moment of a real observable. -/
def secondMoment (f : ι → ℝ) : ℝ :=
  p.expectation (fun i => f i ^ 2)

theorem secondMoment_nonneg (f : ι → ℝ) :
    0 ≤ p.secondMoment f := by
  apply p.expectation_nonneg
  intro i
  exact sq_nonneg _

/-- Collision probability, also the purity of the corresponding diagonal
quantum state when the finite labels are enumerated by a basis. -/
def collisionProbability : ℝ := ∑ i, p.weight i ^ 2

theorem collisionProbability_nonneg :
    0 ≤ p.collisionProbability := by
  classical
  unfold collisionProbability
  exact Finset.sum_nonneg (fun i hi => sq_nonneg _)

theorem weight_le_one (i : ι) : p.weight i ≤ 1 := by
  classical
  have hrest : 0 ≤ ∑ j ∈ (Finset.univ.erase i), p.weight j := by
    apply Finset.sum_nonneg
    intro j hj
    exact p.nonneg j
  have hdecomp : p.weight i + ∑ j ∈ (Finset.univ.erase i), p.weight j = 1 := by
    rw [← p.normalised]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  linarith

theorem collisionProbability_le_one :
    p.collisionProbability ≤ 1 := by
  classical
  unfold collisionProbability
  have hterm : ∀ i : ι, p.weight i ^ 2 ≤ p.weight i := by
    intro i
    have hi := p.nonneg i
    have hle := p.weight_le_one i
    nlinarith
  calc
    (∑ i, p.weight i ^ 2) ≤ ∑ i, p.weight i :=
      Finset.sum_le_sum (fun i hi => hterm i)
    _ = 1 := p.normalised

theorem collisionProbability_eq_expectation_weight :
    p.collisionProbability = p.expectation p.weight := by
  classical
  unfold collisionProbability expectation
  simp only [pow_two]

end FiniteProbability

end LeanPhy.StatMech
