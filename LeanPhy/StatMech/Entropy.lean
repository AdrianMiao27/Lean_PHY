import LeanPhy.StatMech.Probability
import LeanPhy.StatMech.Markov
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Finite second moments and collision probability

This module is the finite, algebraic part of several entropy calculations.
`secondMoment` is shared by classical distributions, Gibbs states and the
classical output of a POVM.  The collision probability is the second moment
of the probability mass itself.  It is also the quantity called purity for a
diagonal quantum state and the exponential of minus the Renyi-2 entropy.

Only finite sums are used here.  No measure, continuity, thermodynamic limit,
or von Neumann entropy theorem is hidden in the API.
-/

namespace LeanPhy.StatMech

open scoped BigOperators

namespace FiniteDistribution

variable {n : Nat} (p : FiniteDistribution n)

/-! ## A reusable second-moment interface -/

/-- The finite second moment of a real observable. -/
def secondMoment (f : Fin n → ℝ) : ℝ :=
  p.expectation (fun i => f i ^ 2)

theorem secondMoment_eq_sum (f : Fin n → ℝ) :
    p.secondMoment f = ∑ i, p.weight i * f i ^ 2 := rfl

theorem secondMoment_nonneg (f : Fin n → ℝ) :
    0 ≤ p.secondMoment f := by
  unfold secondMoment
  apply p.expectation_nonneg
  intro i
  exact sq_nonneg _

/-! ## Collision probability and Renyi-2 core -/

/-- The collision probability, equivalently the expectation of the mass
function under the same distribution. -/
noncomputable def collisionProbability : ℝ :=
  ∑ i, p.weight i ^ 2

theorem collisionProbability_nonneg :
    0 ≤ p.collisionProbability := by
  unfold collisionProbability
  exact Finset.sum_nonneg (fun i hi => sq_nonneg _)

theorem weight_le_one (i : Fin n) : p.weight i ≤ 1 := by
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
  unfold collisionProbability
  have hterm : ∀ i : Fin n, p.weight i ^ 2 ≤ p.weight i := by
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
  unfold collisionProbability expectation
  simp only [pow_two]

theorem collisionProbability_le_secondMoment_one :
    p.collisionProbability ≤ p.secondMoment (fun _ => 1) := by
  have h := p.collisionProbability_le_one
  unfold secondMoment
  rw [p.expectation_const]
  simpa using h

/-- The finite Renyi-2 entropy.  Its logarithm is deliberately kept at the
analysis boundary; all algebraic facts use `collisionProbability` directly. -/
noncomputable def renyiTwo : ℝ := -Real.log p.collisionProbability

theorem collisionProbability_uniform (hn : 0 < n) :
    (uniformDistribution n hn).collisionProbability = (n : ℝ)⁻¹ := by
  unfold collisionProbability
  change (∑ i : Fin n, ((n : ℝ)⁻¹) ^ 2) = (n : ℝ)⁻¹
  rw [Finset.sum_const, Finset.card_fin]
  rw [nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnR]

end FiniteDistribution

end LeanPhy.StatMech
