import Mathlib.Tactic

/-!
# Finite probability and observables

This is a deliberately small bridge shared by statistical mechanics, finite
classical stochastic models, and the classical post-processing of a quantum
measurement.  A distribution is a nonnegative, normalized function on a
finite outcome type.  All statements here are finite sums; no measure,
integral, thermodynamic limit, or entropy continuity theorem is hidden in the
definitions.
-/

namespace LeanPhy.StatMech

open scoped BigOperators

/-- A normalized probability distribution on `Fin n`. -/
structure FiniteDistribution (n : Nat) where
  weight : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  normalised : ∑ i, weight i = 1

namespace FiniteDistribution

variable {n : Nat} (p : FiniteDistribution n)

/-- Expectation of a real observable on the finite outcome space. -/
def expectation (f : Fin n → ℝ) : ℝ := ∑ i, p.weight i * f i

@[simp] theorem expectation_const (c : ℝ) : p.expectation (fun _ => c) = c := by
  unfold expectation
  rw [← Finset.sum_mul]
  rw [p.normalised]
  ring

theorem expectation_add (f g : Fin n → ℝ) :
    p.expectation (f + g) = p.expectation f + p.expectation g := by
  unfold expectation
  simp only [Pi.add_apply]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

theorem expectation_smul (c : ℝ) (f : Fin n → ℝ) :
    p.expectation (c • f) = c * p.expectation f := by
  unfold expectation
  simp only [Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem expectation_nonneg {f : Fin n → ℝ} (hf : ∀ i, 0 ≤ f i) :
    0 ≤ p.expectation f := by
  unfold expectation
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (p.nonneg i) (hf i)

/-- The finite variance of an observable. -/
def variance (f : Fin n → ℝ) : ℝ :=
  p.expectation (fun i => (f i - p.expectation f) ^ 2)

theorem variance_nonneg (f : Fin n → ℝ) : 0 ≤ p.variance f := by
  apply p.expectation_nonneg
  intro i
  exact sq_nonneg _

theorem variance_const (c : ℝ) : p.variance (fun _ => c) = 0 := by
  unfold variance
  rw [expectation_const]
  simp [expectation, ← Finset.sum_mul, p.normalised]

theorem expectation_one : p.expectation (fun _ => 1) = 1 := by
  exact p.expectation_const 1

end FiniteDistribution

end LeanPhy.StatMech
