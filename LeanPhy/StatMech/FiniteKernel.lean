import LeanPhy.StatMech.FiniteProbability
import LeanPhy.Mathematics.FiniteProcess
import Mathlib.Tactic

/-!
# Finite Markov kernels on arbitrary finite state types

This is the generic-label counterpart of `StatMech.Markov`.  A kernel acts on
`FiniteProbability ι`, so lattice sites, spin labels, graph vertices and
measurement outcomes can retain their native finite types.  Every theorem is
finite sum algebra; irreducibility, mixing rates and continuum limits remain
separate analysis inputs.
-/

namespace LeanPhy.StatMech

open scoped BigOperators

structure FiniteKernel (ι : Type*) [Fintype ι] where
  transition : ι → ι → ℝ
  nonneg : ∀ i j, 0 ≤ transition i j
  row_normalized : ∀ i, ∑ j, transition i j = 1

namespace FiniteKernel

variable {ι : Type*} [Fintype ι] (K : FiniteKernel ι)

/-- Push a finite probability through a row-normalized transition kernel. -/
noncomputable def step (p : FiniteProbability ι) : FiniteProbability ι where
  weight := fun j => ∑ i, p.weight i * K.transition i j
  nonneg := by
    intro j
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (p.nonneg i) (K.nonneg i j)
  normalised := by
    classical
    change (∑ j, ∑ i, p.weight i * K.transition i j) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp [K.row_normalized, p.normalised]

/- `FiniteProbability` is already bundled with nonnegativity and
   normalization.  The trivial predicate here lets it participate in the
   general state-map graph while retaining those invariants in the state type. -/
noncomputable def toStateMap :
    LeanPhy.Mathematics.StateMap (FiniteProbability ι) (FiniteProbability ι)
      (fun _ => True) (fun _ => True) where
  toFun := K.step
  preserves := by intro p _; exact trivial

@[simp] theorem step_weight (p : FiniteProbability ι) (j : ι) :
    (K.step p).weight j = ∑ i, p.weight i * K.transition i j := rfl

/-- The observable-side pullback associated with a finite kernel. -/
def pullback (f : ι → ℝ) : ι → ℝ :=
  fun i => ∑ j, K.transition i j * f j

theorem step_expectation (p : FiniteProbability ι) (f : ι → ℝ) :
    (K.step p).expectation f = p.expectation (K.pullback f) := by
  classical
  unfold FiniteProbability.expectation FiniteKernel.step pullback
  change (∑ i, (∑ j, p.weight j * K.transition j i) * f i) =
    ∑ i, p.weight i * (∑ j, K.transition i j * f j)
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/- The expectation identity is exposed as the generic observable-transport
   certificate.  This makes the Markov/Heisenberg duality compositional with
   any other proof-preserving state map that supplies a compatible pullback. -/
noncomputable def toObservableTransport :
    LeanPhy.Mathematics.ObservableTransport K.toStateMap
      (ι → ℝ) (ι → ℝ) ℝ
      (fun p f => p.expectation f) (fun p f => p.expectation f) where
  pullback := K.pullback
  compatible := by
    intro p _ f
    exact K.step_expectation p f

theorem step_expectation_const (p : FiniteProbability ι) :
    (K.step p).expectation (fun _ => 1) = 1 := by
  exact (K.step p).expectation_const 1

/-- Composition in the order `after ∘ before`. -/
noncomputable def compose (after before : FiniteKernel ι) : FiniteKernel ι where
  transition := fun i k => ∑ j, before.transition i j * after.transition j k
  nonneg := by
    intro i k
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (before.nonneg i j) (after.nonneg j k)
  row_normalized := by
    intro i
    classical
    change (∑ k, ∑ j, before.transition i j * after.transition j k) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp [before.row_normalized, after.row_normalized]

@[simp] theorem compose_transition (after before : FiniteKernel ι) (i k : ι) :
    (after.compose before).transition i k =
      ∑ j, before.transition i j * after.transition j k := rfl

theorem step_compose (after before : FiniteKernel ι)
    (p : FiniteProbability ι) :
    (after.compose before).step p = after.step (before.step p) := by
  apply FiniteProbability.ext
  funext k
  classical
  simp only [step_weight, compose_transition]
  symm
  change (∑ i, (∑ j, p.weight j * before.transition j i) * after.transition i k) =
    ∑ i, p.weight i * (∑ j, before.transition i j * after.transition j k)
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A kernel with normalized columns as well as rows. -/
structure DoublyStochasticKernel (ι : Type*) [Fintype ι]
    extends FiniteKernel ι where
  column_normalized : ∀ j, ∑ i, transition i j = 1

/-- The uniform finite probability on any nonempty finite type. -/
noncomputable def uniformProbability [Nonempty ι] : FiniteProbability ι where
  weight := fun _ => (Fintype.card ι : ℝ)⁻¹
  nonneg := by
    intro i
    exact inv_nonneg.mpr (by positivity)
  normalised := by
    classical
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
    field_simp [hc]
    simp [Finset.card_univ]

theorem doublyStochastic_step_uniform [Nonempty ι]
    (K : DoublyStochasticKernel ι) :
    K.toFiniteKernel.step uniformProbability = uniformProbability := by
  apply FiniteProbability.ext
  funext j
  classical
  change ∑ i, (Fintype.card ι : ℝ)⁻¹ * K.transition i j =
    (Fintype.card ι : ℝ)⁻¹
  rw [← Finset.mul_sum, K.column_normalized]
  simp

end FiniteKernel

end LeanPhy.StatMech
