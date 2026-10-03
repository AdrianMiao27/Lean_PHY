import LeanPhy.StatMech.Probability
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-!
# Finite Markov kernels

Finite transition kernels are shared by lattice models, kinetic theory,
classical Monte Carlo, measurement post-processing and open-system limits.  A
kernel carries non-negativity and row normalization as fields.  Its action on a
finite distribution therefore produces another distribution by a kernel
checked proof, and composition is associative at the level of the explicit
finite sums.  Stationarity of the uniform distribution is derived for doubly
stochastic kernels.  No ergodic, mixing, continuum or thermodynamic-limit
claim is made here.
-/

namespace LeanPhy.StatMech

open scoped BigOperators

namespace FiniteDistribution

/-- Distributions are determined by their weight functions; proof fields are
propositions and hence irrelevant. -/
theorem ext {n : Nat} {p q : FiniteDistribution n}
    (h : p.weight = q.weight) : p = q := by
  cases p
  cases q
  cases h
  rfl

end FiniteDistribution

/-- A finite Markov transition kernel. -/
structure FiniteMarkovKernel (n : Nat) where
  transition : Fin n → Fin n → ℝ
  nonneg : ∀ i j, 0 ≤ transition i j
  row_normalized : ∀ i, ∑ j, transition i j = 1

/-! ## Action on distributions -/

noncomputable def step {n : Nat} (K : FiniteMarkovKernel n)
    (p : FiniteDistribution n) : Fin n → ℝ :=
  fun j => ∑ i, p.weight i * K.transition i j

theorem step_nonneg {n : Nat} (K : FiniteMarkovKernel n)
    (p : FiniteDistribution n) : ∀ j, 0 ≤ step K p j := by
  intro j
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (p.nonneg i) (K.nonneg i j)

theorem step_normalized {n : Nat} (K : FiniteMarkovKernel n)
    (p : FiniteDistribution n) : ∑ j, step K p j = 1 := by
  unfold step
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp [K.row_normalized, p.normalised]

/-- The push-forward of a finite distribution along a Markov kernel. -/
noncomputable def stepDistribution {n : Nat} (K : FiniteMarkovKernel n)
    (p : FiniteDistribution n) : FiniteDistribution n where
  weight := step K p
  nonneg := step_nonneg K p
  normalised := step_normalized K p

theorem step_expectation_one {n : Nat} (K : FiniteMarkovKernel n)
    (p : FiniteDistribution n) :
    (stepDistribution K p).expectation (fun _ => 1) = 1 :=
  (stepDistribution K p).expectation_one

/-- The dual (observable-side) action of a Markov kernel. -/
noncomputable def pullbackObservable {n : Nat} (K : FiniteMarkovKernel n)
    (f : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, K.transition i j * f j

/-! The expectation identity is the finite-state Heisenberg picture: pushing a
state forward is equivalent to pulling an observable backward. -/
theorem step_expectation {n : Nat} (K : FiniteMarkovKernel n)
    (p : FiniteDistribution n) (f : Fin n → ℝ) :
    (stepDistribution K p).expectation f =
      p.expectation (pullbackObservable K f) := by
  unfold FiniteDistribution.expectation stepDistribution step pullbackObservable
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

/-! ## Composition and stationary uniform measure -/

noncomputable def compose {n : Nat} (K L : FiniteMarkovKernel n) :
    FiniteMarkovKernel n where
  transition := fun i k => ∑ j, K.transition i j * L.transition j k
  nonneg := by
    intro i k
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (K.nonneg i j) (L.nonneg j k)
  row_normalized := by
    intro i
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp [L.row_normalized, K.row_normalized]

theorem compose_step {n : Nat} (K L : FiniteMarkovKernel n)
    (p : FiniteDistribution n) :
    stepDistribution L (stepDistribution K p) = stepDistribution (compose K L) p := by
  apply FiniteDistribution.ext
  funext k
  change (∑ i, (∑ j, p.weight j * K.transition j i) * L.transition i k) =
    ∑ i, p.weight i * (∑ j, K.transition i j * L.transition j k)
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A doubly stochastic kernel has normalized columns as well as rows. -/
structure DoublyStochasticKernel (n : Nat) extends FiniteMarkovKernel n where
  column_normalized : ∀ j, ∑ i, transition i j = 1

/-- The uniform distribution on a nonempty finite state space. -/
noncomputable def uniformDistribution (n : Nat) (hn : 0 < n) :
    FiniteDistribution n where
  weight := fun _ => (n : ℝ)⁻¹
  nonneg := by
    intro i
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    exact inv_nonneg.mpr hnR.le
  normalised := by
    rw [Finset.sum_const, Finset.card_fin]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    rw [nsmul_eq_mul]
    norm_num [hnR]

theorem doubly_stochastic_uniform {n : Nat} (hn : 0 < n)
    (K : DoublyStochasticKernel n) :
    stepDistribution K.toFiniteMarkovKernel (uniformDistribution n hn) =
      uniformDistribution n hn := by
  apply FiniteDistribution.ext
  funext j
  change (∑ i, (n : ℝ)⁻¹ * K.transition i j) = (n : ℝ)⁻¹
  rw [← Finset.mul_sum, K.column_normalized]
  simp

end LeanPhy.StatMech
