import LeanPhy.StatMech.FiniteKernel
import Mathlib.Tactic

/-!
# Detailed balance and reversible finite dynamics

Detailed balance is the common finite equilibrium condition behind Metropolis
chains, lattice spin updates, kinetic discretisations, reversible Markov
models and several weak-coupling open-system reductions.  This module records
only the algebraic finite statement.  It does not infer irreducibility,
mixing rates, a spectral gap, a continuous-time generator or a thermodynamic
limit.
-/

namespace LeanPhy.StatMech

open scoped BigOperators

namespace FiniteKernel

variable {ι : Type*} [Fintype ι] (K : FiniteKernel ι)

/-- A finite probability is reversible for a kernel when every directed
transition obeys the pairwise detailed-balance equation. -/
def IsDetailedBalance (p : FiniteProbability ι) : Prop :=
  ∀ i j, p.weight i * K.transition i j = p.weight j * K.transition j i

theorem detailedBalance_swap (p : FiniteProbability ι)
    (h : K.IsDetailedBalance p) (i j : ι) :
    p.weight j * K.transition j i = p.weight i * K.transition i j :=
  (h i j).symm

/-- Detailed balance makes the reference distribution stationary. -/
theorem step_eq_of_detailedBalance (p : FiniteProbability ι)
    (h : K.IsDetailedBalance p) : K.step p = p := by
  apply FiniteProbability.ext
  funext j
  classical
  calc
    (K.step p).weight j = ∑ i, p.weight i * K.transition i j := rfl
    _ = ∑ i, p.weight j * K.transition j i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact h i j
    _ = p.weight j * ∑ i, K.transition j i := by
      rw [Finset.mul_sum]
    _ = p.weight j := by rw [K.row_normalized, mul_one]

/-- The weighted transition pairing is symmetric under detailed balance.  It
is the finite algebraic form of reversibility/self-adjointness in the Gibbs
weighted inner product. -/
theorem pullback_pairing_symmetric (p : FiniteProbability ι)
    (h : K.IsDetailedBalance p) (f g : ι → ℝ) :
    p.expectation (fun i => f i * K.pullback g i) =
      p.expectation (fun i => K.pullback f i * g i) := by
  classical
  unfold FiniteProbability.expectation FiniteKernel.pullback
  calc
    (∑ i, p.weight i * (f i * ∑ j, K.transition i j * g j)) =
        ∑ i, ∑ j, (p.weight i * K.transition i j) * (f i * g j) := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            p.weight i * (f i * ∑ j, K.transition i j * g j) =
                (p.weight i * f i) * ∑ j, K.transition i j * g j := by ring
            _ = ∑ j, (p.weight i * f i) * (K.transition i j * g j) := by
                  rw [Finset.mul_sum]
            _ = ∑ j, (p.weight i * K.transition i j) * (f i * g j) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
    _ = ∑ i, ∑ j, (p.weight j * K.transition j i) * (f i * g j) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [h i j]
    _ = ∑ j, ∑ i, (p.weight j * K.transition j i) * (g j * f i) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∑ j, p.weight j * (g j * ∑ i, K.transition j i * f i) := by
          apply Finset.sum_congr rfl
          intro j hj
          calc
            ∑ i, p.weight j * K.transition j i * (g j * f i) =
                ∑ i, (p.weight j * g j) * (K.transition j i * f i) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = (p.weight j * g j) * ∑ i, K.transition j i * f i := by
                  rw [Finset.mul_sum]
            _ = p.weight j * (g j * ∑ i, K.transition j i * f i) := by ring
    _ = ∑ i, p.weight i * ((∑ j, K.transition i j * f j) * g i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring

end FiniteKernel

/-! ## Symmetric conductance models

Many reversible finite models are specified by positive site weights and a
symmetric nonnegative conductance rather than by transition probabilities
directly.  The following constructor turns that physically natural data into
a normalized kernel and its Gibbs-like reference probability.  All statements
are finite and algebraic: no claim about mixing, a spectral gap, or a
continuum/thermodynamic limit is made.
-/

structure ConductanceModel (ι : Type*) [Fintype ι] [Nonempty ι] where
  weight : ι → ℝ
  conductance : ι → ι → ℝ
  weight_pos : ∀ i, 0 < weight i
  conductance_nonneg : ∀ i j, 0 ≤ conductance i j
  symmetric : ∀ i j, conductance i j = conductance j i
  row_sum : ∀ i, ∑ j, conductance i j = weight i

namespace ConductanceModel

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem sum_pos_of_pos (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    0 < ∑ i, w i := by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  obtain ⟨i, hi⟩ := hne
  have hsum : w i ≤ ∑ j, w j := by
    exact Finset.single_le_sum (fun j hj => le_of_lt (hw j)) hi
  exact lt_of_lt_of_le (hw i) hsum

noncomputable def partition (M : ConductanceModel ι) : ℝ :=
  ∑ i, M.weight i

theorem partition_pos (M : ConductanceModel ι) : 0 < M.partition := by
  unfold partition
  exact sum_pos_of_pos M.weight M.weight_pos

noncomputable def kernel (M : ConductanceModel ι) : FiniteKernel ι where
  transition := fun i j => M.conductance i j / M.weight i
  nonneg := by
    intro i j
    exact div_nonneg (M.conductance_nonneg i j) (le_of_lt (M.weight_pos i))
  row_normalized := by
    intro i
    calc
      (∑ j, M.conductance i j / M.weight i) =
          (∑ j, M.conductance i j) / M.weight i := by
            rw [Finset.sum_div]
      _ = M.weight i / M.weight i := by rw [M.row_sum i]
      _ = 1 := div_self (ne_of_gt (M.weight_pos i))

@[simp] theorem kernel_transition (M : ConductanceModel ι) (i j : ι) :
    (M.kernel).transition i j = M.conductance i j / M.weight i := rfl

noncomputable def equilibrium (M : ConductanceModel ι) : FiniteProbability ι where
  weight := fun i => M.weight i / M.partition
  nonneg := by
    intro i
    exact div_nonneg (le_of_lt (M.weight_pos i)) (le_of_lt M.partition_pos)
  normalised := by
    unfold partition
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt M.partition_pos)

@[simp] theorem equilibrium_weight (M : ConductanceModel ι) (i : ι) :
    (M.equilibrium).weight i = M.weight i / M.partition := rfl

theorem detailedBalance (M : ConductanceModel ι) :
    (M.kernel).IsDetailedBalance M.equilibrium := by
  intro i j
  rw [equilibrium_weight, kernel_transition, equilibrium_weight, kernel_transition]
  rw [M.symmetric i j]
  field_simp [ne_of_gt (M.weight_pos i), ne_of_gt (M.weight_pos j),
    ne_of_gt M.partition_pos]

theorem stationary (M : ConductanceModel ι) :
    (M.kernel).step M.equilibrium = M.equilibrium := by
  exact (M.kernel).step_eq_of_detailedBalance M.equilibrium M.detailedBalance

/-- The rank-one conductance model associated with arbitrary positive finite
weights.  Its transition kernel forgets the starting point and samples the
normalized weight, giving a direct Gibbs-to-Markov bridge. -/
noncomputable def fromWeights (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    ConductanceModel ι := by
  let Z : ℝ := ∑ i, w i
  have hZ : 0 < Z := by
    exact sum_pos_of_pos w hw
  exact
    { weight := w
      conductance := fun i j => w i * w j / Z
      weight_pos := hw
      conductance_nonneg := by
        intro i j
        exact div_nonneg (mul_nonneg (le_of_lt (hw i)) (le_of_lt (hw j)))
          (le_of_lt hZ)
      symmetric := by
        intro i j
        ring
      row_sum := by
        intro i
        calc
          (∑ j, w i * w j / Z) = (∑ j, w i * w j) / Z := by
            rw [Finset.sum_div]
          _ = (w i * ∑ j, w j) / Z := by rw [Finset.mul_sum]
          _ = w i := by
            field_simp [ne_of_gt hZ]
            rfl }

@[simp] theorem fromWeights_weight (w : ι → ℝ) (hw : ∀ i, 0 < w i) (i : ι) :
    (fromWeights w hw).weight i = w i := rfl

@[simp] theorem fromWeights_conductance (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (i j : ι) :
    (fromWeights w hw).conductance i j =
      w i * w j / (∑ k, w k) := rfl

theorem fromWeights_stationary (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    ((fromWeights w hw).kernel).step (fromWeights w hw).equilibrium =
      (fromWeights w hw).equilibrium := by
  exact (fromWeights w hw).stationary

end ConductanceModel

end LeanPhy.StatMech

/-! Domain aliases for equilibrium/reversible finite dynamics. -/

namespace LeanPhy

namespace StatMech
abbrev ReversibleFiniteKernel {ι : Type*} [Fintype ι] :=
  FiniteKernel.IsDetailedBalance (ι := ι)
end StatMech

namespace Condensed
abbrev ReversibleHoppingKernel {ι : Type*} [Fintype ι] :=
  StatMech.FiniteKernel.IsDetailedBalance (ι := ι)
end Condensed

namespace GaugeTheory
abbrev ReversibleLatticeKernel {ι : Type*} [Fintype ι] :=
  StatMech.FiniteKernel.IsDetailedBalance (ι := ι)
end GaugeTheory

namespace QuantumInfo
abbrev ReversibleMeasurementKernel {ι : Type*} [Fintype ι] :=
  StatMech.FiniteKernel.IsDetailedBalance (ι := ι)
end QuantumInfo

namespace StatMech
abbrev SymmetricConductanceEquilibrium {ι : Type*} [Fintype ι] [Nonempty ι] :=
  ConductanceModel (ι := ι)
end StatMech

namespace Condensed
abbrev HoppingConductanceModel {ι : Type*} [Fintype ι] [Nonempty ι] :=
  StatMech.ConductanceModel (ι := ι)
end Condensed

namespace GaugeTheory
abbrev LatticeConductanceModel {ι : Type*} [Fintype ι] [Nonempty ι] :=
  StatMech.ConductanceModel (ι := ι)
end GaugeTheory

end LeanPhy
