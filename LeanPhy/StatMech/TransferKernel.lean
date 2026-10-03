import LeanPhy.StatMech.FiniteKernel
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Positive transfer matrices as finite Markov kernels

Transfer matrices in lattice statistical mechanics are often specified as
unnormalized nonnegative Boltzmann weights.  This adapter normalizes each row
and exposes the result through the existing `FiniteKernel` API.  It therefore
connects transfer-matrix calculations, finite Gibbs/Markov states and
observable pullbacks without identifying a partition function with a
probability distribution by fiat.

The row-sum positivity condition is explicit.  It rules out an empty or
forbidden row and is the only extra assumption needed for normalization.
Thermodynamic limits, Perron--Frobenius asymptotics and mixing rates remain
outside this finite layer.
-/

namespace LeanPhy.StatMech

open scoped BigOperators

/-- A finite nonnegative transfer matrix with strictly positive row sums. -/
structure PositiveTransferMatrix (ι : Type*) [Fintype ι] where
  weight : ι → ι → ℝ
  nonneg : ∀ i j, 0 ≤ weight i j
  rowSum_pos : ∀ i, 0 < ∑ j, weight i j

namespace PositiveTransferMatrix

variable {ι : Type*} [Fintype ι] (T : PositiveTransferMatrix ι)

/-- The total outgoing Boltzmann weight from a state. -/
def rowSum (i : ι) : ℝ := ∑ j, T.weight i j

@[simp] theorem rowSum_eq (i : ι) : T.rowSum i = ∑ j, T.weight i j := rfl

/-- Row normalization of the transfer matrix. -/
noncomputable def toKernel : FiniteKernel ι where
  transition := fun i j => T.weight i j / T.rowSum i
  nonneg := by
    intro i j
    exact div_nonneg (T.nonneg i j) (le_of_lt (T.rowSum_pos i))
  row_normalized := by
    intro i
    rw [show (∑ j, T.weight i j / T.rowSum i) =
      (∑ j, T.weight i j) / T.rowSum i by rw [Finset.sum_div]]
    rw [← T.rowSum_eq i]
    exact div_self (ne_of_gt (T.rowSum_pos i))

@[simp] theorem toKernel_transition (i j : ι) :
    T.toKernel.transition i j = T.weight i j / T.rowSum i := rfl

theorem toKernel_step_weight (p : FiniteProbability ι) (j : ι) :
    (T.toKernel.step p).weight j =
      ∑ i, p.weight i * (T.weight i j / T.rowSum i) := by
  rfl

theorem toKernel_preserves_probability (p : FiniteProbability ι) :
    ∑ j, (T.toKernel.step p).weight j = 1 := by
  exact (T.toKernel.step p).normalised

theorem toKernel_expectation_duality (p : FiniteProbability ι) (f : ι → ℝ) :
    (T.toKernel.step p).expectation f =
      p.expectation (T.toKernel.pullback f) := by
  exact T.toKernel.step_expectation p f

end PositiveTransferMatrix

end LeanPhy.StatMech
