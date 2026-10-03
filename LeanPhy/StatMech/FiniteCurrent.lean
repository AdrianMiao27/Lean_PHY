import LeanPhy.Mathematics.FiniteDivergence
import LeanPhy.StatMech.FiniteKernel
import Mathlib.Tactic

/-!
# Markov currents as finite conservation certificates

The probability transported by a finite Markov kernel can be viewed as a
current on the complete directed graph of states.  Its divergence is exactly
`p' - p`, where `p'` is the pushed-forward distribution.  This is a useful
bridge between stochastic dynamics, finite-volume continuity equations,
lattice hopping and measurement post-processing.

Only finite sums and the row-normalisation field of `FiniteKernel` are used.
No continuous-time process, positivity-preserving semigroup, stationary
limit or physical interpretation is inferred.
-/

namespace LeanPhy.StatMech

open scoped BigOperators

namespace FiniteKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (K : FiniteKernel ι)

/-- The directed edge current induced by a probability distribution and a
finite Markov kernel. -/
def current (p : FiniteProbability ι) : (ι × ι) → ℝ :=
  fun e => p.weight e.1 * K.transition e.1 e.2

@[simp] theorem current_apply (p : FiniteProbability ι) (e : ι × ι) :
    K.current p e = p.weight e.1 * K.transition e.1 e.2 := rfl

def markovTail : (ι × ι) → ι := Prod.fst
def markovHead : (ι × ι) → ι := Prod.snd

/-- The Markov current divergence is the change in probability at a state. -/
theorem divergence_current (p : FiniteProbability ι) (j : ι) :
    Mathematics.FiniteDivergence.divergence markovTail markovHead (K.current p) j =
      (K.step p).weight j - p.weight j := by
  classical
  unfold Mathematics.FiniteDivergence.divergence current markovTail markovHead
  simp [Fintype.sum_prod_type]
  rw [← Finset.mul_sum, K.row_normalized, mul_one]

/-- The pushed-forward Markov distribution is a conservation certificate for
the induced edge current. -/
theorem conservationCertificate (p : FiniteProbability ι) :
    Mathematics.FiniteDivergence.ConservationCertificate
      markovTail markovHead (K.current p) (fun j => (K.step p).weight j - p.weight j) := by
  refine ⟨fun j => ?_⟩
  exact K.divergence_current p j

/-! Every Markov step has a zero-total probability source when represented as
the complete directed-edge current. -/
theorem total_step_source_zero (p : FiniteProbability ι) :
    ∑ j, ((K.step p).weight j - p.weight j) = 0 := by
  exact (K.conservationCertificate p).total_source_zero

end FiniteKernel

end LeanPhy.StatMech

namespace LeanPhy

namespace StatMech

def MarkovCurrentConservation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : FiniteKernel ι) (p : FiniteProbability ι) : Prop :=
  Mathematics.FiniteDivergence.ConservationCertificate
    FiniteKernel.markovTail FiniteKernel.markovHead
    (FiniteKernel.current K p) (fun j => (K.step p).weight j - p.weight j)

end StatMech

namespace Condensed

def HoppingMarkovCurrent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : StatMech.FiniteKernel ι) (p : StatMech.FiniteProbability ι) : Prop :=
  Mathematics.FiniteDivergence.ConservationCertificate
    StatMech.FiniteKernel.markovTail StatMech.FiniteKernel.markovHead
    (StatMech.FiniteKernel.current K p)
    (fun j => (K.step p).weight j - p.weight j)

end Condensed

namespace GaugeTheory

def LatticeMarkovCurrent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : StatMech.FiniteKernel ι) (p : StatMech.FiniteProbability ι) : Prop :=
  Mathematics.FiniteDivergence.ConservationCertificate
    StatMech.FiniteKernel.markovTail StatMech.FiniteKernel.markovHead
    (StatMech.FiniteKernel.current K p)
    (fun j => (K.step p).weight j - p.weight j)

end GaugeTheory

end LeanPhy
