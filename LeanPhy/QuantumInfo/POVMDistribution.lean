import LeanPhy.QuantumInfo.POVM
import LeanPhy.Quantum.DiagonalState
import LeanPhy.StatMech.Probability
import LeanPhy.StatMech.FiniteProbability
import LeanPhy.StatMech.Entropy

/-!
# Quantum-to-classical finite measurement bridge

A finite POVM followed by a density matrix produces an ordinary finite
probability distribution.  This adapter is intentionally restricted to
`Fin n` outcomes so that the statistical-mechanics and measurement layers can
share the same expectation and Markov-kernel APIs without introducing a
measure-theoretic probability space.
-/

namespace LeanPhy.QuantumInfo

open LeanPhy.Quantum
open LeanPhy.StatMech
open scoped BigOperators

noncomputable def POVM.toFiniteDistribution {d n : Nat}
    (M : POVM d (Fin n)) (rho : State d) (hrho : IsDensity rho) :
    FiniteDistribution n where
  weight := probability M rho
  nonneg := probability_nonneg M rho hrho
  normalised := probability_sum_is_one M rho hrho

/-- The same measurement adapter without forcing outcome labels to be `Fin n`.
This is the preferred interface for named finite outcomes such as spin labels,
polarization modes, lattice sites, or colour states. -/
noncomputable def POVM.toFiniteProbability {d : Nat} {ι : Type} [Fintype ι]
    (M : POVM d ι) (rho : State d) (hrho : IsDensity rho) :
    FiniteProbability ι where
  weight := probability M rho
  nonneg := probability_nonneg M rho hrho
  normalised := probability_sum_is_one M rho hrho

@[simp] theorem POVM.toFiniteProbability_weight {d : Nat} {ι : Type} [Fintype ι]
    (M : POVM d ι) (rho : State d) (hrho : IsDensity rho) (i : ι) :
    (M.toFiniteProbability rho hrho).weight i = probability M rho i := rfl

theorem POVM.measurement_probability_expectation {d : Nat} {ι : Type} [Fintype ι]
    (M : POVM d ι) (rho : State d) (hrho : IsDensity rho)
    (f : ι → ℝ) :
    (M.toFiniteProbability rho hrho).expectation f =
      ∑ i, probability M rho i * f i := rfl

theorem POVM.measurement_probability_collisionProbability {d : Nat} {ι : Type}
    [Fintype ι] (M : POVM d ι) (rho : State d) (hrho : IsDensity rho) :
    (M.toFiniteProbability rho hrho).collisionProbability =
      ∑ i, probability M rho i ^ 2 := rfl

@[simp] theorem POVM.toFiniteDistribution_weight {d n : Nat}
    (M : POVM d (Fin n)) (rho : State d) (hrho : IsDensity rho) (i : Fin n) :
    (M.toFiniteDistribution rho hrho).weight i = probability M rho i := rfl

theorem POVM.measurement_expectation {d n : Nat}
    (M : POVM d (Fin n)) (rho : State d) (hrho : IsDensity rho)
    (f : Fin n → ℝ) :
    (M.toFiniteDistribution rho hrho).expectation f =
      ∑ i, probability M rho i * f i := rfl

/-! The same adapter exposes the algebraic collision probability used in
finite statistical mechanics.  This lets a measurement distribution,
a Gibbs distribution and a classical Markov state share one second-order API.
-/

theorem POVM.measurement_collisionProbability {d n : Nat}
    (M : POVM d (Fin n)) (rho : State d) (hrho : IsDensity rho) :
    (M.toFiniteDistribution rho hrho).collisionProbability =
      ∑ i, probability M rho i ^ 2 := rfl

/-- The same POVM output can be viewed as a diagonal quantum state.  Its
matrix purity is exactly the collision probability of the classical outcome
distribution, so measurement statistics can be passed back into finite
quantum-matrix calculations without reproving the sum identity. -/
theorem POVM.measurement_matrixPurity {d n : Nat}
    (M : POVM d (Fin n)) (rho : State d) (hrho : IsDensity rho) :
    matrixPurity (diagonalState (M.toFiniteDistribution rho hrho)) =
      ((M.toFiniteDistribution rho hrho).collisionProbability : ℂ) :=
  diagonalState_purity (M.toFiniteDistribution rho hrho)

end LeanPhy.QuantumInfo
