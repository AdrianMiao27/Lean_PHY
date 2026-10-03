import LeanPhy.QuantumInfo.Channel
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LeanPhy.QuantumInfo

open LeanPhy.Quantum
open scoped BigOperators Matrix

noncomputable def lindbladGenerator {n : Nat} {ι : Type} [Fintype ι]
    (H : Operator n) (L : ι → Operator n) (rho : State n) : State n :=
  (-Complex.I) • (H * rho - rho * H) +
    ∑ k, (L k * rho * Matrix.conjTranspose (L k) -
      (1 / 2 : ℂ) •
        (Matrix.conjTranspose (L k) * L k * rho +
          rho * Matrix.conjTranspose (L k) * L k))

theorem trace_commutator_zero {n : Nat} (H rho : State n) :
    Matrix.trace (H * rho - rho * H) = 0 := by
  simp only [Matrix.trace_sub]
  rw [Matrix.trace_mul_comm H rho]
  exact sub_self _

theorem trace_lindblad_dissipator {n : Nat} (L rho : State n) :
    Matrix.trace (L * rho * Matrix.conjTranspose L -
      (1 / 2 : ℂ) •
        (Matrix.conjTranspose L * L * rho + rho * Matrix.conjTranspose L * L)) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add]
  have h₁ : Matrix.trace (L * rho * Matrix.conjTranspose L) =
      Matrix.trace (Matrix.conjTranspose L * L * rho) :=
    Matrix.trace_mul_cycle L rho (Matrix.conjTranspose L)
  have h₂ : Matrix.trace (Matrix.conjTranspose L * L * rho) =
      Matrix.trace (rho * Matrix.conjTranspose L * L) :=
    Matrix.trace_mul_cycle (Matrix.conjTranspose L) L rho
  rw [h₁, h₂]
  ring

theorem lindblad_trace_zero {n : Nat} {ι : Type} [Fintype ι]
    (H : Operator n) (L : ι → Operator n) (rho : State n) :
    Matrix.trace (lindbladGenerator H L rho) = 0 := by
  unfold lindbladGenerator
  rw [Matrix.trace_add, Matrix.trace_smul, trace_commutator_zero]
  simp only [Matrix.trace_sum]
  have hz : ∀ k : ι,
      Matrix.trace (L k * rho * Matrix.conjTranspose (L k) -
        (1 / 2 : ℂ) •
          (Matrix.conjTranspose (L k) * L k * rho +
            rho * Matrix.conjTranspose (L k) * L k)) = 0 := by
    intro k
    exact trace_lindblad_dissipator (L k) rho
  simp only [smul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro k hk
  exact hz k

end LeanPhy.QuantumInfo
