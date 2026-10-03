import LeanPhy.QuantumInfo.KrausBundle
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-!
# Heisenberg-picture interface for finite channels

For a Kraus family `K_i`, the Schrödinger action is
`rho ↦ sum_i K_i rho K_i†`, while the dual observable action is
`A ↦ sum_i K_i† A K_i`.  This file proves the finite trace-pairing identity
between the two pictures, unitality of the dual of a trace-preserving family,
and reversal of Kraus composition.  These are the common algebraic steps in
open quantum systems, quantum control, lattice transfer calculations and
measurement post-processing.  No continuous adjoint semigroup or domain
statement for unbounded operators is asserted.
-/

namespace LeanPhy.QuantumInfo

open LeanPhy.Quantum
open scoped BigOperators Matrix

/-- The finite Heisenberg-picture action associated with a Kraus family. -/
noncomputable def adjointKraus {n : Nat} {ι : Type} [Fintype ι]
    (K : ι → Operator n) (A : Operator n) : Operator n :=
  ∑ k, Matrix.conjTranspose (K k) * A * K k

/-! ## Trace pairing and structural laws -/

theorem expectation_applyKraus_adjoint {n : Nat} {ι : Type} [Fintype ι]
    (K : ι → Operator n) (rho : State n) (A : Operator n) :
    expectation (applyKraus K rho) A = expectation rho (adjointKraus K A) := by
  change Matrix.trace ((∑ k, K k * rho * Matrix.conjTranspose (K k)) * A) =
    Matrix.trace (rho * (∑ k, Matrix.conjTranspose (K k) * A * K k))
  calc
    Matrix.trace ((∑ k, K k * rho * Matrix.conjTranspose (K k)) * A) =
        ∑ k, Matrix.trace (K k * rho * Matrix.conjTranspose (K k) * A) := by
      rw [Finset.sum_mul, Matrix.trace_sum]
    _ = ∑ k, Matrix.trace (rho * Matrix.conjTranspose (K k) * A * K k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [show K k * rho * Matrix.conjTranspose (K k) * A =
        (K k * rho) * (Matrix.conjTranspose (K k) * A) by noncomm_ring]
      rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
      congr 1
      noncomm_ring
    _ = Matrix.trace (rho * (∑ k, Matrix.conjTranspose (K k) * A * K k)) := by
      rw [Finset.mul_sum]
      simp only [Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      noncomm_ring

theorem adjointKraus_complete {n : Nat} {ι : Type} [Fintype ι]
    (K : ι → Operator n)
    (htp : (∑ k, Matrix.conjTranspose (K k) * K k) = 1) :
    adjointKraus K (1 : Operator n) = 1 := by
  unfold adjointKraus
  simpa using htp

theorem adjointKraus_add {n : Nat} {ι : Type} [Fintype ι]
    (K : ι → Operator n) (A B : Operator n) :
    adjointKraus K (A + B) = adjointKraus K A + adjointKraus K B := by
  unfold adjointKraus
  simp only [mul_add, add_mul, Finset.sum_add_distrib]

theorem adjointKraus_smul {n : Nat} {ι : Type} [Fintype ι]
    (K : ι → Operator n) (c : ℂ) (A : Operator n) :
    adjointKraus K (c • A) = c • adjointKraus K A := by
  unfold adjointKraus
  simp only [Matrix.mul_smul, smul_mul_assoc, Finset.smul_sum]

theorem adjointKraus_comp {n : Nat} {ι κ : Type} [Fintype ι] [Fintype κ]
    (K : ι → Operator n) (L : κ → Operator n) (A : Operator n) :
    adjointKraus K (adjointKraus L A) =
      adjointKraus (fun p : κ × ι => L p.1 * K p.2) A := by
  unfold adjointKraus
  simp only [Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.conjTranspose_mul]
  noncomm_ring

/-! ## Bundled channels expose the same dual API -/

theorem KrausChannel.expectation_duality {n : Nat} {ι : Type} [Fintype ι]
    (C : KrausChannel n ι) (rho : State n) (A : Operator n) :
    expectation (C.toFiniteChannel rho) A = expectation rho (adjointKraus C.op A) := by
  rw [KrausChannel.toFiniteChannel_apply]
  exact expectation_applyKraus_adjoint C.op rho A

theorem KrausChannel.adjoint_unital {n : Nat} {ι : Type} [Fintype ι]
    (C : KrausChannel n ι) : adjointKraus C.op (1 : Operator n) = 1 :=
  adjointKraus_complete C.op C.complete

end LeanPhy.QuantumInfo
