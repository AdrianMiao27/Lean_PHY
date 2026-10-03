import LeanPhy.QuantumInfo.Channel
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace LeanPhy.QuantumInfo
open LeanPhy.Quantum
open scoped BigOperators Matrix

/-- A finite Kraus channel bundles its operator family together with the
completeness relation.  The relation is the exact finite-dimensional
trace-preservation invariant and cannot be dropped during composition. -/
structure KrausChannel (n : Nat) (ι : Type) [Fintype ι] where
  op : ι → Operator n
  complete : (∑ i, Matrix.conjTranspose (op i) * op i) = 1

/-- Forget the Kraus presentation and expose the bundled finite channel API. -/
noncomputable def KrausChannel.toFiniteChannel {n : Nat} {ι : Type} [Fintype ι]
    (C : KrausChannel n ι) : FiniteChannel n :=
  fromKraus C.op C.complete

theorem KrausChannel.toFiniteChannel_apply {n : Nat} {ι : Type} [Fintype ι]
    (C : KrausChannel n ι) (rho : State n) :
    C.toFiniteChannel rho = applyKraus C.op rho := rfl

theorem KrausChannel.trace_preserving {n : Nat} {ι : Type} [Fintype ι]
    (C : KrausChannel n ι) (rho : State n) :
    Matrix.trace (applyKraus C.op rho) = Matrix.trace rho :=
  kraus_trace C.op rho C.complete

theorem KrausChannel.map_isDensity {n : Nat} {ι : Type} [Fintype ι]
    (C : KrausChannel n ι) (rho : State n) (hrho : IsDensity rho) :
    IsDensity (applyKraus C.op rho) :=
  applyKraus_isDensity C.op rho hrho C.complete

/-- Composition in the order `after ∘ before`; the new Kraus operators are
`after_i * before_j`. -/
noncomputable def KrausChannel.compose {n : Nat} {ι κ : Type}
    [Fintype ι] [Fintype κ]
    (after : KrausChannel n ι) (before : KrausChannel n κ) :
    KrausChannel n (ι × κ) where
  op := fun p => after.op p.1 * before.op p.2
  complete := by
    simp only [Fintype.sum_prod_type]
    calc
      (∑ x, ∑ y,
          Matrix.conjTranspose (after.op x * before.op y) *
            (after.op x * before.op y))
          = ∑ y,
              Matrix.conjTranspose (before.op y) *
                (∑ x, Matrix.conjTranspose (after.op x) * after.op x) *
                before.op y := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y hy
        calc
          (∑ x,
              Matrix.conjTranspose (after.op x * before.op y) *
                (after.op x * before.op y))
              = ∑ x,
                  Matrix.conjTranspose (before.op y) *
                    (Matrix.conjTranspose (after.op x) * after.op x) *
                    before.op y := by
            apply Finset.sum_congr rfl
            intro x hx
            simp only [Matrix.conjTranspose_mul]
            noncomm_ring
          _ = Matrix.conjTranspose (before.op y) *
                (∑ x, Matrix.conjTranspose (after.op x) * after.op x) *
                before.op y := by
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = 1 := by
        rw [after.complete]
        simp [before.complete]

theorem KrausChannel.compose_toFiniteChannel_apply {n : Nat} {ι κ : Type}
    [Fintype ι] [Fintype κ]
    (after : KrausChannel n ι) (before : KrausChannel n κ) (rho : State n) :
    (after.compose before).toFiniteChannel rho =
      after.toFiniteChannel (before.toFiniteChannel rho) := by
  rw [KrausChannel.toFiniteChannel_apply, KrausChannel.toFiniteChannel_apply,
    KrausChannel.toFiniteChannel_apply]
  exact (kraus_comp before.op after.op rho).symm

/-- A bundled Kraus channel carries the finite complete-positivity theorem. -/
theorem KrausChannel.completelyPositive {n : Nat} {ι : Type} [Fintype ι]
    (C : KrausChannel n ι) : CompletelyPositiveKraus C.op :=
  applyKraus_completelyPositive C.op

end LeanPhy.QuantumInfo
