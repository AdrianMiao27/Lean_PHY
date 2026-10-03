import LeanPhy.QuantumInfo.POVM
import LeanPhy.QuantumInfo.Channel
import Mathlib.Tactic

/-!
# Finite-dimensional measurement instruments

`POVM` records the effects of a measurement.  This file adds the operational
layer used in calculations: one Kraus operator is attached to each outcome.
The one-Kraus-per-outcome interface is intentional.  A general instrument is
obtained by adding a finite internal Kraus index, and can then be reduced to
this API by coarse graining its outcomes.

Theorems below establish the finite-dimensional Born rule and conditional
states without adding physical axioms: positivity is a matrix theorem,
probability is the trace of the unnormalised branch, and normalization uses
the explicit completeness hypothesis.
-/

namespace LeanPhy.QuantumInfo

open LeanPhy.Quantum
open scoped BigOperators Matrix ComplexOrder MatrixOrder

/-- A one-Kraus-per-outcome finite measurement instrument. -/
structure KrausInstrument (n : Nat) (ι : Type) [Fintype ι] where
  op : ι → Operator n
  complete : (∑ i, Matrix.conjTranspose (op i) * op i) = 1

/-- The POVM effect associated to one outcome of an instrument. -/
noncomputable def effect {n : Nat} {ι : Type} [Fintype ι]
    (I : KrausInstrument n ι) (i : ι) : Operator n :=
  Matrix.conjTranspose (I.op i) * I.op i

theorem effect_positive {n : Nat} {ι : Type} [Fintype ι]
    (I : KrausInstrument n ι) (i : ι) : (effect I i).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self (I.op i)

/-- Forgetting the post-measurement operation gives the induced POVM. -/
noncomputable def toPOVM {n : Nat} {ι : Type} [Fintype ι]
    (I : KrausInstrument n ι) : POVM n ι where
  effect := effect I
  positive := effect_positive I
  complete := I.complete

theorem toPOVM_effect {n : Nat} {ι : Type} [Fintype ι]
    (I : KrausInstrument n ι) (i : ι) :
    (toPOVM I).effect i = effect I i := rfl

/-- The unnormalised state in outcome branch `i`. -/
noncomputable def outcomeState {n : Nat} {ι : Type} [Fintype ι]
    (I : KrausInstrument n ι) (rho : State n) (i : ι) : State n :=
  I.op i * rho * Matrix.conjTranspose (I.op i)

theorem outcomeState_positive {n : Nat} {ι : Type} [Fintype ι]
    (I : KrausInstrument n ι) (rho : State n) (hrho : rho.PosSemidef) (i : ι) :
    (outcomeState I rho i).PosSemidef := by
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hrho (I.op i)

/-- The trace of a branch is the Born weight of its induced POVM effect. -/
theorem outcomeState_trace {n : Nat} {ι : Type} [Fintype ι]
    (I : KrausInstrument n ι) (rho : State n) (i : ι) :
    Matrix.trace (outcomeState I rho i) = weight (toPOVM I) rho i := by
  change Matrix.trace (I.op i * rho * Matrix.conjTranspose (I.op i)) =
    Matrix.trace (rho * effect I i)
  unfold effect
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]

theorem outcomeState_trace_nonneg {n : Nat} {ι : Type} [Fintype ι]
    (I : KrausInstrument n ι) (rho : State n) (hrho : IsDensity rho) (i : ι) :
    0 ≤ Matrix.trace (outcomeState I rho i) := by
  rw [outcomeState_trace]
  exact trace_mul_posSemidef_nonneg rho (effect I i) hrho.2.1 (effect_positive I i)

/-- The traces of all unnormalised outcome branches sum to one. -/
theorem outcomeState_trace_sum_is_one {n : Nat} {ι : Type} [Fintype ι]
    (I : KrausInstrument n ι) (rho : State n) (hrho : IsDensity rho) :
    (∑ i, Matrix.trace (outcomeState I rho i)) = 1 := by
  rw [Finset.sum_congr rfl (fun i _ ↦ outcomeState_trace I rho i)]
  exact weight_sum_is_one (toPOVM I) rho hrho

/-- The conditional post-measurement state, for a branch of positive probability. -/
noncomputable def conditionalState {n : Nat} {ι : Type} [Fintype ι]
    (I : KrausInstrument n ι) (rho : State n) (i : ι) : State n :=
  (probability (toPOVM I) rho i)⁻¹ • outcomeState I rho i

theorem conditionalState_isDensity {n : Nat} {ι : Type} [Fintype ι]
    (I : KrausInstrument n ι) (rho : State n) (hrho : IsDensity rho) (i : ι)
    (hi : 0 < probability (toPOVM I) rho i) :
    IsDensity (conditionalState I rho i) := by
  have hbranch : (outcomeState I rho i).PosSemidef :=
    outcomeState_positive I rho hrho.2.1 i
  have hscale : 0 ≤ (probability (toPOVM I) rho i)⁻¹ :=
    inv_nonneg.mpr hi.le
  refine ⟨?_, Matrix.PosSemidef.smul hbranch hscale, ?_⟩
  · exact (Matrix.PosSemidef.smul hbranch hscale).isHermitian
  change Matrix.trace (conditionalState I rho i) = 1
  rw [conditionalState, Matrix.trace_smul]
  rw [outcomeState_trace, weight_eq_ofReal_probability (toPOVM I) rho hrho i]
  rw [Algebra.smul_def]
  change Complex.ofReal ((probability (toPOVM I) rho i)⁻¹) *
      Complex.ofReal (probability (toPOVM I) rho i) = (1 : ℂ)
  rw [← Complex.ofReal_mul]
  rw [inv_mul_cancel₀ (ne_of_gt hi)]
  simp

/-! ## General finite instruments with an internal Kraus index -/

/-- A general finite measurement instrument.  Outcome `i` may collect a finite
family of Kraus operators indexed by `κ`; the completeness relation includes
both indices.  The one-Kraus interface above is the special case where `κ` is
subsingleton.
-/
structure MultiKrausInstrument (n : Nat) (ι κ : Type)
    [Fintype ι] [Fintype κ] where
  op : ι → κ → Operator n
  complete : (∑ i, ∑ k, Matrix.conjTranspose (op i k) * op i k) = 1

/-- The POVM effect obtained by coarse-graining all Kraus operators belonging
to one outcome. -/
noncomputable def multiEffect {n : Nat} {ι κ : Type} [Fintype ι] [Fintype κ]
    (I : MultiKrausInstrument n ι κ) (i : ι) : Operator n :=
  ∑ k, Matrix.conjTranspose (I.op i k) * I.op i k

/-- The POVM induced by a multi-Kraus instrument. -/
noncomputable def multiToPOVM {n : Nat} {ι κ : Type} [Fintype ι] [Fintype κ]
    (I : MultiKrausInstrument n ι κ) : POVM n ι where
  effect := multiEffect I
  positive := by
    intro i
    apply kraus_sum_posSemidef
    intro k
    exact Matrix.posSemidef_conjTranspose_mul_self (I.op i k)
  complete := by
    exact I.complete

/-- The unnormalised state of a coarse-grained outcome. -/
noncomputable def multiOutcomeState {n : Nat} {ι κ : Type}
    [Fintype ι] [Fintype κ] (I : MultiKrausInstrument n ι κ)
    (rho : State n) (i : ι) : State n :=
  ∑ k, I.op i k * rho * Matrix.conjTranspose (I.op i k)

theorem multiOutcomeState_positive {n : Nat} {ι κ : Type}
    [Fintype ι] [Fintype κ] (I : MultiKrausInstrument n ι κ)
    (rho : State n) (hrho : IsDensity rho) (i : ι) :
    (multiOutcomeState I rho i).PosSemidef := by
  unfold multiOutcomeState
  apply kraus_sum_posSemidef
  intro k
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hrho.2.1 (I.op i k)

theorem multiOutcomeState_trace {n : Nat} {ι κ : Type}
    [Fintype ι] [Fintype κ] (I : MultiKrausInstrument n ι κ)
    (rho : State n) (i : ι) :
    Matrix.trace (multiOutcomeState I rho i) = weight (multiToPOVM I) rho i := by
  unfold multiOutcomeState weight multiToPOVM multiEffect
  rw [Matrix.trace_sum]
  calc
    (∑ k, Matrix.trace (I.op i k * rho * Matrix.conjTranspose (I.op i k))) =
        ∑ k, Matrix.trace (rho * (Matrix.conjTranspose (I.op i k) * I.op i k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
    _ = Matrix.trace (rho * (∑ k, Matrix.conjTranspose (I.op i k) * I.op i k)) := by
      rw [Finset.mul_sum, Matrix.trace_sum]

theorem multiOutcomeState_trace_sum_is_one {n : Nat} {ι κ : Type}
    [Fintype ι] [Fintype κ] (I : MultiKrausInstrument n ι κ)
    (rho : State n) (hrho : IsDensity rho) :
    (∑ i, Matrix.trace (multiOutcomeState I rho i)) = 1 := by
  rw [Finset.sum_congr rfl (fun i _ => multiOutcomeState_trace I rho i)]
  exact weight_sum_is_one (multiToPOVM I) rho hrho

/-- The normalized state for a coarse-grained outcome of a multi-Kraus
instrument, defined when its Born probability is positive. -/
noncomputable def multiConditionalState {n : Nat} {ι κ : Type}
    [Fintype ι] [Fintype κ] (I : MultiKrausInstrument n ι κ)
    (rho : State n) (i : ι) : State n :=
  (probability (multiToPOVM I) rho i)⁻¹ • multiOutcomeState I rho i

theorem multiConditionalState_isDensity {n : Nat} {ι κ : Type}
    [Fintype ι] [Fintype κ] (I : MultiKrausInstrument n ι κ)
    (rho : State n) (hrho : IsDensity rho) (i : ι)
    (hi : 0 < probability (multiToPOVM I) rho i) :
    IsDensity (multiConditionalState I rho i) := by
  have hbranch : (multiOutcomeState I rho i).PosSemidef :=
    multiOutcomeState_positive I rho hrho i
  have hscale : 0 ≤ (probability (multiToPOVM I) rho i)⁻¹ :=
    inv_nonneg.mpr hi.le
  refine ⟨?_, Matrix.PosSemidef.smul hbranch hscale, ?_⟩
  · exact (Matrix.PosSemidef.smul hbranch hscale).isHermitian
  · change Matrix.trace (multiConditionalState I rho i) = 1
    rw [multiConditionalState, Matrix.trace_smul]
    rw [multiOutcomeState_trace]
    rw [weight_eq_ofReal_probability (multiToPOVM I) rho hrho i]
    rw [Algebra.smul_def]
    change Complex.ofReal ((probability (multiToPOVM I) rho i)⁻¹) *
        Complex.ofReal (probability (multiToPOVM I) rho i) = (1 : ℂ)
    rw [← Complex.ofReal_mul]
    rw [inv_mul_cancel₀ (ne_of_gt hi)]
    simp

end LeanPhy.QuantumInfo
