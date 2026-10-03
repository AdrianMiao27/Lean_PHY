import LeanPhy.Mathematics.FiniteDivergence
import Mathlib.Tactic

/-!
# Approximate finite conservation laws

Numerical, truncated and finite-volume models often satisfy a continuity
equation only up to a certified local residual.  This module turns those
pointwise residual bounds into a global source bound.  The statement is
purely a finite real-sum estimate: it does not infer convergence, stability,
positivity, a continuum boundary condition or a physical conservation law.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

namespace FiniteDivergence

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- A local continuity equation with an explicit nonnegative error radius at
each vertex. -/
structure ConservationError
    (tail head : E → V) (current : E → ℝ) (source : V → ℝ)
    (radius : V → ℝ) : Prop where
  radius_nonneg : ∀ v, 0 ≤ radius v
  residual_bound : ∀ v,
    |residual tail head current source v| ≤ radius v

theorem ConservationError.total_source_abs_le
    {tail head : E → V} {current : E → ℝ} {source radius : V → ℝ}
    (h : ConservationError tail head current source radius) :
    |∑ v, source v| ≤ ∑ v, radius v := by
  have hdiv : ∑ v, divergence tail head current v = 0 :=
    total_divergence_zero tail head current
  have hsum : (∑ v, source v) = -∑ v, residual tail head current source v := by
    unfold residual
    rw [Finset.sum_sub_distrib, hdiv]
    simp
  rw [hsum, abs_neg]
  calc
    |∑ v, residual tail head current source v| ≤
        ∑ v, |residual tail head current source v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v, radius v := by
      exact Finset.sum_le_sum (fun v hv => h.residual_bound v)

/-- Exact local conservation is a zero-radius approximate certificate. -/
theorem ConservationError.of_zero
    {tail head : E → V} {current : E → ℝ} {source : V → ℝ}
    (hlocal : ∀ v, residual tail head current source v = 0) :
    ConservationError tail head current source (fun _ => 0) := by
  refine ⟨fun _ => le_rfl, fun v => ?_⟩
  simp [hlocal v]

/-- A uniform local radius gives a cardinality-scaled global source bound. -/
theorem ConservationError.total_source_abs_le_uniform
    {tail head : E → V} {current : E → ℝ} {source : V → ℝ}
    {ε : ℝ}
    (h : ConservationError tail head current source (fun _ => ε)) :
    |∑ v, source v| ≤ (Fintype.card V : ℝ) * ε := by
  calc
    |∑ v, source v| ≤ ∑ v, (fun _ : V => ε) v :=
      h.total_source_abs_le
    _ = (Fintype.card V : ℝ) * ε := by
      simp [Finset.sum_const, nsmul_eq_mul]

end FiniteDivergence

end LeanPhy.Mathematics

namespace LeanPhy

namespace Mathematics

abbrev ApproximateConservation {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] := FiniteDivergence.ConservationError (V := V) (E := E)

end Mathematics

namespace GaugeTheory

abbrev LatticeConservationError {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] := Mathematics.FiniteDivergence.ConservationError (V := V) (E := E)

end GaugeTheory

namespace Condensed

abbrev HoppingConservationError {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] := Mathematics.FiniteDivergence.ConservationError (V := V) (E := E)

end Condensed

namespace StatMech

abbrev ProbabilityFlowError {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] := Mathematics.FiniteDivergence.ConservationError (V := V) (E := E)

end StatMech

namespace QuantumInfo

abbrev MeasurementFlowError {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] := Mathematics.FiniteDivergence.ConservationError (V := V) (E := E)

end QuantumInfo

end LeanPhy
