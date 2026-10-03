import LeanPhy.Mathematics.ContinuousAnalysis
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Tactic

namespace LeanPhy.Mathematics

open MeasureTheory
open scoped BigOperators

universe u v

/-!
# Continuous path-integral certificates

This module records the part of a continuum path-integral calculation that is
well-defined in ordinary mathlib measure theory: an integrable complex weight,
a non-zero partition function, and integrable observable insertions.  It does
not assert that a measure on an infinite-dimensional path space exists, nor
does it infer Osterwalder--Schrader positivity or a renormalisation limit.
Those facts remain explicit hypotheses or research obligations.
-/

structure ContinuousPathIntegral (α : Type u) [MeasurableSpace α]
    (μ : Measure α) where
  weight : α → ℂ
  weight_integrable : Integrable weight μ
  partition : ℂ
  partition_eq : (∫ x, weight x ∂μ) = partition
  partition_ne_zero : partition ≠ 0

namespace ContinuousPathIntegral

variable {α : Type u} [MeasurableSpace α] {μ : Measure α}

noncomputable def insertion (P : ContinuousPathIntegral α μ) (O : α → ℂ) : ℂ :=
  ∫ x, P.weight x * O x ∂μ

noncomputable def expectation (P : ContinuousPathIntegral α μ) (O : α → ℂ) : ℂ :=
  P.insertion O / P.partition

structure ObservableCertificate (P : ContinuousPathIntegral α μ) (O : α → ℂ)
    (value : ℂ) : Prop where
  integrable : Integrable (fun x => P.weight x * O x) μ
  integral_eq : P.insertion O = value

theorem expectation_eq_of_certificate (P : ContinuousPathIntegral α μ)
    (O : α → ℂ) (value : ℂ) (C : ObservableCertificate P O value) :
    P.expectation O = value / P.partition := by
  unfold expectation
  rw [C.integral_eq]

theorem expectation_const (P : ContinuousPathIntegral α μ) (c : ℂ) :
    P.expectation (fun _ => c) = c := by
  unfold expectation insertion
  have hi : (∫ x, P.weight x * c ∂μ) = (∫ x, P.weight x ∂μ) * c := by
    calc
      (∫ x, P.weight x * c ∂μ) = ∫ x, c • P.weight x ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp [smul_eq_mul, mul_comm]
      _ = c • ∫ x, P.weight x ∂μ := integral_smul c P.weight
      _ = (∫ x, P.weight x ∂μ) * c := by simp [smul_eq_mul, mul_comm]
  rw [hi, P.partition_eq]
  field_simp [P.partition_ne_zero]

theorem expectation_add (P : ContinuousPathIntegral α μ)
    (O Q : α → ℂ)
    (hO : Integrable (fun x => P.weight x * O x) μ)
    (hQ : Integrable (fun x => P.weight x * Q x) μ) :
    P.expectation (fun x => O x + Q x) = P.expectation O + P.expectation Q := by
  unfold expectation insertion
  have hadd : (∫ x, P.weight x * (O x + Q x) ∂μ) =
      (∫ x, P.weight x * O x ∂μ) + (∫ x, P.weight x * Q x ∂μ) := by
    calc
      (∫ x, P.weight x * (O x + Q x) ∂μ) =
          ∫ x, (P.weight x * O x) + (P.weight x * Q x) ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
      _ = _ := integral_add hO hQ
  rw [hadd]
  ring

theorem expectation_smul (P : ContinuousPathIntegral α μ)
    (c : ℂ) (O : α → ℂ) (hO : Integrable (fun x => P.weight x * O x) μ) :
    P.expectation (fun x => c * O x) = c * P.expectation O := by
  unfold expectation insertion
  have hmul : (∫ x, P.weight x * (c * O x) ∂μ) =
      c • (∫ x, P.weight x * O x ∂μ) := by
    calc
      (∫ x, P.weight x * (c * O x) ∂μ) =
          ∫ x, c • (P.weight x * O x) ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with x
            simp [smul_eq_mul]
            ring
      _ = c • ∫ x, P.weight x * O x ∂μ := integral_smul c _
  rw [hmul]
  simp [smul_eq_mul]
  ring

theorem integral_comp_measurePreserving {β : Type v} [MeasurableSpace β]
    {ν : Measure β} (e : α ≃ᵐ β) (h : MeasurePreserving e μ ν) (g : β → ℂ) :
    (∫ x, g (e x) ∂μ) = ∫ y, g y ∂ν := by
  exact h.integral_comp e.measurableEmbedding g

end ContinuousPathIntegral
end LeanPhy.Mathematics
