import LeanPhy.Mathematics.FiniteWeightedResponse
import LeanPhy.Mathematics.FiniteCorrelator
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

/-!
# Analytic source derivatives of finite complex path sums

The source convention is `w_i(z) = w_i exp(z A_i)`, without an implicit factor
of `i`. For oscillatory real-time conventions that factor belongs in the
insertion `A`. At zero source the original nonzero-partition proof is reused;
at other complex sources a new nonzero-partition proof is required.

The derivative of the actual normalized source expectation is the existing
connected correlator of the tilted measure. This is not a truncated source
polynomial and does not assume positivity, a logarithm branch, a continuum
measure, time ordering, or Lorentzian response/causality.
-/

namespace LeanPhy.Mathematics.FinitePathIntegral

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def sourceWeight (P : FinitePathIntegral ι) (A : ι → ℂ)
    (z : ℂ) (i : ι) : ℂ := P.weight i * Complex.exp (z * A i)

noncomputable def sourcePartition (P : FinitePathIntegral ι) (A : ι → ℂ) (z : ℂ) : ℂ :=
  FiniteWeighted.partition (P.sourceWeight A z)

/-- Raw source expectation; derivative theorems require a nonzero partition
at the source under study. It has no physical normalization meaning at a zero. -/
noncomputable def sourceExpectation (P : FinitePathIntegral ι) (A O : ι → ℂ) (z : ℂ) : ℂ :=
  FiniteWeighted.expectation (P.sourceWeight A z) O

noncomputable def withSource (P : FinitePathIntegral ι) (A : ι → ℂ) (z : ℂ)
    (hZ : P.sourcePartition A z ≠ 0) : FinitePathIntegral ι where
  weight := P.sourceWeight A z
  partition_ne_zero := hZ

@[simp] theorem sourceWeight_zero (P : FinitePathIntegral ι) (A : ι → ℂ) :
    P.sourceWeight A 0 = P.weight := by
  funext i
  simp [sourceWeight]

@[simp] theorem sourcePartition_zero (P : FinitePathIntegral ι) (A : ι → ℂ) :
    P.sourcePartition A 0 = P.partition := by
  simp only [sourcePartition, sourceWeight_zero, FiniteWeighted.partition, partition]

@[simp] theorem sourceExpectation_zero (P : FinitePathIntegral ι) (A O : ι → ℂ) :
    P.sourceExpectation A O 0 = P.expectation O := by
  simp only [sourceExpectation, sourceWeight_zero, FiniteWeighted.expectation,
    FiniteWeighted.insertion, FiniteWeighted.partition, expectation, insertion, partition]

theorem withSource_expectation (P : FinitePathIntegral ι) (A O : ι → ℂ) (z : ℂ)
    (hZ : P.sourcePartition A z ≠ 0) :
    (P.withSource A z hZ).expectation O = P.sourceExpectation A O z := rfl

theorem hasDerivAt_sourceWeight (P : FinitePathIntegral ι) (A : ι → ℂ) (z : ℂ) (i : ι) :
    HasDerivAt (fun s => P.sourceWeight A s i) (P.sourceWeight A z i * A i) z := by
  have h := (((hasDerivAt_id z).mul_const (A i)).cexp).const_mul (P.weight i)
  simpa [sourceWeight, mul_assoc] using h

theorem hasDerivAt_sourcePartition (P : FinitePathIntegral ι) (A : ι → ℂ) (z : ℂ) :
    HasDerivAt (P.sourcePartition A)
      (FiniteWeighted.insertion (P.sourceWeight A z) A) z :=
  HasDerivAt.fun_sum (fun i _ => P.hasDerivAt_sourceWeight A z i)

/-- Away from partition zeros, source derivatives are connected insertions
in the tilted measure; no positivity is needed for this identity. -/
theorem hasDerivAt_sourceExpectation (P : FinitePathIntegral ι) (A O : ι → ℂ) (z : ℂ)
    (hZ : P.sourcePartition A z ≠ 0) :
    HasDerivAt (P.sourceExpectation A O)
      ((P.withSource A z hZ).connectedCorrelator O A) z := by
  exact FiniteWeighted.hasDerivAt_expectation_fixed (P.sourceWeight A) O A z
    (P.hasDerivAt_sourceWeight A z) hZ

/-- The original measure already supplies the required zero-source condition. -/
theorem hasDerivAt_sourceExpectation_zero (P : FinitePathIntegral ι) (A O : ι → ℂ) :
    HasDerivAt (P.sourceExpectation A O) (P.connectedCorrelator O A) 0 := by
  have h := FiniteWeighted.hasDerivAt_expectation_fixed (P.sourceWeight A) O A 0
    (P.hasDerivAt_sourceWeight A 0)
    (by simpa only [sourceWeight_zero, FiniteWeighted.partition, partition] using P.partition_ne_zero_cert)
  convert! h using 1
  simp only [sourceWeight_zero]
  rfl

/-- Contact terms are retained when the observable also depends on the source. -/
theorem hasDerivAt_sourceExpectation_moving (P : FinitePathIntegral ι) (A : ι → ℂ)
    (O : ℂ → ι → ℂ) (O' : ι → ℂ) (z : ℂ)
    (hZ : P.sourcePartition A z ≠ 0)
    (hO : ∀ i, HasDerivAt (fun s => O s i) (O' i) z) :
    HasDerivAt (fun s => P.sourceExpectation A (O s) s)
      ((P.withSource A z hZ).expectation O' +
        (P.withSource A z hZ).connectedCorrelator (O z) A) z :=
  FiniteWeighted.hasDerivAt_expectation_score (P.sourceWeight A) O A O' z
    (P.hasDerivAt_sourceWeight A z) hO hZ

/-- Sources compose by addition in this commuting finite insertion algebra. -/
theorem sourceWeight_add (P : FinitePathIntegral ι) (A : ι → ℂ) (z s : ℂ) (i : ι) :
    P.sourceWeight A (z + s) i = P.sourceWeight A z i * Complex.exp (s * A i) := by
  simp [sourceWeight, add_mul, Complex.exp_add, mul_assoc]

end LeanPhy.Mathematics.FinitePathIntegral
