import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Actual noncommuting evolution and perturbation derivatives

The finite-time Duhamel identity is derived from exponential time derivatives
and the fundamental theorem of calculus. It is then used to differentiate a
generator perturbation without assuming that the generator and perturbation
commute. This supplies physical evolution/response with analytic evidence,
rather than requiring the integral identity as a certificate input.
-/

namespace LeanPhy.Mathematics.Duhamel

open NormedSpace MeasureTheory Filter
open scoped Topology Interval

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

noncomputable def flow (G : A) (t : ℝ) : A := exp (t • G)

theorem flow_derivative (G : A) (t : ℝ) :
    HasDerivAt (flow G) (flow G t * G) t :=
  hasDerivAt_exp_smul_const G t

theorem flow_derivative_left (G : A) (t : ℝ) :
    HasDerivAt (flow G) (G * flow G t) t :=
  hasDerivAt_exp_smul_const' G t

theorem flow_continuous (G : A) : Continuous (flow G) :=
  continuous_iff_continuousAt.mpr (fun t => (flow_derivative G t).continuousAt)

@[simp] theorem flow_zero (G : A) : flow G 0 = 1 := by simp [flow]

theorem flow_add (G : A) (t s : ℝ) : flow G (t + s) = flow G t * flow G s := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  unfold flow
  rw [add_smul]
  exact exp_add_of_commute (((Commute.refl G).smul_left t).smul_right s)

@[simp] theorem flow_mul_neg (G : A) (t : ℝ) : flow G t * flow G (-t) = 1 := by
  rw [← flow_add]; simp

@[simp] theorem flow_neg_mul (G : A) (t : ℝ) : flow G (-t) * flow G t = 1 := by
  rw [← flow_add]; simp

theorem integrand_continuous (G D B : A) (t : ℝ) :
    Continuous (fun s => flow G (t - s) * D * flow B s) := by
  exact (((flow_continuous G).comp (continuous_const.sub continuous_id)).mul
    continuous_const).mul (flow_continuous B)

/-- Exact finite-time response, retaining the order of both propagators. -/
theorem difference (G B : A) (t : ℝ) :
    flow B t - flow G t = ∫ s in (0 : ℝ)..t, flow G (t - s) * (B - G) * flow B s := by
  have hd (s : ℝ) : HasDerivAt (fun s => flow G (t - s) * flow B s)
      (flow G (t - s) * (B - G) * flow B s) s := by
    have h := ((flow_derivative G (t - s)).scomp s
      ((hasDerivAt_const s t).sub (hasDerivAt_id s))).mul (flow_derivative_left B s)
    convert h using 1
    all_goals first | rfl |
      (simp only [Function.comp_apply, zero_sub, one_smul, neg_smul]; noncomm_ring)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((integrand_continuous G (B - G) B t).intervalIntegrable 0 t)
  simpa using he.symm

/-- Exact response divided by its scalar amplitude, before taking a limit. -/
theorem perturbation_difference (G V : A) (t ε : ℝ) :
    flow (G + ε • V) t - flow G t =
      ε • ∫ s in (0 : ℝ)..t, flow G (t - s) * V * flow (G + ε • V) s := by
  rw [difference]
  simp only [add_sub_cancel_left, mul_smul_comm, smul_mul_assoc,
    intervalIntegral.integral_smul]

/-- First variation of the actual exponential, as an ordered insertion integral. -/
noncomputable def insertion (G V : A) (t : ℝ) : A :=
  ∫ s in (0 : ℝ)..t, flow G (t - s) * V * flow G s

theorem hasDerivAt_perturbation (G V : A) (t : ℝ) :
    HasDerivAt (fun ε : ℝ => flow (G + ε • V) t) (insertion G V t) 0 := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hc : Continuous (fun ε : ℝ =>
      ∫ s in (0 : ℝ)..t, flow G (t - s) * V * flow (G + ε • V) s) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    change Continuous (fun p : ℝ × ℝ => flow G (t - p.2) * V * exp (p.2 • (G + p.1 • V)))
    exact (((flow_continuous G).comp (continuous_const.sub continuous_snd)).mul
      continuous_const).mul (exp_continuous.comp (continuous_snd.smul
        (continuous_const.add (continuous_fst.smul continuous_const))))
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hlim := (hc.continuousAt (x := 0)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  have he : (fun ε : ℝ => ε⁻¹ •
      (flow (G + (0 + ε) • V) t - flow (G + (0 : ℝ) • V) t)) =ᶠ[𝓝[≠] 0]
      (fun ε : ℝ => ∫ s in (0 : ℝ)..t, flow G (t - s) * V * flow (G + ε • V) s) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hn : ε ≠ 0 := hε
    simp only [zero_add, zero_smul, add_zero, perturbation_difference, smul_smul,
      inv_mul_cancel₀ hn, one_smul]
  exact Filter.Tendsto.congr' he.symm (by simpa [insertion] using hlim)

/-- The familiar scalar-looking rule requires a commuting perturbation. -/
theorem insertion_of_commute (G V : A) (t : ℝ) (h : Commute G V) :
    insertion G V t = t • (flow G t * V) := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have he (s : ℝ) : flow G (t - s) * V * flow G s = flow G t * V := by
    have hc : Commute V (flow G s) := (h.symm.smul_right s).exp_right
    rw [mul_assoc, hc.eq, ← mul_assoc, ← flow_add]
    congr 2
    ring
  simp only [insertion, he, intervalIntegral.integral_const, sub_zero]

/-- Conjugation by the actual exponential group, before imposing unitarity. -/
noncomputable def conjugate (G O : A) (t : ℝ) : A :=
  flow G t * O * flow G (-t)

@[simp] theorem conjugate_zero (G O : A) : conjugate G O 0 = O := by
  simp [conjugate]

theorem conjugate_derivative (G O : A) (t : ℝ) :
    HasDerivAt (conjugate G O) (G * conjugate G O t - conjugate G O t * G) t := by
  have hn := (flow_derivative G (-t)).scomp t (hasDerivAt_id t).neg
  have h := ((flow_derivative_left G t).mul_const O).mul hn
  convert h using 1
  all_goals first | rfl |
    (simp only [conjugate, Function.comp_apply, neg_smul, one_smul]; noncomm_ring)

noncomputable def conjugateVariation (G V O : A) (t : ℝ) : A :=
  insertion G V t * O * flow G (-t) + flow G t * O * insertion G V (-t)

/-- Product differentiation retains the variations of both propagators. -/
theorem hasDerivAt_conjugate_perturbation (G V O : A) (t : ℝ) :
    HasDerivAt (fun ε : ℝ => conjugate (G + ε • V) O t)
      (conjugateVariation G V O t) 0 := by
  simpa [conjugate, conjugateVariation, Pi.mul_apply] using
    ((hasDerivAt_perturbation G V t).mul_const O).fun_mul
      (hasDerivAt_perturbation G V (-t))

theorem insertion_inverse (G V : A) (t : ℝ) :
    insertion G V (-t) = -(flow G (-t) * insertion G V t * flow G (-t)) := by
  have h := (hasDerivAt_perturbation G V t).fun_mul (hasDerivAt_perturbation G V (-t))
  simp only [flow_mul_neg, zero_smul, add_zero] at h
  have hz := h.unique (hasDerivAt_const (0 : ℝ) (1 : A))
  have hh := congrArg (fun z => flow G (-t) * z) hz
  simp only [mul_add, ← mul_assoc, flow_neg_mul, one_mul, mul_zero] at hh
  exact eq_neg_of_add_eq_zero_right hh

theorem conjugateVariation_eq_commutator (G V O : A) (t : ℝ) :
    conjugateVariation G V O t =
      (insertion G V t * flow G (-t)) * conjugate G O t -
        conjugate G O t * (insertion G V t * flow G (-t)) := by
  have hc : (insertion G V t * flow G (-t)) * conjugate G O t =
      insertion G V t * O * flow G (-t) := by
    unfold conjugate
    calc
      _ = insertion G V t * (flow G (-t) * flow G t) * O * flow G (-t) := by
        noncomm_ring
      _ = _ := by rw [flow_neg_mul]; simp
  rw [hc, conjugateVariation, insertion_inverse]
  unfold conjugate
  noncomm_ring

theorem insertion_right_inverse (G V : A) (t : ℝ) :
    insertion G V t * flow G (-t) = ∫ s in (0 : ℝ)..t, conjugate G V s := by
  let L := (ContinuousLinearMap.mul ℝ A).flip (flow G (-t))
  have h := L.intervalIntegral_comp_comm
    ((integrand_continuous G V G t).intervalIntegrable (μ := volume) 0 t)
  have he (s : ℝ) : L (flow G (t - s) * V * flow G s) = conjugate G V (t - s) := by
    change (flow G (t - s) * V * flow G s) * flow G (-t) = _
    rw [mul_assoc, ← flow_add]
    unfold conjugate
    congr 2
    ring
  simp only [he] at h
  change (∫ s in (0 : ℝ)..t, conjugate G V (t - s)) = insertion G V t * flow G (-t) at h
  rw [intervalIntegral.integral_comp_sub_left] at h
  simpa using h.symm

/-- Ordered insertions yield an integrated commutator, without a stationarity
or commuting-perturbation premise. The integral is oriented for negative time. -/
theorem conjugateVariation_eq_integral (G V O : A) (t : ℝ) :
    conjugateVariation G V O t = ∫ s in (0 : ℝ)..t,
      conjugate G V s * conjugate G O t - conjugate G O t * conjugate G V s := by
  let L := (ContinuousLinearMap.mul ℝ A).flip (conjugate G O t) -
    ContinuousLinearMap.mul ℝ A (conjugate G O t)
  have hc : Continuous (conjugate G V) :=
    continuous_iff_continuousAt.mpr (fun s => (conjugate_derivative G V s).continuousAt)
  have h := L.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 t)
  rw [conjugateVariation_eq_commutator, insertion_right_inverse]
  exact h.symm

end LeanPhy.Mathematics.Duhamel
