import LeanPhy.Quantum.TimeDependentEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Linear response from actual nonautonomous evolution

An amplitude family supplies solutions of `Uε' = -i (H(t) + ε V(t)) Uε`,
their common initial value and joint continuity in amplitude and time. No
amplitude derivative or response integral is assumed. The exact comparison
identity and continuity of finite integrals prove the derivative at zero.
`H` and `V` can both depend on time, with no stationarity or commuting premise.

The switched readout has zero response before its preparation time. The
unswitched integral is oriented and need not vanish for earlier times.
Initial-state and probe derivatives are retained separately.
-/

namespace LeanPhy.Quantum.TimeDependent

open LeanPhy.Quantum.Dynamics LeanPhy.Mathematics MeasureTheory Filter
open scoped Matrix Matrix.Norms.Operator Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure DrivenFamily (H V : ℝ → Matrix ι ι ℂ) (a : ℝ) where
  evolution : ∀ ε : ℝ, Evolution (fun t => H t + ε • V t) a
  continuous : Continuous (fun p : ℝ × ℝ => (evolution p.1).op p.2)
  drive_continuous : Continuous V

variable {H V : ℝ → Matrix ι ι ℂ} {a : ℝ}

noncomputable def DrivenFamily.base (F : DrivenFamily H V a) : Evolution H a where
  op := (F.evolution 0).op
  initial := (F.evolution 0).initial
  hermitian t := by simpa only [zero_smul, add_zero] using (F.evolution 0).hermitian t
  equation t := by simpa only [zero_smul, add_zero] using (F.evolution 0).equation t

noncomputable def DrivenFamily.relative (F : DrivenFamily H V a) (ε t : ℝ) :
    Matrix ι ι ℂ := ((F.evolution 0).op t)ᴴ * (F.evolution ε).op t

@[simp] theorem DrivenFamily.relative_zero (F : DrivenFamily H V a) (t : ℝ) :
    F.relative 0 t = 1 := (F.evolution 0).unitary t

theorem DrivenFamily.relative_unitary (F : DrivenFamily H V a) (ε t : ℝ) :
    (F.relative ε t)ᴴ * F.relative ε t = 1 := by
  unfold DrivenFamily.relative
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    _ = ((F.evolution ε).op t)ᴴ *
        ((F.evolution 0).op t * ((F.evolution 0).op t)ᴴ) * (F.evolution ε).op t := by
      noncomm_ring
    _ = 1 := by rw [(F.evolution 0).right_unitary]; simp [(F.evolution ε).unitary]

/-- Exact amplitude difference; both time order and the perturbed curve remain. -/
theorem DrivenFamily.relative_difference (F : DrivenFamily H V a) (ε t : ℝ) :
    F.relative ε t - 1 = ε • (-Complex.I • ∫ s in a..t,
      ((F.evolution 0).op s)ᴴ * V s * (F.evolution ε).op s) := by
  have h := (F.evolution 0).comparison (F.evolution ε)
    (by simpa only [zero_smul, add_zero, add_sub_cancel_left] using!
      (continuous_const (y := ε)).smul F.drive_continuous) t
  simpa only [DrivenFamily.relative, zero_smul, add_zero, add_sub_cancel_left,
    Matrix.mul_smul, Matrix.smul_mul, smul_comm (-Complex.I),
    intervalIntegral.integral_smul] using h

noncomputable def DrivenFamily.insertion (F : DrivenFamily H V a) (t : ℝ) :
    Matrix ι ι ℂ := ∫ s in a..t, (F.evolution 0).observable (V s) s

theorem DrivenFamily.relative_derivative (F : DrivenFamily H V a) (t : ℝ) :
    HasDerivAt (fun ε => F.relative ε t) (-Complex.I • F.insertion t) 0 := by
  have hc : Continuous (fun ε : ℝ => -Complex.I • ∫ s in a..t,
      ((F.evolution 0).op s)ᴴ * V s * (F.evolution ε).op s) := by
    have hi : Continuous (fun ε : ℝ => ∫ s in a..t,
        ((F.evolution 0).op s)ᴴ * V s * (F.evolution ε).op s) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      exact (((F.evolution 0).continuous.matrix_conjTranspose.comp continuous_snd).mul
        (F.drive_continuous.comp continuous_snd)).mul F.continuous
    exact (continuous_const (y := -Complex.I)).smul hi
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hlim := (hc.continuousAt (x := 0)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  have he : (fun ε : ℝ => ε⁻¹ • (F.relative (0 + ε) t - F.relative 0 t))
      =ᶠ[𝓝[≠] 0] (fun ε : ℝ => -Complex.I • ∫ s in a..t,
        ((F.evolution 0).op s)ᴴ * V s * (F.evolution ε).op s) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hn : ε ≠ 0 := hε
    simp only [zero_add, F.relative_zero, F.relative_difference, smul_smul,
      inv_mul_cancel₀ hn, one_smul]
  exact Filter.Tendsto.congr' he.symm
    (by simpa only [DrivenFamily.insertion, Evolution.observable] using hlim)

theorem DrivenFamily.relative_adjoint_derivative (F : DrivenFamily H V a) (t : ℝ) :
    HasDerivAt (fun ε => (F.relative ε t)ᴴ) (Complex.I • F.insertion t) 0 := by
  have hd := F.relative_derivative t
  have hs := hasDerivAt_adjoint hd
  have hp := hs.fun_mul hd
  simp only [F.relative_unitary, F.relative_zero,
    Matrix.conjTranspose_one, one_mul, mul_one] at hp hs
  have hz := hp.unique (hasDerivAt_const (0 : ℝ) (1 : Matrix ι ι ℂ))
  have he : (-Complex.I • F.insertion t)ᴴ = Complex.I • F.insertion t := by
    rw [neg_smul, ← sub_eq_add_neg, sub_eq_zero] at hz
    simpa only [neg_smul] using hz
  rwa [he] at hs

theorem DrivenFamily.observable_eq_relative (F : DrivenFamily H V a)
    (O : Matrix ι ι ℂ) (ε t : ℝ) :
    (F.evolution ε).observable O t =
      (F.relative ε t)ᴴ * (F.evolution 0).observable O t * F.relative ε t := by
  simp only [DrivenFamily.relative, Evolution.observable, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  symm
  calc
    _ = ((F.evolution ε).op t)ᴴ *
        ((F.evolution 0).op t * ((F.evolution 0).op t)ᴴ) * O *
        ((F.evolution 0).op t * ((F.evolution 0).op t)ᴴ) * (F.evolution ε).op t := by
      noncomm_ring
    _ = _ := by rw [(F.evolution 0).right_unitary]; simp

theorem DrivenFamily.observable_derivative (F : DrivenFamily H V a)
    (O : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun ε => (F.evolution ε).observable O t)
      (Complex.I • (F.insertion t * (F.evolution 0).observable O t -
        (F.evolution 0).observable O t * F.insertion t)) 0 := by
  convert ((F.relative_adjoint_derivative t).mul_const
    ((F.evolution 0).observable O t)).mul (F.relative_derivative t) using 1 <;> try rfl
  · funext ε
    exact F.observable_eq_relative O ε t
  · simp only [F.relative_zero, Matrix.conjTranspose_one, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul, neg_smul, Matrix.mul_neg, smul_sub, smul_add, smul_neg, sub_eq_add_neg]

/-- The two-time response kernel; no time-translation invariance is presumed. -/
noncomputable def DrivenFamily.kernel (F : DrivenFamily H V a)
    (ρ O : Matrix ι ι ℂ) (t s : ℝ) : ℂ :=
  Complex.I * commutatorResponse ρ ((F.evolution 0).observable (V s) s)
    ((F.evolution 0).observable O t)

theorem DrivenFamily.response_integral (F : DrivenFamily H V a)
    (ρ O : Matrix ι ι ℂ) (t : ℝ) :
    Matrix.trace (ρ * (Complex.I • (F.insertion t * (F.evolution 0).observable O t -
      (F.evolution 0).observable O t * F.insertion t))) =
        ∫ s in a..t, F.kernel ρ O t s := by
  let T := (F.evolution 0).observable O t
  let L := (traceMap (ι := ι)).comp
    ((ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ) ρ).comp
      ((Complex.I • (ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ)).flip T) -
        (Complex.I • ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ) T)))
  have hc : Continuous (fun s => (F.evolution 0).observable (V s) s) :=
    ((F.evolution 0).continuous.matrix_conjTranspose.mul F.drive_continuous).mul
      (F.evolution 0).continuous
  have h := L.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) a t)
  have hL (X : Matrix ι ι ℂ) : L X = Matrix.trace (ρ *
      (Complex.I • (X * T) - Complex.I • (T * X))) := rfl
  simp only [hL, ← smul_sub] at h
  simpa only [T, DrivenFamily.insertion, DrivenFamily.kernel, commutatorResponse,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] using! h.symm

/-- The response integral is a derivative of the actual driven readout. -/
theorem DrivenFamily.expectation_derivative (F : DrivenFamily H V a)
    (ρ O : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun ε => Matrix.trace (ρ * (F.evolution ε).observable O t))
      (∫ s in a..t, F.kernel ρ O t s) 0 := by
  rw [← F.response_integral]
  exact hasDerivAt_trace ((F.observable_derivative O t).const_mul ρ)

set_option maxHeartbeats 800000 in
/-- Amplitude-dependent preparations and probes have separate contact terms.
The matrix derivative premise on the preparation does not by itself certify
positivity of an arbitrary input family. Use actual density curves for that. -/
theorem DrivenFamily.expectation_contacts (F : DrivenFamily H V a)
    (ρ O : ℝ → Matrix ι ι ℂ) (ρ' O' : Matrix ι ι ℂ)
    (hρ : HasDerivAt ρ ρ' 0) (hO : HasDerivAt O O' 0) (t : ℝ) :
    HasDerivAt (fun ε => Matrix.trace (ρ ε * (F.evolution ε).observable (O ε) t))
      (Matrix.trace (ρ' * (F.evolution 0).observable (O 0) t +
        ρ 0 * (F.evolution 0).observable O' t) + ∫ s in a..t, F.kernel (ρ 0) (O 0) t s) 0 := by
  have hp := (hO.const_mul ((F.evolution 0).op t)ᴴ).mul_const ((F.evolution 0).op t)
  have hd := ((F.relative_adjoint_derivative t).fun_mul hp).fun_mul
    (F.relative_derivative t)
  have ht := hasDerivAt_trace (hρ.fun_mul hd)
  have he : (fun ε => Matrix.trace (ρ ε * ((F.relative ε t)ᴴ *
      (F.evolution 0).observable (O ε) t * F.relative ε t))) =
      (fun ε => Matrix.trace (ρ ε * (F.evolution ε).observable (O ε) t)) := by
    funext ε
    exact congrArg (fun X => Matrix.trace (ρ ε * X))
      (F.observable_eq_relative (O ε) ε t).symm
  change HasDerivAt (fun ε => Matrix.trace (ρ ε * ((F.relative ε t)ᴴ *
    (F.evolution 0).observable (O ε) t * F.relative ε t))) _ 0 at ht
  rw [he] at ht
  convert ht using 1
  rw [← F.response_integral]
  simp only [F.relative_zero, Matrix.conjTranspose_one, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul, neg_smul, Matrix.mul_neg,
    Evolution.observable, ← Matrix.trace_add, smul_sub]
  congr 1
  noncomm_ring

noncomputable def DrivenFamily.switchedExpectation (F : DrivenFamily H V a)
    (ρ O : Matrix ι ι ℂ) (ε t : ℝ) : ℂ :=
  if t ≤ a then Matrix.trace (ρ * (F.evolution 0).observable O t)
  else Matrix.trace (ρ * (F.evolution ε).observable O t)

noncomputable def DrivenFamily.causalResponse (F : DrivenFamily H V a)
    (ρ O : Matrix ι ι ℂ) (t : ℝ) : ℂ :=
  if t ≤ a then 0 else ∫ s in a..t, F.kernel ρ O t s

theorem DrivenFamily.switched_derivative (F : DrivenFamily H V a)
    (ρ O : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun ε => F.switchedExpectation ρ O ε t) (F.causalResponse ρ O t) 0 := by
  by_cases ht : t ≤ a
  · simpa only [DrivenFamily.switchedExpectation, DrivenFamily.causalResponse,
      ite_eq_left ht] using hasDerivAt_const (0 : ℝ)
        (Matrix.trace (ρ * (F.evolution 0).observable O t))
  · simpa only [DrivenFamily.switchedExpectation, DrivenFamily.causalResponse,
      ite_eq_right ht] using F.expectation_derivative ρ O t

theorem DrivenFamily.causal_past (F : DrivenFamily H V a)
    (ρ O : Matrix ι ι ℂ) (t : ℝ) (ht : t ≤ a) : F.causalResponse ρ O t = 0 := by
  simp [DrivenFamily.causalResponse, ht]

/-- No response if the source is absent throughout the integration interval;
its values at future times do not enter this condition. -/
theorem DrivenFamily.response_zero_on (F : DrivenFamily H V a)
    (ρ O : Matrix ι ι ℂ) (t : ℝ) (hV : ∀ s ∈ Set.uIcc a t, V s = 0) :
    (∫ s in a..t, F.kernel ρ O t s) = 0 := by
  calc
    _ = ∫ _ in a..t, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      simp [DrivenFamily.kernel, hV s hs, Evolution.observable, commutatorResponse]
    _ = 0 := intervalIntegral.integral_zero

/-- Different extensions of a drive outside the observed interval give the
same first response. Equality of the base curves follows from the ODE. -/
theorem DrivenFamily.response_congr {W : ℝ → Matrix ι ι ℂ}
    (F : DrivenFamily H V a) (G : DrivenFamily H W a)
    (ρ O : Matrix ι ι ℂ) (t : ℝ) (hVW : Set.EqOn V W (Set.uIcc a t)) :
    (∫ s in a..t, F.kernel ρ O t s) = ∫ s in a..t, G.kernel ρ O t s := by
  have he : (F.evolution 0).op = (G.evolution 0).op := F.base.unique G.base
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [DrivenFamily.kernel, Evolution.observable, he, hVW hs]

end LeanPhy.Quantum.TimeDependent
