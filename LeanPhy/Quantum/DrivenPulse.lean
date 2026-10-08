import LeanPhy.Quantum.DrivenResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Constructed continuous pulses in a moving frame

For an actual background evolution U and a Hermitian B, every continuous real
envelope f supplies an actual amplitude family for
`H(t) + ε f(t) U(t) B U(t)†`. Its solution is
`U(t) exp(-i ε (∫ₐᵗ f) B)`. This is a rotating-frame drive, not an arbitrary
laboratory-frame `H(t) + ε f(t) B`. It need not commute with H, and all time,
amplitude-continuity and initial-value obligations are proved here.
-/

namespace LeanPhy.Quantum.TimeDependent

open LeanPhy.Quantum.Dynamics LeanPhy.Mathematics MeasureTheory
open scoped Matrix Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : ℝ → Matrix ι ι ℂ} {a : ℝ}

noncomputable def pulseArea (f : ℝ → ℝ) (a t : ℝ) : ℝ := ∫ s in a..t, f s

theorem pulseArea_derivative (f : ℝ → ℝ) (hf : Continuous f) (a t : ℝ) :
    HasDerivAt (pulseArea f a) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a t)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem pulseArea_continuous (f : ℝ → ℝ) (hf : Continuous f) (a : ℝ) :
    Continuous (pulseArea f a) :=
  continuous_iff_continuousAt.mpr (fun t => (pulseArea_derivative f hf a t).continuousAt)

noncomputable def rotatingDrive (U : Evolution H a) (B : Matrix ι ι ℂ)
    (f : ℝ → ℝ) (t : ℝ) : Matrix ι ι ℂ := f t • (U.op t * B * (U.op t)ᴴ)

theorem rotatingDrive_continuous (U : Evolution H a) (B : Matrix ι ι ℂ)
    (f : ℝ → ℝ) (hf : Continuous f) : Continuous (rotatingDrive U B f) := by
  exact hf.smul ((U.continuous.mul continuous_const).mul U.continuous.matrix_conjTranspose)

/-- An explicit nonautonomous solution, with arbitrary continuous envelope. -/
noncomputable def pulseEvolution (U : Evolution H a) (B : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (f : ℝ → ℝ) (hf : Continuous f) (ε : ℝ) :
    Evolution (fun t => H t + ε • rotatingDrive U B f t) a where
  op t := U.op t * propagator B (-(ε * pulseArea f a t))
  hermitian t := (U.hermitian t).add
    (((Matrix.isHermitian_mul_mul_conjTranspose (U.op t) hB).smul
      (isSelfAdjoint_iff.mpr (star_trivial (f t)))).smul
        (isSelfAdjoint_iff.mpr (star_trivial ε)))
  initial := by simp [U.initial, pulseArea, propagator]
  equation t := by
    have hp := (pulseArea_derivative f hf a t).const_mul ε |>.neg
    have hb := (Duhamel.flow_derivative_left (Complex.I • B)
      (-(ε * pulseArea f a t))).scomp t hp
    change HasDerivAt (fun s => propagator B (-(ε * pulseArea f a s)))
      (-(ε * f t) • ((Complex.I • B) * propagator B (-(ε * pulseArea f a t)))) t at hb
    have hm : (U.op t * B * (U.op t)ᴴ) *
        (U.op t * propagator B (-(ε * pulseArea f a t))) =
      U.op t * B * propagator B (-(ε * pulseArea f a t)) := by
      calc
        _ = U.op t * B * ((U.op t)ᴴ * U.op t) *
            propagator B (-(ε * pulseArea f a t)) := by noncomm_ring
        _ = _ := by rw [U.unitary]; simp
    convert (U.equation t).mul hb using 1 <;> try rfl
    simp only [rotatingDrive, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul]
    rw [hm]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, Complex.ofReal_neg,
      Complex.ofReal_mul, smul_add, ← Matrix.mul_assoc]
    module


/-- A constructed family discharges the assumptions of the general response API. -/
noncomputable def pulseFamily (U : Evolution H a) (B : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (f : ℝ → ℝ) (hf : Continuous f) :
    DrivenFamily H (rotatingDrive U B f) a where
  evolution := pulseEvolution U B hB f hf
  drive_continuous := rotatingDrive_continuous U B f hf
  continuous := by
    change Continuous (fun p : ℝ × ℝ =>
      U.op p.2 * propagator B (-(p.1 * pulseArea f a p.2)))
    exact (U.continuous.comp continuous_snd).mul
      ((Duhamel.flow_continuous (Complex.I • B)).comp
        (continuous_fst.mul ((pulseArea_continuous f hf a).comp continuous_snd)).neg)

@[simp] theorem pulseFamily_base (U : Evolution H a) (B : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ) :
    ((pulseFamily U B hB f hf).evolution 0).op t = U.op t := by
  simp [pulseFamily, pulseEvolution, propagator]

/-- The laboratory-frame drive pulls back to the chosen pulse in the background frame. -/
theorem rotatingDrive_observable (U : Evolution H a) (B : Matrix ι ι ℂ)
    (f : ℝ → ℝ) (t : ℝ) : U.observable (rotatingDrive U B f t) t = f t • B := by
  simp only [Evolution.observable, rotatingDrive, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc
    _ = ((U.op t)ᴴ * U.op t) * B * ((U.op t)ᴴ * U.op t) := by noncomm_ring
    _ = B := by rw [U.unitary]; simp

theorem pulseFamily_kernel (U : Evolution H a) (B : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (f : ℝ → ℝ) (hf : Continuous f)
    (ρ O : Matrix ι ι ℂ) (t s : ℝ) :
    (pulseFamily U B hB f hf).kernel ρ O t s =
      (f s : ℂ) * (Complex.I * commutatorResponse ρ B (U.observable O t)) := by
  simp only [DrivenFamily.kernel, Evolution.observable, pulseFamily_base]
  change Complex.I * commutatorResponse ρ (U.observable (rotatingDrive U B f s) s)
    (U.observable O t) = _
  rw [rotatingDrive_observable]
  simp only [commutatorResponse, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub,
    Matrix.trace_smul, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
  simp only [Evolution.observable]
  ac_rfl

/-- The pulse-area readout is derived from the actual constructed evolution. -/
theorem pulseFamily_response (U : Evolution H a) (B : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (f : ℝ → ℝ) (hf : Continuous f)
    (ρ O : Matrix ι ι ℂ) (t : ℝ) :
    (∫ s in a..t, (pulseFamily U B hB f hf).kernel ρ O t s) =
      pulseArea f a t • (Complex.I * commutatorResponse ρ B (U.observable O t)) := by
  simp_rw [pulseFamily_kernel, ← Complex.real_smul]
  exact intervalIntegral.integral_smul_const _ _

/-- The previous constant-drive API is included as an actual amplitude family. -/
noncomputable def autonomousFamily (H V : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hV : V.IsHermitian) (a : ℝ) :
    DrivenFamily (fun _ => H) (fun _ => V) a where
  evolution ε := autonomous (H + ε • V)
    (hH.add (hV.smul (isSelfAdjoint_iff.mpr (star_trivial ε)))) a
  drive_continuous := continuous_const
  continuous := by
    change Continuous (fun p : ℝ × ℝ => Duhamel.flow
      (Complex.I • (H + p.1 • V)) (a - p.2))
    unfold Duhamel.flow
    apply NormedSpace.exp_continuous.comp
    fun_prop

end LeanPhy.Quantum.TimeDependent
