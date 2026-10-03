import LeanPhy.Mathematics.Hilbert
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Continuous-time evolution certificates

This module connects the bounded Hilbert-flow interface to the Bochner
interval integral.  A variation-of-constants certificate records the
integrability and endpoint identity needed by a Duhamel argument.  A separate
norm majorant then turns that identity into a checked finite-time forcing
bound.  The module does not construct a generator, prove existence of a
solution, or hide domain and continuity assumptions.
-/

namespace LeanPhy.Mathematics

open MeasureTheory
open scoped Interval

universe u v

/-! An interval integral certificate is the interval analogue of
`IntegralCertificate`; the value is usable only together with a genuine
`IntervalIntegrable` witness. -/

structure IntervalIntegralCertificate {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a b : ℝ) (value : E) : Prop where
  integrable : IntervalIntegrable f volume a b
  integral_eq : (∫ t in a..b, f t) = value

namespace IntervalIntegralCertificate

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem of_eq {f : ℝ → E} {a b : ℝ} {value : E}
    (hf : IntervalIntegrable f volume a b)
    (heq : (∫ t in a..b, f t) = value) :
    IntervalIntegralCertificate f a b value :=
  ⟨hf, heq⟩

theorem add {f g : ℝ → E} {a b : ℝ} {x y : E}
    (hf : IntervalIntegralCertificate f a b x)
    (hg : IntervalIntegralCertificate g a b y) :
    IntervalIntegralCertificate (fun t => f t + g t) a b (x + y) := by
  refine ⟨hf.integrable.add hg.integrable, ?_⟩
  rw [intervalIntegral.integral_add hf.integrable hg.integrable,
    hf.integral_eq, hg.integral_eq]

theorem smul {f : ℝ → E} {a b : ℝ} (c : ℝ) {x : E}
    (hf : IntervalIntegralCertificate f a b x) :
    IntervalIntegralCertificate (fun t => c • f t) a b (c • x) := by
  refine ⟨hf.integrable.smul c, ?_⟩
  rw [hf.integrable.integral_smul c, hf.integral_eq]

theorem map {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace E]
    [CompleteSpace F] (L : E →L[ℝ] F) {f : ℝ → E} {a b : ℝ} {x : E}
    (hf : IntervalIntegralCertificate f a b x) :
    IntervalIntegralCertificate (fun t => L (f t)) a b (L x) := by
  refine ⟨?_, ?_⟩
  · exact ⟨L.integrable_comp hf.integrable.1, L.integrable_comp hf.integrable.2⟩
  · rw [ContinuousLinearMap.intervalIntegral_comp_comm L hf.integrable, hf.integral_eq]

end IntervalIntegralCertificate

/-! A norm majorant for a forcing term. -/

structure SourceNormCertificate {E : Type u}
    [NormedAddCommGroup E] (source : ℝ → E) (majorant : ℝ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ majorant t
  pointwise : ∀ t, ‖source t‖ ≤ majorant t

namespace SourceNormCertificate

variable {E : Type u} [NormedAddCommGroup E]

theorem widen {source : ℝ → E} {majorant majorant' : ℝ → ℝ}
    (h : SourceNormCertificate source majorant)
    (hle : ∀ t, majorant t ≤ majorant' t)
    (hnonneg : ∀ t, 0 ≤ majorant' t) :
    SourceNormCertificate source majorant' :=
  ⟨hnonneg, fun t => (h.pointwise t).trans (hle t)⟩

end SourceNormCertificate

/-! A proof-bearing variation-of-constants/Duhamel representation. -/

structure VariationOfConstantsCertificate
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (F : Hilbert.Flow (𝕜 := 𝕜) (E := E))
    (source u : ℝ → E) (x : E) : Prop where
  forcing_integrable : ∀ t,
    IntervalIntegrable (fun s => F.op (t - s) (source s)) volume 0 t
  endpoint_eq : ∀ t,
    u t = F.evolve t x + ∫ s in (0 : ℝ)..t, F.op (t - s) (source s)

namespace VariationOfConstantsCertificate

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [CompleteSpace E]
  {F : Hilbert.Flow (𝕜 := 𝕜) (E := E)}
  {source u : ℝ → E} {x : E}

theorem initial (h : VariationOfConstantsCertificate F source u x) :
    u 0 = x := by
  rw [h.endpoint_eq 0, F.evolve_zero]
  simp

theorem norm_error_le
    {bound majorant : ℝ → ℝ}
    (h : VariationOfConstantsCertificate F source u x)
    (hF : Hilbert.FlowNormCertificate F bound)
    (hsource : SourceNormCertificate source majorant)
    (hmajorant : ∀ t, 0 ≤ t →
      IntervalIntegrable (fun s => bound (t - s) * majorant s) volume 0 t)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖u t - F.evolve t x‖ ≤
      ∫ s in (0 : ℝ)..t, bound (t - s) * majorant s := by
  rw [h.endpoint_eq t]
  simp only [add_sub_cancel_left]
  refine (intervalIntegral.norm_integral_le_integral_norm ht).trans ?_
  apply intervalIntegral.integral_mono_on ht (h.forcing_integrable t).norm
    (hmajorant t ht)
  intro s hs
  calc
    ‖F.op (t - s) (source s)‖ ≤ ‖F.op (t - s)‖ * ‖source s‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ bound (t - s) * majorant s := by
      exact mul_le_mul (hF.op_le (t - s)) (hsource.pointwise s)
        (norm_nonneg _) (hF.nonneg (t - s))

end VariationOfConstantsCertificate

end LeanPhy.Mathematics
