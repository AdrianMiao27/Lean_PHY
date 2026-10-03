import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

/-!
# Continuous analysis certificates

This module is the first bridge from LeanPhy's finite algebraic layer to the
actual analytic objects used in physics.  A certificate stores a genuine
mathlib proposition (`Tendsto`, `Integrable`/Bochner integral, or `Summable`/
`tsum`) together with the claimed value.  The composition lemmas below are
ordinary theorem applications, so a downstream proof cannot turn a numerical
guess or a runtime Boolean into a limit or integral theorem.

The certificates deliberately do not assert existence.  A limit, integral, or
series is usable only after the corresponding continuity, integrability, or
summability hypothesis has been supplied.  This is the boundary needed for
continuum path integrals, spectral limits, and renormalisation estimates.
-/

namespace LeanPhy.Mathematics

universe u v w z

open Filter
open scoped Topology BigOperators

/-! ## Limits -/

structure LimitCertificate {α : Type u} {β : Type v} [TopologicalSpace β]
    (l : Filter α) (f : α → β) (value : β) : Prop where
  tendsto : Tendsto f l (𝓝 value)

namespace LimitCertificate

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type z}

theorem of_tendsto [TopologicalSpace β] {l : Filter α} {f : α → β} {value : β}
    (h : Tendsto f l (𝓝 value)) : LimitCertificate l f value :=
  ⟨h⟩

theorem comp [TopologicalSpace β] [TopologicalSpace γ]
    {l : Filter α} {f : α → β} {g : β → γ} {x : β}
    (hf : LimitCertificate l f x) (hg : ContinuousAt g x) :
    LimitCertificate l (g ∘ f) (g x) :=
  ⟨hg.tendsto.comp hf.tendsto⟩

theorem comp_eq [TopologicalSpace β] [TopologicalSpace γ]
    {l : Filter α} {f : α → β} {g : β → γ} {x : β} {y : γ}
    (hf : LimitCertificate l f x) (hg : ContinuousAt g x) (hxy : g x = y) :
    LimitCertificate l (g ∘ f) y := by
  simpa [hxy] using hf.comp hg

theorem add [TopologicalSpace β] [Add β] [ContinuousAdd β]
    {l : Filter α} {f g : α → β} {x y : β}
    (hf : LimitCertificate l f x) (hg : LimitCertificate l g y) :
    LimitCertificate l (fun a => f a + g a) (x + y) :=
  ⟨hf.tendsto.add hg.tendsto⟩

theorem sub [TopologicalSpace β] [Sub β] [ContinuousSub β]
    {l : Filter α} {f g : α → β} {x y : β}
    (hf : LimitCertificate l f x) (hg : LimitCertificate l g y) :
    LimitCertificate l (fun a => f a - g a) (x - y) :=
  ⟨hf.tendsto.sub hg.tendsto⟩

theorem smul [TopologicalSpace R] [TopologicalSpace β] [SMul R β]
    [ContinuousSMul R β] {l : Filter α} {f : α → R} {g : α → β}
    {c : R} {x : β} (hf : LimitCertificate l f c)
    (hg : LimitCertificate l g x) :
    LimitCertificate l (fun a => f a • g a) (c • x) :=
  ⟨hf.tendsto.smul hg.tendsto⟩

theorem norm [SeminormedAddGroup β] {l : Filter α} {f : α → β} {x : β}
    (hf : LimitCertificate l f x) :
    LimitCertificate l (fun a => ‖f a‖) ‖x‖ :=
  ⟨hf.tendsto.norm⟩

theorem map_continuous [TopologicalSpace β] [TopologicalSpace γ]
    {l : Filter α} {f : α → β} {g : β → γ}
    {x : β} (hf : LimitCertificate l f x) (hg : Continuous g) :
    LimitCertificate l (g ∘ f) (g x) :=
  hf.comp hg.continuousAt

end LimitCertificate

/-! ## Bochner integrals -/

structure IntegralCertificate {α : Type u} [MeasurableSpace α]
    {β : Type v} [NormedAddCommGroup β] [NormedSpace ℝ β]
    (μ : MeasureTheory.Measure α)
    (f : α → β) (value : β) : Prop where
  integrable : MeasureTheory.Integrable f μ
  integral_eq : (∫ x, f x ∂μ) = value

namespace IntegralCertificate

open MeasureTheory

variable {α : Type u} [MeasurableSpace α] {β : Type v} {γ : Type w}
variable [NormedAddCommGroup β] [NormedSpace ℝ β]

theorem of_integral {μ : Measure α} {f : α → β} {value : β}
    (hint : Integrable f μ) (hvalue : (∫ x, f x ∂μ) = value) :
    IntegralCertificate μ f value :=
  ⟨hint, hvalue⟩

theorem add {μ : Measure α} {f g : α → β} {x y : β}
    (hf : IntegralCertificate μ f x) (hg : IntegralCertificate μ g y) :
    IntegralCertificate μ (fun a => f a + g a) (x + y) := by
  refine ⟨hf.integrable.add hg.integrable, ?_⟩
  calc
    (∫ a, f a + g a ∂μ) = (∫ a, f a ∂μ) + ∫ a, g a ∂μ :=
      integral_add hf.integrable hg.integrable
    _ = x + y := by rw [hf.integral_eq, hg.integral_eq]

theorem smul (c : ℝ) {μ : Measure α} {f : α → β} {x : β}
    (hf : IntegralCertificate μ f x) :
    IntegralCertificate μ (fun a => c • f a) (c • x) := by
  refine ⟨hf.integrable.smul c, ?_⟩
  calc
    (∫ a, c • f a ∂μ) = c • ∫ a, f a ∂μ := integral_smul c f
    _ = c • x := by rw [hf.integral_eq]

theorem map {μ : Measure α} [CompleteSpace β]
    {δ : Type w} [NormedAddCommGroup δ] [NormedSpace ℝ δ] [CompleteSpace δ]
    {f : α → β} {x : β} (L : β →L[ℝ] δ)
    (hf : IntegralCertificate μ f x) :
    IntegralCertificate μ (fun a => L (f a)) (L x) := by
  refine ⟨L.integrable_comp hf.integrable, ?_⟩
  calc
    (∫ a, L (f a) ∂μ) = L (∫ a, f a ∂μ) :=
      L.integral_comp_comm hf.integrable
    _ = L x := by rw [hf.integral_eq]

end IntegralCertificate

/-! ## Infinite series -/

structure SeriesCertificate {α : Type u} {β : Type v}
    [AddCommMonoid β] [TopologicalSpace β]
    (f : α → β) (value : β) : Prop where
  summable : Summable f
  tsum_eq : (∑' a, f a) = value

namespace SeriesCertificate

variable {α : Type u} {β : Type v} {γ : Type w}

theorem of_summable [AddCommMonoid β] [TopologicalSpace β] [T2Space β]
    {f : α → β} {value : β}
    (hs : Summable f) (heq : (∑' a, f a) = value) :
    SeriesCertificate f value :=
  ⟨hs, heq⟩

theorem add [AddCommMonoid β] [TopologicalSpace β] [T2Space β] [ContinuousAdd β]
    {f g : α → β} {x y : β}
    (hf : SeriesCertificate f x) (hg : SeriesCertificate g y) :
    SeriesCertificate (fun a => f a + g a) (x + y) := by
  refine ⟨hf.summable.add hg.summable, ?_⟩
  calc
    (∑' a, (f a + g a)) = (∑' a, f a) + (∑' a, g a) :=
      hf.summable.tsum_add hg.summable
    _ = x + y := by rw [hf.tsum_eq, hg.tsum_eq]

theorem map [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β]
    {δ : Type w} [NormedAddCommGroup δ] [NormedSpace ℝ δ]
    [TopologicalSpace δ] [T2Space δ]
    (L : β →L[ℝ] δ) {f : α → β} {x : β}
    (hf : SeriesCertificate f x) :
    SeriesCertificate (fun a => L (f a)) (L x) := by
  have hs : HasSum (fun a => L (f a)) (L x) := by
    rw [← hf.tsum_eq]
    exact L.hasSum hf.summable.hasSum
  exact ⟨hs.summable, hs.tsum_eq⟩

end SeriesCertificate

/-! ## A combined convergence record -/

structure ConvergenceCertificate {α : Type u} {β : Type v} [TopologicalSpace β]
    (l : Filter α) (f : α → β) (value : β) : Prop where
  limit : LimitCertificate l f value

namespace ConvergenceCertificate

variable {α : Type u} {β : Type v} [TopologicalSpace β]

theorem of_limit {l : Filter α} {f : α → β} {value : β}
    (h : LimitCertificate l f value) : ConvergenceCertificate l f value :=
  ⟨h⟩

end ConvergenceCertificate

end LeanPhy.Mathematics
