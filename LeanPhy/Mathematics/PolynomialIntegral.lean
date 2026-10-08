import LeanPhy.Mathematics.PolynomialEvaluation
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

/-!
# Actual variations of polynomial integrals on finite intervals

Continuity of the input profiles supplies the domination needed to
differentiate under the integral. No interchange-of-limits or integrable
derivative conclusion is an input. The argument covers arbitrary finite
polynomials and oriented intervals, including coincident endpoints.
-/

namespace LeanPhy.Mathematics.PolynomialIntegral

open MeasureTheory Filter Set
open scoped BigOperators Topology Interval

variable {ι : Type*} [Fintype ι]

noncomputable def affineValue (P : MvPolynomial ι ℝ) (u v : ι → ℝ → ℝ) (s t : ℝ) : ℝ :=
  MvPolynomial.eval (fun i => u i t + s * v i t) P

noncomputable def affineDerivative (P : MvPolynomial ι ℝ)
    (u v : ι → ℝ → ℝ) (s t : ℝ) : ℝ :=
  ∑ i, affineValue (MvPolynomial.pderiv i P) u v s t * v i t

omit [Fintype ι] in
theorem continuous_affineValue (P : MvPolynomial ι ℝ) (u v : ι → ℝ → ℝ)
    (hu : ∀ i, Continuous (u i)) (hv : ∀ i, Continuous (v i)) :
    Continuous (fun p : ℝ × ℝ => affineValue P u v p.1 p.2) := by
  apply P.continuous_eval.comp
  exact continuous_pi (fun i => (hu i).comp continuous_snd |>.add
    (continuous_fst.mul ((hv i).comp continuous_snd)))

theorem continuous_affineDerivative (P : MvPolynomial ι ℝ) (u v : ι → ℝ → ℝ)
    (hu : ∀ i, Continuous (u i)) (hv : ∀ i, Continuous (v i)) :
    Continuous (fun p : ℝ × ℝ => affineDerivative P u v p.1 p.2) :=
  continuous_finsetSum _ (fun i _ =>
    (continuous_affineValue _ u v hu hv).mul ((hv i).comp continuous_snd))

theorem hasDerivAt_affineValue (P : MvPolynomial ι ℝ) (u v : ι → ℝ → ℝ) (s t : ℝ) :
    HasDerivAt (fun r => affineValue P u v r t) (affineDerivative P u v s t) s := by
  apply PolynomialEvaluation.hasDerivAt_eval
  intro i
  simpa using ((hasDerivAt_id s).mul_const (v i t)).const_add (u i t)

/-- The domination hypothesis is proved using continuity on a compact
parameter-by-position rectangle. It is not delegated to the caller. -/
theorem hasDerivAt_integral (P : MvPolynomial ι ℝ) (u v : ι → ℝ → ℝ)
    (hu : ∀ i, Continuous (u i)) (hv : ∀ i, Continuous (v i)) (a b : ℝ) :
    HasDerivAt (fun s => ∫ t in a..b, affineValue P u v s t)
      (∫ t in a..b, affineDerivative P u v 0 t) 0 := by
  have hc := continuous_affineValue P u v hu hv
  have hd := continuous_affineDerivative P u v hu hv
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_uIcc (a := a) (b := b))).bddAbove_image
    (hd.norm.continuousOn : ContinuousOn
      (fun p : ℝ × ℝ => ‖affineDerivative P u v p.1 p.2‖)
      (Icc (-1 : ℝ) 1 ×ˢ uIcc a b))
  have hs : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := affineValue P u v) (F' := affineDerivative P u v) (bound := fun _ => M) hs
    (Filter.Eventually.of_forall (fun s =>
      (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    ((hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b)
    ((hd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun t ht s hs =>
      hM ⟨(s, t), ⟨⟨le_of_lt hs.1, le_of_lt hs.2⟩, uIoc_subset_uIcc ht⟩, rfl⟩))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t _ s _ => hasDerivAt_affineValue P u v s t))).2

end LeanPhy.Mathematics.PolynomialIntegral
