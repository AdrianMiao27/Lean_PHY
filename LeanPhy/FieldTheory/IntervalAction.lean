import LeanPhy.FieldTheory.CurveJet
import LeanPhy.FieldTheory.VariationalResidual
import LeanPhy.Mathematics.PolynomialIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

/-!
# Finite-interval actions with proved variations and boundary terms

The action is the actual interval integral of a polynomial density evaluated
on a C² profile. Its derivative under `φ + s η` follows from compactness and
polynomial evaluation. The first-variation theorem retains both endpoints;
fixed or matched endpoint fluxes are separate hypotheses. This covers coupled
finite-mode dynamics and one-dimensional static textures, not a general
spacetime divergence theorem or existence of stationary solutions.
-/

namespace LeanPhy.FieldTheory.IntervalAction

open FieldEvaluation MeasureTheory
open LeanPhy.Mathematics
open scoped BigOperators ContDiff Interval

variable {Field : Type*} [Fintype Field]

def direction : Unit → ℝ := fun _ => 1

noncomputable def action (L : FirstOrderLagrangian ℝ Field Unit)
    (φ : Field → ℝ → ℝ) (a b : ℝ) : ℝ := ∫ t in a..b, value L direction φ t

noncomputable def bulk (L : FirstOrderLagrangian ℝ Field Unit)
    (φ η : Field → ℝ → ℝ) (t : ℝ) : ℝ := ∑ i, euler L direction φ i t * η i t

noncomputable def endpoint (L : FirstOrderLagrangian ℝ Field Unit)
    (φ η : Field → ℝ → ℝ) : ℝ → ℝ := FieldEvaluation.boundary L direction φ η ()

theorem contDiff_endpoint (L : FirstOrderLagrangian ℝ Field Unit)
    (φ η : Field → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ 2 (φ i))
    (hη : ∀ i, ContDiff ℝ 1 (η i)) : ContDiff ℝ 1 (endpoint L φ η) :=
  ContDiff.sum (fun i _ => (contDiff_value _ direction φ (n := 1) hφ).mul (hη i))

omit [Fintype Field] in
theorem continuous_euler (L : FirstOrderLagrangian ℝ Field Unit)
    (φ : Field → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ 2 (φ i)) (i : Field) :
    Continuous (euler L direction φ i) := by
  have hp : ContDiff ℝ 1 (momentum L direction φ i ()) := contDiff_value _ _ _ hφ
  change Continuous (fun t => force L direction φ i t -
    ∑ μ, directional (direction μ) (momentum L direction φ i μ) t)
  simpa only [Fintype.sum_unique] using!
    (contDiff_value (MvPolynomial.pderiv (i, none) L) direction φ (n := 1) hφ).continuous.sub
      (contDiff_directional (direction ()) _ (n := 0) hp).continuous

theorem continuous_bulk (L : FirstOrderLagrangian ℝ Field Unit)
    (φ η : Field → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ 2 (φ i))
    (hη : ∀ i, Continuous (η i)) : Continuous (bulk L φ η) :=
  continuous_finsetSum _ (fun i _ => (continuous_euler L φ hφ i).mul (hη i))

/-- Differentiating the actual action is justified by the proved polynomial
integral theorem. No dominated-convergence conclusion is assumed. -/
theorem hasDerivAt_action (L : FirstOrderLagrangian ℝ Field Unit)
    (φ η : Field → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ 1 (φ i))
    (hη : ∀ i, ContDiff ℝ 1 (η i)) (a b : ℝ) :
    HasDerivAt (fun s => action L (perturb φ η s) a b)
      (∫ t in a..b, variation L direction φ η t) 0 := by
  have hc (q : Field → ℝ → ℝ) (hq : ∀ i, ContDiff ℝ 1 (q i))
      (p : Field × Option Unit) : Continuous (fun t => coordinates direction q t p) := by
    rcases p with ⟨i, _ | μ⟩
    · exact (hq i).continuous
    · exact (contDiff_directional _ _ (n := 0) (hq i)).continuous
  have h := PolynomialIntegral.hasDerivAt_integral L
    (fun p t => coordinates direction φ t p) (fun p t => coordinates direction η t p)
    (hc φ hφ) (hc η hη) a b
  have hv (s t : ℝ) : value L direction (perturb φ η s) t =
      PolynomialIntegral.affineValue L
        (fun p t => coordinates direction φ t p) (fun p t => coordinates direction η t p) s t := by
    unfold value PolynomialIntegral.affineValue
    rw [show coordinates direction (perturb φ η s) t =
      (fun p => coordinates direction φ t p + s * coordinates direction η t p) from
      funext (coordinates_perturb _ _ _ t
        (fun i => (hφ i).differentiable (by norm_num) t)
        (fun i => (hη i).differentiable (by norm_num) t) s)]
  change HasDerivAt (fun s => ∫ t in a..b, value L direction (perturb φ η s) t) _ 0
  simp_rw [hv]
  convert! h using 1
  congr 1
  funext t
  simp [PolynomialIntegral.affineDerivative, PolynomialIntegral.affineValue,
    Fintype.sum_prod_type, Fintype.sum_option, Finset.sum_add_distrib,
    variation, force, momentum, value, coordinates]
  rfl

theorem integral_first_variation (L : FirstOrderLagrangian ℝ Field Unit)
    (φ η : Field → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ 2 (φ i))
    (hη : ∀ i, ContDiff ℝ 1 (η i)) (a b : ℝ) :
    (∫ t in a..b, variation L direction φ η t) =
      (∫ t in a..b, bulk L φ η t) + endpoint L φ η b - endpoint L φ η a := by
  have hpoint (t : ℝ) : variation L direction φ η t =
      bulk L φ η t + deriv (endpoint L φ η) t := by
    simpa only [bulk, divergence, Fintype.sum_unique] using!
      first_variation L direction φ η t hφ
        (fun i => (hη i).differentiable (by norm_num) t)
  have hb := contDiff_endpoint L φ η hφ hη
  have hdc : Continuous (deriv (endpoint L φ η)) :=
    (contDiff_directional (1 : ℝ) _ (n := 0) hb).continuous
  simp_rw [hpoint]
  rw [intervalIntegral.integral_add
    ((continuous_bulk L φ η hφ (fun i => (hη i).continuous)).intervalIntegrable a b)
    (hdc.intervalIntegrable a b)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => (hb.differentiable (by norm_num) t).hasDerivAt)
    (hdc.intervalIntegrable a b)]
  ring

/-- The derivative of the integrated action with its endpoint flux retained. -/
theorem hasDerivAt_action_boundary (L : FirstOrderLagrangian ℝ Field Unit)
    (φ η : Field → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ 2 (φ i))
    (hη : ∀ i, ContDiff ℝ 1 (η i)) (a b : ℝ) :
    HasDerivAt (fun s => action L (perturb φ η s) a b)
      ((∫ t in a..b, bulk L φ η t) + endpoint L φ η b - endpoint L φ η a) 0 := by
  rw [← integral_first_variation L φ η hφ hη a b]
  exact hasDerivAt_action L φ η (fun i => (hφ i).of_le (by norm_num)) hη a b

/-- Matching endpoint flux includes periodic data and other admissible
boundary conditions; equality must be proved for the actual profiles. -/
theorem hasDerivAt_action_matched_endpoints (L : FirstOrderLagrangian ℝ Field Unit)
    (φ η : Field → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ 2 (φ i))
    (hη : ∀ i, ContDiff ℝ 1 (η i)) (a b : ℝ)
    (hboundary : endpoint L φ η b = endpoint L φ η a) :
    HasDerivAt (fun s => action L (perturb φ η s) a b) (∫ t in a..b, bulk L φ η t) 0 := by
  simpa [hboundary] using hasDerivAt_action_boundary L φ η hφ hη a b

theorem hasDerivAt_action_fixed_endpoints (L : FirstOrderLagrangian ℝ Field Unit)
    (φ η : Field → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ 2 (φ i))
    (hη : ∀ i, ContDiff ℝ 1 (η i)) (a b : ℝ)
    (ha : ∀ i, η i a = 0) (hb : ∀ i, η i b = 0) :
    HasDerivAt (fun s => action L (perturb φ η s) a b) (∫ t in a..b, bulk L φ η t) 0 :=
  hasDerivAt_action_matched_endpoints L φ η hφ hη a b (by
    simp [endpoint, FieldEvaluation.boundary, ha, hb])

/-- Euler equations imply stationarity for fixed-endpoint variations. This
does not assert that the stationary profile minimizes the action. -/
theorem stationary_of_euler (L : FirstOrderLagrangian ℝ Field Unit)
    (φ η : Field → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ 2 (φ i))
    (hη : ∀ i, ContDiff ℝ 1 (η i)) (a b : ℝ)
    (ha : ∀ i, η i a = 0) (hb : ∀ i, η i b = 0)
    (hE : ∀ t ∈ Set.uIcc a b, ∀ i, euler L direction φ i t = 0) :
    HasDerivAt (fun s => action L (perturb φ η s) a b) 0 0 := by
  have hzero : (∫ t in a..b, bulk L φ η t) = 0 := by
    calc
      _ = ∫ _ in a..b, (0 : ℝ) := intervalIntegral.integral_congr
        (fun t ht => by simp [bulk, hE t ht])
      _ = 0 := by simp
  simpa [hzero] using hasDerivAt_action_fixed_endpoints L φ η hφ hη a b ha hb

/-- A proved formal symmetry supplies a balance law for the actual profile.
Off-shell Euler residuals are retained under the integral. -/
theorem noether_balance (L : FirstOrderLagrangian ℝ Field Unit)
    (η : Field → JetPolynomial ℝ Field Unit) (B : Unit → JetPolynomial ℝ Field Unit)
    (hSymmetry : FirstOrderLagrangian.firstVariation L η = FirstOrderLagrangian.divergence B)
    (φ : Field → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (a b : ℝ) :
    CurveJet.evaluate φ b (FirstOrderLagrangian.noetherCurrent L η B ()) -
      CurveJet.evaluate φ a (FirstOrderLagrangian.noetherCurrent L η B ()) =
      ∫ t in a..b, -(∑ i, euler L direction φ i t * CurveJet.evaluate φ t (η i)) := by
  let J := FirstOrderLagrangian.noetherCurrent L η B ()
  have he (t : ℝ) : CurveJet.evaluate φ t (JetPolynomial.totalDerivative () J) =
      -(∑ i, euler L direction φ i t * CurveJet.evaluate φ t (η i)) := by
    have h := congrArg (CurveJet.evaluate φ t)
      (FirstOrderLagrangian.noether_off_shell L η B hSymmetry)
    simpa [FirstOrderLagrangian.divergence, J, CurveJet.evaluate_eulerLagrange L φ hφ,
      direction] using! h
  have hc : Continuous (fun t => CurveJet.evaluate φ t (JetPolynomial.totalDerivative () J)) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (CurveJet.hasDerivAt_evaluate φ hφ _ t).continuousAt)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc a b) => CurveJet.hasDerivAt_evaluate φ hφ J t)
    (hc.intervalIntegrable a b)
  simpa only [he] using h.symm

/-- A Noether current has equal endpoint values on a smooth solution.
This is a finite-mode charge or one-dimensional profile current; it does not
silently integrate out any additional spatial coordinates. -/
theorem noether_conserved (L : FirstOrderLagrangian ℝ Field Unit)
    (η : Field → JetPolynomial ℝ Field Unit) (B : Unit → JetPolynomial ℝ Field Unit)
    (hSymmetry : FirstOrderLagrangian.firstVariation L η = FirstOrderLagrangian.divergence B)
    (φ : Field → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (a b : ℝ)
    (hE : ∀ t ∈ Set.uIcc a b, ∀ i, euler L direction φ i t = 0) :
    CurveJet.evaluate φ b (FirstOrderLagrangian.noetherCurrent L η B ()) =
      CurveJet.evaluate φ a (FirstOrderLagrangian.noetherCurrent L η B ()) := by
  have h := noether_balance L η B hSymmetry φ hφ a b
  have hz : (∫ t in a..b, -(∑ i, euler L direction φ i t * CurveJet.evaluate φ t (η i))) = 0 := by
    calc
      _ = ∫ _ in a..b, (0 : ℝ) := intervalIntegral.integral_congr
        (fun t ht => by simp [hE t ht])
      _ = 0 := by simp
  exact sub_eq_zero.mp (h.trans hz)

/-- Certified equation residuals and explicit symmetry breaking give an
integrated current drift. Uniform bounds are required on the entire interval;
point samples cannot establish these premises. -/
theorem noether_drift_certificate (L : FirstOrderLagrangian ℝ Field Unit)
    (η : Field → JetPolynomial ℝ Field Unit) (B : Unit → JetPolynomial ℝ Field Unit)
    (φ : Field → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (a b : ℝ)
    (ε M : Field → ℝ) (δ : ℝ)
    (hE : ∀ t ∈ Set.uIcc a b, ∀ i, ErrorCertificate (euler L direction φ i t) 0 (ε i))
    (hη : ∀ t ∈ Set.uIcc a b, ∀ i, |CurveJet.evaluate φ t (η i)| ≤ M i)
    (hBreaking : ∀ t ∈ Set.uIcc a b, ErrorCertificate
      (CurveJet.evaluate φ t (FirstOrderLagrangian.firstVariation L η -
        FirstOrderLagrangian.divergence B)) 0 δ) :
    ErrorCertificate
      (CurveJet.evaluate φ b (FirstOrderLagrangian.noetherCurrent L η B ()))
      (CurveJet.evaluate φ a (FirstOrderLagrangian.noetherCurrent L η B ()))
      ((δ + ∑ i, ε i * M i) * |b - a|) := by
  let J := FirstOrderLagrangian.noetherCurrent L η B ()
  have hlocal (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      ErrorCertificate (CurveJet.evaluate φ t (JetPolynomial.totalDerivative () J)) 0
        (δ + ∑ i, ε i * M i) := by
    have h := FirstOrderLagrangian.noether_residual_certificate L η B (CurveJet.evaluate φ t)
      ε M δ (fun i => by simpa only [CurveJet.evaluate_eulerLagrange L φ hφ] using! hE t ht i)
      (hη t ht) (hBreaking t ht)
    simpa only [FirstOrderLagrangian.divergence, Fintype.sum_unique] using h
  refine ⟨mul_nonneg (hlocal a (Set.left_mem_uIcc)).nonneg (abs_nonneg _), ?_⟩
  have hc : Continuous (fun t => CurveJet.evaluate φ t (JetPolynomial.totalDerivative () J)) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (CurveJet.hasDerivAt_evaluate φ hφ _ t).continuousAt)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc a b) => CurveJet.hasDerivAt_evaluate φ hφ J t)
    (hc.intervalIntegrable a b)
  rw [Real.dist_eq, ← hi]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := δ + ∑ i, ε i * M i)
    (f := fun t => CurveJet.evaluate φ t (JetPolynomial.totalDerivative () J)) (fun t ht => by
      simpa only [Real.norm_eq_abs, Real.dist_eq, sub_zero] using
        (hlocal t (Set.uIoc_subset_uIcc ht)).bound)
  simpa only [Real.norm_eq_abs] using hb

end LeanPhy.FieldTheory.IntervalAction
