import LeanPhy.Mathematics.FiniteSchwingerDyson
import LeanPhy.Mathematics.FiniteRGDiagnostics
import LeanPhy.Workflow.Core

set_option autoImplicit false

/-!
# Finite lattice / truncated-field research exit

This client is deliberately parameterised by the configuration labels, weight
table, blocking map, observables and numerical radii.  It demonstrates the
research chain that is currently available for lattice and truncated-field
exploration:

* a proved finite weight symmetry becomes a unit-Jacobian
  Schwinger--Dyson/Ward insertion;
* an operator scaling certificate is transported through an exact finite
  blocking map;
* a pointwise blocking defect is accumulated into a partition and normalized
  observable error budget, including composition of two stages.

The client does not infer a continuum functional integral, a critical
exponent, a beta function, or a thermodynamic limit.  Those remain explicit
obligations in the package below.
-/

namespace LeanPhy.Examples.FiniteLatticeResearch

open LeanPhy.Mathematics LeanPhy.Workflow
open scoped BigOperators

theorem symmetry_gives_ward_insertion
    {ι : Type*} [Fintype ι]
    (P : FinitePathIntegral ι) (e : Equiv.Perm ι)
    (hinvolutive : ∀ i, e (e i) = i)
    (hsym : FinitePathIntegral.WeightSymmetry P e) (O : ι → ℂ) :
    P.expectation (fun i => O (e i) - O i) = 0 :=
  P.weight_symmetry_ward e hinvolutive hsym O

theorem scaled_readout_under_blocking
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (fineObs : ι → ℂ) (coarseObs : κ → ℂ) (lambda : ℂ)
    (hscale : FinitePathIntegral.FiniteRGStep.ScalingCertificate
      R fineObs coarseObs lambda) :
    (R.finePathIntegral h).expectation fineObs =
      lambda * (R.coarsePathIntegral h).expectation coarseObs :=
  R.expectation_scales h fineObs coarseObs lambda hscale

theorem pointwise_rg_defect_controls_partition
    {ι : Type*} [Fintype ι]
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (C : FinitePathIntegral.FiniteRGStep.FixedPointDefect R) :
    ErrorCertificate
      (∑ y, R.coarseWeight y) (∑ y, R.fineWeight y)
      (∑ y, C.radius y) :=
  C.partition_error R

noncomputable def pointwise_rg_defect_certificate
    {ι : Type*} [Fintype ι]
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (C : FinitePathIntegral.FiniteRGStep.FixedPointDefect R)
    (O : ι → ℂ)
    (coarseLower fineLower : ℝ)
    (hcoarse_pos : 0 < coarseLower) (hfine_pos : 0 < fineLower)
    (hcoarse_lower : coarseLower ≤
      ‖(R.coarsePathIntegral h).partition‖)
    (hfine_lower : fineLower ≤ ‖(R.finePathIntegral h).partition‖)
    (insertionUpper : ℝ) (hinsertionUpper_nonneg : 0 ≤ insertionUpper)
    (hinsertion_upper :
      ‖(R.finePathIntegral h).insertion O‖ ≤ insertionUpper) :
    FinitePathIntegral.NormalizedExpectationCertificate
      (R.coarsePathIntegral h) (R.finePathIntegral h) O :=
  C.toExpectationComparison R h O coarseLower fineLower hcoarse_pos hfine_pos
    hcoarse_lower hfine_lower insertionUpper hinsertionUpper_nonneg
    hinsertion_upper

theorem pointwise_rg_defect_controls_readout
    {ι : Type*} [Fintype ι]
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (C : FinitePathIntegral.FiniteRGStep.FixedPointDefect R)
    (O : ι → ℂ)
    (coarseLower fineLower : ℝ)
    (hcoarse_pos : 0 < coarseLower) (hfine_pos : 0 < fineLower)
    (hcoarse_lower : coarseLower ≤
      ‖(R.coarsePathIntegral h).partition‖)
    (hfine_lower : fineLower ≤ ‖(R.finePathIntegral h).partition‖)
    (insertionUpper : ℝ) (hinsertionUpper_nonneg : 0 ≤ insertionUpper)
    (hinsertion_upper :
      ‖(R.finePathIntegral h).insertion O‖ ≤ insertionUpper) :
    ErrorCertificate
      ((R.coarsePathIntegral h).expectation O)
      ((R.finePathIntegral h).expectation O)
      (pointwise_rg_defect_certificate R h C O coarseLower fineLower
        hcoarse_pos hfine_pos hcoarse_lower hfine_lower insertionUpper
        hinsertionUpper_nonneg hinsertion_upper).radius :=
  (pointwise_rg_defect_certificate R h C O coarseLower fineLower
    hcoarse_pos hfine_pos hcoarse_lower hfine_lower insertionUpper
    hinsertionUpper_nonneg hinsertion_upper).error

theorem two_stage_rg_budget
    {ι : Type*} [Fintype ι]
    (R S : FinitePathIntegral.FiniteRGStep ι ι)
    (hmiddle : S.fineWeight = R.coarseWeight)
    (first : FinitePathIntegral.FiniteRGStep.FixedPointDefect R)
    (second : FinitePathIntegral.FiniteRGStep.FixedPointDefect S) :
    ErrorCertificate
      (∑ y, (R.coarsen S.coarse).coarseWeight y)
      (∑ y, R.fineWeight y)
      (∑ y, (first.radius y + second.radius y)) :=
  FinitePathIntegral.FiniteRGStep.FixedPointDefect.compose_partition_error
    R S hmiddle first second

theorem exact_fixed_point_has_zero_budget
    {ι : Type*} [Fintype ι]
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (hR : FinitePathIntegral.FiniteRGStep.IsFixedPoint R) :
    ∀ y, (FinitePathIntegral.FiniteRGStep.FixedPointDefect.exact R hR).radius y = 0 := by
  intro y
  rfl

def package : TheoryPackage :=
  TheoryPackage.empty "finite lattice RG and Ward diagnostics"
    "finite lattice, truncated field theory and exploratory renormalization"
    |>.addAssumptionText "explicit nonzero partition certificate"
      "normalized expectations are formed only after a finite partition nonzero proof"
      "finite-model input"
    |>.addAssumptionText "all blocking and defect radii are finite"
      "each numerical blocking stage supplies a finite pointwise error radius"
      "finite-model input"
    |>.addModelText "finite-lattice-path" "finite weighted configuration model"
      "finite configuration labels" "complex weighted paths"
      "complex observables" "finite symmetry, blocking and normalized readouts"
      ["explicit nonzero partition certificate",
       "all blocking and defect radii are finite"]
    |>.addTheoremForModel "finite-lattice-path"
      "symmetry to Ward insertion"
      "a proved involutive weight symmetry gives a unit-Jacobian finite Schwinger--Dyson insertion"
      "symmetry_gives_ward_insertion" [] (@symmetry_gives_ward_insertion.{0})
    |>.addTheoremForModel "finite-lattice-path"
      "scaled blocked readout"
      "an explicitly supplied operator scaling law transports through finite blocking"
      "scaled_readout_under_blocking" [] (@scaled_readout_under_blocking.{0,0})
    |>.addTheoremForModel "finite-lattice-path"
      "partition defect budget"
      "pointwise coarse-weight defects sum to a certified partition error"
      "pointwise_rg_defect_controls_partition" [] (@pointwise_rg_defect_controls_partition.{0})
    |>.addTheoremForModel "finite-lattice-path"
      "normalized readout defect budget"
      "denominator and insertion bounds turn a blocking defect into a normalized observable certificate"
      "pointwise_rg_defect_controls_readout" [] (@pointwise_rg_defect_controls_readout.{0})
    |>.addTheoremForModel "finite-lattice-path"
      "two-stage RG error composition"
      "consecutive finite blocking defects add only after the intermediate weights are identified"
      "two_stage_rg_budget" [] (@two_stage_rg_budget.{0})
    |>.addTheoremForModel "finite-lattice-path"
      "exact fixed-point zero radius"
      "an exact finite fixed point is represented by a zero-radius defect ledger"
      "exact_fixed_point_has_zero_budget" [] (@exact_fixed_point_has_zero_budget.{0})
    |>.addBoundaryText "finite-model scope"
      "These results concern finite sums and finite blocking maps; they do not prove a continuum measure, reflection positivity, or universality."
    |>.addObligationText "continuum Schwinger--Dyson bridge"
      "supply a model-specific measure, domain and limiting argument for the target continuum theory"
      "continuum analysis"
    |>.addObligationText "physical RG flow"
      "derive a coupling projection, scale convention and cumulative truncation bound for a chosen lattice or field theory"
      "model-dependent RG analysis"
    |>.addObligationText "thermodynamic and critical limits"
      "establish volume-uniform estimates before interpreting fixed-point defects or readouts as critical physics"
      "finite-size scaling analysis"

example : package.claimCount = 6 := rfl
example : package.obligationCount = 3 := rfl
example : package.hasErrors = false := by decide

end LeanPhy.Examples.FiniteLatticeResearch
