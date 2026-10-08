import LeanPhy.Examples.SecondOrderDeformationResearch
import LeanPhy.Examples.AdjointDeformationResearch

/-!
# Normalize, solve, and transport second-order deformations

The Heisenberg example reduces nine cochain coordinates to five actual H²
coordinates. A zero correction in normalized generators transports to a
nonzero correction in the original generators. Direct solving and normalized
solving may choose different corrections; their difference is a cocycle.
-/
namespace LeanPhy.Examples.DeformationGaugeResearch

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieDeformation LeanPhy.Mathematics.LieCochainCoordinates
open LeanPhy.Generated LeanPhy.Workflow
open SecondOrderDeformationResearch
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1600000
noncomputable section

/-- Omitting the quadratic term in the inverse would give a nonzero top component. -/
theorem inverse_identity_generators (x u v : ℚ) :
    (secondGauge (LinearMap.id : ℚ →ₗ[ℚ] ℚ) 0).symm (x,u,v) = (x,u-x,v-u+x) := by
  simp [secondGauge_symm_apply]

theorem heisenberg_normalized_equations (a : Fin 5 → ℚ) :
    HeisenbergSecondOrder.representativeObstructionValues a =
      ![a 0*a 4-a 1*a 3,-(a 0*a 2+a 1*a 4)] := by
  ext i
  fin_cases i <;> simp [HeisenbergSecondOrder.representativeObstructionValues] <;> ring

theorem heisenberg_test_on_classes (ω : HeisenbergSecondOrder.C2)
    (hω : IsTwoCocycle HeisenbergSecondOrder.coefficients ω) :
    SecondExtendable ω ↔ HeisenbergSecondOrder.representativeObstructionValues
      (HeisenbergSecondOrder.reduction.project ω) = 0 :=
  HeisenbergSecondOrder.normalized_extension_iff ω hω

theorem heisenberg_obstruction_invariant (ω η : HeisenbergSecondOrder.C2)
    (E : Equivalence ω η) :
    HeisenbergSecondOrder.secondOrderSolver.obstructionCoordinates ω =
      HeisenbergSecondOrder.secondOrderSolver.obstructionCoordinates η :=
  HeisenbergSecondOrder.secondOrderSolver.obstructionCoordinates_equivalence E

def direction (t u : ℚ) : HeisenbergSecondOrder.C2 :=
  HeisenbergSecondOrder.twoFrom (cancellable t u)

theorem direction_closed (t u : ℚ) : IsTwoCocycle HeisenbergSecondOrder.coefficients (direction t u) :=
  (HeisenbergSecondOrder.closed_coordinates _).mpr (cancellable_conditions t u).1

theorem computed_class_coordinates (t u : ℚ) :
    HeisenbergSecondOrder.reduction.project (direction t u) = ![-u,t,0,0,0] := by
  change HeisenbergSecondOrderCE.project.toLin' (HeisenbergSecondOrder.twoCoordinates
    (HeisenbergSecondOrder.twoCoordinates.symm (cancellable t u))) = _
  rw [LinearEquiv.apply_symm_apply]
  ext i
  fin_cases i <;> simp [HeisenbergSecondOrderCE.project,cancellable,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem normalized_conditions (t u : ℚ) :
    HeisenbergSecondOrder.representativeObstructionValues
      (HeisenbergSecondOrder.reduction.project (direction t u)) = 0 := by
  rw [computed_class_coordinates,heisenberg_normalized_equations]
  ext i
  fin_cases i <;> simp

theorem normalized_correction_explicit (t u : ℚ) :
    HeisenbergSecondOrder.normalizedCorrection (direction t u) (direction_closed t u) =
      HeisenbergSecondOrder.twoFrom ![0,0,0,0,0,0,0,t*u,0] := by
  have hr : HeisenbergSecondOrder.reduction.represent ![-u,t,0,0,0] =
      HeisenbergSecondOrder.twoFrom ![-u,t,0,0,0,0,0,0,0] := by
    change HeisenbergSecondOrder.twoFrom (HeisenbergSecondOrderCE.represent.toLin' ![-u,t,0,0,0]) = _
    congr 1
    ext i
    fin_cases i <;> simp [HeisenbergSecondOrderCE.represent,
      Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  have hp : HeisenbergSecondOrder.reduction.primitive (direction t u) =
      HeisenbergSecondOrder.oneFrom ![0,0,0,0,0,0,-u,0,0] := by
    change HeisenbergSecondOrder.oneFrom (HeisenbergSecondOrderCE.primitive.toLin'
      (HeisenbergSecondOrder.twoCoordinates (HeisenbergSecondOrder.twoCoordinates.symm (cancellable t u)))) = _
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    ext i
    fin_cases i <;> simp [HeisenbergSecondOrderCE.primitive,cancellable,
      Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  have hc : HeisenbergSecondOrder.secondOrderSolver.correction
      (HeisenbergSecondOrder.twoFrom ![-u,t,0,0,0,0,0,0,0]) = 0 := by
    rw [HeisenbergSecondOrder.correction_coordinates]
    have hv : HeisenbergSecondOrder.correctionValues ![-u,t,0,0,0,0,0,0,0] = 0 := by
      ext i
      fin_cases i <;> simp [HeisenbergSecondOrder.correctionValues]
    rw [hv]
    apply LieCochain2.ext
    intro x y
    ext r
    fin_cases r <;> simp [HeisenbergSecondOrder.twoFrom]
  refine (LieDeformation.Reduction.correctionFromRepresentative_eq
    HeisenbergSecondOrder.reduction HeisenbergSecondOrder.secondOrderSolver
    (direction t u) (direction_closed t u)).trans ?_
  erw [computed_class_coordinates, hr, hp, hc]
  apply LieCochain2.ext
  intro x y
  ext r
  fin_cases r <;>
    simp [transportCorrection, HeisenbergSecondOrder.twoFrom, HeisenbergSecondOrder.oneFrom,
      HeisenbergSecondOrder.algebra, HeisenbergSecondOrder.bracket, adjointLieModule,
      differential1, direction, cancellable] <;> ring

def normalizedModel (t u : ℚ) : LeanPhy.Mathematics.LieAlgebra ℚ (Space × Space × Space) :=
  HeisenbergSecondOrder.normalizedModel (direction t u) (direction_closed t u) (normalized_conditions t u)

theorem normalized_model_bracket (t u : ℚ) :
    (normalizedModel t u).bracket = secondBracket (direction t u)
      (HeisenbergSecondOrder.twoFrom ![0,0,0,0,0,0,0,t*u,0]) := by
  change secondBracket (direction t u)
    (HeisenbergSecondOrder.normalizedCorrection (direction t u) (direction_closed t u)) = _
  rw [normalized_correction_explicit]

def normalizationEquivalence (t u : ℚ) :=
  HeisenbergSecondOrder.normalizationEquivalence (direction t u) (direction_closed t u) (normalized_conditions t u)

theorem normalization_preserves_bracket (t u : ℚ) (x y : Space × Space × Space) :
    (normalizationEquivalence t u).linearEquiv
      ((normalizationEquivalence t u).sourceModel.bracket x y) =
    (normalizationEquivalence t u).targetModel.bracket
      ((normalizationEquivalence t u).linearEquiv x) ((normalizationEquivalence t u).linearEquiv y) :=
  (normalizationEquivalence t u).map_bracket x y

theorem normalization_commutes_parameter (t u : ℚ) (x : Space × Space × Space) :
    (normalizationEquivalence t u).linearEquiv (secondEpsilon (R := ℚ) x) =
      secondEpsilon (R := ℚ) ((normalizationEquivalence t u).linearEquiv x) :=
  (normalizationEquivalence t u).map_epsilon x

theorem chosen_corrections_differ (t u : ℚ) (h : t*u ≠ 0) :
    HeisenbergSecondOrder.normalizedCorrection (direction t u) (direction_closed t u) ≠
      HeisenbergSecondOrder.twoFrom (HeisenbergSecondOrder.correctionValues (cancellable t u)) := by
  rw [normalized_correction_explicit,cancellable_correction]
  intro heq
  have hh := congrArg (fun ω : HeisenbergSecondOrder.C2 => ω (e 0) (e 2) 0) heq
  exact h (by simpa [HeisenbergSecondOrder.twoFrom,e] using hh.symm)

theorem correction_difference_closed (t u : ℚ) :
    IsTwoCocycle HeisenbergSecondOrder.coefficients
      (HeisenbergSecondOrder.normalizedCorrection (direction t u) (direction_closed t u) -
        HeisenbergSecondOrder.twoFrom (HeisenbergSecondOrder.correctionValues (cancellable t u))) := by
  apply (HeisenbergSecondOrder.all_corrections_iff _ _ (cancellable_conditions t u).2).mp
  exact HeisenbergSecondOrder.normalizedCorrection_cancels _ _ (normalized_conditions t u)

theorem obstructed_class_no_extension (ω : HeisenbergSecondOrder.C2)
    (E : Equivalence ω (HeisenbergSecondOrder.twoFrom (heisenbergFamily ![1,0,1,0,0]))) :
    ¬SecondExtendable ω := by
  intro h
  exact heisenberg_no_correction (E.secondExtendable_iff.mp h)

theorem sl2_closed_extends (ω : Sl2Adjoint.C2)
    (hω : IsTwoCocycle Sl2Adjoint.coefficients ω) : SecondExtendable ω :=
  (AdjointDeformationResearch.removeSl2 ω hω).secondExtendable_iff.mpr secondExtendable_zero

def package : TheoryPackage :=
  TheoryPackage.empty "Second-order changes of generators" "symmetry algebra exploration"
    |>.addAssumptionText "declared adjoint models"
      "rational Heisenberg and sl2 brackets with canonical adjoint coefficients; closedness and equivalence retained explicitly"
      "examples/lie-cohomology/second-order/heisenberg.json; examples/lie-cohomology/adjoint/sl2.json"
    |>.addTheoremWithAssumptions "quadratic inverse term" "the inverse identity generator change retains its necessary quadratic term"
      "LeanPhy.Examples.DeformationGaugeResearch.inverse_identity_generators" ["declared adjoint models"] inverse_identity_generators
    |>.addTheoremWithAssumptions "five-coordinate obstruction equations" "the complete Heisenberg obstruction is expressed in five H2 coordinates"
      "LeanPhy.Examples.DeformationGaugeResearch.heisenberg_normalized_equations" ["declared adjoint models"] heisenberg_normalized_equations
    |>.addTheoremWithAssumptions "extension test on H2" "a closed direction extends exactly when its representative obstruction vanishes"
      "LeanPhy.Examples.DeformationGaugeResearch.heisenberg_test_on_classes" ["declared adjoint models"] heisenberg_test_on_classes
    |>.addTheoremWithAssumptions "obstruction invariance" "first-order equivalence preserves the actual computed obstruction coordinates"
      "LeanPhy.Examples.DeformationGaugeResearch.heisenberg_obstruction_invariant" ["declared adjoint models"] heisenberg_obstruction_invariant
    |>.addTheoremWithAssumptions "closed unnormalized family" "the original two-parameter direction is closed"
      "LeanPhy.Examples.DeformationGaugeResearch.direction_closed" ["declared adjoint models"] direction_closed
    |>.addTheoremWithAssumptions "computed H2 coordinates" "the two-parameter direction has coordinates minus u and t"
      "LeanPhy.Examples.DeformationGaugeResearch.computed_class_coordinates" ["declared adjoint models"] computed_class_coordinates
    |>.addTheoremWithAssumptions "solvable normalized family" "the representative obstruction equations vanish for the displayed family"
      "LeanPhy.Examples.DeformationGaugeResearch.normalized_conditions" ["declared adjoint models"] normalized_conditions
    |>.addTheoremWithAssumptions "transported correction" "normalized solving produces t times u in the e1,e2 bracket"
      "LeanPhy.Examples.DeformationGaugeResearch.normalized_correction_explicit" ["declared adjoint models"] normalized_correction_explicit
    |>.addTheoremWithAssumptions "transported actual Lie model" "the actual second-jet Lie algebra has the transported correction bracket"
      "LeanPhy.Examples.DeformationGaugeResearch.normalized_model_bracket" ["declared adjoint models"] normalized_model_bracket
    |>.addTheoremWithAssumptions "second-order bracket equivalence" "the computed invertible normalization map preserves the full second-jet bracket"
      "LeanPhy.Examples.DeformationGaugeResearch.normalization_preserves_bracket" ["declared adjoint models"] normalization_preserves_bracket
    |>.addTheoremWithAssumptions "formal parameter compatibility" "the computed normalization commutes with multiplication by the formal parameter"
      "LeanPhy.Examples.DeformationGaugeResearch.normalization_commutes_parameter" ["declared adjoint models"] normalization_commutes_parameter
    |>.addTheoremWithAssumptions "distinct valid corrections" "direct and normalized solvers choose different corrections when t times u is nonzero"
      "LeanPhy.Examples.DeformationGaugeResearch.chosen_corrections_differ" ["declared adjoint models"] chosen_corrections_differ
    |>.addTheoremWithAssumptions "correction freedom is a cocycle" "the difference of the two computed corrections is a closed adjoint cochain"
      "LeanPhy.Examples.DeformationGaugeResearch.correction_difference_closed" ["declared adjoint models"] correction_difference_closed
    |>.addTheoremWithAssumptions "whole-class obstruction" "every direction equivalent to the obstructed representative fails to extend"
      "LeanPhy.Examples.DeformationGaugeResearch.obstructed_class_no_extension" ["declared adjoint models"] obstructed_class_no_extension
    |>.addTheoremWithAssumptions "sl2 second-order extension" "every closed sl2 direction admits a second-order extension through its trivializing equivalence"
      "LeanPhy.Examples.DeformationGaugeResearch.sl2_closed_extends" ["declared adjoint models"] sl2_closed_extends
    |>.addBoundaryText "order-two equivalence"
      "explicit invertible generator changes through second order; original generators fixed modulo the formal parameter; no H3 computation, all-orders extension, analytic convergence or group integration"
    |>.addObligationText "physical interpretation"
      "identify symmetry generators and allowed changes of generators with a physical model" "research model"

def project : ResearchProject := ResearchProject.ofPackages "Deformation normalization research" [package]
def manifest : ResearchManifest :=
  ResearchManifest.ofProject "Deformation normalization research manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Mathematics.LieDeformationGauge", "LeanPhy.Examples.DeformationGaugeResearch",
      "LeanPhy.Examples.Generated.HeisenbergSecondOrder", "LeanPhy.Examples.Generated.Sl2Adjoint",
      "examples/lie-cohomology/second-order/heisenberg.json", "examples/lie-cohomology/adjoint/sl2.json",
      "scripts/second_order_deformation.py", "scripts/lie_cohomology.py", "scripts/reduce_cohomology.py",
      "lean-toolchain", "lakefile.toml"]
example : project.claimCount = 15 := rfl
example : project.obligationCount = 1 := rfl
example : project.diagnosticCount = 0 := by decide
def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args

end
end LeanPhy.Examples.DeformationGaugeResearch
