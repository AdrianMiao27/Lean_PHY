import LeanPhy.Examples.Generated.AffineFourThird
import LeanPhy.Examples.Generated.HeisenbergThird
import LeanPhy.Examples.Generated.AbelianThird
import LeanPhy.Examples.Generated.Sl2Third
import LeanPhy.CLI

/-! Actual H³ calculations and intrinsic obstructions for symmetry exploration. -/
namespace LeanPhy.Examples.ThirdCohomologyResearch
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates LeanPhy.Mathematics.LieDeformation
open LeanPhy.Generated LeanPhy.Workflow
set_option maxSynthPendingDepth 7
set_option maxHeartbeats 1600000
noncomputable section

theorem affine_h3_dimension : Module.finrank ℚ (H3 AffineFourThird.coefficients) = 1 :=
  AffineFourThird.h3_finrank
theorem heisenberg_h3_dimension : Module.finrank ℚ (H3 HeisenbergThird.coefficients) = 2 :=
  HeisenbergThird.h3_finrank
theorem abelian_h3_dimension : Module.finrank ℚ (H3 AbelianThird.coefficients) = 3 :=
  AbelianThird.h3_finrank
theorem sl2_h3_dimension : Module.finrank ℚ (H3 Sl2Third.coefficients) = 0 :=
  Sl2Third.h3_finrank

/-- This alternating cochain is excluded from H³ by its outgoing differential. -/
def nonclosed : AffineFourThird.C3 := AffineFourThird.threeFrom ![0,0,0,1]

theorem outgoing_differential_nonzero :
    differential3 AffineFourThird.coefficients nonclosed (e 0) (e 1) (e 2) (e 3) 0 = -1 := by
  norm_num [differential3Expr,AffineFourThird.coefficients,AffineFourThird.action,
    AffineFourThird.algebra,AffineFourThird.bracket,nonclosed,AffineFourThird.threeFrom,
    AffineFourThird.threeLinear,AffineFourThird.threeExpr,e]

theorem nonclosed_not_cocycle : ¬IsThreeCocycle AffineFourThird.coefficients nonclosed := by
  intro h
  have hv := congrFun ((isThreeCocycle_iff _ _).mp h (e 0) (e 1) (e 2) (e 3)) 0
  rw [outgoing_differential_nonzero] at hv
  norm_num at hv

/-- A projection is not an exactness decision until closedness is checked. -/
theorem nonclosed_projection_zero : AffineFourThird.thirdReduction.project nonclosed = 0 := by
  change AffineFourThirdThirdCE.project.toLin' (AffineFourThird.threeValues nonclosed) = 0
  ext i; fin_cases i
  norm_num [AffineFourThirdThirdCE.project,AffineFourThird.threeValues,AffineFourThird.readThird,
    nonclosed,AffineFourThird.threeFrom,AffineFourThird.threeLinear,AffineFourThird.threeExpr,e,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem nonclosed_not_boundary : ¬IsThreeCoboundary AffineFourThird.coefficients nonclosed :=
  fun h => nonclosed_not_cocycle (three_coboundary_is_cocycle _ h)

theorem affine_generator_nonzero :
    classOfThree AffineFourThird.coefficients (AffineFourThird.thirdReduction.represent ![1])
      (AffineFourThird.thirdReduction.represent_closed ![1]) ≠ 0 := by
  intro h
  have hh := congrArg AffineFourThird.h3Equiv h
  change AffineFourThird.thirdReduction.project (AffineFourThird.thirdReduction.represent ![1]) =
    AffineFourThird.h3Equiv 0 at hh
  rw [AffineFourThird.thirdReduction.project_represent,map_zero] at hh
  have h0 := congrFun hh 0
  norm_num at h0

/-- All five H² coordinates are retained; the intrinsic target has dimension two. -/
theorem heisenberg_intrinsic_equations (a : Fin 5 → ℚ) :
    HeisenbergThird.intrinsicObstruction (HeisenbergThird.reduction.represent a) =
      ![a 0*a 4-a 1*a 3,-(a 0*a 2+a 1*a 4)] := by
  change HeisenbergThirdThirdCE.project.toLin'
    (HeisenbergThird.threeValues (obstructionCochain
      (HeisenbergThird.twoFrom (HeisenbergThirdCE.represent.toLin' a)))) = _
  ext i; fin_cases i <;>
    simp [HeisenbergThirdThirdCE.project,HeisenbergThirdCE.represent,HeisenbergThird.threeValues,
      HeisenbergThird.readThird,obstructionCochain,obstructionTrilinear,obstruction,
      HeisenbergThird.twoFrom,e,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem heisenberg_intrinsic_nonzero :
    obstructionClass (HeisenbergThird.reduction.represent ![1,0,1,0,0])
      (HeisenbergThird.reduction.represent_closed _) ≠ 0 := by
  intro h
  have hh := congrArg HeisenbergThird.h3Equiv h
  change HeisenbergThird.intrinsicObstruction (HeisenbergThird.reduction.represent ![1,0,1,0,0]) = HeisenbergThird.h3Equiv 0 at hh
  rw [heisenberg_intrinsic_equations,map_zero] at hh
  have h1 := congrFun hh 1
  norm_num at h1

theorem heisenberg_no_extension :
    ¬SecondExtendable (HeisenbergThird.reduction.represent ![1,0,1,0,0]) := by
  rw [secondExtendable_iff_obstructionClass_zero _ (HeisenbergThird.reduction.represent_closed _)]
  exact heisenberg_intrinsic_nonzero

theorem sl2_extends_from_h3 (ω : Sl2Third.C2) (hω : IsTwoCocycle Sl2Third.coefficients ω) :
    SecondExtendable ω := by
  apply (Sl2Third.intrinsic_extension_iff ω hω).mpr
  exact Subsingleton.elim _ _

/-- Gauge changes preserve the intrinsic class, not only a zero/nonzero flag. -/
theorem heisenberg_class_invariant (ω η : HeisenbergThird.C2) (E : Equivalence ω η) :
    obstructionClass ω E.source_cocycle = obstructionClass η E.target_cocycle :=
  obstructionClass_equivalence E

def package : TheoryPackage :=
  TheoryPackage.empty "Intrinsic Lie deformation obstructions" "symmetry algebra exploration"
    |>.addAssumptionText "declared rational models"
      "rational structure constants; trivial scalar coefficients for the four-dimensional affine example; canonical adjoint coefficients for the three-dimensional examples"
      "examples/lie-cohomology/third/"
    |>.addTheoremWithAssumptions "four-dimensional H3" "the actual scalar H3 of aff(1) plus a two-dimensional abelian algebra has dimension one"
      "LeanPhy.Examples.ThirdCohomologyResearch.affine_h3_dimension" ["declared rational models"] affine_h3_dimension
    |>.addTheoremWithAssumptions "Heisenberg H3" "the canonical adjoint H3 of the Heisenberg algebra has dimension two"
      "LeanPhy.Examples.ThirdCohomologyResearch.heisenberg_h3_dimension" ["declared rational models"] heisenberg_h3_dimension
    |>.addTheoremWithAssumptions "abelian H3" "the canonical adjoint H3 of the three-dimensional abelian algebra has dimension three"
      "LeanPhy.Examples.ThirdCohomologyResearch.abelian_h3_dimension" ["declared rational models"] abelian_h3_dimension
    |>.addTheoremWithAssumptions "sl2 H3" "the canonical adjoint H3 of sl2 over the rationals vanishes"
      "LeanPhy.Examples.ThirdCohomologyResearch.sl2_h3_dimension" ["declared rational models"] sl2_h3_dimension
    |>.addTheoremWithAssumptions "nonzero outgoing differential" "the displayed alternating three-cochain has a nonzero degree-three differential"
      "LeanPhy.Examples.ThirdCohomologyResearch.outgoing_differential_nonzero" ["declared rational models"] outgoing_differential_nonzero
    |>.addTheoremWithAssumptions "closedness excludes a cochain" "the displayed alternating cochain is not a three-cocycle"
      "LeanPhy.Examples.ThirdCohomologyResearch.nonclosed_not_cocycle" ["declared rational models"] nonclosed_not_cocycle
    |>.addTheoremWithAssumptions "zero projection without closedness" "the same nonclosed cochain has zero reduction projection"
      "LeanPhy.Examples.ThirdCohomologyResearch.nonclosed_projection_zero" ["declared rational models"] nonclosed_projection_zero
    |>.addTheoremWithAssumptions "zero projection is insufficient" "the nonclosed zero-projection cochain is not a boundary"
      "LeanPhy.Examples.ThirdCohomologyResearch.nonclosed_not_boundary" ["declared rational models"] nonclosed_not_boundary
    |>.addTheoremWithAssumptions "nonzero quotient class" "the displayed closed representative has a nonzero actual H3 class"
      "LeanPhy.Examples.ThirdCohomologyResearch.affine_generator_nonzero" ["declared rational models"] affine_generator_nonzero
    |>.addTheoremWithAssumptions "intrinsic quadratic equations" "the Heisenberg intrinsic H3 obstruction is an explicit pair of quadratics in five H2 coordinates"
      "LeanPhy.Examples.ThirdCohomologyResearch.heisenberg_intrinsic_equations" ["declared rational models"] heisenberg_intrinsic_equations
    |>.addTheoremWithAssumptions "nonzero intrinsic obstruction" "the displayed first-order Heisenberg class has a nonzero H3 obstruction"
      "LeanPhy.Examples.ThirdCohomologyResearch.heisenberg_intrinsic_nonzero" ["declared rational models"] heisenberg_intrinsic_nonzero
    |>.addTheoremWithAssumptions "no second-order extension" "no correction yields a second-order Lie model for that class"
      "LeanPhy.Examples.ThirdCohomologyResearch.heisenberg_no_extension" ["declared rational models"] heisenberg_no_extension
    |>.addTheoremWithAssumptions "extension from vanishing H3" "every closed sl2 direction extends through second order by the computed H3 criterion"
      "LeanPhy.Examples.ThirdCohomologyResearch.sl2_extends_from_h3" ["declared rational models"] sl2_extends_from_h3
    |>.addTheoremWithAssumptions "intrinsic gauge invariance" "first-order equivalence preserves the actual H3 obstruction class"
      "LeanPhy.Examples.ThirdCohomologyResearch.heisenberg_class_invariant" ["declared rational models"] heisenberg_class_invariant
    |>.addBoundaryText "finite order and declared coefficients"
      "actual H3 and second-order extension only; no all-orders formal integrability, convergence, group integration or physical realization"
    |>.addObligationText "physical interpretation"
      "identify the Lie generators, coefficient module and permitted equivalences with the proposed physical system" "research model"

def project : ResearchProject := ResearchProject.ofPackages "Intrinsic obstruction research" [package]
def manifest : ResearchManifest :=
  ResearchManifest.ofProject "Intrinsic obstruction research manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Mathematics.LieCohomology3", "LeanPhy.Mathematics.FiniteLieCohomology3",
      "LeanPhy.Mathematics.LieDeformationObstruction", "LeanPhy.Examples.ThirdCohomologyResearch",
      "LeanPhy.Examples.Generated.AffineFourThird", "LeanPhy.Examples.Generated.HeisenbergThird",
      "LeanPhy.Examples.Generated.AbelianThird", "LeanPhy.Examples.Generated.Sl2Third",
      "examples/lie-cohomology/third/affine-four.json", "examples/lie-cohomology/third/heisenberg.json",
      "examples/lie-cohomology/third/abelian.json", "examples/lie-cohomology/third/sl2.json",
      "scripts/third_cohomology.py", "scripts/third_cochain_coordinates.py", "scripts/lie_cohomology.py", "scripts/reduce_cohomology.py",
      "lean-toolchain", "lakefile.toml"]
example : project.claimCount = 14 := rfl
example : project.obligationCount = 1 := rfl
example : project.diagnosticCount = 0 := by decide
def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args

end
end LeanPhy.Examples.ThirdCohomologyResearch
