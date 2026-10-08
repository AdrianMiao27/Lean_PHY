import LeanPhy.Examples.Generated.AffineTrivial
import LeanPhy.Examples.Generated.AffineCharacter
import LeanPhy.Examples.Generated.SolvableVector
import LeanPhy.CLI

/-!
# Research calculations generated from structure constants

Changing the coefficient action changes the affine H2 dimension. A solvable
three-dimensional algebra with two-dimensional coefficients supplies a second
example with nonzero d2, four H2 parameters, and a checked exactness decision.
All coordinate and matrix-identification proofs are generated and compiled.
-/

namespace LeanPhy.Examples.StructureConstantResearch

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology LeanPhy.Workflow
open LeanPhy.Mathematics.LieCochainCoordinates

set_option maxSynthPendingDepth 5

theorem affine_trivial_dimension :
    Module.finrank ℚ (H2 Generated.AffineTrivial.coefficients) = 0 :=
  Generated.AffineTrivial.h2_finrank

theorem affine_character_dimension :
    Module.finrank ℚ (H2 Generated.AffineCharacter.coefficients) = 1 :=
  Generated.AffineCharacter.h2_finrank

theorem same_affine_algebra :
    Generated.AffineTrivial.algebra = Generated.AffineCharacter.algebra := rfl

theorem coefficient_dependence :
    Module.finrank ℚ (H2 Generated.AffineTrivial.coefficients) ≠
      Module.finrank ℚ (H2 Generated.AffineCharacter.coefficients) := by
  rw [affine_trivial_dimension, affine_character_dimension]
  decide

theorem solvable_vector_dimension :
    Module.finrank ℚ (H2 Generated.SolvableVector.coefficients) = 4 :=
  Generated.SolvableVector.h2_finrank

/-- A cochain whose next differential is nonzero: closedness cannot be skipped. -/
def nonclosed : Generated.SolvableVector.C2 :=
  Generated.SolvableVector.twoFrom (Pi.single 4 1)

theorem nonclosed_not_cocycle : ¬IsTwoCocycle Generated.SolvableVector.coefficients nonclosed := by
  intro h
  have hz := congrArg (fun t => t (e 0) (e 1) (e 2) 0) h
  norm_num [nonclosed, differential2_apply, Generated.SolvableVector.twoFrom,
    Generated.SolvableVector.coefficients, Generated.SolvableVector.action,
    Generated.SolvableVector.algebra, Generated.SolvableVector.bracket, e] at hz

theorem nonclosed_zero_coordinates : Generated.SolvableVector.reduction.project nonclosed = 0 := by
  ext r
  fin_cases r <;>
    norm_num [Generated.SolvableVector.reduction, CohomologyReduction.transport,
      MatrixCohomologyReduction.toReduction, Generated.SolvableVectorCE.certificate,
      Generated.SolvableVectorCE.project, Generated.SolvableVector.twoCoordinates,
      Generated.SolvableVector.twoValues, nonclosed, Generated.SolvableVector.twoFrom, e,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem solvable_normal_form (ω : Generated.SolvableVector.C2)
    (hω : IsTwoCocycle Generated.SolvableVector.coefficients ω) :
    differential1 Generated.SolvableVector.coefficients (Generated.SolvableVector.reduction.primitive ω) +
      Generated.SolvableVector.reduction.represent (Generated.SolvableVector.reduction.project ω) = ω :=
  Generated.SolvableVector.normal_form ω hω

theorem solvable_exactness (ω : Generated.SolvableVector.C2)
    (hω : IsTwoCocycle Generated.SolvableVector.coefficients ω) :
    IsTwoCoboundary Generated.SolvableVector.coefficients ω ↔
      Generated.SolvableVector.reduction.project ω = 0 :=
  Generated.SolvableVector.boundary_iff ω hω

theorem solvable_class_coordinates (ω : Generated.SolvableVector.C2)
    (hω : IsTwoCocycle Generated.SolvableVector.coefficients ω) :
    Generated.SolvableVector.h2Equiv (classOf Generated.SolvableVector.coefficients ω hω) =
      Generated.SolvableVector.reduction.project ω := rfl

def package : TheoryPackage :=
  TheoryPackage.empty "Structure constant cohomology" "finite Lie cohomology"
    |>.addAssumptionText "declared models"
      "rational brackets and coefficient actions in affine-trivial, affine-character and solvable-vector JSON inputs"
      "examples/lie-cohomology"
    |>.addTheoremWithAssumptions "affine trivial H2" "the affine algebra has H2 dimension zero for trivial scalar coefficients"
      "LeanPhy.Examples.StructureConstantResearch.affine_trivial_dimension" ["declared models"] affine_trivial_dimension
    |>.addTheoremWithAssumptions "affine character H2" "the supplied nontrivial character gives H2 dimension one"
      "LeanPhy.Examples.StructureConstantResearch.affine_character_dimension" ["declared models"] affine_character_dimension
    |>.addTheoremWithAssumptions "same affine algebra" "the two affine coefficient examples use the identical Lie algebra"
      "LeanPhy.Examples.StructureConstantResearch.same_affine_algebra" ["declared models"] same_affine_algebra
    |>.addTheoremWithAssumptions "coefficient dependence" "changing the coefficient action changes the computed H2 dimension"
      "LeanPhy.Examples.StructureConstantResearch.coefficient_dependence" ["declared models"] coefficient_dependence
    |>.addTheoremWithAssumptions "solvable vector H2" "the declared solvable algebra with vector coefficients has H2 dimension four"
      "LeanPhy.Examples.StructureConstantResearch.solvable_vector_dimension" ["declared models"] solvable_vector_dimension
    |>.addTheoremWithAssumptions "nonclosed cochain" "the supplied two-cochain has nonzero d2"
      "LeanPhy.Examples.StructureConstantResearch.nonclosed_not_cocycle" ["declared models"] nonclosed_not_cocycle
    |>.addTheoremWithAssumptions "zero coordinates without closedness" "the nonclosed cochain has zero class-coordinate projection, so closedness cannot be omitted"
      "LeanPhy.Examples.StructureConstantResearch.nonclosed_zero_coordinates" ["declared models"] nonclosed_zero_coordinates
    |>.addTheoremWithAssumptions "computed normal form" "every closed cochain decomposes into a boundary and a computed representative"
      "LeanPhy.Examples.StructureConstantResearch.solvable_normal_form" ["declared models"] solvable_normal_form
    |>.addTheoremWithAssumptions "computed exactness" "a closed cochain is exact iff its four class coordinates vanish"
      "LeanPhy.Examples.StructureConstantResearch.solvable_exactness" ["declared models"] solvable_exactness
    |>.addTheoremWithAssumptions "quotient coordinates" "computed coordinates are the image under the actual H2 quotient equivalence"
      "LeanPhy.Examples.StructureConstantResearch.solvable_class_coordinates" ["declared models"] solvable_class_coordinates
    |>.addBoundaryText "finite rational scope"
      "finite rational models and supplied representations; no automatic interpretation as physical states or anomalies"
    |>.addObligationText "physical model identification"
      "justify the selected brackets, coefficient action, normalization and relation to the target physical theory"
      "research model"

def project : ResearchProject := ResearchProject.ofPackages "Generated Lie cohomology" [package]

def manifest : ResearchManifest :=
  ResearchManifest.ofProject "Structure constant research manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Examples.StructureConstantResearch", "scripts/lie_cohomology.py",
      "examples/lie-cohomology/affine-trivial.json", "examples/lie-cohomology/affine-character.json",
      "examples/lie-cohomology/solvable-vector.json", "lean-toolchain", "lakefile.toml"]

example : project.claimCount = 10 := rfl
example : project.obligationCount = 1 := rfl
example : project.diagnosticCount = 0 := by decide

def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args

end LeanPhy.Examples.StructureConstantResearch
