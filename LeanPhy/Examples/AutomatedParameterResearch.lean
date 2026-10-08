import LeanPhy.Examples.Generated.SolvableStrata
import LeanPhy.Examples.Generated.DeterminantStrata
import LeanPhy.Mathematics.SolvableLieFamily
import LeanPhy.CLI

/-!
# From automatic parameter branches to actual Lie cohomology

The matrix solver emits eight branches for the declared solvable family.
The bridges below identify its input matrices with both full CE differentials,
so its computed quotient equivalence describes actual H2 at every parameter.
An independent handwritten all-parameter formula checks the meaning of the tree.
The second generated family exhibits intersecting determinant-zero loci.
-/

namespace LeanPhy.Examples.AutomatedParameterResearch

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.SolvableLieFamily LeanPhy.Generated LeanPhy.Workflow
open scoped _root_.Classical

noncomputable section
set_option maxSynthPendingDepth 5

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem first_matrix (a b t : K) :
    (SolvableStrata.d1 ![a, b, t]).toLin' = DiagonalCohomology.diagonal (boundaryWeights a b t) := by
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i <;> simp [SolvableStrata.d1, DiagonalCohomology.diagonal, boundaryWeights,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg]

omit [CharZero K] in
theorem second_matrix (a b t : K) :
    (SolvableStrata.d2 ![a, b, t]).toLin' = DiagonalCohomology.diagonal (closureWeights a b t) := by
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i <;> simp [SolvableStrata.d2, DiagonalCohomology.diagonal, closureWeights,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg,
    neg_add_rev, add_assoc, add_comm, add_left_comm]

theorem first_ce_bridge (a b t : K) (φ : Space K →ₗ[K] K) :
    twoCoordinates a b t (differential1 (coefficients a b t) φ) =
      (SolvableStrata.d1 ![a, b, t]).toLin' (oneCoordinates φ) := by
  rw [first_matrix]
  exact differential1_coordinates a b t φ

theorem second_ce_bridge (a b t : K) (ω : C2 a b t) :
    (SolvableStrata.d2 ![a, b, t]).toLin' (twoCoordinates a b t ω) =
      readThird (differential2 (coefficients a b t) ω) := by
  rw [second_matrix]
  exact differential2_coordinates a b t ω

def automaticReduction (a b t : K) :
    Reduction (coefficients a b t) (Fin (SolvableStrata.dimension ![a, b, t]) → K) :=
  (SolvableStrata.certificate ![a, b, t]).toReduction.transport
    oneCoordinates (twoCoordinates a b t) readThird
    (first_ce_bridge a b t) (second_ce_bridge a b t)
    (readThird_detect a b t)

def automaticH2Equiv (a b t : K) :
    H2 (coefficients a b t) ≃ₗ[K] (Fin (SolvableStrata.dimension ![a, b, t]) → K) :=
  (automaticReduction a b t).h2Equiv _

theorem automatic_h2_dimension (a b t : K) :
    Module.finrank K (H2 (coefficients a b t)) = SolvableStrata.dimension ![a, b, t] := by
  rw [(automaticH2Equiv a b t).finrank_eq]
  simp

/-- The full generated tree agrees with an independent all-parameter theorem. -/
theorem tree_matches_resonances (a b t : K) :
    SolvableStrata.dimension ![a, b, t] =
      (if t = a then 1 else 0) + (if t = b then 1 else 0) + (if t = a + b then 1 else 0) := by
  rw [← automatic_h2_dimension, h2_finrank]

theorem automatic_exactness (a b t : K) (ω : C2 a b t)
    (hω : IsTwoCocycle (coefficients a b t) ω) :
    IsTwoCoboundary (coefficients a b t) ω ↔ (automaticReduction a b t).project ω = 0 :=
  (automaticReduction a b t).exact_iff ω hω

theorem automatic_normal_form (a b t : K) (ω : C2 a b t)
    (hω : IsTwoCocycle (coefficients a b t) ω) :
    differential1 (coefficients a b t) ((automaticReduction a b t).primitive ω) +
      (automaticReduction a b t).represent ((automaticReduction a b t).project ω) = ω :=
  (automaticReduction a b t).normal_form ω hω

theorem computed_generic_dimension : Module.finrank ℝ (H2 (coefficients (1 : ℝ) 1 0)) = 0 := by
  rw [automatic_h2_dimension]
  norm_num [SolvableStrata.dimension]

theorem computed_double_resonance : Module.finrank ℝ (H2 (coefficients (1 : ℝ) 1 1)) = 2 := by
  rw [automatic_h2_dimension]
  norm_num [SolvableStrata.dimension]

theorem computed_full_degeneracy : Module.finrank ℝ (H2 (coefficients (0 : ℝ) 0 0)) = 3 := by
  rw [automatic_h2_dimension]
  norm_num [SolvableStrata.dimension]

abbrev DeterminantCohomology (s t : K) :=
  CohomologyReduction.Cohomology (DeterminantStrata.d1 ![s, t]).toLin'
    (DeterminantStrata.d2 ![s, t]).toLin'

theorem determinant_generic (s t : K) (hm : s - t ≠ 0) (hp : s + t ≠ 0) :
    Module.finrank K (DeterminantCohomology s t) = 0 := by
  rw [DeterminantStrata.finrank_eq]
  simp only [DeterminantStrata.dimension, Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases hs : s = 0
  · have ht : t ≠ 0 := by intro ht; apply hm; simp [hs, ht]
    simp [hs, ht]
  · have hm' : s + -t ≠ 0 := by simpa [sub_eq_add_neg] using hm
    simp [hs, hm', hp]

theorem determinant_positive_locus : Module.finrank ℝ (DeterminantCohomology (1 : ℝ) 1) = 1 := by
  rw [DeterminantStrata.finrank_eq]
  norm_num [DeterminantStrata.dimension]

theorem determinant_negative_locus : Module.finrank ℝ (DeterminantCohomology (1 : ℝ) (-1)) = 1 := by
  rw [DeterminantStrata.finrank_eq]
  norm_num [DeterminantStrata.dimension]

theorem determinant_intersection : Module.finrank ℝ (DeterminantCohomology (0 : ℝ) 0) = 2 := by
  rw [DeterminantStrata.finrank_eq]
  norm_num [DeterminantStrata.dimension]

def package : TheoryPackage :=
  TheoryPackage.empty "Automatically stratified cohomology" "parameter exploration"
    |>.addAssumptionText "declared polynomial families"
      "the generated solvable CE matrices and the symmetric two-by-two matrix, with their supplied coordinates over characteristic-zero fields"
      "LeanPhy.Examples.Generated.SolvableStrata; LeanPhy.Examples.Generated.DeterminantStrata"
    |>.addTheoremWithAssumptions "first CE bridge" "the first generated matrix is the full CE differential in the declared coordinates"
      "LeanPhy.Examples.AutomatedParameterResearch.first_ce_bridge" ["declared polynomial families"] @first_ce_bridge.{0}
    |>.addTheoremWithAssumptions "second CE bridge" "the second generated matrix agrees with the next CE differential in detecting coordinates"
      "LeanPhy.Examples.AutomatedParameterResearch.second_ce_bridge" ["declared polynomial families"] @second_ce_bridge.{0}
    |>.addTheoremWithAssumptions "computed H2 dimension" "the exhaustive generated tree computes actual H2 at every parameter"
      "LeanPhy.Examples.AutomatedParameterResearch.automatic_h2_dimension" ["declared polynomial families"] @automatic_h2_dimension.{0}
    |>.addTheoremWithAssumptions "tree and resonance formula" "the generated tree agrees with the independent complete resonance formula"
      "LeanPhy.Examples.AutomatedParameterResearch.tree_matches_resonances" ["declared polynomial families"] @tree_matches_resonances.{0}
    |>.addTheoremWithAssumptions "computed exactness" "a closed cochain is exact iff its computed class coordinates vanish"
      "LeanPhy.Examples.AutomatedParameterResearch.automatic_exactness" ["declared polynomial families"] @automatic_exactness.{0}
    |>.addTheoremWithAssumptions "computed normal form" "the computed primitive and representative decompose every closed cochain"
      "LeanPhy.Examples.AutomatedParameterResearch.automatic_normal_form" ["declared polynomial families"] @automatic_normal_form.{0}
    |>.addTheoremWithAssumptions "generic Lie point" "the computed real H2 dimension at (1,1,0) is zero"
      "LeanPhy.Examples.AutomatedParameterResearch.computed_generic_dimension" ["declared polynomial families"] computed_generic_dimension
    |>.addTheoremWithAssumptions "double Lie resonance" "the computed real H2 dimension at (1,1,1) is two"
      "LeanPhy.Examples.AutomatedParameterResearch.computed_double_resonance" ["declared polynomial families"] computed_double_resonance
    |>.addTheoremWithAssumptions "full Lie degeneracy" "the computed real H2 dimension at (0,0,0) is three"
      "LeanPhy.Examples.AutomatedParameterResearch.computed_full_degeneracy" ["declared polynomial families"] computed_full_degeneracy
    |>.addTheoremWithAssumptions "generic determinant point" "both nonzero determinant factors imply zero middle cohomology"
      "LeanPhy.Examples.AutomatedParameterResearch.determinant_generic" ["declared polynomial families"] @determinant_generic.{0}
    |>.addTheoremWithAssumptions "positive determinant locus" "the real dimension at (1,1) is one"
      "LeanPhy.Examples.AutomatedParameterResearch.determinant_positive_locus" ["declared polynomial families"] determinant_positive_locus
    |>.addTheoremWithAssumptions "negative determinant locus" "the real dimension at (1,-1) is one"
      "LeanPhy.Examples.AutomatedParameterResearch.determinant_negative_locus" ["declared polynomial families"] determinant_negative_locus
    |>.addTheoremWithAssumptions "determinant intersection" "the real dimension at the intersection (0,0) is two"
      "LeanPhy.Examples.AutomatedParameterResearch.determinant_intersection" ["declared polynomial families"] determinant_intersection
    |>.addBoundaryText "conditional symbolic computation"
      "each generated candidate must compile; branches are exhaustive but need not be minimal or proved nonempty; no analytic or physical phase-transition inference"
    |>.addObligationText "physical interpretation"
      "supply the physical model and the interpretation of parameters and cohomology classes" "research model"

def project : ResearchProject := ResearchProject.ofPackages "Automatic parameter research" [package]

def manifest : ResearchManifest :=
  ResearchManifest.ofProject "Automatic parameter research manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Examples.AutomatedParameterResearch", "LeanPhy.Examples.Generated.SolvableStrata",
      "LeanPhy.Examples.Generated.DeterminantStrata", "examples/cohomology/solvable-parameters.json",
      "examples/cohomology/determinant-parameters.json", "scripts/stratify_cohomology.py",
      "scripts/requirements-symbolic.txt", "lean-toolchain", "lakefile.toml"]

example : project.claimCount = 13 := rfl
example : project.obligationCount = 1 := rfl
example : project.diagnosticCount = 0 := by decide

def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args

end
end LeanPhy.Examples.AutomatedParameterResearch
