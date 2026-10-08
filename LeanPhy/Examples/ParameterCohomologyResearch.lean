import LeanPhy.Mathematics.SolvableLieFamily
import LeanPhy.CLI

/-!
# Exploring cohomology jumps without numerical sampling

The three-parameter family is proved over arbitrary fields. This report
specializes it to real parameters, records generic and resonant dimensions,
and shows why a primitive obtained by generic division cannot be reused on a
resonance. No analytic continuity or physical phase-transition claim is made.
-/

namespace LeanPhy.Examples.ParameterCohomologyResearch

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology LeanPhy.Workflow
open LeanPhy.Mathematics.SolvableLieFamily
open scoped _root_.Classical

set_option maxSynthPendingDepth 5

theorem dimension_formula (a b t : ℝ) :
    Module.finrank ℝ (H2 (coefficients a b t)) =
      (if t = a then 1 else 0) + (if t = b then 1 else 0) + (if t = a + b then 1 else 0) :=
  h2_finrank a b t

theorem generic_dimension (a b t : ℝ) (ha : t ≠ a) (hb : t ≠ b) (hab : t ≠ a + b) :
    Module.finrank ℝ (H2 (coefficients a b t)) = 0 := generic_h2_zero a b t ha hb hab

theorem double_resonance : Module.finrank ℝ (H2 (coefficients (1 : ℝ) 1 1)) = 2 := by
  norm_num [h2_finrank]

theorem closure_resonance : Module.finrank ℝ (H2 (coefficients (1 : ℝ) 1 2)) = 1 := by
  norm_num [h2_finrank]

theorem full_degeneracy : Module.finrank ℝ (H2 (coefficients (0 : ℝ) 0 0)) = 3 := by
  norm_num [h2_finrank]

theorem unit_class_jumps (a b t : ℝ) :
    classOf (coefficients a b t) (unit01 a b t) (unit01_closed a b t) ≠ 0 ↔ t = a :=
  unit01_class_nonzero_iff a b t

theorem closure_changes (a b t : ℝ) :
    IsTwoCocycle (coefficients a b t) (unit12 a b t) ↔ t = a + b := unit12_closed_iff a b t

theorem generic_primitive_works (a b t : ℝ) (ha : t ≠ a) (hb : t ≠ b) (hab : t ≠ a + b)
    (ω : C2 a b t) (hω : IsTwoCocycle (coefficients a b t) ω) :
    differential1 (coefficients a b t) ((reduction a b t).primitive ω) = ω :=
  generic_primitive a b t ha hb hab ω hω

theorem generic_primitive_fails_at_resonance :
    differential1 (coefficients (1 : ℝ) 1 1)
      ((reduction (1 : ℝ) 1 1).primitive (unit01 1 1 1)) ≠ unit01 1 1 1 := by
  intro h
  have hex : IsTwoCoboundary (coefficients (1 : ℝ) 1 1) (unit01 1 1 1) := ⟨_, h⟩
  exact ((unit01_exact_iff (1 : ℝ) 1 1).mp hex) rfl

theorem normal_form_at_all_parameters (a b t : ℝ) (ω : C2 a b t)
    (hω : IsTwoCocycle (coefficients a b t) ω) :
    differential1 (coefficients a b t) ((reduction a b t).primitive ω) +
      (reduction a b t).represent ((reduction a b t).project ω) = ω := normal_form a b t ω hω

theorem rational_to_complex_dimension (a b t : ℚ) :
    Module.finrank ℂ (H2 (coefficients (a : ℂ) (b : ℂ) (t : ℂ))) =
      Module.finrank ℚ (H2 (coefficients a b t)) :=
  h2_finrank_map (Rat.castHom ℂ) a b t

theorem same_stratum_dimension (a b t a' b' t' : ℝ)
    (h₀ : t = a ↔ t' = a') (h₁ : t = b ↔ t' = b') (h₂ : t = a + b ↔ t' = a' + b') :
    Module.finrank ℝ (H2 (coefficients a b t)) =
      Module.finrank ℝ (H2 (coefficients a' b' t')) :=
  (stratumEquiv a b t a' b' t' h₀ h₁ h₂).finrank_eq

def package : TheoryPackage :=
  TheoryPackage.empty "Parameter-dependent Lie cohomology" "symbolic cohomology"
    |>.addAssumptionText "declared family"
      "[e0,e1]=a e1, [e0,e2]=b e2, [e1,e2]=0; e0 acts by t on scalar coefficients and e1,e2 act trivially"
      "LeanPhy.Mathematics.SolvableLieFamily"
    |>.addTheoremWithAssumptions "complete dimension formula" "H2 dimension is the sum of the three resonance indicators"
      "LeanPhy.Examples.ParameterCohomologyResearch.dimension_formula" ["declared family"] dimension_formula
    |>.addTheoremWithAssumptions "generic vanishing" "outside all three resonance loci the H2 dimension is zero"
      "LeanPhy.Examples.ParameterCohomologyResearch.generic_dimension" ["declared family"] generic_dimension
    |>.addTheoremWithAssumptions "double resonance" "at a=b=t=1 the H2 dimension is two"
      "LeanPhy.Examples.ParameterCohomologyResearch.double_resonance" ["declared family"] double_resonance
    |>.addTheoremWithAssumptions "closure resonance" "at a=b=1,t=2 the H2 dimension is one"
      "LeanPhy.Examples.ParameterCohomologyResearch.closure_resonance" ["declared family"] closure_resonance
    |>.addTheoremWithAssumptions "full degeneracy" "at a=b=t=0 the H2 dimension is three"
      "LeanPhy.Examples.ParameterCohomologyResearch.full_degeneracy" ["declared family"] full_degeneracy
    |>.addTheoremWithAssumptions "class jumps" "the first unit cocycle has nonzero class exactly when t=a"
      "LeanPhy.Examples.ParameterCohomologyResearch.unit_class_jumps" ["declared family"] unit_class_jumps
    |>.addTheoremWithAssumptions "closedness changes" "the third unit cochain is closed exactly when t=a+b"
      "LeanPhy.Examples.ParameterCohomologyResearch.closure_changes" ["declared family"] closure_changes
    |>.addTheoremWithAssumptions "generic primitive" "the supplied primitive solves every closed cochain away from all resonance loci"
      "LeanPhy.Examples.ParameterCohomologyResearch.generic_primitive_works" ["declared family"] generic_primitive_works
    |>.addTheoremWithAssumptions "resonant primitive obstruction" "the generic primitive fails to solve a nontrivial resonant class"
      "LeanPhy.Examples.ParameterCohomologyResearch.generic_primitive_fails_at_resonance" ["declared family"]
      generic_primitive_fails_at_resonance
    |>.addTheoremWithAssumptions "uniform normal form" "the boundary-plus-representative normal form holds at every parameter point"
      "LeanPhy.Examples.ParameterCohomologyResearch.normal_form_at_all_parameters" ["declared family"]
      normal_form_at_all_parameters
    |>.addTheoremWithAssumptions "field extension" "extension from rational to complex coefficients preserves this family's H2 dimension"
      "LeanPhy.Examples.ParameterCohomologyResearch.rational_to_complex_dimension" ["declared family"]
      rational_to_complex_dimension
    |>.addTheoremWithAssumptions "same resonance stratum" "matching resonance patterns give an explicit H2 equivalence and equal dimension"
      "LeanPhy.Examples.ParameterCohomologyResearch.same_stratum_dimension" ["declared family"] same_stratum_dimension
    |>.addBoundaryText "algebraic family"
      "exact algebraic parameter dependence; no assertion of physical phase transition, continuity, or automatic classification of arbitrary families"
    |>.addObligationText "physical interpretation"
      "identify the bracket parameters and coefficient character with a concrete physical model"
      "research model"

def project : ResearchProject := ResearchProject.ofPackages "Parameter cohomology research" [package]

def manifest : ResearchManifest :=
  ResearchManifest.ofProject "Parameter cohomology research manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Examples.ParameterCohomologyResearch", "LeanPhy.Mathematics.SolvableLieFamily",
      "LeanPhy.Mathematics.DiagonalCohomology", "lean-toolchain", "lakefile.toml"]

example : project.claimCount = 12 := rfl
example : project.obligationCount = 1 := rfl
example : project.diagnosticCount = 0 := by decide

def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args

end LeanPhy.Examples.ParameterCohomologyResearch
