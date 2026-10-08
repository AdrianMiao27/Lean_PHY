import LeanPhy.Mathematics.LieDeformationThirdObstruction
import LeanPhy.Examples.ParameterizedObstructionResearch
import LeanPhy.Examples.Generated.Sl2Third

/-! Third-order extensions depend on the chosen second-order correction. -/
namespace LeanPhy.Examples.ThirdOrderDeformationResearch
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieDeformation LeanPhy.Mathematics.LieCochainCoordinates
open LeanPhy.Generated LeanPhy.Workflow
open ParameterizedObstructionResearch
open scoped _root_.Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
set_option maxSynthPendingDepth 7
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

/-- The previously displayed correction leaves a nonzero obstruction at the next order. -/
theorem displayed_third_obstruction (g t u : K) :
    thirdObstructionCochain (direction g t u) (displayedCorrection g t u) (e 0) (e 1) (e 2) =
      ![t*u^2/g,t^2*u/g,0] := by
  calc
    _ = thirdObstruction (direction g t u) (displayedCorrection g t u) (e 0) (e 1) (e 2) :=
      thirdObstructionCochain_apply _ _ _ _ _
    _ = _ := by
      ext r; fin_cases r <;>
        simp [thirdObstruction,direction,displayedCorrection,HeisenbergThirdParameter.twoFrom,e] <;> ring

/-- No third correction can alter the first component of the CE differential. -/
theorem third_differential_first_zero (g : K) (ρ : HeisenbergThirdParameter.C2 ![g] ⟨⟩) :
    differential2 (HeisenbergThirdParameter.coefficients ![g] ⟨⟩) ρ (e 0) (e 1) (e 2) 0 = 0 := by
  have h := congrFun (HeisenbergThirdParameter.differential2_coordinates ![g] ⟨⟩ ρ) 0
  simpa [HeisenbergThirdParameter.readThird,HeisenbergThirdParameterCE.d2,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using h.symm

/-- Failure quantifies over every possible third correction. -/
theorem displayed_correction_blocked (g t u : K) (hg : g ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0) :
    ¬ThirdExtendable (direction g t u) (displayedCorrection g t u) := by
  rintro ⟨ρ,D,hD⟩
  have hr := ((thirdAlgebra_exists_iff _ _ _).mp ⟨D,hD⟩).2.2
  have hv := congrFun (congrArg (fun q : HeisenbergThirdParameter.C3 ![g] ⟨⟩ =>
    q (e 0) (e 1) (e 2)) hr) 0
  change differential2 (HeisenbergThirdParameter.coefficients ![g] ⟨⟩) ρ (e 0) (e 1) (e 2) 0 +
    thirdObstructionCochain (direction g t u) (displayedCorrection g t u) (e 0) (e 1) (e 2) 0 = 0 at hv
  erw [third_differential_first_zero g ρ,displayed_third_obstruction g t u] at hv
  simpa [hg,ht,hu] using hv

/-- Adding closed terms changes the valid second-order choice. -/
def adjustedSecond (g t u s : K) : HeisenbergThirdParameter.C2 ![g] ⟨⟩ :=
  HeisenbergThirdParameter.twoFrom ![g] ⟨⟩ ![0,s,0,t*u/g,-t*t/g,0,u*u/g,0,0]

/-- A genuinely nonzero third coefficient can be required. -/
def displayedThird (g u s : K) : HeisenbergThirdParameter.C2 ![g] ⟨⟩ :=
  HeisenbergThirdParameter.twoFrom ![g] ⟨⟩ ![0,0,0,s*u/g,0,0,0,0,0]

theorem adjusted_second_valid (g t u s : K) (hg : g ≠ 0) :
    secondResidual (direction g t u) (adjustedSecond g t u s) = 0 := by
  apply secondResidual_eq_zero_of_increasing
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> fin_cases k <;> norm_num at hjk
  ext r; fin_cases r <;>
    simp [secondResidual,direction,adjustedSecond,differential2_apply,obstructionTrilinear,obstruction,
      HeisenbergThirdParameter.twoFrom,HeisenbergThirdParameter.coefficients,adjointLieModule,
      HeisenbergThirdParameter.algebra,HeisenbergThirdParameter.bracket,e] <;> field_simp
  all_goals grind

theorem adjusted_third_obstruction (g t u s : K) :
    thirdObstructionCochain (direction g t u) (adjustedSecond g t u s) (e 0) (e 1) (e 2) =
      ![0,0,-s*u] := by
  calc
    _ = thirdObstruction (direction g t u) (adjustedSecond g t u s) (e 0) (e 1) (e 2) :=
      thirdObstructionCochain_apply _ _ _ _ _
    _ = _ := by
      ext r; fin_cases r <;>
        simp [thirdObstruction,direction,adjustedSecond,HeisenbergThirdParameter.twoFrom,e] <;> ring

theorem displayed_third_valid (g t u s : K) (hg : g ≠ 0) :
    thirdResidual (direction g t u) (adjustedSecond g t u s) (displayedThird g u s) = 0 := by
  apply three_ext_increasing
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> fin_cases k <;> norm_num at hjk
  change differential2 (HeisenbergThirdParameter.coefficients ![g] ⟨⟩) (displayedThird g u s)
    (e 0) (e 1) (e 2) +
    thirdObstructionCochain (direction g t u) (adjustedSecond g t u s) (e 0) (e 1) (e 2) = 0
  rw [adjusted_third_obstruction]
  ext r; fin_cases r <;>
    simp [displayedThird,differential2_apply,HeisenbergThirdParameter.twoFrom,
      HeisenbergThirdParameter.coefficients,adjointLieModule,HeisenbergThirdParameter.algebra,
      HeisenbergThirdParameter.bracket,e] <;> field_simp
  all_goals grind

def displayedModel (g t u s : K) (hg : g ≠ 0) :
    LeanPhy.Mathematics.LieAlgebra K (ThirdJet (HSpace K)) :=
  thirdAlgebra _ _ _ (direction_closed g t u) (adjusted_second_valid g t u s hg)
    (displayed_third_valid g t u s hg)

theorem displayed_model_bracket (g t u s : K) (hg : g ≠ 0) :
    (displayedModel g t u s hg).bracket =
      thirdBracket (direction g t u) (adjustedSecond g t u s) (displayedThird g u s) := rfl

theorem adjusted_second_extends (g t u s : K) (hg : g ≠ 0) :
    ThirdExtendable (direction g t u) (adjustedSecond g t u s) :=
  ⟨displayedThird g u s, displayedModel g t u s hg,rfl⟩

/-- The same first-order direction admits both a blocked and an extendable
second-order choice. A failure of one choice does not exclude the direction. -/
theorem second_choice_matters (g : K) (hg : g ≠ 0) :
    secondResidual (direction g 1 1) (displayedCorrection g 1 1) = 0 ∧
    ¬ThirdExtendable (direction g 1 1) (displayedCorrection g 1 1) ∧
    ThirdExtendable (direction g 1 1) (adjustedSecond g 1 1 1) :=
  ⟨displayedCorrection_cancels g 1 1 hg,
    displayed_correction_blocked g 1 1 hg one_ne_zero one_ne_zero,
    adjusted_second_extends g 1 1 1 hg⟩

theorem zero_third_correction_fails (g t u s : K) (hu : u ≠ 0) (hs : s ≠ 0) :
    thirdResidual (direction g t u) (adjustedSecond g t u s) 0 ≠ 0 := by
  intro h
  have hv := congrFun (congrArg (fun q : HeisenbergThirdParameter.C3 ![g] ⟨⟩ =>
    q (e 0) (e 1) (e 2)) h) 2
  change ((differential2ToThree (HeisenbergThirdParameter.coefficients ![g] ⟨⟩)) 0 +
    thirdObstructionCochain (direction g t u) (adjustedSecond g t u s)) (e 0) (e 1) (e 2) 2 = 0 at hv
  rw [map_zero,zero_add,adjusted_third_obstruction] at hv
  simp [hu,hs] at hv

/-- The existing parameter H³ certificate is sufficient to compute at third order. -/
theorem computed_coordinates_vanish (g t u s : K) (hg : g ≠ 0) :
    LieDeformation.ThirdReduction.thirdCoordinates (HeisenbergThirdParameter.thirdReduction ![g] ⟨⟩)
      (direction g t u) (adjustedSecond g t u s) = 0 :=
  (LieDeformation.ThirdReduction.third_extendable_iff _ _ _ (direction_closed g t u)
    (adjusted_second_valid g t u s hg)).mp (adjusted_second_extends g t u s hg)

def computedThirdModel (g t u s : K) (hg : g ≠ 0) :
    LeanPhy.Mathematics.LieAlgebra K (ThirdJet (HSpace K)) :=
  LieDeformation.ThirdReduction.thirdModel (HeisenbergThirdParameter.thirdReduction ![g] ⟨⟩)
    (direction g t u) (adjustedSecond g t u s) (direction_closed g t u)
    (adjusted_second_valid g t u s hg) (computed_coordinates_vanish g t u s hg)

theorem computed_model_truncates (g t u s : K) (hg : g ≠ 0) (x y : ThirdJet (HSpace K)) :
    ((computedThirdModel g t u s hg).bracket x y).1 =
      secondBracket (direction g t u) (adjustedSecond g t u s) x.1 y.1 := rfl

/-- Zero adjoint H³ also supports the next extension for each valid lower model. -/
theorem sl2_every_second_choice_extends (ω ν : Sl2Third.C2)
    (hω : IsTwoCocycle Sl2Third.coefficients ω) (hν : secondResidual ω ν = 0) :
    ThirdExtendable ω ν := by
  apply (LieDeformation.ThirdReduction.third_extendable_iff Sl2Third.thirdReduction ω ν hω hν).mpr
  exact Subsingleton.elim _ _

def package : TheoryPackage :=
  TheoryPackage.empty "Third-order Lie deformation research" "symmetry algebra exploration"
    |>.addAssumptionText "declared adjoint models"
      "canonical adjoint Heisenberg parameter family over a characteristic-zero field and rational sl2; all nonzero-coupling and lower-order Jacobi hypotheses remain explicit"
      "examples/lie-cohomology/third-parameters/heisenberg.json and examples/lie-cohomology/third/sl2.json"
    |>.addTheoremWithAssumptions "displayed third obstruction" "the previous second correction leaves the displayed cubic obstruction"
      "LeanPhy.Examples.ThirdOrderDeformationResearch.displayed_third_obstruction" ["declared adjoint models"] (@displayed_third_obstruction.{0})
    |>.addTheoremWithAssumptions "third differential first zero" "every third correction has zero CE differential in the first output coordinate"
      "LeanPhy.Examples.ThirdOrderDeformationResearch.third_differential_first_zero" ["declared adjoint models"] (@third_differential_first_zero.{0})
    |>.addTheoremWithAssumptions "displayed correction blocked" "nonzero g, t and u forbid all third corrections for the previous second choice"
      "LeanPhy.Examples.ThirdOrderDeformationResearch.displayed_correction_blocked" ["declared adjoint models"] (@displayed_correction_blocked.{0})
    |>.addTheoremWithAssumptions "adjusted second valid" "the adjusted second correction preserves the second-order Jacobi equation"
      "LeanPhy.Examples.ThirdOrderDeformationResearch.adjusted_second_valid" ["declared adjoint models"] (@adjusted_second_valid.{0})
    |>.addTheoremWithAssumptions "adjusted third obstruction" "the adjusted choice leaves exactly the central obstruction minus s times u"
      "LeanPhy.Examples.ThirdOrderDeformationResearch.adjusted_third_obstruction" ["declared adjoint models"] (@adjusted_third_obstruction.{0})
    |>.addTheoremWithAssumptions "displayed third valid" "the explicit third coefficient cancels the new residual at nonzero coupling"
      "LeanPhy.Examples.ThirdOrderDeformationResearch.displayed_third_valid" ["declared adjoint models"] (@displayed_third_valid.{0})
    |>.addTheoremWithAssumptions "displayed model bracket" "the actual third-jet Lie algebra has the declared convolution bracket"
      "LeanPhy.Examples.ThirdOrderDeformationResearch.displayed_model_bracket" ["declared adjoint models"] (@displayed_model_bracket.{0})
    |>.addTheoremWithAssumptions "adjusted second extends" "the adjusted second-order model extends through third order"
      "LeanPhy.Examples.ThirdOrderDeformationResearch.adjusted_second_extends" ["declared adjoint models"] (@adjusted_second_extends.{0})
    |>.addTheoremWithAssumptions "second choice matters" "one direction has both a blocked and an extendable valid second-order choice"
      "LeanPhy.Examples.ThirdOrderDeformationResearch.second_choice_matters" ["declared adjoint models"] (@second_choice_matters.{0})
    |>.addTheoremWithAssumptions "zero third correction fails" "a nonzero s times u requires a nonzero third-order correction"
      "LeanPhy.Examples.ThirdOrderDeformationResearch.zero_third_correction_fails" ["declared adjoint models"] (@zero_third_correction_fails.{0})
    |>.addTheoremWithAssumptions "computed coordinates vanish" "the certified parameter H3 reduction detects the same third-order extension"
      "LeanPhy.Examples.ThirdOrderDeformationResearch.computed_coordinates_vanish" ["declared adjoint models"] (@computed_coordinates_vanish.{0})
    |>.addTheoremWithAssumptions "computed model truncates" "the computed third-order model truncates to the specified second-order bracket"
      "LeanPhy.Examples.ThirdOrderDeformationResearch.computed_model_truncates" ["declared adjoint models"] (@computed_model_truncates.{0})
    |>.addTheoremWithAssumptions "sl2 every second choice extends" "every valid rational sl2 second-order model extends through third order"
      "LeanPhy.Examples.ThirdOrderDeformationResearch.sl2_every_second_choice_extends" ["declared adjoint models"] (@sl2_every_second_choice_extends)
    |>.addBoundaryText "specified second-order choice"
      "extension through epsilon cubed for the supplied first and second corrections; no canonical third obstruction on H2 alone, all-orders solution, convergence or Lie-group integration"
    |>.addObligationText "physical interpretation"
      "identify generators, deformation parameters and allowed second-order choices with a physical research model" "research model"

def project : ResearchProject := ResearchProject.ofPackages "Third-order deformation research" [package]
def manifest : ResearchManifest :=
  ResearchManifest.ofProject "Third-order deformation research manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Examples.ThirdOrderDeformationResearch",
      "LeanPhy.Mathematics.LieDeformationThirdOrder", "LeanPhy.Mathematics.LieDeformationThirdObstruction",
      "LeanPhy.Examples.ParameterizedObstructionResearch", "LeanPhy.Examples.Generated.HeisenbergThirdParameter",
      "LeanPhy.Examples.Generated.Sl2Third", "examples/lie-cohomology/third-parameters/heisenberg.json",
      "examples/lie-cohomology/third/sl2.json", "scripts/symbolic_third_cohomology.py",
      "scripts/third_cohomology.py", "lean-toolchain", "lakefile.toml"]
example : project.claimCount = 13 := rfl
example : project.obligationCount = 1 := rfl
example : project.diagnosticCount = 0 := by decide
def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args

end
end LeanPhy.Examples.ThirdOrderDeformationResearch
