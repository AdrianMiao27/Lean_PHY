import LeanPhy.Examples.Generated.HeisenbergThirdSearch
import LeanPhy.Examples.Generated.Filiform4ThirdObstructed
import LeanPhy.Examples.Generated.NonclosedThirdSearch
import LeanPhy.Examples.Generated.SecondObstructedThirdSearch
import LeanPhy.CLI

/-! Joint search separates a poor second-order choice from a true higher obstruction. -/
namespace LeanPhy.Examples.ThirdOrderSearchResearch
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieDeformation LeanPhy.Mathematics.LieCochainCoordinates
open LeanPhy.Generated LeanPhy.Workflow
set_option maxSynthPendingDepth 7
set_option maxHeartbeats 1600000
noncomputable section

/-- The generated primitive searches both corrections without a fixed ansatz. -/
theorem heisenberg_search_succeeds : ThirdDirectionExtendable HeisenbergThirdSearch.direction :=
  HeisenbergThirdSearch.search_succeeds

theorem heisenberg_first_choice_valid :
    secondResidual HeisenbergThirdSearch.direction HeisenbergThirdSearch.secondCandidate = 0 :=
  HeisenbergThirdSearch.secondCandidate_cancels

/-- Failure of the sequential primitive does not imply failure of joint search. -/
theorem heisenberg_first_choice_blocked :
    ¬ThirdExtendable HeisenbergThirdSearch.direction HeisenbergThirdSearch.secondCandidate := by
  rintro ⟨ρ,D,hD⟩
  have hr := ((thirdAlgebra_exists_iff _ _ _).mp ⟨D,hD⟩).2.2
  have h := congrFun ((thirdResidual_eq_zero_iff _ _ _).mp hr (e 0) (e 1) (e 2)) 0
  have hd : differential2 HeisenbergThirdSearch.coefficients ρ (e 0) (e 1) (e 2) 0 = 0 := by
    have hh := congrFun (HeisenbergThirdSearch.differential2_coordinates ρ) 0
    simpa [HeisenbergThirdSearch.readThird,HeisenbergThirdSearchCE.d2,
      Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh.symm
  change differential2 HeisenbergThirdSearch.coefficients ρ (e 0) (e 1) (e 2) 0 +
    thirdObstruction HeisenbergThirdSearch.direction HeisenbergThirdSearch.secondCandidate (e 0) (e 1) (e 2) 0 = 0 at h
  erw [hd] at h
  norm_num [thirdObstruction,HeisenbergThirdSearch.direction,HeisenbergThirdSearch.secondCandidate,
    HeisenbergThirdSearch.twoFrom,e] at h

/-- All original independent coordinates of both computed corrections are exposed. -/
theorem heisenberg_computed_pair :
    HeisenbergThirdSearch.pairTwoCoordinates HeisenbergThirdSearch.searchedCorrections =
      ![0,0,0,1,-1,0,1,0,0,0,0,0,0,0,0,0,0,0] :=
  HeisenbergThirdSearch.correction_coordinates

theorem heisenberg_actual_model :
    HeisenbergThirdSearch.certifiedModel.bracket = thirdBracket HeisenbergThirdSearch.direction
      HeisenbergThirdSearch.searchedCorrections.1 HeisenbergThirdSearch.searchedCorrections.2 := rfl

theorem heisenberg_all_models (ν ρ : HeisenbergThirdSearch.C2) :
    (∃ D : LeanPhy.Mathematics.LieAlgebra ℚ (ThirdJet HeisenbergThirdSearch.Space),
      D.bracket = thirdBracket HeisenbergThirdSearch.direction ν ρ) ↔
    HeisenbergThirdSearchJointImage.d1.toLin'
      (HeisenbergThirdSearch.pairTwoCoordinates (ν,ρ) - HeisenbergThirdSearch.correctionValues) = 0 :=
  HeisenbergThirdSearch.all_pairs_iff ν ρ HeisenbergThirdSearch.search_conditions

/-- The nilpotent four-dimensional example passes both lower-order equations. -/
theorem filiform_second_order_succeeds : SecondExtendable Filiform4ThirdObstructed.direction :=
  Filiform4ThirdObstructed.second_order_succeeds

theorem filiform_obstruction_nonzero : Filiform4ThirdObstructed.obstructionValues 4 = 2 := by
  norm_num [Filiform4ThirdObstructed.obstructionValues]

/-- Nonexistence quantifies over every second choice and every third correction. -/
theorem filiform_no_third_direction_extension : ¬ThirdDirectionExtendable Filiform4ThirdObstructed.direction :=
  Filiform4ThirdObstructed.search_impossible

theorem filiform_every_second_choice_blocked (ν : Filiform4ThirdObstructed.C2) :
    ¬ThirdExtendable Filiform4ThirdObstructed.direction ν :=
  fun h => filiform_no_third_direction_extension ⟨ν,h⟩

/-- A zero block target cannot repair a violation of first-order Jacobi. -/
theorem nonclosed_zero_projection : NonclosedThirdSearch.obstructionValues = 0 := by
  ext i; fin_cases i <;> norm_num [NonclosedThirdSearch.obstructionValues]

theorem nonclosed_no_model : ¬ThirdDirectionExtendable NonclosedThirdSearch.direction :=
  NonclosedThirdSearch.search_impossible

theorem second_order_obstruction_no_model : ¬ThirdDirectionExtendable SecondObstructedThirdSearch.direction :=
  SecondObstructedThirdSearch.search_impossible

theorem filiform_separates_orders :
    SecondExtendable Filiform4ThirdObstructed.direction ∧
      ¬ThirdDirectionExtendable Filiform4ThirdObstructed.direction :=
  ⟨filiform_second_order_succeeds,filiform_no_third_direction_extension⟩

def package : TheoryPackage :=
  TheoryPackage.empty "Joint third-order correction search" "symmetry algebra exploration"
    |>.addAssumptionText "declared rational models"
      "canonical adjoint Heisenberg and four-dimensional filiform brackets, with specified rational first directions; all corrections remain unrestricted"
      "examples/lie-cohomology/third-search/"
    |>.addTheoremWithAssumptions "heisenberg search succeeds" "joint search finds second and third corrections for the declared Heisenberg direction"
      "LeanPhy.Examples.ThirdOrderSearchResearch.heisenberg_search_succeeds" ["declared rational models"] (@heisenberg_search_succeeds)
    |>.addTheoremWithAssumptions "heisenberg first choice valid" "the sequential second-order primitive satisfies the second-order Jacobi equation"
      "LeanPhy.Examples.ThirdOrderSearchResearch.heisenberg_first_choice_valid" ["declared rational models"] (@heisenberg_first_choice_valid)
    |>.addTheoremWithAssumptions "heisenberg first choice blocked" "that valid sequential primitive cannot be extended for any third correction"
      "LeanPhy.Examples.ThirdOrderSearchResearch.heisenberg_first_choice_blocked" ["declared rational models"] (@heisenberg_first_choice_blocked)
    |>.addTheoremWithAssumptions "heisenberg computed pair" "all independent coordinates of the automatically repaired pair are checked"
      "LeanPhy.Examples.ThirdOrderSearchResearch.heisenberg_computed_pair" ["declared rational models"] (@heisenberg_computed_pair)
    |>.addTheoremWithAssumptions "heisenberg actual model" "the computed pair defines the declared actual third-jet Lie algebra"
      "LeanPhy.Examples.ThirdOrderSearchResearch.heisenberg_actual_model" ["declared rational models"] (@heisenberg_actual_model)
    |>.addTheoremWithAssumptions "heisenberg all models" "all possible Heisenberg pairs are exactly the computed solution plus the joint kernel"
      "LeanPhy.Examples.ThirdOrderSearchResearch.heisenberg_all_models" ["declared rational models"] (@heisenberg_all_models)
    |>.addTheoremWithAssumptions "filiform second order succeeds" "the four-dimensional nilpotent direction admits a checked second-order correction"
      "LeanPhy.Examples.ThirdOrderSearchResearch.filiform_second_order_succeeds" ["declared rational models"] (@filiform_second_order_succeeds)
    |>.addTheoremWithAssumptions "filiform obstruction nonzero" "a joint image obstruction coordinate is exactly two"
      "LeanPhy.Examples.ThirdOrderSearchResearch.filiform_obstruction_nonzero" ["declared rational models"] (@filiform_obstruction_nonzero)
    |>.addTheoremWithAssumptions "filiform no third direction extension" "no second and third correction pair extends the four-dimensional direction"
      "LeanPhy.Examples.ThirdOrderSearchResearch.filiform_no_third_direction_extension" ["declared rational models"] (@filiform_no_third_direction_extension)
    |>.addTheoremWithAssumptions "filiform every second choice blocked" "every second-order choice for that direction fails at third order"
      "LeanPhy.Examples.ThirdOrderSearchResearch.filiform_every_second_choice_blocked" ["declared rational models"] (@filiform_every_second_choice_blocked)
    |>.addTheoremWithAssumptions "nonclosed zero projection" "a nonclosed direction can have zero joint obstruction coordinates"
      "LeanPhy.Examples.ThirdOrderSearchResearch.nonclosed_zero_projection" ["declared rational models"] (@nonclosed_zero_projection)
    |>.addTheoremWithAssumptions "nonclosed no model" "the missing first-order cocycle equation still forbids every joint model"
      "LeanPhy.Examples.ThirdOrderSearchResearch.nonclosed_no_model" ["declared rational models"] (@nonclosed_no_model)
    |>.addTheoremWithAssumptions "second order obstruction no model" "a direction already obstructed at second order also fails joint search"
      "LeanPhy.Examples.ThirdOrderSearchResearch.second_order_obstruction_no_model" ["declared rational models"] (@second_order_obstruction_no_model)
    |>.addTheoremWithAssumptions "filiform separates orders" "second-order existence does not imply third-order existence even after changing the second correction"
      "LeanPhy.Examples.ThirdOrderSearchResearch.filiform_separates_orders" ["declared rational models"] (@filiform_separates_orders)
    |>.addBoundaryText "finite-order search"
      "complete joint second/third correction search for each fixed first direction; the block cokernel is not CE H3; no all-orders solution or convergence claim"
    |>.addObligationText "physical interpretation"
      "identify the supplied brackets, first directions and allowed generator changes with a physical model" "research model"

def project : ResearchProject := ResearchProject.ofPackages "Joint correction search research" [package]
def manifest : ResearchManifest :=
  ResearchManifest.ofProject "Joint correction search manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Examples.ThirdOrderSearchResearch", "LeanPhy.Mathematics.LieDeformationThirdSearch",
      "LeanPhy.Mathematics.LieDeformationThirdOrder", "LeanPhy.Mathematics.LieDeformationThirdObstruction",
      "LeanPhy.Examples.Generated.HeisenbergThirdSearch", "LeanPhy.Examples.Generated.Filiform4ThirdObstructed",
      "LeanPhy.Examples.Generated.NonclosedThirdSearch", "LeanPhy.Examples.Generated.SecondObstructedThirdSearch",
      "examples/lie-cohomology/third-search/heisenberg.json", "examples/lie-cohomology/third-search/filiform.json",
      "examples/lie-cohomology/third-search/nonclosed.json", "examples/lie-cohomology/third-search/second-obstructed.json",
      "scripts/third_order_search.py", "scripts/third_cochain_coordinates.py", "scripts/third_cohomology.py",
      "scripts/lie_cohomology.py", "scripts/reduce_cohomology.py", "scripts/second_order_deformation.py",
      "lean-toolchain", "lakefile.toml"]
example : project.claimCount = 14 := rfl
example : project.obligationCount = 1 := rfl
example : project.diagnosticCount = 0 := by decide
def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args

end
end LeanPhy.Examples.ThirdOrderSearchResearch
