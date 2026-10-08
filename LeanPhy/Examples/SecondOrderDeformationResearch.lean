import LeanPhy.Examples.Generated.AbelianSecondOrder
import LeanPhy.Examples.Generated.HeisenbergSecondOrder
import LeanPhy.CLI

/-!
# Exploring second-order extensions of symmetry algebras

Two complete generated solvers decide extension for arbitrary rational
adjoint two-cochains. The Heisenberg example distinguishes a removable
nonzero quadratic Jacobi term from a nonzero cokernel obstruction.
-/
namespace LeanPhy.Examples.SecondOrderDeformationResearch

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates LeanPhy.Mathematics.LieDeformation
open LeanPhy.Generated LeanPhy.Workflow
set_option maxSynthPendingDepth 5
noncomputable section

abbrev Space := Fin 3 → ℚ

def heisenbergFamily (a : Fin 5 → ℚ) : Fin 9 → ℚ :=
  ![a 0,a 1,0,-a 4,a 2,0,a 3,a 4,0]

theorem heisenberg_closed (a : Fin 5 → ℚ) :
    IsTwoCocycle HeisenbergSecondOrder.coefficients
      (HeisenbergSecondOrder.twoFrom (heisenbergFamily a)) := by
  rw [HeisenbergSecondOrder.closed_coordinates]
  ext r
  fin_cases r <;> simp [heisenbergFamily, HeisenbergSecondOrderCE.d2,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem heisenberg_obstructions (a : Fin 5 → ℚ) :
    HeisenbergSecondOrder.obstructionValues (heisenbergFamily a) =
      ![a 0 * a 4 - a 1 * a 3, -(a 0 * a 2 + a 1 * a 4)] := by
  ext r
  fin_cases r <;> simp [HeisenbergSecondOrder.obstructionValues, heisenbergFamily] <;> ring

theorem heisenberg_extension_iff (a : Fin 5 → ℚ) :
    (∃ ν : HeisenbergSecondOrder.C2, ∃ D : LeanPhy.Mathematics.LieAlgebra ℚ (Space × Space × Space),
      D.bracket = secondBracket (HeisenbergSecondOrder.twoFrom (heisenbergFamily a)) ν) ↔
      a 0 * a 4 - a 1 * a 3 = 0 ∧ a 0 * a 2 + a 1 * a 4 = 0 := by
  refine (HeisenbergSecondOrder.secondOrderSolver.model_exists_iff
    (HeisenbergSecondOrder.twoFrom (heisenbergFamily a))).trans ?_
  rw [HeisenbergSecondOrder.obstruction_coordinates]
  change IsTwoCocycle HeisenbergSecondOrder.coefficients _ ∧ _ ↔ _
  rw [and_iff_right (heisenberg_closed a), heisenberg_obstructions]
  simp [funext_iff, Fin.forall_fin_succ]
  intro _
  constructor <;> intro h <;> linarith

theorem heisenberg_no_correction :
    ¬∃ ν : HeisenbergSecondOrder.C2, ∃ D : LeanPhy.Mathematics.LieAlgebra ℚ (Space × Space × Space),
      D.bracket = secondBracket (HeisenbergSecondOrder.twoFrom (heisenbergFamily ![1,0,1,0,0])) ν := by
  rw [heisenberg_extension_iff]
  norm_num

/-- This non-normalized closed direction has a genuinely nonzero exact Jacobi term. -/
def cancellable (t u : ℚ) : Fin 9 → ℚ := ![0,t,0,0,0,0,0,0,u]

theorem cancellable_conditions (t u : ℚ) :
    HeisenbergSecondOrder.SecondOrderConditions (cancellable t u) := by
  constructor <;> ext r <;> fin_cases r <;>
    simp [cancellable, HeisenbergSecondOrderCE.d2, HeisenbergSecondOrder.obstructionValues,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem cancellable_quadratic (t u : ℚ) :
    obstruction (HeisenbergSecondOrder.twoFrom (cancellable t u)) (e 0) (e 1) (e 2) =
      ![0,0,-(t*u)] := by
  ext r
  fin_cases r <;> simp [obstruction, HeisenbergSecondOrder.twoFrom, cancellable, e] <;> ring

theorem cancellable_correction (t u : ℚ) :
    HeisenbergSecondOrder.correctionValues (cancellable t u) = ![0,0,0,t*u,0,0,0,0,0] := by
  ext r
  fin_cases r <;> simp [HeisenbergSecondOrder.correctionValues, cancellable]

def correctedModel (t u : ℚ) : LeanPhy.Mathematics.LieAlgebra ℚ (Space × Space × Space) :=
  HeisenbergSecondOrder.secondOrderModel (cancellable t u) (cancellable_conditions t u)

theorem corrected_model_bracket (t u : ℚ) :
    (correctedModel t u).bracket = secondBracket (HeisenbergSecondOrder.twoFrom (cancellable t u))
      (HeisenbergSecondOrder.twoFrom ![0,0,0,t*u,0,0,0,0,0]) := by
  unfold correctedModel
  rw [HeisenbergSecondOrder.secondOrderModel_bracket, cancellable_correction]

theorem zero_correction_fails (t u : ℚ) (h : t*u ≠ 0) :
    ¬∃ D : LeanPhy.Mathematics.LieAlgebra ℚ (Space × Space × Space),
      D.bracket = secondBracket (HeisenbergSecondOrder.twoFrom (cancellable t u)) 0 := by
  rintro ⟨D,hD⟩
  have hr := obstruction_of_secondOrder_model _ _ D hD (e 0) (e 1) (e 2)
  have hz : differential2 HeisenbergSecondOrder.coefficients (0 : HeisenbergSecondOrder.C2) = 0 :=
    map_zero (differential2Linear HeisenbergSecondOrder.coefficients)
  change differential2 HeisenbergSecondOrder.coefficients 0 _ _ _ + _ = 0 at hr
  rw [hz] at hr
  have hh := congrFun hr 2
  simp only [LinearMap.zero_apply, Pi.zero_apply, zero_add, cancellable_quadratic,
    Matrix.cons_val_two] at hh
  exact h (neg_eq_zero.mp hh)

theorem all_cancellable_corrections (t u : ℚ) (ν : HeisenbergSecondOrder.C2) :
    secondResidual (HeisenbergSecondOrder.twoFrom (cancellable t u)) ν = 0 ↔
      IsTwoCocycle HeisenbergSecondOrder.coefficients
        (ν - HeisenbergSecondOrder.twoFrom ![0,0,0,t*u,0,0,0,0,0]) := by
  rw [HeisenbergSecondOrder.all_corrections_iff _ _ (cancellable_conditions t u).2,
    cancellable_correction]

/-- A zero quadratic term alone cannot rescue a direction that is not closed. -/
def nonclosed : Fin 9 → ℚ := ![0,0,0,1,0,0,0,0,0]

theorem nonclosed_obstruction_zero : HeisenbergSecondOrder.obstructionValues nonclosed = 0 := by
  ext r
  fin_cases r <;> norm_num [nonclosed, HeisenbergSecondOrder.obstructionValues]

theorem nonclosed_no_model :
    ¬∃ ν : HeisenbergSecondOrder.C2, ∃ D : LeanPhy.Mathematics.LieAlgebra ℚ (Space × Space × Space),
      D.bracket = secondBracket (HeisenbergSecondOrder.twoFrom nonclosed) ν := by
  rw [HeisenbergSecondOrder.second_order_exists_iff]
  intro h
  have hz := congrFun h.1 2
  norm_num [nonclosed, HeisenbergSecondOrderCE.d2, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hz

def abelianFamily (a b : ℚ) : Fin 9 → ℚ := ![a,0,0,0,0,0,0,b,0]

theorem abelian_extension_iff (a b : ℚ) :
    (∃ ν : AbelianSecondOrder.C2, ∃ D : LeanPhy.Mathematics.LieAlgebra ℚ (Space × Space × Space),
      D.bracket = secondBracket (AbelianSecondOrder.twoFrom (abelianFamily a b)) ν) ↔ a*b=0 := by
  rw [AbelianSecondOrder.second_order_exists_iff]
  simp [AbelianSecondOrder.SecondOrderConditions, AbelianSecondOrderCE.d2,
    AbelianSecondOrder.obstructionValues, abelianFamily, funext_iff, Fin.forall_fin_succ]

def package : TheoryPackage :=
  TheoryPackage.empty "Computed second-order deformations" "symmetry algebra exploration"
    |>.addAssumptionText "declared rational brackets"
      "rational abelian and Heisenberg brackets with canonical adjoint coefficients; explicit first-order cochain families"
      "examples/lie-cohomology/second-order/abelian.json; examples/lie-cohomology/second-order/heisenberg.json"
    |>.addTheoremWithAssumptions "Heisenberg closed family" "the five-parameter family is closed for the canonical adjoint differential"
      "LeanPhy.Examples.SecondOrderDeformationResearch.heisenberg_closed" ["declared rational brackets"] heisenberg_closed
    |>.addTheoremWithAssumptions "Heisenberg quadratic equations" "the complete projected obstruction is the displayed pair of quadratic polynomials"
      "LeanPhy.Examples.SecondOrderDeformationResearch.heisenberg_obstructions" ["declared rational brackets"] heisenberg_obstructions
    |>.addTheoremWithAssumptions "Heisenberg extension locus" "any second-order correction exists exactly when both quadratic equations vanish"
      "LeanPhy.Examples.SecondOrderDeformationResearch.heisenberg_extension_iff" ["declared rational brackets"] heisenberg_extension_iff
    |>.addTheoremWithAssumptions "Heisenberg nonexistence" "the displayed direction admits no second-order Lie model for any correction"
      "LeanPhy.Examples.SecondOrderDeformationResearch.heisenberg_no_correction" ["declared rational brackets"] heisenberg_no_correction
    |>.addTheoremWithAssumptions "solvable exact obstruction" "the non-normalized two-parameter family satisfies both closedness and obstruction conditions"
      "LeanPhy.Examples.SecondOrderDeformationResearch.cancellable_conditions" ["declared rational brackets"] cancellable_conditions
    |>.addTheoremWithAssumptions "nonzero exact Jacobi term" "the raw quadratic Jacobi term is minus t times u in the central coordinate"
      "LeanPhy.Examples.SecondOrderDeformationResearch.cancellable_quadratic" ["declared rational brackets"] cancellable_quadratic
    |>.addTheoremWithAssumptions "computed nonzero correction" "the solver supplies t times u in the e0,e2 bracket"
      "LeanPhy.Examples.SecondOrderDeformationResearch.cancellable_correction" ["declared rational brackets"] cancellable_correction
    |>.addTheoremWithAssumptions "actual corrected Lie model" "the constructed second-jet Lie algebra has the specified computed bracket"
      "LeanPhy.Examples.SecondOrderDeformationResearch.corrected_model_bracket" ["declared rational brackets"] corrected_model_bracket
    |>.addTheoremWithAssumptions "correction is necessary" "when t times u is nonzero, the zero correction fails Jacobi"
      "LeanPhy.Examples.SecondOrderDeformationResearch.zero_correction_fails" ["declared rational brackets"] zero_correction_fails
    |>.addTheoremWithAssumptions "all correction freedom" "all valid corrections differ from the computed one by an adjoint cocycle"
      "LeanPhy.Examples.SecondOrderDeformationResearch.all_cancellable_corrections" ["declared rational brackets"] all_cancellable_corrections
    |>.addTheoremWithAssumptions "quadratic test is insufficient" "a nonclosed direction can have zero projected quadratic obstruction"
      "LeanPhy.Examples.SecondOrderDeformationResearch.nonclosed_obstruction_zero" ["declared rational brackets"] nonclosed_obstruction_zero
    |>.addTheoremWithAssumptions "closedness is necessary" "the displayed nonclosed direction admits no second-order model despite zero quadratic obstruction"
      "LeanPhy.Examples.SecondOrderDeformationResearch.nonclosed_no_model" ["declared rational brackets"] nonclosed_no_model
    |>.addTheoremWithAssumptions "abelian extension locus" "the abelian two-parameter family extends through order two exactly on a times b equals zero"
      "LeanPhy.Examples.SecondOrderDeformationResearch.abelian_extension_iff" ["declared rational brackets"] abelian_extension_iff
    |>.addBoundaryText "second-order scope"
      "explicit rational finite-dimensional jet models through order two; obstruction coordinates compute the cokernel of d2, not H3; no all-orders extension, convergence or Lie-group integration follows"
    |>.addObligationText "physical interpretation"
      "identify the declared symmetry brackets and deformation parameters with a concrete physical model" "research model"

def project : ResearchProject := ResearchProject.ofPackages "Second-order deformation research" [package]
def manifest : ResearchManifest :=
  ResearchManifest.ofProject "Second-order deformation research manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Mathematics.LieDeformationSecondOrder", "LeanPhy.Examples.SecondOrderDeformationResearch",
      "LeanPhy.Examples.Generated.AbelianSecondOrder", "LeanPhy.Examples.Generated.HeisenbergSecondOrder",
      "examples/lie-cohomology/second-order/abelian.json", "examples/lie-cohomology/second-order/heisenberg.json",
      "scripts/second_order_deformation.py", "scripts/lie_cohomology.py", "scripts/reduce_cohomology.py",
      "lean-toolchain", "lakefile.toml"]
example : project.claimCount = 13 := rfl
example : project.obligationCount = 1 := rfl
example : project.diagnosticCount = 0 := by decide
def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args

end
end LeanPhy.Examples.SecondOrderDeformationResearch
