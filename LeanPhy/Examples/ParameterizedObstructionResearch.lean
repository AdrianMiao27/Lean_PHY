import LeanPhy.Examples.Generated.HeisenbergThirdParameter
import LeanPhy.Examples.Generated.AffineFourThirdCharacter
import LeanPhy.Examples.Generated.AffineFourThirdVector
import LeanPhy.CLI

/-! Parameter degenerations, representation resonances and intrinsic H³ obstructions. -/
namespace LeanPhy.Examples.ParameterizedObstructionResearch
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieDeformation LeanPhy.Mathematics.LieCochainCoordinates
open LeanPhy.Generated LeanPhy.Workflow
open scoped _root_.Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
set_option maxSynthPendingDepth 7
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

theorem heisenberg_dimension (g : K) :
    Module.finrank K (H3 (HeisenbergThirdParameter.coefficients ![g] ⟨⟩)) = if g=0 then 3 else 2 := by
  rw [HeisenbergThirdParameter.h3_finrank]
  simp [HeisenbergThirdParameterThirdCE.dimension]

theorem scalar_resonance_dimension (a t : K) :
    Module.finrank K (H3 (AffineFourThirdCharacter.coefficients ![a,t] ⟨⟩)) =
      (if t=a then 3 else 0) + (if t=0 then 1 else 0) := by
  rw [AffineFourThirdCharacter.h3_finrank]
  simp only [AffineFourThirdCharacterThirdCE.dimension,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,Matrix.head_cons]
  split_ifs <;> grind

theorem scalar_generic_vanishes (a t : K) (hta : t ≠ a) (ht : t ≠ 0) :
    Module.finrank K (H3 (AffineFourThirdCharacter.coefficients ![a,t] ⟨⟩)) = 0 := by
  simp [scalar_resonance_dimension,hta,ht]

theorem scalar_resonance_intersection :
    Module.finrank K (H3 (AffineFourThirdCharacter.coefficients (K := K) ![0,0] ⟨⟩)) = 4 := by
  simp [scalar_resonance_dimension]

theorem vector_validity_iff (a u : K) : AffineFourThirdVector.Conditions ![a,u] ↔ a=u := by
  constructor
  · intro h; have hq := h.q0; dsimp at hq; linear_combination hq
  · intro h; constructor; simp [h]

theorem vector_dimension (a u : K) (hp : AffineFourThirdVector.Conditions ![a,u]) :
    Module.finrank K (H3 (AffineFourThirdVector.coefficients ![a,u] hp)) = if u=0 then 4 else 0 := by
  rw [AffineFourThirdVector.h3_finrank]
  simp [AffineFourThirdVectorThirdCE.dimension]

theorem invalid_vector_has_no_model (a u : K) (h : a ≠ u) :
    ¬AffineFourThirdVector.ModelLaws ![a,u] := by
  apply AffineFourThirdVector.invalid_of_conditions_fail _ ⟨⟩
  simpa [vector_validity_iff] using h

abbrev HSpace (K : Type*) := Fin 3 → K

def direction (g t u : K) : HeisenbergThirdParameter.C2 ![g] ⟨⟩ :=
  HeisenbergThirdParameter.twoFrom ![g] ⟨⟩ ![0,t,0,0,0,0,0,0,u]

theorem direction_closed (g t u : K) :
    IsTwoCocycle (HeisenbergThirdParameter.coefficients ![g] ⟨⟩) (direction g t u) := by
  apply differential2_eq_zero_of_increasing
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> fin_cases k <;> norm_num at hjk
  ext r; fin_cases r <;>
    simp [direction,differential2_apply,HeisenbergThirdParameter.twoFrom,
      HeisenbergThirdParameter.coefficients,adjointLieModule,HeisenbergThirdParameter.algebra,
      HeisenbergThirdParameter.bracket,e] <;> ring

def displayedCorrection (g t u : K) : HeisenbergThirdParameter.C2 ![g] ⟨⟩ :=
  HeisenbergThirdParameter.twoFrom ![g] ⟨⟩ ![0,0,0,t*u/g,0,0,0,0,0]

theorem displayedCorrection_cancels (g t u : K) (hg : g ≠ 0) :
    secondResidual (direction g t u) (displayedCorrection g t u) = 0 := by
  apply secondResidual_eq_zero_of_increasing
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> fin_cases k <;> norm_num at hjk
  ext r; fin_cases r <;>
    simp [secondResidual,direction,displayedCorrection,differential2_apply,obstructionTrilinear,obstruction,
      HeisenbergThirdParameter.twoFrom,HeisenbergThirdParameter.coefficients,adjointLieModule,
      HeisenbergThirdParameter.algebra,HeisenbergThirdParameter.bracket,e] <;> field_simp <;> grind

theorem nonzero_coupling_extends (g t u : K) (hg : g ≠ 0) : SecondExtendable (direction g t u) :=
  ⟨displayedCorrection g t u,secondAlgebra _ _ (direction_closed g t u)
    ((secondResidual_eq_zero_iff _ _).mp (displayedCorrection_cancels g t u hg)),rfl⟩

theorem zero_coupling_extension_iff (t u : K) : SecondExtendable (direction 0 t u) ↔ t*u=0 := by
  have hd (ν : HeisenbergThirdParameter.C2 (K := K) ![0] ⟨⟩) :
      differential2 (HeisenbergThirdParameter.coefficients ![0] ⟨⟩) ν = 0 := by
    apply HeisenbergThirdParameter.readThird_detect ![0] ⟨⟩ ν
    rw [← HeisenbergThirdParameter.differential2_coordinates ![0] ⟨⟩ ν]
    ext i; fin_cases i <;> simp [HeisenbergThirdParameterCE.d2,
      Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  constructor
  · rintro ⟨ν,D,hD⟩
    have hc := ((secondAlgebra_exists_iff _ _).mp ⟨D,hD⟩).2 (e 0) (e 1) (e 2)
    change differential2 (HeisenbergThirdParameter.coefficients (K := K) ![0] ⟨⟩) ν (e 0) (e 1) (e 2) +
      obstruction (direction 0 t u) (e 0) (e 1) (e 2) = 0 at hc
    rw [hd ν] at hc
    have h := congrFun hc 2
    simpa [direction,HeisenbergThirdParameter.twoFrom,obstruction,e,mul_comm] using h
  · intro h
    have hc : secondResidual (direction 0 t u) 0 = 0 := by
      change differential2 (HeisenbergThirdParameter.coefficients (K := K) ![0] ⟨⟩) 0 +
        obstructionTrilinear (direction 0 t u) = 0
      rw [hd 0,zero_add]
      apply trilinear_eq_zero_of_basis
      intro i j k
      ext r; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases r <;>
        simp [obstructionTrilinear,obstruction,direction,HeisenbergThirdParameter.twoFrom,e,h,mul_comm]
    exact ⟨0,secondAlgebra _ _ (direction_closed 0 t u) ((secondResidual_eq_zero_iff _ _).mp hc),rfl⟩

/-- The legal extension locus retains the degenerate fiber explicitly. -/
theorem family_extension_iff (g t u : K) : SecondExtendable (direction g t u) ↔ g ≠ 0 ∨ t*u=0 := by
  by_cases hg : g=0
  · subst g; simpa using zero_coupling_extension_iff t u
  · exact iff_of_true (nonzero_coupling_extends g t u hg) (Or.inl hg)

theorem degeneration_obstructs : ¬SecondExtendable (direction (0 : K) 1 1) := by
  rw [zero_coupling_extension_iff]; norm_num

/-- A complete H³ calculation supplies a correction in each legal fiber. -/
def computedModel (g t u : K) (h : g ≠ 0 ∨ t*u=0) :
    LeanPhy.Mathematics.LieAlgebra K (HSpace K × HSpace K × HSpace K) :=
  HeisenbergThirdParameter.intrinsicModel ![g] ⟨⟩ (direction g t u) (direction_closed g t u)
    ((HeisenbergThirdParameter.intrinsic_extension_iff _ _ _ (direction_closed g t u)).mp
      ((family_extension_iff g t u).mpr h))

theorem computed_model_bracket (g t u : K) (h : g ≠ 0 ∨ t*u=0) :
    (computedModel g t u h).bracket = secondBracket (direction g t u)
      (HeisenbergThirdParameter.intrinsicCorrection ![g] ⟨⟩ (direction g t u)) := rfl

theorem actual_obstruction_zero_iff (g t u : K) :
    obstructionClass (direction g t u) (direction_closed g t u) = 0 ↔ g ≠ 0 ∨ t*u=0 :=
  (secondExtendable_iff_obstructionClass_zero _ _).symm.trans (family_extension_iff g t u)

theorem computed_coordinates_zero_iff (g t u : K) :
    HeisenbergThirdParameter.intrinsicObstruction ![g] ⟨⟩ (direction g t u) = 0 ↔ g ≠ 0 ∨ t*u=0 :=
  (HeisenbergThirdParameter.intrinsic_extension_iff _ _ _ (direction_closed g t u)).symm.trans
    (family_extension_iff g t u)

def package : TheoryPackage :=
  TheoryPackage.empty "Parameter-dependent H3 obstructions" "symmetry algebra exploration"
    |>.addAssumptionText "declared characteristic-zero families"
      "polynomial Heisenberg and affine brackets over characteristic-zero fields; canonical adjoint, scalar character and constrained vector coefficients"
      "examples/lie-cohomology/third-parameters/"
    |>.addTheoremWithAssumptions "Heisenberg H3 degeneration" "the adjoint H3 dimension is three at zero coupling and two otherwise"
      "LeanPhy.Examples.ParameterizedObstructionResearch.heisenberg_dimension" ["declared characteristic-zero families"] (@heisenberg_dimension.{0})
    |>.addTheoremWithAssumptions "complete scalar resonance formula" "the scalar H3 dimension counts both resonance loci and their intersection"
      "LeanPhy.Examples.ParameterizedObstructionResearch.scalar_resonance_dimension" ["declared characteristic-zero families"] (@scalar_resonance_dimension.{0})
    |>.addTheoremWithAssumptions "generic scalar vanishing" "H3 vanishes away from both declared resonance equations"
      "LeanPhy.Examples.ParameterizedObstructionResearch.scalar_generic_vanishes" ["declared characteristic-zero families"] (@scalar_generic_vanishes.{0})
    |>.addTheoremWithAssumptions "resonance intersection" "the intersection of the two scalar resonance loci has H3 dimension four"
      "LeanPhy.Examples.ParameterizedObstructionResearch.scalar_resonance_intersection" ["declared characteristic-zero families"] (@scalar_resonance_intersection.{0})
    |>.addTheoremWithAssumptions "exact representation condition" "the discovered representation condition is exactly equality of the two parameters"
      "LeanPhy.Examples.ParameterizedObstructionResearch.vector_validity_iff" ["declared characteristic-zero families"] (@vector_validity_iff.{0})
    |>.addTheoremWithAssumptions "legal vector H3" "on the valid representation locus the H3 dimension jumps from zero to four"
      "LeanPhy.Examples.ParameterizedObstructionResearch.vector_dimension" ["declared characteristic-zero families"] (@vector_dimension.{0})
    |>.addTheoremWithAssumptions "invalid representation rejected" "unequal parameters cannot satisfy the full bracket and representation laws"
      "LeanPhy.Examples.ParameterizedObstructionResearch.invalid_vector_has_no_model" ["declared characteristic-zero families"] (@invalid_vector_has_no_model.{0})
    |>.addTheoremWithAssumptions "closed direction on every fiber" "the displayed first-order deformation is closed for every base coupling"
      "LeanPhy.Examples.ParameterizedObstructionResearch.direction_closed" ["declared characteristic-zero families"] (@direction_closed.{0})
    |>.addTheoremWithAssumptions "nonzero coupling correction" "the correction t times u divided by g cancels the residual when g is nonzero"
      "LeanPhy.Examples.ParameterizedObstructionResearch.displayedCorrection_cancels" ["declared characteristic-zero families"] (@displayedCorrection_cancels.{0})
    |>.addTheoremWithAssumptions "extension at nonzero coupling" "every displayed direction has an actual second-order Lie model at nonzero coupling"
      "LeanPhy.Examples.ParameterizedObstructionResearch.nonzero_coupling_extends" ["declared characteristic-zero families"] (@nonzero_coupling_extends.{0})
    |>.addTheoremWithAssumptions "degenerate extension criterion" "at zero coupling a second-order extension exists exactly when t times u vanishes"
      "LeanPhy.Examples.ParameterizedObstructionResearch.zero_coupling_extension_iff" ["declared characteristic-zero families"] (@zero_coupling_extension_iff.{0})
    |>.addTheoremWithAssumptions "complete family extension locus" "the exact extension locus includes the degenerate and nondegenerate fibers"
      "LeanPhy.Examples.ParameterizedObstructionResearch.family_extension_iff" ["declared characteristic-zero families"] (@family_extension_iff.{0})
    |>.addTheoremWithAssumptions "extension lost at degeneration" "the displayed unit direction fails to extend at zero coupling"
      "LeanPhy.Examples.ParameterizedObstructionResearch.degeneration_obstructs" ["declared characteristic-zero families"] (@degeneration_obstructs.{0})
    |>.addTheoremWithAssumptions "generated actual model" "the computed H3 primitive supplies the second-order bracket in every legal fiber"
      "LeanPhy.Examples.ParameterizedObstructionResearch.computed_model_bracket" ["declared characteristic-zero families"] (@computed_model_bracket.{0})
    |>.addTheoremWithAssumptions "intrinsic class vanishing locus" "the true H3 obstruction class vanishes exactly on the proved family extension locus"
      "LeanPhy.Examples.ParameterizedObstructionResearch.actual_obstruction_zero_iff" ["declared characteristic-zero families"] (@actual_obstruction_zero_iff.{0})
    |>.addTheoremWithAssumptions "computed obstruction vanishing locus" "the automatic H3 coordinates detect the same complete extension locus"
      "LeanPhy.Examples.ParameterizedObstructionResearch.computed_coordinates_zero_iff" ["declared characteristic-zero families"] (@computed_coordinates_zero_iff.{0})
    |>.addBoundaryText "fiberwise finite-order scope"
      "H3 and second-order extension on all declared parameter fibers; no cross-fiber identification, all-orders integrability, analytic limit or physical realization"
    |>.addObligationText "physical interpretation"
      "identify the generators, couplings, coefficient representations and allowed equivalences with a physical system" "research model"

def project : ResearchProject := ResearchProject.ofPackages "Parameterized obstruction research" [package]
def manifest : ResearchManifest :=
  ResearchManifest.ofProject "Parameterized obstruction research manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Examples.ParameterizedObstructionResearch",
      "LeanPhy.Examples.Generated.HeisenbergThirdParameter", "LeanPhy.Examples.Generated.AffineFourThirdCharacter",
      "LeanPhy.Examples.Generated.AffineFourThirdVector", "LeanPhy.Mathematics.LieDeformationObstruction",
      "LeanPhy.Mathematics.FiniteLieCohomology3", "LeanPhy.Mathematics.LieCohomology3",
      "examples/lie-cohomology/third-parameters/heisenberg.json",
      "examples/lie-cohomology/third-parameters/affine-character.json",
      "examples/lie-cohomology/third-parameters/affine-vector.json",
      "scripts/symbolic_third_cohomology.py", "scripts/third_cochain_coordinates.py", "scripts/third_cohomology.py",
      "scripts/symbolic_lie_cohomology.py", "scripts/stratify_cohomology.py", "scripts/lie_cohomology.py",
      "scripts/reduce_cohomology.py", "lean-toolchain", "lakefile.toml"]
example : project.claimCount = 16 := rfl
example : project.obligationCount = 1 := rfl
example : project.diagnosticCount = 0 := by decide
def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args

end
end LeanPhy.Examples.ParameterizedObstructionResearch
