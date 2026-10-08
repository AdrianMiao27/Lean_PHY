import LeanPhy.Examples.Generated.AffineAdjointParameter
import LeanPhy.Examples.Generated.HeisenbergAdjointParameter
import LeanPhy.Examples.Generated.Sl2Adjoint
import LeanPhy.CLI

/-!
# Computed adjoint cohomology as a deformation workflow

The generators infer the canonical adjoint action from brackets alone. The
affine parameter family has two classes at zero and none away from zero;
the Heisenberg family has nine and five respectively. The generated sl₂
model has no first-order classes. Complete reductions provide actual normal
forms, invertible generator changes and jet Lie algebras, not only dimensions.
-/

namespace LeanPhy.Examples.AdjointDeformationResearch

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology LeanPhy.Generated LeanPhy.Workflow
open scoped _root_.Classical
noncomputable section
set_option maxSynthPendingDepth 5
variable {K : Type*} [Field K] [CharZero K]

theorem affine_dimension (g : K) :
    Module.finrank K (H2 (adjointLieModule (AffineAdjointParameter.algebra ![g] ⟨⟩))) =
      if g = 0 then 2 else 0 := by
  change Module.finrank K (H2 (AffineAdjointParameter.coefficients ![g] ⟨⟩)) = _
  rw [AffineAdjointParameter.h2_finrank]
  simp [AffineAdjointParameterCE.dimension]

theorem heisenberg_dimension (g : K) :
    Module.finrank K (H2 (adjointLieModule (HeisenbergAdjointParameter.algebra ![g] ⟨⟩))) =
      if g = 0 then 9 else 5 := by
  change Module.finrank K (H2 (HeisenbergAdjointParameter.coefficients ![g] ⟨⟩)) = _
  rw [HeisenbergAdjointParameter.h2_finrank]
  simp [HeisenbergAdjointParameterCE.dimension]

theorem affine_coordinates_zero (g : K) (hg : g ≠ 0) (ω : AffineAdjointParameter.C2 ![g] ⟨⟩) :
    (AffineAdjointParameter.reduction ![g] ⟨⟩).project ω = 0 := by
  have hd : AffineAdjointParameterCE.dimension ![g] = 0 := by simp [AffineAdjointParameterCE.dimension,hg]
  have : Subsingleton (Fin (AffineAdjointParameterCE.dimension ![g]) → K) := by
    rw [hd]; infer_instance
  exact Subsingleton.elim _ _

def removeAffine (g : K) (hg : g ≠ 0) (ω : AffineAdjointParameter.C2 ![g] ⟨⟩)
    (hω : IsTwoCocycle (adjointLieModule (AffineAdjointParameter.algebra ![g] ⟨⟩)) ω) :
    LieDeformation.Equivalence ω 0 :=
  AffineAdjointParameter.trivializeDeformation ![g] ⟨⟩ ω hω (affine_coordinates_zero g hg ω)

theorem affine_all_removable (g : K) (hg : g ≠ 0) (ω : AffineAdjointParameter.C2 ![g] ⟨⟩)
    (hω : IsTwoCocycle (adjointLieModule (AffineAdjointParameter.algebra ![g] ⟨⟩)) ω) :
    Nonempty (LieDeformation.Equivalence ω 0) := ⟨removeAffine g hg ω hω⟩

def affineOriginReduction : Reduction (AffineAdjointParameter.coefficients ![(0 : K)] ⟨⟩) (Fin 2 → K) := by
  have hd : AffineAdjointParameterCE.dimension ![(0 : K)] = 2 := by simp [AffineAdjointParameterCE.dimension]
  have S := AffineAdjointParameter.reduction ![(0 : K)] ⟨⟩
  rw [hd] at S
  exact S

def affineOriginDirection : AffineAdjointParameter.C2 ![(0 : K)] ⟨⟩ :=
  (affineOriginReduction (K := K)).represent ![1,0]

theorem affine_origin_closed : IsTwoCocycle (AffineAdjointParameter.coefficients ![(0 : K)] ⟨⟩)
    affineOriginDirection := (affineOriginReduction (K := K)).represent_closed ![1,0]

theorem affine_origin_not_removable :
    ¬Nonempty (LieDeformation.Equivalence (affineOriginDirection (K := K)) 0) := by
  rw [LieDeformation.Reduction.removable_iff (affineOriginReduction (K := K)) _ affine_origin_closed]
  change (affineOriginReduction (K := K)).project ((affineOriginReduction (K := K)).represent ![(1 : K),0]) ≠ 0
  rw [(affineOriginReduction (K := K)).project_represent]
  intro h
  have hh := congrFun h 0
  exact one_ne_zero hh

def heisenbergReduction (g : K) (hg : g ≠ 0) :
    Reduction (HeisenbergAdjointParameter.coefficients ![g] ⟨⟩) (Fin 5 → K) := by
  have hd : HeisenbergAdjointParameterCE.dimension ![g] = 5 := by simp [HeisenbergAdjointParameterCE.dimension,hg]
  have S := HeisenbergAdjointParameter.reduction ![g] ⟨⟩
  rw [hd] at S
  exact S

def heisenbergRepresentative (g : K) (hg : g ≠ 0) (a : Fin 5 → K) :
    HeisenbergAdjointParameter.C2 ![g] ⟨⟩ := (heisenbergReduction g hg).represent a

theorem heisenberg_representative_closed (g : K) (hg : g ≠ 0) (a : Fin 5 → K) :
    IsTwoCocycle (adjointLieModule (HeisenbergAdjointParameter.algebra ![g] ⟨⟩))
      (heisenbergRepresentative g hg a) := (heisenbergReduction g hg).represent_closed a

def heisenbergModel (g : K) (hg : g ≠ 0) (a : Fin 5 → K) :
    LeanPhy.Mathematics.LieAlgebra K ((Fin 3 → K) × (Fin 3 → K)) :=
  LieDeformation.Reduction.deformation (heisenbergReduction g hg) a

theorem heisenberg_representatives_equivalent_iff (g : K) (hg : g ≠ 0) (a b : Fin 5 → K) :
    Nonempty (LieDeformation.Equivalence (heisenbergRepresentative g hg a)
      (heisenbergRepresentative g hg b)) ↔ a = b :=
  LieDeformation.Reduction.representatives_equivalent_iff (heisenbergReduction g hg) a b

def normalizeHeisenberg (g : K) (hg : g ≠ 0) (ω : HeisenbergAdjointParameter.C2 ![g] ⟨⟩)
    (hω : IsTwoCocycle (adjointLieModule (HeisenbergAdjointParameter.algebra ![g] ⟨⟩)) ω) :
    LieDeformation.Equivalence ω
      (heisenbergRepresentative g hg ((heisenbergReduction g hg).project ω)) :=
  LieDeformation.Reduction.normalize (heisenbergReduction g hg) ω hω

theorem heisenberg_normalization_preserves_bracket (g : K) (hg : g ≠ 0)
    (ω : HeisenbergAdjointParameter.C2 ![g] ⟨⟩)
    (hω : IsTwoCocycle (adjointLieModule (HeisenbergAdjointParameter.algebra ![g] ⟨⟩)) ω)
    (x y : (Fin 3 → K) × (Fin 3 → K)) :
    (normalizeHeisenberg g hg ω hω).linearEquiv (LieDeformation.bracket ω x y) =
      LieDeformation.bracket (heisenbergRepresentative g hg ((heisenbergReduction g hg).project ω))
        ((normalizeHeisenberg g hg ω hω).linearEquiv x) ((normalizeHeisenberg g hg ω hω).linearEquiv y) :=
  (normalizeHeisenberg g hg ω hω).map_bracket x y

theorem heisenberg_class_nonzero (g : K) (hg : g ≠ 0) (a : Fin 5 → K) (ha : a ≠ 0) :
    classOf (adjointLieModule (HeisenbergAdjointParameter.algebra ![g] ⟨⟩))
      (heisenbergRepresentative g hg a) (heisenberg_representative_closed g hg a) ≠ 0 := by
  intro h
  have hb := (classOf_eq_zero_iff _ _ _).mp h
  have hp := ((heisenbergReduction g hg).exact_iff _ (heisenberg_representative_closed g hg a)).mp hb
  exact ha ((heisenbergReduction g hg).project_represent a ▸ hp)

theorem sl2_dimension : Module.finrank ℚ (H2 (adjointLieModule Sl2Adjoint.algebra)) = 0 :=
  Sl2Adjoint.h2_finrank

def removeSl2 (ω : Sl2Adjoint.C2) (hω : IsTwoCocycle (adjointLieModule Sl2Adjoint.algebra) ω) :
    LieDeformation.Equivalence ω 0 := Sl2Adjoint.trivializeDeformation ω hω (Subsingleton.elim _ _)

theorem sl2_all_removable (ω : Sl2Adjoint.C2) (hω : IsTwoCocycle (adjointLieModule Sl2Adjoint.algebra) ω) :
    Nonempty (LieDeformation.Equivalence ω 0) := ⟨removeSl2 ω hω⟩

theorem sl2_primitive (ω : Sl2Adjoint.C2) (hω : IsTwoCocycle (adjointLieModule Sl2Adjoint.algebra) ω) :
    differential1 (adjointLieModule Sl2Adjoint.algebra) (Sl2Adjoint.reduction.primitive ω) = ω := by
  have h := Sl2Adjoint.normal_form ω hω
  have hp : Sl2Adjoint.reduction.project ω = 0 := Subsingleton.elim _ _
  change differential1 Sl2Adjoint.coefficients (Sl2Adjoint.reduction.primitive ω) = ω
  simpa only [hp,map_zero,add_zero] using h

def package : TheoryPackage :=
  TheoryPackage.empty "Computed adjoint deformation classes" "symmetry algebra exploration"
    |>.addAssumptionText "canonical adjoint inputs"
      "declared rational sl2 brackets and polynomial affine/Heisenberg brackets; canonical adjoint coefficients; characteristic-zero fields for parameter families"
      "examples/lie-cohomology/adjoint/sl2.json; examples/lie-cohomology/adjoint/affine-parameter.json; examples/lie-cohomology/adjoint/heisenberg-parameter.json"
    |>.addTheoremWithAssumptions "affine class dimension" "the affine adjoint H2 dimension is two at zero and zero otherwise"
      "LeanPhy.Examples.AdjointDeformationResearch.affine_dimension" ["canonical adjoint inputs"] @affine_dimension.{0}
    |>.addTheoremWithAssumptions "Heisenberg class dimension" "the Heisenberg adjoint H2 dimension is nine at zero and five otherwise"
      "LeanPhy.Examples.AdjointDeformationResearch.heisenberg_dimension" ["canonical adjoint inputs"] @heisenberg_dimension.{0}
    |>.addTheoremWithAssumptions "affine first-order rigidity" "every closed direction at a nonzero affine parameter has a computed trivializing equivalence"
      "LeanPhy.Examples.AdjointDeformationResearch.affine_all_removable" ["canonical adjoint inputs"] @affine_all_removable.{0}
    |>.addTheoremWithAssumptions "affine degeneration direction" "the origin has an explicitly represented closed direction"
      "LeanPhy.Examples.AdjointDeformationResearch.affine_origin_closed" ["canonical adjoint inputs"] @affine_origin_closed.{0}
    |>.addTheoremWithAssumptions "affine degeneration is nontrivial" "the displayed origin direction is not removable"
      "LeanPhy.Examples.AdjointDeformationResearch.affine_origin_not_removable" ["canonical adjoint inputs"] @affine_origin_not_removable.{0}
    |>.addTheoremWithAssumptions "complete representative family" "each five-tuple gives a closed Heisenberg deformation direction"
      "LeanPhy.Examples.AdjointDeformationResearch.heisenberg_representative_closed" ["canonical adjoint inputs"] @heisenberg_representative_closed.{0}
    |>.addTheoremWithAssumptions "unique representative coordinates" "two represented Heisenberg directions are equivalent exactly when their five-tuples agree"
      "LeanPhy.Examples.AdjointDeformationResearch.heisenberg_representatives_equivalent_iff" ["canonical adjoint inputs"] @heisenberg_representatives_equivalent_iff.{0}
    |>.addTheoremWithAssumptions "computed normalization" "the actual computed invertible generator change preserves the deformed bracket"
      "LeanPhy.Examples.AdjointDeformationResearch.heisenberg_normalization_preserves_bracket" ["canonical adjoint inputs"] @heisenberg_normalization_preserves_bracket.{0}
    |>.addTheoremWithAssumptions "nonzero representative class" "every nonzero five-tuple gives a nonzero adjoint H2 class"
      "LeanPhy.Examples.AdjointDeformationResearch.heisenberg_class_nonzero" ["canonical adjoint inputs"] @heisenberg_class_nonzero.{0}
    |>.addTheoremWithAssumptions "sl2 adjoint dimension" "the generated sl2 adjoint H2 quotient has dimension zero"
      "LeanPhy.Examples.AdjointDeformationResearch.sl2_dimension" ["canonical adjoint inputs"] sl2_dimension
    |>.addTheoremWithAssumptions "sl2 first-order rigidity" "every closed sl2 direction has an explicit trivializing equivalence"
      "LeanPhy.Examples.AdjointDeformationResearch.sl2_all_removable" ["canonical adjoint inputs"] sl2_all_removable
    |>.addTheoremWithAssumptions "sl2 exact primitive" "the computed primitive differentiates to the supplied closed direction"
      "LeanPhy.Examples.AdjointDeformationResearch.sl2_primitive" ["canonical adjoint inputs"] sl2_primitive
    |>.addBoundaryText "first-order classification"
      "closed adjoint directions modulo invertible generator changes fixing reduction and tangent; computed dimensions do not prove higher-order extension, analytic rigidity, convergence or Lie-group integration"
    |>.addObligationText "physical interpretation"
      "identify the brackets, deformation directions and allowed generator changes with a concrete physical symmetry problem" "research model"

def project : ResearchProject := ResearchProject.ofPackages "Adjoint deformation research" [package]
def manifest : ResearchManifest :=
  ResearchManifest.ofProject "Adjoint deformation research manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Mathematics.LieDeformationReduction", "LeanPhy.Examples.AdjointDeformationResearch",
      "LeanPhy.Examples.Generated.Sl2Adjoint", "LeanPhy.Examples.Generated.AffineAdjointParameter",
      "LeanPhy.Examples.Generated.HeisenbergAdjointParameter", "examples/lie-cohomology/adjoint/sl2.json",
      "examples/lie-cohomology/adjoint/affine-parameter.json", "examples/lie-cohomology/adjoint/heisenberg-parameter.json",
      "scripts/lie_cohomology.py", "scripts/symbolic_lie_cohomology.py", "scripts/reduce_cohomology.py",
      "scripts/stratify_cohomology.py", "scripts/requirements-symbolic.txt", "lean-toolchain", "lakefile.toml"]
example : project.claimCount = 12 := rfl
example : project.obligationCount = 1 := rfl
example : project.diagnosticCount = 0 := by decide
def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args

end
end LeanPhy.Examples.AdjointDeformationResearch
