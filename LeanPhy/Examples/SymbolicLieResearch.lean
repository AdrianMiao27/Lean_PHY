import LeanPhy.Examples.Generated.HeisenbergParameter
import LeanPhy.Examples.Generated.AffineVectorParameters
import LeanPhy.Examples.Generated.JacobiParameters
import LeanPhy.CLI

/-!
# Exploring polynomial Lie families from structure constants

All model laws, coordinate bridges and complete parameter trees are generated
from JSON inputs and checked by Lean. This client records the resulting H2
jumps and proves precisely which input loci admit the declared models.
No physical interpretation of a contraction or deformation is assumed.
-/

namespace LeanPhy.Examples.SymbolicLieResearch

open LeanPhy.Mathematics.LieCohomology LeanPhy.Workflow
open LeanPhy.Generated
open scoped _root_.Classical

noncomputable section
set_option maxSynthPendingDepth 5

variable {K : Type*} [Field K] [CharZero K]

omit [Field K] [CharZero K] in
theorem heisenbergConditions (g : K) : HeisenbergParameter.Conditions ![g] := ⟨⟩

theorem heisenberg_dimension (g : K) :
    Module.finrank K (H2 (HeisenbergParameter.coefficients ![g] (heisenbergConditions g))) =
      if g = 0 then 3 else 2 := by
  rw [HeisenbergParameter.h2_finrank]
  simp [HeisenbergParameterCE.dimension]

theorem heisenberg_nonzero (g : K) (hg : g ≠ 0) :
    Module.finrank K (H2 (HeisenbergParameter.coefficients ![g] (heisenbergConditions g))) = 2 := by
  simp [heisenberg_dimension, hg]

theorem heisenberg_zero :
    Module.finrank ℝ (H2 (HeisenbergParameter.coefficients ![(0 : ℝ)] (heisenbergConditions 0))) = 3 := by
  simp [heisenberg_dimension]

theorem heisenberg_exactness (g : K) (ω : HeisenbergParameter.C2 ![g] (heisenbergConditions g))
    (hω : IsTwoCocycle (HeisenbergParameter.coefficients ![g] (heisenbergConditions g)) ω) :
    IsTwoCoboundary (HeisenbergParameter.coefficients ![g] (heisenbergConditions g)) ω ↔
      (HeisenbergParameter.reduction ![g] (heisenbergConditions g)).project ω = 0 :=
  HeisenbergParameter.boundary_iff _ _ ω hω

theorem heisenberg_normal_form (g : K) (ω : HeisenbergParameter.C2 ![g] (heisenbergConditions g))
    (hω : IsTwoCocycle (HeisenbergParameter.coefficients ![g] (heisenbergConditions g)) ω) :
    differential1 (HeisenbergParameter.coefficients ![g] (heisenbergConditions g))
      ((HeisenbergParameter.reduction ![g] (heisenbergConditions g)).primitive ω) +
      (HeisenbergParameter.reduction ![g] (heisenbergConditions g)).represent
        ((HeisenbergParameter.reduction ![g] (heisenbergConditions g)).project ω) = ω :=
  HeisenbergParameter.normal_form _ _ ω hω

theorem affine_domain_iff (a u : K) : AffineVectorParameters.Conditions ![a,u] ↔ u = a := by
  constructor
  · intro hp
    have h := hp.q0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_mul, one_mul] at h
    grind
  · intro h
    constructor
    simp [h]

theorem affineConditions (a : K) : AffineVectorParameters.Conditions ![a,a] :=
  (affine_domain_iff a a).mpr rfl

theorem affine_dimension (a : K) :
    Module.finrank K (H2 (AffineVectorParameters.coefficients ![a,a] (affineConditions a))) =
      if a = 0 then 1 else 0 := by
  rw [AffineVectorParameters.h2_finrank]
  simp [AffineVectorParametersCE.dimension]

theorem affine_nonzero (a : K) (ha : a ≠ 0) :
    Module.finrank K (H2 (AffineVectorParameters.coefficients ![a,a] (affineConditions a))) = 0 := by
  simp [affine_dimension, ha]

theorem affine_zero :
    Module.finrank ℝ (H2 (AffineVectorParameters.coefficients ![(0 : ℝ),0] (affineConditions 0))) = 1 := by
  simp [affine_dimension]

theorem affine_wrong_character : ¬AffineVectorParameters.Conditions ![(1 : ℝ),0] := by
  rw [affine_domain_iff]
  norm_num

omit [CharZero K] in
theorem jacobi_domain_iff (a b : K) : JacobiParameters.Conditions ![a,b] ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro hp
    exact mul_eq_zero.mp hp.q0
  · intro h
    constructor
    exact mul_eq_zero.mpr h

theorem jacobi_invalid_point : ¬JacobiParameters.Conditions ![(1 : ℝ),1] := by
  rw [jacobi_domain_iff]
  norm_num

omit [CharZero K] in
theorem jacobiConditions (a b : K) (h : a = 0 ∨ b = 0) : JacobiParameters.Conditions ![a,b] :=
  (jacobi_domain_iff a b).mpr h

theorem jacobi_dimension (a b : K) (h : a = 0 ∨ b = 0) :
    Module.finrank K (H2 (JacobiParameters.coefficients ![a,b] (jacobiConditions a b h))) =
      if a = 0 ∧ b = 0 then 3 else 1 := by
  rw [JacobiParameters.h2_finrank]
  simp only [JacobiParametersCE.dimension, Matrix.cons_val_zero, Matrix.cons_val_one]
  split_ifs <;> grind

theorem jacobi_origin :
    Module.finrank ℝ (H2 (JacobiParameters.coefficients ![(0 : ℝ),0]
      (jacobiConditions 0 0 (Or.inl rfl)))) = 3 := by
  simp [jacobi_dimension]

def package : TheoryPackage :=
  TheoryPackage.empty "Symbolic Lie structure constants" "polynomial Lie cohomology"
    |>.addAssumptionText "declared polynomial inputs"
      "the three generated JSON Lie brackets and coefficient actions over characteristic-zero fields; Conditions records every polynomial equality and nonzero premise"
      "examples/lie-cohomology/heisenberg-parameter.json; examples/lie-cohomology/affine-vector-parameters.json; examples/lie-cohomology/jacobi-parameters.json"
    |>.addTheoremWithAssumptions "Heisenberg dimension" "the actual H2 dimension is three at zero bracket parameter and two otherwise"
      "LeanPhy.Examples.SymbolicLieResearch.heisenberg_dimension" ["declared polynomial inputs"] @heisenberg_dimension.{0}
    |>.addTheoremWithAssumptions "Heisenberg nonzero parameter" "every nonzero bracket parameter has H2 dimension two"
      "LeanPhy.Examples.SymbolicLieResearch.heisenberg_nonzero" ["declared polynomial inputs"] @heisenberg_nonzero.{0}
    |>.addTheoremWithAssumptions "Heisenberg zero parameter" "the zero bracket gives dimension three"
      "LeanPhy.Examples.SymbolicLieResearch.heisenberg_zero" ["declared polynomial inputs"] heisenberg_zero
    |>.addTheoremWithAssumptions "computed exactness" "closed cochains are exact iff their generated class coordinates vanish"
      "LeanPhy.Examples.SymbolicLieResearch.heisenberg_exactness" ["declared polynomial inputs"] @heisenberg_exactness.{0}
    |>.addTheoremWithAssumptions "computed normal form" "generated primitives and representatives decompose every closed cochain"
      "LeanPhy.Examples.SymbolicLieResearch.heisenberg_normal_form" ["declared polynomial inputs"] @heisenberg_normal_form.{0}
    |>.addTheoremWithAssumptions "representation domain" "the affine-vector input condition is exactly u=a"
      "LeanPhy.Examples.SymbolicLieResearch.affine_domain_iff" ["declared polynomial inputs"] @affine_domain_iff.{0}
    |>.addTheoremWithAssumptions "affine-vector dimension" "on the representation domain the H2 dimension is one at zero and zero otherwise"
      "LeanPhy.Examples.SymbolicLieResearch.affine_dimension" ["declared polynomial inputs"] @affine_dimension.{0}
    |>.addTheoremWithAssumptions "affine nonzero parameter" "the nonzero affine-vector parameter has H2 dimension zero"
      "LeanPhy.Examples.SymbolicLieResearch.affine_nonzero" ["declared polynomial inputs"] @affine_nonzero.{0}
    |>.addTheoremWithAssumptions "affine zero parameter" "the zero affine bracket with its declared vector action has H2 dimension one"
      "LeanPhy.Examples.SymbolicLieResearch.affine_zero" ["declared polynomial inputs"] affine_zero
    |>.addTheoremWithAssumptions "invalid representation parameter" "a=1,u=0 does not satisfy the declared representation condition"
      "LeanPhy.Examples.SymbolicLieResearch.affine_wrong_character" ["declared polynomial inputs"] affine_wrong_character
    |>.addTheoremWithAssumptions "Jacobi domain" "the declared Jacobi constraint is the union of the two coordinate axes"
      "LeanPhy.Examples.SymbolicLieResearch.jacobi_domain_iff" ["declared polynomial inputs"] @jacobi_domain_iff.{0}
    |>.addTheoremWithAssumptions "invalid Jacobi parameter" "a=b=1 does not satisfy the declared Jacobi condition"
      "LeanPhy.Examples.SymbolicLieResearch.jacobi_invalid_point" ["declared polynomial inputs"] jacobi_invalid_point
    |>.addTheoremWithAssumptions "Jacobi-locus dimension" "on the constraint locus H2 has dimension three at the origin and one elsewhere"
      "LeanPhy.Examples.SymbolicLieResearch.jacobi_dimension" ["declared polynomial inputs"] @jacobi_dimension.{0}
    |>.addTheoremWithAssumptions "Jacobi origin" "the constraint intersection retains three classes"
      "LeanPhy.Examples.SymbolicLieResearch.jacobi_origin" ["declared polynomial inputs"] jacobi_origin
    |>.addBoundaryText "algebraic parameter exploration"
      "actual degree-two cohomology of the declared polynomial families; no physical phase transition, topology, deformation classification or all-degree BRST identification"
    |>.addObligationText "physical interpretation"
      "identify the parameters, representations and resulting cohomology classes in a concrete physical model" "research model"

def project : ResearchProject := ResearchProject.ofPackages "Symbolic Lie research" [package]

def manifest : ResearchManifest :=
  ResearchManifest.ofProject "Symbolic Lie research manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Examples.SymbolicLieResearch", "LeanPhy.Examples.Generated.HeisenbergParameter",
      "LeanPhy.Examples.Generated.AffineVectorParameters", "LeanPhy.Examples.Generated.JacobiParameters",
      "scripts/symbolic_lie_cohomology.py", "scripts/lie_cohomology.py", "scripts/stratify_cohomology.py",
      "examples/lie-cohomology/heisenberg-parameter.json", "examples/lie-cohomology/affine-vector-parameters.json",
      "examples/lie-cohomology/jacobi-parameters.json", "scripts/requirements-symbolic.txt", "lean-toolchain", "lakefile.toml"]

example : project.claimCount = 14 := rfl
example : project.obligationCount = 1 := rfl
example : project.diagnosticCount = 0 := by decide

def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args

end
end LeanPhy.Examples.SymbolicLieResearch
