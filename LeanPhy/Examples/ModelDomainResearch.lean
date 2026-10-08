import LeanPhy.Examples.Generated.DiscoveredLieDomain
import LeanPhy.Examples.Generated.DiscoveredVectorDomain
import LeanPhy.Examples.Generated.ImpossibleLieDomain
import LeanPhy.CLI

/-!
# Discovering the exact domain of a polynomial Lie model

The combined model has [e0,e1]=a e0, [e1,e2]=b e1 and scalar action
e0·v=t v. The generated equations a*b=0 and a*t=0 are necessary and
sufficient. This example describes their union, constructs legal instances,
computes H2 there and rules out illegal points and an impossible bracket.
-/
namespace LeanPhy.Examples.ModelDomainResearch

open LeanPhy.Mathematics.LieCohomology LeanPhy.Generated LeanPhy.Workflow
open scoped _root_.Classical
noncomputable section
set_option maxSynthPendingDepth 5
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem discovered_domain (a b t : K) :
    DiscoveredLieDomain.Conditions ![a,b,t] ↔ a = 0 ∨ (b = 0 ∧ t = 0) := by
  constructor
  · intro h
    have hb := h.q0
    have ht := h.q1
    change a*b=0 at hb
    change a*t=0 at ht
    rcases mul_eq_zero.mp hb with ha | hb
    · exact Or.inl ha
    · rcases mul_eq_zero.mp ht with ha | ht
      · exact Or.inl ha
      · exact Or.inr ⟨hb,ht⟩
  · rintro (ha | ⟨hb,ht⟩) <;> constructor <;> simp [*]

theorem laws_iff_domain (a b t : K) :
    DiscoveredLieDomain.ModelLaws ![a,b,t] ↔ a = 0 ∨ (b = 0 ∧ t = 0) := by
  rw [← discovered_domain]
  constructor
  · intro h; exact (DiscoveredLieDomain.conditions_iff _).mpr ⟨⟨⟩,h⟩
  · intro h; exact ((DiscoveredLieDomain.conditions_iff _).mp h).2

theorem model_exists_iff (a b t : K) :
    (∃ L : LeanPhy.Mathematics.LieAlgebra K (DiscoveredLieDomain.Space K),
      L.bracket = DiscoveredLieDomain.bracket ![a,b,t] ∧
      ∃ M : LeanPhy.Mathematics.LieModule L (DiscoveredLieDomain.Coeff K),
        M.act = DiscoveredLieDomain.action ![a,b,t]) ↔ a = 0 ∨ (b = 0 ∧ t = 0) := by
  rw [← discovered_domain]
  constructor
  · intro h; exact (DiscoveredLieDomain.conditions_iff_model _).mpr ⟨⟨⟩,h⟩
  · intro h; exact ((DiscoveredLieDomain.conditions_iff_model _).mp h).2

theorem domainConditions (a b t : K) (h : a = 0 ∨ (b = 0 ∧ t = 0)) :
    DiscoveredLieDomain.Conditions ![a,b,t] := (discovered_domain a b t).mpr h

theorem plane_is_legal (b t : K) : DiscoveredLieDomain.ModelLaws ![0,b,t] :=
  (laws_iff_domain 0 b t).mpr (Or.inl rfl)

theorem axis_is_legal (a : K) : DiscoveredLieDomain.ModelLaws ![a,0,0] :=
  (laws_iff_domain a 0 0).mpr (Or.inr ⟨rfl,rfl⟩)

theorem off_locus_is_illegal : ¬DiscoveredLieDomain.ModelLaws ![(1 : ℝ),0,1] := by
  rw [laws_iff_domain]
  norm_num

theorem computed_dimension (a b t : K) (h : a = 0 ∨ (b = 0 ∧ t = 0)) :
    Module.finrank K (H2 (DiscoveredLieDomain.coefficients ![a,b,t] (domainConditions a b t h))) =
      if t ≠ 0 then 0 else if a = 0 ∧ b = 0 then 3 else 1 := by
  rw [DiscoveredLieDomain.h2_finrank]
  simp only [DiscoveredLieDomainCE.dimension, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  split_ifs <;> grind

theorem nonzero_character_vanishes (b t : K) (ht : t ≠ 0) :
    Module.finrank K (H2 (DiscoveredLieDomain.coefficients ![0,b,t]
      (domainConditions 0 b t (Or.inl rfl)))) = 0 := by
  simp [computed_dimension,ht]

theorem origin_dimension :
    Module.finrank ℝ (H2 (DiscoveredLieDomain.coefficients ![(0 : ℝ),0,0]
      (domainConditions 0 0 0 (Or.inl rfl)))) = 3 := by
  simp [computed_dimension]

theorem vector_laws_iff (a u : K) : DiscoveredVectorDomain.ModelLaws ![a,u] ↔ a = u := by
  constructor
  · intro hl
    have h := ((DiscoveredVectorDomain.conditions_iff _).mpr ⟨⟨⟩,hl⟩).q0
    change a + -1*u = 0 at h
    grind
  · intro h
    apply ((DiscoveredVectorDomain.conditions_iff _).mp ?_).2
    constructor
    simp [h]

omit [CharZero K] in
theorem impossible_conditions (p : Fin 0 → K) : ¬ImpossibleLieDomain.Conditions p := by
  intro h; exact one_ne_zero h.q0

theorem impossible_laws (p : Fin 0 → K) : ¬ImpossibleLieDomain.ModelLaws p :=
  ImpossibleLieDomain.invalid_of_conditions_fail p ⟨⟩ (impossible_conditions p)

theorem impossible_model (p : Fin 0 → K) :
    ¬∃ L : LeanPhy.Mathematics.LieAlgebra K (ImpossibleLieDomain.Space K),
      L.bracket = ImpossibleLieDomain.bracket p ∧
      ∃ M : LeanPhy.Mathematics.LieModule L (ImpossibleLieDomain.Coeff K),
        M.act = ImpossibleLieDomain.action p := by
  intro h
  exact impossible_conditions p ((ImpossibleLieDomain.conditions_iff_model p).mpr ⟨⟨⟩,h⟩)

def package : TheoryPackage :=
  TheoryPackage.empty "Discovered Lie validity domains" "model exploration"
    |>.addAssumptionText "declared raw families"
      "the raw polynomial brackets and actions in the discovery JSON inputs, over characteristic-zero fields; no user equations supplied"
      "examples/lie-cohomology/discovery/combined.json; examples/lie-cohomology/discovery/vector.json; examples/lie-cohomology/discovery/impossible.json"
    |>.addTheoremWithAssumptions "discovered domain" "the generated equations define a plane union a line"
      "LeanPhy.Examples.ModelDomainResearch.discovered_domain" ["declared raw families"] @discovered_domain.{0}
    |>.addTheoremWithAssumptions "full laws iff domain" "full Jacobi and representation laws hold exactly on the discovered domain"
      "LeanPhy.Examples.ModelDomainResearch.laws_iff_domain" ["declared raw families"] @laws_iff_domain.{0}
    |>.addTheoremWithAssumptions "actual model existence" "actual Lie algebra and module structures with the supplied operations exist exactly on that domain"
      "LeanPhy.Examples.ModelDomainResearch.model_exists_iff" ["declared raw families"] @model_exists_iff.{0}
    |>.addTheoremWithAssumptions "legal plane" "every point on a=0 is legal"
      "LeanPhy.Examples.ModelDomainResearch.plane_is_legal" ["declared raw families"] @plane_is_legal.{0}
    |>.addTheoremWithAssumptions "legal axis" "the b=t=0 branch remains legal even when a is nonzero"
      "LeanPhy.Examples.ModelDomainResearch.axis_is_legal" ["declared raw families"] @axis_is_legal.{0}
    |>.addTheoremWithAssumptions "illegal point" "the point (1,0,1) violates the model laws"
      "LeanPhy.Examples.ModelDomainResearch.off_locus_is_illegal" ["declared raw families"] off_locus_is_illegal
    |>.addTheoremWithAssumptions "cohomology on discovered domain" "the complete H2 dimension is computed on every legal point"
      "LeanPhy.Examples.ModelDomainResearch.computed_dimension" ["declared raw families"] @computed_dimension.{0}
    |>.addTheoremWithAssumptions "nonzero character" "on a=0 a nonzero scalar character implies H2 dimension zero"
      "LeanPhy.Examples.ModelDomainResearch.nonzero_character_vanishes" ["declared raw families"] @nonzero_character_vanishes.{0}
    |>.addTheoremWithAssumptions "origin classes" "the origin retains three independent classes"
      "LeanPhy.Examples.ModelDomainResearch.origin_dimension" ["declared raw families"] origin_dimension
    |>.addTheoremWithAssumptions "vector representation domain" "the generated full vector model laws hold exactly when a=u"
      "LeanPhy.Examples.ModelDomainResearch.vector_laws_iff" ["declared raw families"] @vector_laws_iff.{0}
    |>.addTheoremWithAssumptions "impossible laws" "the fixed invalid bracket cannot satisfy the full model laws"
      "LeanPhy.Examples.ModelDomainResearch.impossible_laws" ["declared raw families"] @impossible_laws.{0}
    |>.addTheoremWithAssumptions "impossible model" "no actual Lie model exists with the fixed invalid bracket and action"
      "LeanPhy.Examples.ModelDomainResearch.impossible_model" ["declared raw families"] @impossible_model.{0}
    |>.addBoundaryText "exact algebraic validity"
      "equations characterize the declared operations; no minimal ideal, irreducible decomposition, topology, physical phase or general nonemptiness claim"
    |>.addObligationText "physical interpretation"
      "identify the raw parameters, actions and cohomology classes with a concrete physical model" "research model"

def project : ResearchProject := ResearchProject.ofPackages "Model domain research" [package]
def manifest : ResearchManifest :=
  ResearchManifest.ofProject "Model domain research manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Examples.ModelDomainResearch", "LeanPhy.Examples.Generated.DiscoveredLieDomain",
      "LeanPhy.Examples.Generated.DiscoveredVectorDomain", "LeanPhy.Examples.Generated.ImpossibleLieDomain",
      "examples/lie-cohomology/discovery/combined.json", "examples/lie-cohomology/discovery/vector.json",
      "examples/lie-cohomology/discovery/impossible.json", "scripts/symbolic_lie_cohomology.py",
      "scripts/lie_cohomology.py", "scripts/stratify_cohomology.py", "scripts/requirements-symbolic.txt",
      "lean-toolchain", "lakefile.toml"]
example : project.claimCount = 12 := rfl
example : project.obligationCount = 1 := rfl
example : project.diagnosticCount = 0 := by decide
def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args
end
end LeanPhy.Examples.ModelDomainResearch
