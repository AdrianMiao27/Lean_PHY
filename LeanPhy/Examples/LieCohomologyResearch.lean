import LeanPhy.Mathematics.CentralExtension
import LeanPhy.GaugeTheory.QuadraticGhost
import LeanPhy.CLI
import LeanPhy.Examples.HeisenbergCohomology

/-!
# A worked Lie-cohomology research calculation

The area cocycle on an abelian plane gives a nontrivial Heisenberg extension.
On the affine algebra `[e₀,e₁] = -e₁`, a nonzero cocycle is instead a
coboundary, and an explicit shear removes the central term. For the same affine
algebra the degree-one CE differential is intertwined with the quadratic ghost
differential, checking the ghost sign against the declared Lie bracket.

This checks algebraic claims only. Integration, unitary representations,
physical anomalies, and a general ghost/CE chain equivalence remain separate.
-/

namespace LeanPhy.Examples.LieCohomologyResearch

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology LeanPhy.Workflow
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial

abbrev Plane := Fin 2 → ℚ

def e (i : Fin 2) : Plane := Pi.single i 1

def abelianPlane : LeanPhy.Mathematics.LieAlgebra ℚ Plane where
  bracket := fun _ _ => 0
  add_left := by intros; simp
  add_right := by intros; simp
  smul_left := by intros; simp
  smul_right := by intros; simp
  zero_left := by intros; rfl
  alternating := by intros; rfl
  antisymm := by intros; simp
  jacobi := by intros; simp

def area (x y : Plane) : ℚ := x 0 * y 1 - x 1 * y 0

def areaCocycle : LieCochain2 abelianPlane (trivialLieModule abelianPlane : LieModule abelianPlane ℚ) where
  eval := area
  map_add_left' := by intros; simp [area]; ring
  map_add_right' := by intros; simp [area]; ring
  map_smul_left' := by intros; simp [area]; ring
  map_smul_right' := by intros; simp [area]; ring
  alternating' := by intro x; simp [area]; ring

theorem area_closed : IsTwoCocycle (trivialLieModule abelianPlane) areaCocycle := by
  rw [twoCocycle_trivial_iff]
  intro x y z
  simp [abelianPlane, areaCocycle]

theorem area_not_boundary : ¬IsTwoCoboundary (trivialLieModule abelianPlane) areaCocycle := by
  rintro ⟨φ, hφ⟩
  have h := congrArg (fun ω : LieCochain2 abelianPlane (trivialLieModule abelianPlane) =>
    ω (e 0) (e 1)) hφ
  norm_num [differential1_trivial, abelianPlane, areaCocycle, area, e] at h

theorem heisenberg_class_nonzero :
    classOf (trivialLieModule abelianPlane) areaCocycle area_closed ≠ 0 :=
  mt (classOf_eq_zero_iff _ _ _).mp area_not_boundary

def heisenberg : LeanPhy.Mathematics.LieAlgebra ℚ (Plane × ℚ) :=
  CentralExtension.algebra areaCocycle area_closed

def q : Plane × ℚ := (e 0, 0)
def p : Plane × ℚ := (e 1, 0)
def z : Plane × ℚ := (0, 1)

theorem heisenberg_bracket : heisenberg.bracket q p = z := by
  apply Prod.ext
  · rfl
  · norm_num [heisenberg, CentralExtension.algebra, CentralExtension.bracket,
      areaCocycle, area, q, p, z, e]

theorem heisenberg_center (x : Plane × ℚ) : heisenberg.bracket z x = 0 :=
  CentralExtension.inclusion_central areaCocycle 1 x

theorem heisenberg_not_trivial : ¬Nonempty (CentralExtension.Equivalence areaCocycle 0) := by
  rintro ⟨E⟩
  apply area_not_boundary
  refine ⟨E.sectionCochain, ?_⟩
  simpa using E.coboundary_section

/-- A nonabelian affine bracket with the sign used by the quadratic ghost model. -/
def affineBracket (x y : Plane) : Plane := ![0, -area x y]

def affine : LeanPhy.Mathematics.LieAlgebra ℚ Plane where
  bracket := affineBracket
  add_left := by intros; ext i; fin_cases i <;> simp [affineBracket, area]; ring
  add_right := by intros; ext i; fin_cases i <;> simp [affineBracket, area]; ring
  smul_left := by intros; ext i; fin_cases i <;> simp [affineBracket, area]; ring
  smul_right := by intros; ext i; fin_cases i <;> simp [affineBracket, area]; ring
  zero_left := by intro x; ext i; fin_cases i <;> simp [affineBracket, area]
  alternating := by intro x; ext i; fin_cases i <;> simp [affineBracket, area]; ring
  antisymm := by intros; ext i; fin_cases i <;> simp [affineBracket, area]; ring
  jacobi := by intros; ext i; fin_cases i <;> simp [affineBracket, area]; ring

def affineCoefficients : LieModule affine ℚ := trivialLieModule affine

theorem affine_basis_bracket : affine.bracket (e 0) (e 1) = -e 1 := by
  ext i
  fin_cases i <;> norm_num [affine, affineBracket, area, e]

theorem affine_d2_d1 (φ : Plane →ₗ[ℚ] ℚ) :
    differential2 affineCoefficients (differential1 affineCoefficients φ) = 0 :=
  differential2_differential1 _ _

def affineBoundary : LieCochain2 affine affineCoefficients :=
  differential1 affineCoefficients (LinearMap.proj 1)

theorem affineBoundary_closed : IsTwoCocycle affineCoefficients affineBoundary :=
  differential2_differential1 _ _

theorem affineBoundary_nonzero : affineBoundary ≠ 0 := by
  intro h
  have hh := congrArg (fun ω : LieCochain2 affine affineCoefficients => ω (e 0) (e 1)) h
  change differential1 (trivialLieModule affine) (LinearMap.proj 1) (e 0) (e 1) = 0 at hh
  rw [differential1_trivial, affine_basis_bracket, map_neg, neg_neg] at hh
  norm_num [e] at hh

theorem affineBoundary_class_zero : classOf affineCoefficients affineBoundary affineBoundary_closed = 0 :=
  (classOf_eq_zero_iff _ _ _).mpr ⟨LinearMap.proj 1, rfl⟩

def removeAffineCentralTerm : CentralExtension.Equivalence affineBoundary 0 :=
  CentralExtension.equivalenceOfCoboundary affineBoundary 0 (LinearMap.proj 1)
    (by simp [affineBoundary, affineCoefficients]) affineBoundary_closed

theorem affine_central_term_removable (x y : Plane × ℚ) :
    removeAffineCentralTerm.linearEquiv (CentralExtension.bracket affineBoundary x y) =
      CentralExtension.bracket (0 : LieCochain2 affine affineCoefficients)
        (removeAffineCentralTerm.linearEquiv x) (removeAffineCentralTerm.linearEquiv y) :=
  removeAffineCentralTerm.map_bracket x y

/-- The degree-one cochain represented as a linear ghost polynomial. -/
noncomputable def oneGhost (φ : Plane →ₗ[ℚ] ℚ) : GhostPolynomial ℚ 2 :=
  φ (e 0) • generator 0 + φ (e 1) • generator 1

/-- A degree-two cochain represented by its only independent component. -/
noncomputable def twoGhost (ω : LieCochain2 affine affineCoefficients) : GhostPolynomial ℚ 2 :=
  ω (e 0) (e 1) • (generator 0 * generator 1)

/-- A degree-one CE/ghost intertwining theorem with a checked bracket sign. -/
theorem affine_ghost_bridge (φ : Plane →ₗ[ℚ] ℚ) :
    quadratic (R := ℚ) (0 : Fin 2) 1 (oneGhost φ) =
      twoGhost (differential1 affineCoefficients φ) := by
  unfold oneGhost twoGhost
  have hce : differential1 affineCoefficients φ (e 0) (e 1) = φ (e 1) := by
    change differential1 (trivialLieModule affine) φ (e 0) (e 1) = _
    rw [differential1_trivial, affine_basis_bracket, map_neg, neg_neg]
  rw [hce]
  simp [quadratic, map_smul]

theorem heisenberg_all_closed (ω : HeisenbergCohomology.C2) :
    IsTwoCocycle HeisenbergCohomology.coefficients ω := HeisenbergCohomology.all_closed ω

theorem heisenberg_ce_matrix (φ : HeisenbergCohomology.Space →ₗ[ℚ] ℚ) :
    HeisenbergCohomology.coordinates (differential1 HeisenbergCohomology.coefficients φ) =
      LeanPhy.Generated.Heisenberg.d1.toLin' (LieCochainCoordinates.oneEquiv 3 φ) :=
  HeisenbergCohomology.differential1_coordinates φ

theorem heisenberg_h2_dimension : Module.finrank ℚ (H2 HeisenbergCohomology.coefficients) = 2 :=
  HeisenbergCohomology.h2_finrank

theorem heisenberg_boundary_test (ω : HeisenbergCohomology.C2) :
    IsTwoCoboundary HeisenbergCohomology.coefficients ω ↔
      ω (LieCochainCoordinates.e 0) (LieCochainCoordinates.e 2) = 0 ∧
      ω (LieCochainCoordinates.e 1) (LieCochainCoordinates.e 2) = 0 :=
  HeisenbergCohomology.boundary_iff ω

theorem heisenberg_normal_form (ω : HeisenbergCohomology.C2) :
    differential1 HeisenbergCohomology.coefficients (HeisenbergCohomology.reduction.primitive ω) +
      HeisenbergCohomology.reduction.represent (HeisenbergCohomology.parameters ω) = ω :=
  HeisenbergCohomology.normal_form ω

theorem heisenberg_extension_parameters (ω η : HeisenbergCohomology.C2) :
    Nonempty (CentralExtension.Equivalence ω η) ↔
      HeisenbergCohomology.parameters ω = HeisenbergCohomology.parameters η :=
  HeisenbergCohomology.extension_equivalence_iff ω η

def package : TheoryPackage :=
  TheoryPackage.empty "Lie cohomology and central extensions" "algebraic cohomology"
    |>.addAssumptionText "declared Lie models"
      "rational abelian plane, affine bracket [e_0,e_1] = -e_1, and three-dimensional Heisenberg bracket [e_0,e_1] = e_2; trivial coefficients"
      "LeanPhy.Examples.LieCohomologyResearch"
    |>.addTheoremWithAssumptions "CE nilpotency in degree one" "d_2 d_1 = 0"
      "LeanPhy.Examples.LieCohomologyResearch.affine_d2_d1" ["declared Lie models"] affine_d2_d1
    |>.addTheoremWithAssumptions "area cocycle" "the area form is a two-cocycle on the abelian plane"
      "LeanPhy.Examples.LieCohomologyResearch.area_closed" ["declared Lie models"] area_closed
    |>.addTheoremWithAssumptions "nontrivial H2 class" "the area cocycle has nonzero class in H2"
      "LeanPhy.Examples.LieCohomologyResearch.heisenberg_class_nonzero" ["declared Lie models"]
      heisenberg_class_nonzero
    |>.addTheoremWithAssumptions "Heisenberg bracket" "[q,p] = z in the constructed extension"
      "LeanPhy.Examples.LieCohomologyResearch.heisenberg_bracket" ["declared Lie models"] heisenberg_bracket
    |>.addTheoremWithAssumptions "central generator" "[z,x] = 0 for every x"
      "LeanPhy.Examples.LieCohomologyResearch.heisenberg_center" ["declared Lie models"] heisenberg_center
    |>.addTheoremWithAssumptions "inequivalent central extension" "the Heisenberg extension cannot be removed fixing base and center"
      "LeanPhy.Examples.LieCohomologyResearch.heisenberg_not_trivial" ["declared Lie models"] heisenberg_not_trivial
    |>.addTheoremWithAssumptions "nonzero coboundary" "the affine cocycle is nonzero as a cochain"
      "LeanPhy.Examples.LieCohomologyResearch.affineBoundary_nonzero" ["declared Lie models"] affineBoundary_nonzero
    |>.addTheoremWithAssumptions "zero coboundary class" "the same affine cocycle has zero H2 class"
      "LeanPhy.Examples.LieCohomologyResearch.affineBoundary_class_zero" ["declared Lie models"] affineBoundary_class_zero
    |>.addTheoremWithAssumptions "removable central term" "a supplied shear removes the affine central term"
      "LeanPhy.Examples.LieCohomologyResearch.affine_central_term_removable" ["declared Lie models"] affine_central_term_removable
    |>.addTheoremWithAssumptions "affine ghost CE bridge" "s(ghost(phi)) = ghost(d_1 phi) for every linear cochain"
      "LeanPhy.Examples.LieCohomologyResearch.affine_ghost_bridge" ["declared Lie models"] affine_ghost_bridge
    |>.addTheoremWithAssumptions "all Heisenberg two-cochains closed" "every alternating two-cochain of the declared Heisenberg algebra is closed"
      "LeanPhy.Examples.LieCohomologyResearch.heisenberg_all_closed" ["declared Lie models"] heisenberg_all_closed
    |>.addTheoremWithAssumptions "Heisenberg CE matrix bridge" "the generated d1 matrix represents the declared Lie differential"
      "LeanPhy.Examples.LieCohomologyResearch.heisenberg_ce_matrix" ["declared Lie models"] heisenberg_ce_matrix
    |>.addTheoremWithAssumptions "complete Heisenberg H2 dimension" "the actual H2 quotient has rational dimension two"
      "LeanPhy.Examples.LieCohomologyResearch.heisenberg_h2_dimension" ["declared Lie models"] heisenberg_h2_dimension
    |>.addTheoremWithAssumptions "Heisenberg boundary decision" "a cocycle is a boundary exactly when both class parameters vanish"
      "LeanPhy.Examples.LieCohomologyResearch.heisenberg_boundary_test" ["declared Lie models"] heisenberg_boundary_test
    |>.addTheoremWithAssumptions "Heisenberg normal form" "every two-cochain decomposes into a boundary with primitive and a computed representative"
      "LeanPhy.Examples.LieCohomologyResearch.heisenberg_normal_form" ["declared Lie models"] heisenberg_normal_form
    |>.addTheoremWithAssumptions "Heisenberg extension parameters" "equality of the two parameters characterizes extension equivalence fixing base and center"
      "LeanPhy.Examples.LieCohomologyResearch.heisenberg_extension_parameters" ["declared Lie models"] heisenberg_extension_parameters
    |>.addBoundaryText "algebraic scope" "no topology, Lie-group integration or Hilbert representation is supplied"
    |>.addObligationText "general ghost complex"
      "extend the checked affine degree-one bridge to general Lie algebras, all degrees and matter coefficients"
      "research model"
    |>.addObligationText "physical interpretation"
      "justify the representation, normalization and connection to the target physical charge algebra or anomaly"
      "research model"

def project : ResearchProject := ResearchProject.ofPackages "Lie cohomology research" [package]

def manifest : ResearchManifest :=
  ResearchManifest.ofProject "Lie cohomology research manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Examples.LieCohomologyResearch", "LeanPhy.Examples.HeisenbergCohomology",
      "LeanPhy.Examples.Generated.HeisenbergReduction", "examples/cohomology/heisenberg.json",
      "scripts/reduce_cohomology.py", "lakefile.toml", "lean-toolchain"]

example : project.claimCount = 16 := rfl
example : project.obligationCount = 2 := rfl
example : project.diagnosticCount = 0 := by decide

def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args

end LeanPhy.Examples.LieCohomologyResearch
