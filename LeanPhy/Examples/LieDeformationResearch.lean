import LeanPhy.Mathematics.LieDeformation
import LeanPhy.Examples.Generated.DiscoveredLieDomain
import LeanPhy.CLI

/-!
# Exploring infinitesimal directions and an actual obstruction

Starting at the abelian three-dimensional algebra, take
`ω(e₀,e₁)=a e₀`, `ω(e₁,e₂)=b e₁`. Every `(a,b)` defines a first-order
deformation. Exactly the union `a*b=0` extends through order two; these
directions also have an explicit polynomial family of genuine Lie brackets.
At `(1,1)`, even an arbitrary second-order correction cannot remove Jacobi.
On a nonabelian base, a nonzero infinitesimal bracket can instead be a mere
change of generators. Both cases use the actual adjoint H² quotient.
-/

namespace LeanPhy.Examples.LieDeformationResearch

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates LeanPhy.Workflow
open scoped _root_.Classical
open LeanPhy.Generated

noncomputable section
set_option maxSynthPendingDepth 5
variable {K : Type*} [Field K] [CharZero K]
abbrev Space (K : Type*) := Fin 3 → K

def abelian : LeanPhy.Mathematics.LieAlgebra K (Space K) where
  bracket := fun _ _ => 0
  add_left := by intros; simp
  add_right := by intros; simp
  smul_left := by intros; simp
  smul_right := by intros; simp
  zero_left := by intros; rfl
  alternating := by intros; rfl
  antisymm := by intros; simp
  jacobi := by intros; simp

def direction (a b : K) : LieDeformation.Cochain (abelian : LeanPhy.Mathematics.LieAlgebra K (Space K)) where
  eval := DiscoveredLieDomain.bracket ![a,b,0]
  map_add_left' := by intros; ext i; fin_cases i <;> simp [DiscoveredLieDomain.bracket] <;> ring
  map_add_right' := by intros; ext i; fin_cases i <;> simp [DiscoveredLieDomain.bracket] <;> ring
  map_smul_left' := by intros; ext i; fin_cases i <;> simp [DiscoveredLieDomain.bracket] <;> ring
  map_smul_right' := by intros; ext i; fin_cases i <;> simp [DiscoveredLieDomain.bracket] <;> ring
  alternating' := by intros; ext i; fin_cases i <;> dsimp [DiscoveredLieDomain.bracket] <;> ring

omit [CharZero K] in
theorem abelian_differential2 (ν : LieDeformation.Cochain (abelian : LeanPhy.Mathematics.LieAlgebra K (Space K))) :
    differential2 (adjointLieModule abelian) ν = 0 := by
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro y
  apply LinearMap.ext; intro z
  rw [differential2_apply]
  simp [abelian, adjointLieModule]

omit [CharZero K] in
theorem every_direction_firstOrder (a b : K) :
    IsTwoCocycle (adjointLieModule abelian) (direction a b) := abelian_differential2 _

def firstOrder (a b : K) : LeanPhy.Mathematics.LieAlgebra K (Space K × Space K) :=
  LieDeformation.algebra (direction a b) (every_direction_firstOrder a b)

omit [CharZero K] in
theorem direction_eq_zero_iff (a b : K) : direction a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have ha := congrArg (fun ω : LieDeformation.Cochain (abelian (K := K)) => ω (e 0) (e 1) 0) h
    have hb := congrArg (fun ω : LieDeformation.Cochain (abelian (K := K)) => ω (e 1) (e 2) 1) h
    exact ⟨by simpa [direction, DiscoveredLieDomain.bracket, e] using ha,
      by simpa [direction, DiscoveredLieDomain.bracket, e] using hb⟩
  · rintro ⟨rfl,rfl⟩; ext x y i; fin_cases i <;> simp [direction,DiscoveredLieDomain.bracket]

omit [CharZero K] in
theorem abelian_boundary_iff_zero (ω : LieDeformation.Cochain
    (abelian : LeanPhy.Mathematics.LieAlgebra K (Space K))) :
    IsTwoCoboundary (adjointLieModule abelian) ω ↔ ω = 0 := by
  constructor
  · rintro ⟨φ,rfl⟩; ext x y i; simp [differential1, adjointLieModule, abelian]
  · rintro rfl; exact ⟨0, by ext x y i; simp [differential1, adjointLieModule, abelian]⟩

omit [CharZero K] in
theorem direction_class_zero_iff (a b : K) :
    classOf (adjointLieModule abelian) (direction a b) (every_direction_firstOrder a b) = 0 ↔
      a = 0 ∧ b = 0 := by
  rw [classOf_eq_zero_iff, abelian_boundary_iff_zero, direction_eq_zero_iff]

omit [CharZero K] in
theorem direction_removable_iff (a b : K) :
    Nonempty (LieDeformation.Equivalence (direction a b) 0) ↔ a = 0 ∧ b = 0 := by
  rw [LieDeformation.nonempty_equivalence_zero_iff _ (every_direction_firstOrder a b),
    abelian_boundary_iff_zero, direction_eq_zero_iff]

omit [CharZero K] in
theorem obstruction_basis (a b : K) :
    LieDeformation.obstruction (direction a b) (e 0) (e 1) (e 2) = ![a*b,0,0] := by
  ext i; fin_cases i <;> simp [LieDeformation.obstruction, direction, DiscoveredLieDomain.bracket, e]

/-- No correction, including corrections outside this two-parameter family,
can cancel the displayed obstruction. -/
theorem secondOrder_exists_iff (a b : K) :
    (∃ ν : LieDeformation.Cochain abelian, ∃ A : LeanPhy.Mathematics.LieAlgebra K (Space K × Space K × Space K),
      A.bracket = LieDeformation.secondBracket (direction a b) ν) ↔ a*b=0 := by
  constructor
  · rintro ⟨ν,A,hA⟩
    have h := LieDeformation.obstruction_of_secondOrder_model (direction a b) ν A hA (e 0) (e 1) (e 2)
    rw [abelian_differential2, obstruction_basis] at h
    have h0 := congrFun h 0
    simpa using h0
  · intro hab
    have hc : DiscoveredLieDomain.Conditions ![a,b,0] := ⟨hab, by simp⟩
    refine ⟨0, LieDeformation.secondAlgebra (direction a b) 0 (every_direction_firstOrder a b) ?_, rfl⟩
    intro x y z
    rw [abelian_differential2]
    simpa [LieDeformation.obstruction, direction, DiscoveredLieDomain.algebra] using
      (DiscoveredLieDomain.algebra ![a,b,0] hc).jacobi x y z

theorem obstructed_class_nonzero :
    classOf (adjointLieModule abelian) (direction (1 : ℚ) 1) (every_direction_firstOrder 1 1) ≠ 0 := by
  intro h
  have hh := (direction_class_zero_iff (1 : ℚ) 1).mp h
  norm_num at hh

theorem obstructed_no_secondOrder :
    ¬∃ ν : LieDeformation.Cochain abelian, ∃ A : LeanPhy.Mathematics.LieAlgebra ℚ (Space ℚ × Space ℚ × Space ℚ),
      A.bracket = LieDeformation.secondBracket (direction 1 1) ν := by
  rw [secondOrder_exists_iff]; norm_num

def integratedFamily (a b : K) (hab : a*b=0) (s : K) :
    LeanPhy.Mathematics.LieAlgebra K (Space K) :=
  DiscoveredLieDomain.algebra ![s*a,s*b,0] ⟨by
    change (s*a)*(s*b)=0
    calc _ = s*s*(a*b) := by ring
         _ = 0 := by rw [hab,mul_zero], by simp⟩

theorem integratedFamily_bracket (a b : K) (hab : a*b=0) (s : K) (x y : Space K) :
    (integratedFamily a b hab s).bracket x y = s • direction a b x y := by
  ext i; fin_cases i <;> simp [integratedFamily,DiscoveredLieDomain.algebra,DiscoveredLieDomain.bracket,direction] <;> ring

theorem integratedFamily_origin (a b : K) (hab : a*b=0) (x y : Space K) :
    (integratedFamily a b hab 0).bracket x y = abelian.bracket x y := by
  simp [integratedFamily_bracket,abelian]

def affine : LeanPhy.Mathematics.LieAlgebra ℚ (Space ℚ) :=
  DiscoveredLieDomain.algebra ![1,0,0] ⟨by norm_num, by norm_num⟩

def scalingDirection : LieDeformation.Cochain affine :=
  differential1 (adjointLieModule affine) LinearMap.id

theorem scalingDirection_closed : IsTwoCocycle (adjointLieModule affine) scalingDirection :=
  differential2_differential1 _ _

theorem scalingDirection_eval (x y : Space ℚ) : scalingDirection x y = affine.bracket x y := by
  change affine.bracket x y - affine.bracket y x - affine.bracket x y = affine.bracket x y
  rw [affine.antisymm y x]; abel

theorem scalingDirection_nonzero : scalingDirection ≠ 0 := by
  intro h
  have hh := congrArg (fun ω : LieDeformation.Cochain affine => ω (e 0) (e 1) 0) h
  rw [scalingDirection_eval] at hh
  norm_num [affine,DiscoveredLieDomain.algebra,DiscoveredLieDomain.bracket,e] at hh

def removeScaling : LieDeformation.Equivalence scalingDirection 0 :=
  LieDeformation.equivalenceOfCoboundary scalingDirection 0 LinearMap.id (by simp [scalingDirection])
    scalingDirection_closed

theorem scaling_class_zero : classOf (adjointLieModule affine) scalingDirection scalingDirection_closed = 0 :=
  (classOf_eq_zero_iff _ _ _).mpr ⟨LinearMap.id,rfl⟩

theorem removeScaling_bracket (x y : Space ℚ × Space ℚ) :
    removeScaling.linearEquiv (LieDeformation.bracket scalingDirection x y) =
      LieDeformation.bracket (0 : LieDeformation.Cochain affine)
        (removeScaling.linearEquiv x) (removeScaling.linearEquiv y) :=
  removeScaling.map_bracket x y

def package : TheoryPackage :=
  TheoryPackage.empty "Lie deformation exploration" "symmetry algebra deformation"
    |>.addAssumptionText "declared algebraic models"
      "the stated Lie algebras and alternating cochains; general jet theorems over commutative rings, worked families over characteristic-zero fields"
      "LeanPhy.Mathematics.LieDeformation; LeanPhy.Examples.LieDeformationResearch"
    |>.addTheoremWithAssumptions "all first-order directions" "every parameter pair defines an adjoint cocycle"
      "LeanPhy.Examples.LieDeformationResearch.every_direction_firstOrder" ["declared algebraic models"] @every_direction_firstOrder.{0}
    |>.addTheoremWithAssumptions "actual H2 classes" "a direction represents zero exactly at the origin"
      "LeanPhy.Examples.LieDeformationResearch.direction_class_zero_iff" ["declared algebraic models"] @direction_class_zero_iff.{0}
    |>.addTheoremWithAssumptions "generator changes" "a direction is removable exactly at the origin"
      "LeanPhy.Examples.LieDeformationResearch.direction_removable_iff" ["declared algebraic models"] @direction_removable_iff.{0}
    |>.addTheoremWithAssumptions "quadratic obstruction" "the basis Jacobi obstruction has coefficient a*b"
      "LeanPhy.Examples.LieDeformationResearch.obstruction_basis" ["declared algebraic models"] @obstruction_basis.{0}
    |>.addTheoremWithAssumptions "complete second-order locus" "some second-order correction exists exactly when a*b=0"
      "LeanPhy.Examples.LieDeformationResearch.secondOrder_exists_iff" ["declared algebraic models"] @secondOrder_exists_iff.{0}
    |>.addTheoremWithAssumptions "nonzero obstructed class" "the (1,1) direction has nonzero adjoint H2 class"
      "LeanPhy.Examples.LieDeformationResearch.obstructed_class_nonzero" ["declared algebraic models"] obstructed_class_nonzero
    |>.addTheoremWithAssumptions "no second-order correction" "no arbitrary correction can extend the (1,1) direction through order two"
      "LeanPhy.Examples.LieDeformationResearch.obstructed_no_secondOrder" ["declared algebraic models"] obstructed_no_secondOrder
    |>.addTheoremWithAssumptions "integrated legal directions" "directions on a*b=0 have explicit polynomial families of Lie brackets"
      "LeanPhy.Examples.LieDeformationResearch.integratedFamily_bracket" ["declared algebraic models"] @integratedFamily_bracket.{0}
    |>.addTheoremWithAssumptions "family base point" "the polynomial family starts at the original abelian algebra"
      "LeanPhy.Examples.LieDeformationResearch.integratedFamily_origin" ["declared algebraic models"] @integratedFamily_origin.{0}
    |>.addTheoremWithAssumptions "nonzero removable cochain" "the affine scaling direction is nonzero as a cochain"
      "LeanPhy.Examples.LieDeformationResearch.scalingDirection_nonzero" ["declared algebraic models"] scalingDirection_nonzero
    |>.addTheoremWithAssumptions "zero scaling class" "the affine scaling direction nevertheless has zero H2 class"
      "LeanPhy.Examples.LieDeformationResearch.scaling_class_zero" ["declared algebraic models"] scaling_class_zero
    |>.addTheoremWithAssumptions "explicit generator change" "the supplied invertible generator change preserves the first-order brackets"
      "LeanPhy.Examples.LieDeformationResearch.removeScaling_bracket" ["declared algebraic models"] removeScaling_bracket
    |>.addTheoremWithAssumptions "first-order classification" "actual adjoint H2 equality is equivalent to a reduction- and tangent-preserving bracket equivalence"
      "LeanPhy.Mathematics.LieDeformation.class_eq_iff_nonempty_equivalence" ["declared algebraic models"] @LieDeformation.class_eq_iff_nonempty_equivalence.{0,0}
    |>.addTheoremWithAssumptions "second-order model existence" "full second-order Lie model existence is equivalent to the cocycle and obstruction cancellation equations"
      "LeanPhy.Mathematics.LieDeformation.secondAlgebra_exists_iff" ["declared algebraic models"] @LieDeformation.secondAlgebra_exists_iff.{0,0}
    |>.addBoundaryText "finite order and fixed identification"
      "general classification is first-order with reduction and tangent fixed; second-order existence requires the correction equation; no general higher-order, convergent, global or Lie-group deformation claim"
    |>.addObligationText "physical interpretation"
      "identify the algebra, deformation parameter and generator equivalence with the intended physical symmetry problem" "research model"

def project : ResearchProject := ResearchProject.ofPackages "Lie deformation research" [package]
def manifest : ResearchManifest :=
  ResearchManifest.ofProject "Lie deformation research manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Mathematics.LieDeformation", "LeanPhy.Mathematics.LieCohomology2",
      "LeanPhy.Examples.LieDeformationResearch", "LeanPhy.Examples.Generated.DiscoveredLieDomain",
      "examples/lie-cohomology/discovery/combined.json", "lean-toolchain", "lakefile.toml"]
example : project.claimCount = 14 := rfl
example : project.obligationCount = 1 := rfl
example : project.diagnosticCount = 0 := by decide
def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args

end
end LeanPhy.Examples.LieDeformationResearch
