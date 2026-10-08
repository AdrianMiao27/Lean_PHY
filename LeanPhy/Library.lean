import LeanPhy.Library.Core
import LeanPhy.Mathematics.LieDeformationThirdSearch
import LeanPhy.Mathematics.LieDeformationThirdObstruction
import LeanPhy.Examples.Generated.HeisenbergThirdParameter
import LeanPhy.Examples.Generated.AffineFourThirdCharacter
import LeanPhy.Mathematics.LieDeformationObstruction
import LeanPhy.Mathematics.LieDeformationGauge
import LeanPhy.Quantum.Pauli
import LeanPhy.FieldTheory.CCR
import LeanPhy.GaugeTheory.FieldStrength
import LeanPhy.HighEnergy.Gamma
import LeanPhy.Classical.Symplectic
import LeanPhy.Relativity.Minkowski
import LeanPhy.StatMech.FiniteGibbs
import LeanPhy.GaugeTheory.QuadraticGhost
import LeanPhy.GaugeTheory.LieGhost
import LeanPhy.GaugeTheory.LieGhostFamily
import LeanPhy.GaugeTheory.GhostDegree
import LeanPhy.GaugeTheory.LieGhostCohomology
import LeanPhy.GaugeTheory.LieGhostMatterCohomology
import LeanPhy.Mathematics.LieDeformationReduction
import LeanPhy.Mathematics.LieDeformationSecondOrder
import LeanPhy.Mathematics.LieDeformation
import LeanPhy.Mathematics.CentralExtension
import LeanPhy.Mathematics.SolvableLieFamily
import LeanPhy.Examples.HeisenbergCohomology
import LeanPhy.Examples.Generated.SolvableVector
import LeanPhy.Examples.Generated.SolvableStrata
import LeanPhy.Examples.Generated.DeterminantStrata
import LeanPhy.Examples.Generated.HeisenbergParameter
import LeanPhy.Examples.Generated.AffineVectorParameters
import LeanPhy.Examples.Generated.DiscoveredLieDomain

/-!
# Kernel-checked physics lemma library

Long research developments need a way to find a reusable theorem without
turning a text search result into evidence.  `CheckedLemma` is the small
bridge used here: every entry contains the original proposition and its proof
as dependent fields, so the catalogue cannot contain a claim that did not
elaborate in Lean.  Search only filters already compiled entries and returns
metadata for navigation; it never constructs a proof from a string.

The catalogue is deliberately small and representative.  Domain packages can
extend it with `CheckedLemma.ofTheorem` in their own source files, while the
ordinary Lean theorem namespace remains the authoritative API.  This keeps
the feature compatible with `#check`, `exact?`, editor completion and normal
imports rather than introducing a second theorem language.
-/

namespace LeanPhy.Library

open scoped Matrix

/-! Explicitly typed wrappers keep polymorphic theorem constants from leaving
typeclass metavariables unresolved while the catalogue is elaborated.  The
wrappers are themselves ordinary kernel-checked theorems and preserve the
universal hypotheses for downstream users. -/

theorem number_commutator_universal :
    ∀ {A : Type} [Ring A] (a adag : A),
      LeanPhy.Quantum.commutator a adag = 1 →
      LeanPhy.Quantum.commutator (LeanPhy.FieldTheory.number adag a) adag = adag := by
  intro A _ a adag h
  exact LeanPhy.FieldTheory.number_commutator a adag h

theorem fieldStrength_antisym_universal :
    ∀ {A : Type} [Ring A] (D : Fin 4 → A) (mu nu : Fin 4),
      LeanPhy.GaugeTheory.fieldStrength D mu nu =
        -LeanPhy.GaugeTheory.fieldStrength D nu mu := by
  intro A _ D mu nu
  exact LeanPhy.GaugeTheory.fieldStrength_antisym D mu nu

theorem symplectic_mul_universal :
    ∀ (A B : Matrix (Fin 2) (Fin 2) ℝ),
      Matrix.transpose A * LeanPhy.Classical.symplecticJ * A = LeanPhy.Classical.symplecticJ →
      Matrix.transpose B * LeanPhy.Classical.symplecticJ * B = LeanPhy.Classical.symplecticJ →
      Matrix.transpose (A * B) * LeanPhy.Classical.symplecticJ * (A * B) =
        LeanPhy.Classical.symplecticJ := by
  intro A B hA hB
  exact LeanPhy.Classical.symplectic_mul A B hA hB

theorem finiteGibbsWeight_nonneg_universal :
    ∀ {ι : Type} [Fintype ι] [Nonempty ι]
      (β : ℝ) (E : ι → ℝ) (i : ι),
      0 ≤ LeanPhy.StatMech.finiteGibbsWeight β E i := by
  intro ι _ _ β E i
  exact LeanPhy.StatMech.finiteGibbsWeight_nonneg β E i

def numberCommutatorEntry : CheckedLemma where
  name := "number_commutator"
  domain := "field-theory"
  statement := "[a†a, a†] = a† under [a,a†] = 1"
  source := "LeanPhy.FieldTheory.CCR"
  tags := ["CCR", "ladder", "commutator"]
  proposition := ∀ {A : Type} [Ring A] (a adag : A),
    LeanPhy.Quantum.commutator a adag = 1 →
      LeanPhy.Quantum.commutator (LeanPhy.FieldTheory.number adag a) adag = adag
  proof := number_commutator_universal

def fieldStrengthEntry : CheckedLemma where
  name := "fieldStrength_antisym"
  domain := "gauge"
  statement := "F μ ν = - F ν μ"
  source := "LeanPhy.GaugeTheory.FieldStrength"
  tags := ["gauge", "curvature", "indices"]
  proposition := ∀ {A : Type} [Ring A] (D : Fin 4 → A) (mu nu : Fin 4),
    LeanPhy.GaugeTheory.fieldStrength D mu nu =
      -LeanPhy.GaugeTheory.fieldStrength D nu mu
  proof := fieldStrength_antisym_universal

def symplecticEntry : CheckedLemma where
  name := "symplectic_mul"
  domain := "classical"
  statement := "the product of canonical matrices is canonical"
  source := "LeanPhy.Classical.Symplectic"
  tags := ["Hamiltonian", "symplectic", "canonical"]
  proposition := ∀ (A B : Matrix (Fin 2) (Fin 2) ℝ),
    Matrix.transpose A * LeanPhy.Classical.symplecticJ * A =
        LeanPhy.Classical.symplecticJ →
      Matrix.transpose B * LeanPhy.Classical.symplecticJ * B =
        LeanPhy.Classical.symplecticJ →
      Matrix.transpose (A * B) * LeanPhy.Classical.symplecticJ * (A * B) =
        LeanPhy.Classical.symplecticJ
  proof := symplectic_mul_universal

def gibbsEntry : CheckedLemma where
  name := "finiteGibbsWeight_nonneg"
  domain := "stat-mech"
  statement := "finite Gibbs weights are nonnegative"
  source := "LeanPhy.StatMech.FiniteGibbs"
  tags := ["Gibbs", "probability", "statistical"]
  proposition := ∀ {ι : Type} [Fintype ι] [Nonempty ι]
      (β : ℝ) (E : ι → ℝ) (i : ι),
      0 ≤ LeanPhy.StatMech.finiteGibbsWeight β E i
  proof := finiteGibbsWeight_nonneg_universal

/-! The concrete entries use polymorphic theorems directly.  A universal
theorem is still a useful result in the catalogue: its proposition remains a
Pi type and its proof is the theorem constant that Lean checked. -/

theorem ghost_koszul_nilpotency :
    ∀ {R : Type} [CommRing R] {n : Nat} (f : Module.Dual R (Fin n → R))
      (x : LeanPhy.GaugeTheory.GhostPolynomial R n),
      LeanPhy.GaugeTheory.GhostPolynomial.contract f
        (LeanPhy.GaugeTheory.GhostPolynomial.contract f x) = 0 := by
  intro R _ n f x
  exact LeanPhy.GaugeTheory.GhostPolynomial.contract_sq f x

theorem ghost_left_derivative_car :
    ∀ {R : Type} [CommRing R] {n : Nat} (i j : Fin n)
      (x : LeanPhy.GaugeTheory.GhostPolynomial R n),
      LeanPhy.GaugeTheory.GhostPolynomial.derivative i
          (LeanPhy.GaugeTheory.GhostPolynomial.generator j * x) +
        LeanPhy.GaugeTheory.GhostPolynomial.generator j *
          LeanPhy.GaugeTheory.GhostPolynomial.derivative i x = if i = j then x else 0 := by
  intro R _ n i j x
  exact LeanPhy.GaugeTheory.GhostPolynomial.derivative_generator_mul i j x

theorem ghost_quadratic_nilpotency :
    ∀ {R : Type} [CommRing R] {n : Nat} (i j : Fin n), i ≠ j →
      ∀ x : LeanPhy.GaugeTheory.GhostPolynomial R n,
      LeanPhy.GaugeTheory.GhostPolynomial.quadratic i j
        (LeanPhy.GaugeTheory.GhostPolynomial.quadratic i j x) = 0 := by
  intro R _ n i j hij x
  exact LeanPhy.GaugeTheory.GhostPolynomial.quadratic_sq i j hij x

theorem ghost_quadratic_nontriviality :
    ∀ {R : Type} [CommRing R] [Nontrivial R] {n : Nat} (i j : Fin n), i ≠ j →
      LeanPhy.GaugeTheory.GhostPolynomial.quadratic i j
        (LeanPhy.GaugeTheory.GhostPolynomial.generator (R := R) j) ≠ 0 := by
  intro R _ _ n i j hij
  exact LeanPhy.GaugeTheory.GhostPolynomial.quadratic_nonzero i j hij

open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial in
theorem ghost_finite_nilpotency_criterion :
    ∀ {R : Type} [CommRing R] {n : Nat} (F : Fin n → GhostPolynomial R n),
      (∀ i, parityInvolution (F i) = F i) →
      ((∀ x, vectorField F (vectorField F x) = 0) ↔ ∀ i, vectorField F (F i) = 0) :=
  fun F hF => vectorField_sq_iff F hF

open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Mathematics
  LeanPhy.Mathematics.LieCohomology in
theorem lie_ghost_degree_one_bridge :
    ∀ {R : Type} [CommRing R] {n : Nat} (L : Mathematics.LieAlgebra R (Fin n → R))
      (φ : Module.Dual R (Fin n → R)),
      lieDifferential L (ghostOne φ) = ghostTwo L (differential1 (trivialLieModule L) φ) :=
  fun L φ => lieDifferential_ghostOne L φ

open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial in
theorem lie_ghost_jacobi_nilpotency :
    ∀ {R : Type} [CommRing R] {n : Nat} (L : Mathematics.LieAlgebra R (Fin n → R))
      (x : GhostPolynomial R n), lieDifferential L (lieDifferential L x) = 0 :=
  fun L x => lieDifferential_sq L x

open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Mathematics
  LeanPhy.Mathematics.LieCohomology in
theorem lie_ghost_degree_two_bridge :
    ∀ {R : Type} [CommRing R] {n : Nat} (L : Mathematics.LieAlgebra R (Fin n → R))
      (ω : LieCochain2 L (trivialLieModule L : LieModule L R)),
      lieDifferential L (ghostTwo L ω) = ghostThree L (differential2Cochain (trivialLieModule L) ω) :=
  fun L ω => lieDifferential_ghostTwo L ω

open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial in
theorem lie_ghost_integer_degree :
    ∀ {R : Type} [CommRing R] {n : Nat} (L : Mathematics.LieAlgebra R (Fin n → R))
      {d : Int} {x : GhostPolynomial R n}, x ∈ degree d → lieDifferential L x ∈ degree (d + 1) :=
  by
    intro R _ n L d x hx
    exact lieDifferential_mem_degree L hx

open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial in
theorem ghost_koszul_integer_degree :
    ∀ {R : Type} [CommRing R] {n : Nat} (f : Module.Dual R (Fin n → R))
      {d : Int} {x : GhostPolynomial R n}, x ∈ degree d → contract f x ∈ degree (d - 1) :=
  by
    intro R _ n f d x hx
    exact contract_mem_degree f hx

open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial in
theorem lie_ghost_homogeneous_primitive :
    ∀ {R : Type} [CommRing R] {n : Nat} (L : Mathematics.LieAlgebra R (Fin n → R))
      {k : Nat} {x : GhostPolynomial R n}, x ∈ natDegree (k + 1) →
      ((∃ y, lieDifferential L y = x) ↔ ∃ y ∈ natDegree k, lieDifferential L y = x) :=
  by
    intro R _ n L k x hx
    exact homogeneous_exact_iff L hx

open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial in
theorem lie_ghost_scalar_boundary :
    ∀ {R : Type} [CommRing R] {n : Nat} (L : Mathematics.LieAlgebra R (Fin n → R))
      (r : R), (∃ y, lieDifferential L y = algebraMap R (GhostPolynomial R n) r) ↔ r = 0 :=
  fun L r => scalar_exact_iff L r

open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology in
theorem lie_ghost_closed_reflection :
    ∀ {R : Type} [CommRing R] {n : Nat} (L : Mathematics.LieAlgebra R (Fin n → R))
      (ω : LieCochain2 L (trivialLieModule L : LieModule L R)),
      lieDifferential L (ghostTwo L ω) = 0 ↔ IsTwoCocycle (trivialLieModule L) ω :=
  fun L ω => ghostTwo_closed_iff L ω

open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology in
theorem lie_ghost_exact_reflection :
    ∀ {R : Type} [CommRing R] {n : Nat} (L : Mathematics.LieAlgebra R (Fin n → R))
      (ω : LieCochain2 L (trivialLieModule L : LieModule L R)),
      (∃ y, lieDifferential L y = ghostTwo L ω) ↔ IsTwoCoboundary (trivialLieModule L) ω :=
  fun L ω => ghostTwo_exact_iff L ω

open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology in
theorem lie_ghost_h2_equivalence :
    ∀ {R : Type} [CommRing R] {n : Nat} (L : Mathematics.LieAlgebra R (Fin n → R)),
      Nonempty (H2 (trivialLieModule L : LieModule L R) ≃ₗ[R] GhostH2 L) :=
  fun L => ⟨h2GhostEquiv L⟩

open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology in
theorem lie_ghost_complete_coordinates :
    ∀ {R : Type} [CommRing R] {n : Nat} (L : Mathematics.LieAlgebra R (Fin n → R)),
      Nonempty (LieCochain2 L (trivialLieModule L : LieModule L R) ≃ₗ[R] natDegree (R := R) (n := n) 2) :=
  fun L => ⟨ghostTwoEquiv L⟩

open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology in
theorem lie_matter_nilpotent :
    ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {n : Nat}
      {L : Mathematics.LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M) (x : MatterGhost R n M), matterDifferential 𝒨 (matterDifferential 𝒨 x) = 0 :=
  fun 𝒨 x => matterDifferential_sq 𝒨 x

open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology in
theorem lie_matter_degree :
    ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {n : Nat}
      {L : Mathematics.LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M) {d : Int} {x : MatterGhost R n M}, x ∈ matterDegree d → matterDifferential 𝒨 x ∈ matterDegree (d + 1) :=
  fun 𝒨 _ _ hx => matterDifferential_mem_degree 𝒨 hx

open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology in
theorem lie_matter_invariants :
    ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {n : Nat}
      {L : Mathematics.LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M) (m : M), matterDifferential 𝒨 (matterZero m) = 0 ↔ ∀ v, 𝒨.act v m = 0 :=
  fun 𝒨 m => matterZero_closed_iff 𝒨 m

open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology in
theorem lie_matter_cocycle :
    ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {n : Nat}
      {L : Mathematics.LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M) (φ : LieCochain1 L 𝒨), matterDifferential 𝒨 (matterOne 𝒨 φ) = 0 ↔ IsOneCocycle 𝒨 φ :=
  fun 𝒨 φ => matterOne_closed_iff 𝒨 φ

open LeanPhy.Mathematics.LieCohomology in
theorem lie_d2_d1 :
    ∀ {R V M : Type} [CommRing R] [AddCommGroup V] [Module R V]
      [AddCommGroup M] [Module R M] (L : Mathematics.LieAlgebra R V)
      (𝒨 : Mathematics.LieModule L M) (φ : V →ₗ[R] M),
      differential2 𝒨 (differential1 𝒨 φ) = 0 := by
  intro R V M _ _ _ _ _ L 𝒨 φ
  exact differential2_differential1 𝒨 φ

open LeanPhy.Mathematics.LieCohomology in
theorem lie_h2_zero_iff_boundary :
    ∀ {R V M : Type} [CommRing R] [AddCommGroup V] [Module R V]
      [AddCommGroup M] [Module R M] (L : Mathematics.LieAlgebra R V)
      (𝒨 : Mathematics.LieModule L M) (ω : Mathematics.LieCochain2 L 𝒨)
      (hω : IsTwoCocycle 𝒨 ω),
      classOf 𝒨 ω hω = 0 ↔ IsTwoCoboundary 𝒨 ω := by
  intro R V M _ _ _ _ _ L 𝒨 ω hω
  exact classOf_eq_zero_iff 𝒨 ω hω

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology in
theorem central_extension_classification :
    ∀ {R V M : Type} [CommRing R] [AddCommGroup V] [Module R V]
      [AddCommGroup M] [Module R M] (L : Mathematics.LieAlgebra R V)
      (ω η : LieCochain2 L (trivialLieModule L : Mathematics.LieModule L M))
      (hω : IsTwoCocycle (trivialLieModule L) ω)
      (hη : IsTwoCocycle (trivialLieModule L) η),
      classOf (trivialLieModule L) ω hω = classOf (trivialLieModule L) η hη ↔
        Nonempty (CentralExtension.Equivalence ω η) := by
  intro R V M _ _ _ _ _ L ω η hω hη
  exact CentralExtension.class_eq_iff_nonempty_equivalence ω η hω hη

open LeanPhy.Mathematics in
theorem cohomology_reduction_exactness :
    ∀ {A B C H : Type} [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
      [AddCommGroup C] [Module ℚ C] [AddCommGroup H] [Module ℚ H]
      (d₁ : A →ₗ[ℚ] B) (d₂ : B →ₗ[ℚ] C) (S : CohomologyReduction d₁ d₂ H)
      (b : B), d₂ b = 0 → ((∃ a, d₁ a = b) ↔ S.project b = 0) := by
  intro A B C H _ _ _ _ _ _ _ _ d₁ d₂ S b hb
  exact S.exact_iff b hb

open LeanPhy.Mathematics in
theorem finite_lie_cocycle_check :
    ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {n : Nat}
      (L : Mathematics.LieAlgebra R (Fin n → R)) (𝒨 : Mathematics.LieModule L M)
      (ω : LieCochain2 L 𝒨),
      (∀ i j k : Fin n, i < j → j < k → LieCohomology.differential2 𝒨 ω
        (LieCochainCoordinates.e i) (LieCochainCoordinates.e j) (LieCochainCoordinates.e k) = 0) →
      LieCohomology.IsTwoCocycle 𝒨 ω := by
  intro R M _ _ _ n L 𝒨 ω h
  exact LieCochainCoordinates.differential2_eq_zero_of_increasing 𝒨 ω h

open LeanPhy.Mathematics.DiagonalCohomology in
theorem diagonal_cohomology_exactness :
    ∀ {K I : Type} [Field K] (u v : I → K), (∀ i, v i * u i = 0) →
      ∀ x, diagonal v x = 0 →
        ((∃ y, diagonal u y = x) ↔ ∀ i, u i = 0 → v i = 0 → x i = 0) := by
  intro K I _ u v huv x hx
  exact exact_iff u v huv x hx

open scoped _root_.Classical in
theorem solvable_family_dimension :
    ∀ {K : Type} [Field K] (a b t : K),
      Module.finrank K (Mathematics.LieCohomology.H2 (Mathematics.SolvableLieFamily.coefficients a b t)) =
        (if t = a then 1 else 0) + (if t = b then 1 else 0) + (if t = a + b then 1 else 0) := by
  intro K _ a b t
  exact Mathematics.SolvableLieFamily.h2_finrank a b t

def catalog : List CheckedLemma := [
  CheckedLemma.ofTheorem "pauliXY_commutator" "quantum"
    "[σx, σy] = 2 i σz" "LeanPhy.Quantum.Pauli" ["pauli", "commutator"]
    LeanPhy.Quantum.pauliXY_commutator,
  numberCommutatorEntry,
  fieldStrengthEntry,
  CheckedLemma.ofTheorem "clifford_gamma1" "high-energy"
    "γ₁² = -1" "LeanPhy.HighEnergy.Gamma" ["Dirac", "Clifford", "gamma"]
    LeanPhy.HighEnergy.clifford_gamma1,
  symplecticEntry,
  CheckedLemma.ofTheorem "metric_diagonal" "relativity"
    "the declared Minkowski metric has signature (+---)" "LeanPhy.Relativity.Minkowski"
    ["Lorentz", "metric", "relativity"] LeanPhy.Relativity.metric_diagonal,
  gibbsEntry,
  CheckedLemma.ofTheorem "ghost_koszul_nilpotency" "gauge"
    "contraction with a supplied covector squares to zero on all ghost polynomials"
    "LeanPhy.Library" ["ghost", "Grassmann", "Koszul", "nilpotency"] @ghost_koszul_nilpotency,
  CheckedLemma.ofTheorem "ghost_left_derivative_car" "gauge"
    "partial_i(c_j x) + c_j partial_i(x) = delta_ij x"
    "LeanPhy.Library" ["ghost", "Grassmann", "CAR", "derivative"] @ghost_left_derivative_car,
  CheckedLemma.ofTheorem "ghost_quadratic_nilpotency" "gauge"
    "the quadratic ghost differential c_i c_j partial_j squares to zero for distinct i,j"
    "LeanPhy.Library" ["ghost", "BRST", "quadratic", "nilpotency"] @ghost_quadratic_nilpotency,
  CheckedLemma.ofTheorem "ghost_quadratic_nontriviality" "gauge"
    "the quadratic ghost differential is nonzero over a nontrivial ring for distinct i,j"
    "LeanPhy.Library" ["ghost", "BRST", "quadratic", "nonzero"] @ghost_quadratic_nontriviality,
  CheckedLemma.ofTheorem "ghost_finite_nilpotency_criterion" "gauge"
    "an even-image Grassmann vector field squares to zero exactly when all generator images are closed"
    "LeanPhy.Library" ["ghost", "BRST", "certificate", "nilpotency"] @ghost_finite_nilpotency_criterion,
  CheckedLemma.ofTheorem "lie_ghost_degree_one_bridge" "gauge"
    "the canonical finite Lie ghost derivation agrees with degree-one CE over any commutative ring"
    "LeanPhy.Library" ["ghost", "Lie", "CE", "bridge"] @lie_ghost_degree_one_bridge,
  CheckedLemma.ofTheorem "lie_ghost_jacobi_nilpotency" "gauge"
    "Jacobi implies canonical finite Lie ghost nilpotency over every commutative ring"
    "LeanPhy.Library" ["ghost", "Lie", "Jacobi", "nilpotency"] @lie_ghost_jacobi_nilpotency,
  CheckedLemma.ofTheorem "lie_ghost_degree_two_bridge" "gauge"
    "the ghost differential intertwines CE degrees two and three without characteristic restrictions"
    "LeanPhy.Library" ["ghost", "Lie", "CE", "bridge"] @lie_ghost_degree_two_bridge,
  CheckedLemma.ofTheorem "lie_ghost_integer_degree" "gauge"
    "The canonical Lie ghost differential raises integer ghost degree by one."
    "LeanPhy.Library" ["ghost", "BRST", "integer-degree"] @lie_ghost_integer_degree,
  CheckedLemma.ofTheorem "ghost_koszul_integer_degree" "gauge"
    "Contraction lowers the actual integer ghost degree by one."
    "LeanPhy.Library" ["ghost", "Koszul", "integer-degree"] @ghost_koszul_integer_degree,
  CheckedLemma.ofTheorem "lie_ghost_homogeneous_primitive" "gauge"
    "Homogeneous boundaries have primitives of the preceding degree."
    "LeanPhy.Library" ["ghost", "cohomology", "primitive"] @lie_ghost_homogeneous_primitive,
  CheckedLemma.ofTheorem "lie_ghost_scalar_boundary" "gauge"
    "A scalar pure Lie ghost boundary is exactly zero."
    "LeanPhy.Library" ["ghost", "cohomology", "scalar"] @lie_ghost_scalar_boundary,
  CheckedLemma.ofTheorem "lie_ghost_closed_reflection" "gauge"
    "Degree-two ghost closedness is equivalent to the scalar CE cocycle condition."
    "LeanPhy.Library" ["ghost", "Lie", "cohomology", "H2"] @lie_ghost_closed_reflection,
  CheckedLemma.ofTheorem "lie_ghost_exact_reflection" "gauge"
    "Arbitrary ghost polynomial primitives exist exactly for scalar CE boundaries."
    "LeanPhy.Library" ["ghost", "Lie", "cohomology", "H2"] @lie_ghost_exact_reflection,
  CheckedLemma.ofTheorem "lie_ghost_h2_equivalence" "gauge"
    "Scalar CE H2 is linearly equivalent to the actual homogeneous ghost H2."
    "LeanPhy.Library" ["ghost", "Lie", "cohomology", "H2"] @lie_ghost_h2_equivalence,
  CheckedLemma.ofTheorem "lie_ghost_complete_coordinates" "gauge"
    "Every homogeneous degree-two ghost has a unique scalar two-cochain coordinate."
    "LeanPhy.Library" ["ghost", "Lie", "cohomology", "H2"] @lie_ghost_complete_coordinates,
  CheckedLemma.ofTheorem "lie_matter_nilpotent" "gauge"
    "A certified representation gives nilpotency on all ghost-matter tensors."
    "LeanPhy.Library" ["ghost", "matter", "Lie", "BRST"] @lie_matter_nilpotent,
  CheckedLemma.ofTheorem "lie_matter_degree" "gauge"
    "The matter differential raises integer ghost degree by one."
    "LeanPhy.Library" ["ghost", "matter", "Lie", "BRST"] @lie_matter_degree,
  CheckedLemma.ofTheorem "lie_matter_invariants" "gauge"
    "Constant closed ghost-matter states are precisely invariant vectors."
    "LeanPhy.Library" ["ghost", "matter", "Lie", "BRST"] @lie_matter_invariants,
  CheckedLemma.ofTheorem "lie_matter_cocycle" "gauge"
    "Linear ghost-matter states are closed exactly for CE one-cocycles."
    "LeanPhy.Library" ["ghost", "matter", "Lie", "BRST"] @lie_matter_cocycle,
  CheckedLemma.ofTheorem "lie_d2_d1" "gauge"
    "the degree-two Chevalley--Eilenberg differential annihilates every degree-one coboundary"
    "LeanPhy.Library" ["Lie", "cohomology", "nilpotency"] @lie_d2_d1,
  CheckedLemma.ofTheorem "lie_h2_zero_iff_boundary" "gauge"
    "a cocycle represents zero in H2 exactly when it is a coboundary"
    "LeanPhy.Library" ["Lie", "cohomology", "H2", "quotient"] @lie_h2_zero_iff_boundary,
  CheckedLemma.ofTheorem "central_extension_classification" "gauge"
    "equal H2 classes are equivalent split-carrier central extensions fixing base and center"
    "LeanPhy.Library" ["Lie", "H2", "central-extension"] @central_extension_classification,
  CheckedLemma.ofTheorem "cohomology_reduction_exactness" "mathematics"
    "closed cochains are exact precisely when their certified class coordinates vanish"
    "LeanPhy.Library" ["cohomology", "computation", "certificate"] @cohomology_reduction_exactness,
  CheckedLemma.ofTheorem "heisenberg_h2_dimension" "gauge"
    "the rational three-dimensional Heisenberg Lie algebra has H2 dimension two for trivial coefficients"
    "LeanPhy.Examples.HeisenbergCohomology" ["Lie", "H2", "Heisenberg", "dimension"]
    LeanPhy.Examples.HeisenbergCohomology.h2_finrank,
  CheckedLemma.ofTheorem "finite_lie_cocycle_check" "gauge"
    "increasing basis triples detect the full degree-two CE cocycle condition"
    "LeanPhy.Library" ["Lie", "H2", "coordinates", "cocycle"] @finite_lie_cocycle_check,
  CheckedLemma.ofTheorem "generated_vector_h2_dimension" "gauge"
    "the declared solvable algebra with the supplied vector action has H2 dimension four"
    "LeanPhy.Generated.SolvableVector" ["Lie", "H2", "representation", "structure-constants"]
    LeanPhy.Generated.SolvableVector.h2_finrank,
  CheckedLemma.ofTheorem "diagonal_cohomology_exactness" "mathematics"
    "closed diagonal cochains are exact iff all surviving coordinates vanish, including zero-weight strata"
    "LeanPhy.Library" ["cohomology", "parameters", "diagonal", "exactness"] @diagonal_cohomology_exactness,
  CheckedLemma.ofTheorem "solvable_family_dimension" "gauge"
    "the three-parameter solvable family has H2 dimension equal to the three resonance indicators"
    "LeanPhy.Library" ["Lie", "H2", "parameters", "resonance"] @solvable_family_dimension,
  CheckedLemma.ofTheorem "generated_solvable_strata_dimension" "gauge"
    "the complete generated parameter tree computes the middle cohomology of the supplied CE matrices"
    "LeanPhy.Generated.SolvableStrata" ["cohomology", "parameters", "stratification", "certificate"]
    @LeanPhy.Generated.SolvableStrata.finrank_eq.{0},
  CheckedLemma.ofTheorem "generated_determinant_strata_dimension" "mathematics"
    "the generated parameter tree includes the intersecting determinant-zero loci and the origin"
    "LeanPhy.Generated.DeterminantStrata" ["cohomology", "parameters", "determinant", "stratification"]
    @LeanPhy.Generated.DeterminantStrata.finrank_eq.{0},
  CheckedLemma.ofTheorem "symbolic_heisenberg_dimension" "gauge"
    "the generated bracket-parameter family computes actual H2 including zero bracket degeneration"
    "LeanPhy.Generated.HeisenbergParameter" ["Lie", "H2", "parameters", "structure-constants"]
    @LeanPhy.Generated.HeisenbergParameter.h2_finrank.{0},
  CheckedLemma.ofTheorem "symbolic_vector_exactness" "gauge"
    "with the declared representation conditions, a closed vector-valued cochain is exact iff its computed coordinates vanish"
    "LeanPhy.Generated.AffineVectorParameters" ["Lie", "H2", "representation", "parameters", "exactness"]
    @LeanPhy.Generated.AffineVectorParameters.boundary_iff.{0},
  CheckedLemma.ofTheorem "discovered_lie_model_domain" "gauge"
    "discovered equations and user conditions exactly characterize existence of the supplied Lie algebra and module"
    "LeanPhy.Generated.DiscoveredLieDomain" ["Lie", "Jacobi", "representation", "parameters", "validity"]
    @LeanPhy.Generated.DiscoveredLieDomain.conditions_iff_model.{0},
  CheckedLemma.ofTheorem "adjoint_h2_deformation_classification" "gauge"
    "actual adjoint H2 class equality is equivalent to first-order bracket equivalence fixing reduction and tangent"
    "LeanPhy.Mathematics.LieDeformation" ["Lie", "H2", "adjoint", "deformation", "equivalence"]
    @LeanPhy.Mathematics.LieDeformation.class_eq_iff_nonempty_equivalence.{0,0},
  CheckedLemma.ofTheorem "second_order_deformation_obstruction" "gauge"
    "actual second-order Lie model existence is equivalent to cocycle and quadratic obstruction cancellation"
    "LeanPhy.Mathematics.LieDeformation" ["Lie", "Jacobi", "deformation", "obstruction", "second-order"]
    @LeanPhy.Mathematics.LieDeformation.secondAlgebra_exists_iff.{0,0},
  CheckedLemma.ofTheorem "computed_adjoint_deformation_equivalence" "gauge"
    "a complete adjoint reduction decides first-order equivalence by equality of coordinates"
    "LeanPhy.Mathematics.LieDeformationReduction" ["Lie", "adjoint", "deformation", "normal-form", "coordinates"]
    @LeanPhy.Mathematics.LieDeformation.Reduction.equivalent_iff.{0,0,0},
  CheckedLemma.ofTheorem "computed_deformation_representatives_unique" "gauge"
    "complete adjoint representatives are equivalent exactly when their parameter tuples agree"
    "LeanPhy.Mathematics.LieDeformationReduction" ["Lie", "adjoint", "deformation", "representatives"]
    @LeanPhy.Mathematics.LieDeformation.Reduction.representatives_equivalent_iff.{0,0,0},
  CheckedLemma.ofTheorem "computed_second_order_extension" "gauge"
    "a complete image solver decides existence of any second-order Lie model by closedness and projected quadratic equations"
    "LeanPhy.Mathematics.LieDeformationSecondOrder" ["Lie", "deformation", "second-order", "obstruction", "solver"]
    @LeanPhy.Mathematics.LieDeformation.SecondOrderSolver.model_exists_iff.{0,0,0,0,0},
  CheckedLemma.ofTheorem "all_second_order_corrections" "gauge"
    "all second-order corrections differ from the computed correction by an adjoint cocycle"
    "LeanPhy.Mathematics.LieDeformationSecondOrder" ["Lie", "deformation", "correction", "cocycle"]
    @LeanPhy.Mathematics.LieDeformation.SecondOrderSolver.all_corrections_iff.{0,0,0,0,0},
  CheckedLemma.ofTheorem "second_order_extension_on_h2_classes" "gauge"
    "equal actual H2 classes have the same second-order extendability"
    "LeanPhy.Mathematics.LieDeformationGauge" ["Lie", "H2", "deformation", "second-order", "normalization"]
    @LeanPhy.Mathematics.LieDeformation.secondExtendable_of_class_eq.{0,0},
  CheckedLemma.ofTheorem "second_order_correction_transport" "gauge"
    "the explicit correction transformation preserves the full second-order residual for closed directions"
    "LeanPhy.Mathematics.LieDeformationGauge" ["Lie", "deformation", "generator-change", "correction", "obstruction"]
    @LeanPhy.Mathematics.LieDeformation.transportCorrection_residual.{0,0},
  CheckedLemma.ofTheorem "lie_ce_third_chain" "gauge"
    "the next CE differential annihilates every two-cochain boundary"
    "LeanPhy.Mathematics.LieCohomology3" ["Lie", "H3", "deformation", "obstruction"]
    @LeanPhy.Mathematics.LieCohomology.differential3_differential2.{0,0,0},
  CheckedLemma.ofTheorem "intrinsic_obstruction_closed" "gauge"
    "the quadratic Jacobi obstruction of every closed adjoint direction is a three-cocycle"
    "LeanPhy.Mathematics.LieDeformationObstruction" ["Lie", "H3", "deformation", "obstruction"]
    @LeanPhy.Mathematics.LieDeformation.obstruction_isThreeCocycle.{0,0},
  CheckedLemma.ofTheorem "intrinsic_h3_extension_criterion" "gauge"
    "the true H3 obstruction vanishes exactly when an actual second-order Lie model exists"
    "LeanPhy.Mathematics.LieDeformationObstruction" ["Lie", "H3", "deformation", "obstruction"]
    @LeanPhy.Mathematics.LieDeformation.secondExtendable_iff_obstructionClass_zero.{0,0},
  CheckedLemma.ofTheorem "intrinsic_obstruction_invariance" "gauge"
    "first-order equivalence preserves the actual H3 obstruction class"
    "LeanPhy.Mathematics.LieDeformationObstruction" ["Lie", "H3", "deformation", "obstruction"]
    @LeanPhy.Mathematics.LieDeformation.obstructionClass_equivalence.{0,0},
  CheckedLemma.ofTheorem "intrinsic_obstruction_quadratic" "gauge"
    "scalar multiplication of the direction scales its H3 obstruction by the scalar squared"
    "LeanPhy.Mathematics.LieDeformationObstruction" ["Lie", "H3", "deformation", "obstruction"]
    @LeanPhy.Mathematics.LieDeformation.obstructionClass_smul.{0,0},
  CheckedLemma.ofTheorem "parameter_actual_h3" "gauge"
    "actual H3 is computed on every branch of the declared scalar character family"
    "LeanPhy.Examples.Generated.AffineFourThirdCharacter" ["Lie", "H3", "parameters", "obstruction"]
    @LeanPhy.Generated.AffineFourThirdCharacter.h3_finrank.{0},
  CheckedLemma.ofTheorem "parameter_intrinsic_extension" "gauge"
    "the intrinsic obstruction coordinates decide second-order extension on each closed parameter fiber"
    "LeanPhy.Examples.Generated.HeisenbergThirdParameter" ["Lie", "H3", "parameters", "obstruction"]
    @LeanPhy.Generated.HeisenbergThirdParameter.intrinsic_extension_iff.{0},
  CheckedLemma.ofTheorem "parameter_intrinsic_correction" "gauge"
    "the certified H3 primitive constructs a residual-cancelling correction on every legal fiber"
    "LeanPhy.Examples.Generated.HeisenbergThirdParameter" ["Lie", "H3", "parameters", "obstruction"]
    @LeanPhy.Generated.HeisenbergThirdParameter.intrinsicCorrection_cancels.{0},
  CheckedLemma.ofTheorem "parameter_normalized_extension" "gauge"
    "a complete parameter-dependent H2 normal form gives the same intrinsic extension criterion"
    "LeanPhy.Examples.Generated.HeisenbergThirdParameter" ["Lie", "H3", "parameters", "obstruction"]
    @LeanPhy.Generated.HeisenbergThirdParameter.normalized_extension_iff.{0},
  CheckedLemma.ofTheorem "third_order_model_criterion" "Lie deformation"
    "all three Jacobi equations exactly characterize third-order Lie model existence"
    "LeanPhy.Mathematics.LieDeformationThirdOrder" ["Lie", "H3", "third-order", "obstruction"]
    @LeanPhy.Mathematics.LieDeformation.thirdAlgebra_exists_iff.{0, 0},
  CheckedLemma.ofTheorem "third_order_intrinsic_obstruction" "Lie deformation"
    "the specified second-order model extends exactly when its actual H3 obstruction vanishes"
    "LeanPhy.Mathematics.LieDeformationThirdObstruction" ["Lie", "H3", "third-order", "obstruction"]
    @LeanPhy.Mathematics.LieDeformation.thirdExtendable_iff_obstructionClass_zero.{0, 0},
  CheckedLemma.ofTheorem "third_order_computed_correction" "Lie deformation"
    "a certified H3 primitive constructs a third-order correction when the projected obstruction vanishes"
    "LeanPhy.Mathematics.LieDeformationThirdObstruction" ["Lie", "H3", "third-order", "obstruction"]
    @LeanPhy.Mathematics.LieDeformation.ThirdReduction.thirdCorrection_cancels.{0, 0, 0},
  CheckedLemma.ofTheorem "joint_third_search_criterion" "Lie deformation"
    "all second and third corrections are covered by the checked block-image criterion"
    "LeanPhy.Mathematics.LieDeformationThirdSearch" ["Lie", "third-order", "search", "certificate"]
    @LeanPhy.Mathematics.LieDeformation.JointReduction.extendable_iff.{0,0,0},
  CheckedLemma.ofTheorem "joint_third_search_all_models" "Lie deformation"
    "every valid correction pair differs from the computed pair by the joint kernel"
    "LeanPhy.Mathematics.LieDeformationThirdSearch" ["Lie", "third-order", "search", "certificate"]
    @LeanPhy.Mathematics.LieDeformation.JointReduction.all_models_iff.{0,0,0},
  CheckedLemma.ofTheorem "joint_third_search_nonexistence" "Lie deformation"
    "nonzero joint obstruction excludes every second and third correction pair"
    "LeanPhy.Mathematics.LieDeformationThirdSearch" ["Lie", "third-order", "search", "certificate"]
    @LeanPhy.Mathematics.LieDeformation.JointReduction.no_model.{0,0,0}
]

def all : List CheckedLemma := catalog

def search (query : String) : List CheckedLemma :=
  searchIn catalog query

def names (lemmas : List CheckedLemma := catalog) : List String := namesIn lemmas

def renderJson (lemmas : List CheckedLemma := catalog) : String := renderJsonIn lemmas

end LeanPhy.Library
