import LeanPhy.Examples.Generated.Sl2Ghost
import LeanPhy.Examples.Generated.HeisenbergGhost
import LeanPhy.Examples.Generated.OscillatorGhost
import LeanPhy.GaugeTheory.LieGhostFamily
import LeanPhy.GaugeTheory.GhostDegree
import LeanPhy.Examples.GhostCohomology
import LeanPhy.Examples.GhostMatter
import Mathlib.Data.ZMod.Basic
import LeanPhy.CLI

/-!
# Certified Lie ghost calculations and a failed candidate

Three nonabelian brackets produce actual differentials on the whole finite
ghost algebra. A fourth polynomial vector field demonstrates why independently
nilpotent summands cannot be added without checking their mixed terms.
-/

namespace LeanPhy.Examples.LieGhostResearch

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Workflow

abbrev Ghosts := GhostPolynomial ℚ 3
noncomputable def c (i : Fin 3) : Ghosts := generator i

theorem sl2_images :
    LeanPhy.Generated.Sl2Ghost.brst (c 0) = -(c 1 * c 2) ∧
    LeanPhy.Generated.Sl2Ghost.brst (c 1) = (-2 : ℚ) • (c 0 * c 1) ∧
    LeanPhy.Generated.Sl2Ghost.brst (c 2) = (2 : ℚ) • (c 0 * c 2) := by
  change lieDifferential LeanPhy.Generated.Sl2Ghost.algebra (c 0) = _ ∧
    lieDifferential LeanPhy.Generated.Sl2Ghost.algebra (c 1) = _ ∧
    lieDifferential LeanPhy.Generated.Sl2Ghost.algebra (c 2) = _
  simp [c]

theorem sl2_nonzero : LeanPhy.Generated.Sl2Ghost.brst (c 0) ≠ 0 := by
  rw [sl2_images.1, neg_ne_zero]
  exact pair_ne_zero 1 2 (by decide)

theorem sl2_nilpotent (x : Ghosts) :
    LeanPhy.Generated.Sl2Ghost.brst (LeanPhy.Generated.Sl2Ghost.brst x) = 0 :=
  LeanPhy.Generated.Sl2Ghost.brst_nilpotent x

theorem sl2_ce_bridge (φ : (Fin 3 → ℚ) →ₗ[ℚ] ℚ) :
    LeanPhy.Generated.Sl2Ghost.brst (ghostOne φ) =
      ghostTwo LeanPhy.Generated.Sl2Ghost.algebra
        (differential1 (trivialLieModule LeanPhy.Generated.Sl2Ghost.algebra) φ) :=
  LeanPhy.Generated.Sl2Ghost.ce_bridge φ

theorem sl2_leibniz (x y : Ghosts) :
    LeanPhy.Generated.Sl2Ghost.brst (x * y) = LeanPhy.Generated.Sl2Ghost.brst x * y +
      parityInvolution x * LeanPhy.Generated.Sl2Ghost.brst y :=
  LeanPhy.Generated.Sl2Ghost.brst_leibniz x y

theorem heisenberg_image : LeanPhy.Generated.HeisenbergGhost.brst (c 2) = -(c 0 * c 1) := by
  change lieDifferential LeanPhy.Generated.HeisenbergGhost.algebra (c 2) = _
  simp [c]

theorem heisenberg_nonzero : LeanPhy.Generated.HeisenbergGhost.brst (c 2) ≠ 0 := by
  rw [heisenberg_image, neg_ne_zero]
  exact pair_ne_zero 0 1 (by decide)

theorem oscillator_nilpotent (x : GhostPolynomial ℚ 4) :
    LeanPhy.Generated.OscillatorGhost.brst (LeanPhy.Generated.OscillatorGhost.brst x) = 0 :=
  LeanPhy.Generated.OscillatorGhost.brst_nilpotent x

/-- Each summand is separately a quadratic differential, but their sum is not. -/
noncomputable def incompatibleImages : Fin 3 → Ghosts := ![c 0 * c 1, c 1 * c 2, 0]

theorem incompatible_even (i : Fin 3) :
    parityInvolution (incompatibleImages i) = incompatibleImages i := by
  fin_cases i <;> simp [incompatibleImages, c, generator]

theorem incompatible_square :
    vectorField incompatibleImages (vectorField incompatibleImages (c 0)) =
      -(c 0 * (c 1 * c 2)) := by
  change vectorField incompatibleImages
    (vectorField incompatibleImages (generator 0)) = _
  rw [vectorField_generator]
  change vectorField incompatibleImages (generator 0 * generator 1) = _
  rw [vectorField_mul _ incompatible_even, vectorField_generator, vectorField_generator]
  simp [incompatibleImages, c,
    mul_assoc, show parityInvolution (generator (R := ℚ) (0 : Fin 3)) = -generator 0 from
      generator_isOdd 0]

theorem incompatible_not_nilpotent :
    ¬∀ x, vectorField incompatibleImages (vectorField incompatibleImages x) = 0 := by
  intro h
  have hzero := h (c 0)
  rw [incompatible_square] at hzero
  have heval := congrArg (fun x => derivative 2 (derivative 1 (derivative 0 x))) hzero
  norm_num [c, derivative, contract_mul, generator, Pi.single_apply] at heval

theorem all_ring_nilpotent {R : Type} [CommRing R] {n : Nat}
    (L : LieAlgebra R (Fin n → R)) (x : GhostPolynomial R n) :
    canonicalLieBRST L (canonicalLieBRST L x) = 0 := (canonicalLieBRST L).nilpotent_apply x

theorem all_ring_two_bridge {R : Type} [CommRing R] {n : Nat}
    (L : LieAlgebra R (Fin n → R)) (ω : LieCochain2 L (trivialLieModule L : LieModule L R)) :
    canonicalLieBRST L (ghostTwo L ω) = ghostThree L (differential2Cochain (trivialLieModule L) ω) :=
  lieDifferential_ghostTwo L ω

theorem parameter_nilpotent {R : Type} [CommRing R] (a b : R) (x : GhostPolynomial R 3) :
    LieGhostFamily.differential a b (LieGhostFamily.differential a b x) = 0 :=
  LieGhostFamily.nilpotent a b x

theorem parameter_closed_iff {R : Type} [CommRing R] (a b : R) :
    LieGhostFamily.differential a b (generator 1 * generator 2) = 0 ↔ a + b = 0 :=
  LieGhostFamily.pair_closed_iff a b

theorem characteristic_two_closed :
    LieGhostFamily.differential (1 : ZMod 2) 1 (generator 1 * generator 2) = 0 := by
  rw [LieGhostFamily.pair_closed_iff]
  decide

theorem polynomial_parameter_nilpotent (x : GhostPolynomial (Polynomial ℚ) 3) :
    LieGhostFamily.differential Polynomial.X (-Polynomial.X)
      (LieGhostFamily.differential Polynomial.X (-Polynomial.X) x) = 0 :=
  LieGhostFamily.nilpotent _ _ x

theorem integer_degree_shift {R : Type} [CommRing R] {n : Nat}
    (L : LieAlgebra R (Fin n → R)) {d : Int} {x : GhostPolynomial R n}
    (hx : x ∈ degree d) : integerLieBRST L x ∈ degree (d + 1) :=
  lieDifferential_mem_degree L hx

theorem koszul_degree_shift {R : Type} [CommRing R] {n : Nat}
    (f : Module.Dual R (Fin n → R)) {d : Int} {x : GhostPolynomial R n}
    (hx : x ∈ degree d) : integerKoszul f x ∈ degree (d - 1) :=
  contract_mem_degree f hx

theorem finite_degree_decomposition {R : Type} [CommRing R] {n : Nat}
    (x : GhostPolynomial R n) : ∃ s : Finset Nat, ∑ k ∈ s, degreeProjection k x = x :=
  exists_degree_decomposition x

theorem closed_components {R : Type} [CommRing R] {n : Nat}
    (L : LieAlgebra R (Fin n → R)) {x : GhostPolynomial R n}
    (hx : lieDifferential L x = 0) (k : Nat) : lieDifferential L (degreeProjection k x) = 0 :=
  closed_degreeProjection L hx k

theorem homogeneous_boundaries {R : Type} [CommRing R] {n : Nat}
    (L : LieAlgebra R (Fin n → R)) {k : Nat} {x : GhostPolynomial R n}
    (hx : x ∈ natDegree (k + 1)) :
    (∃ y, lieDifferential L y = x) ↔ ∃ y ∈ natDegree k, lieDifferential L y = x :=
  homogeneous_exact_iff L hx

theorem scalar_boundaries {R : Type} [CommRing R] {n : Nat}
    (L : LieAlgebra R (Fin n → R)) (r : R) :
    (∃ y, lieDifferential L y = algebraMap R (GhostPolynomial R n) r) ↔ r = 0 :=
  scalar_exact_iff L r

theorem degree_cutoff {R : Type} [CommRing R] {n k : Nat} (hk : n < k) :
    natDegree (R := R) (n := n) k = ⊥ := natDegree_eq_bot_of_lt hk

theorem top_closed {R : Type} [CommRing R] {n : Nat}
    (L : LieAlgebra R (Fin n → R)) {x : GhostPolynomial R n}
    (hx : x ∈ natDegree n) : lieDifferential L x = 0 := top_degree_closed L hx

/-- Parity collapses in characteristic two, while actual degree remains separated. -/
theorem characteristic_two_degree_separation :
    (1 : GhostPolynomial (ZMod 2) 1) ∈ homogeneous .odd ∧
    (1 : GhostPolynomial (ZMod 2) 1) ∉ degree 1 := by
  constructor
  · change parityInvolution (1 : GhostPolynomial (ZMod 2) 1) = -1
    rw [map_one]
    have h : (-1 : ZMod 2) = 1 := by decide
    simpa only [map_one, map_neg] using
      congrArg (algebraMap (ZMod 2) (GhostPolynomial (ZMod 2) 1)) h.symm
  · intro h
    have h0 : (1 : GhostPolynomial (ZMod 2) 1) ∈ degree 0 := by
      simpa using scalar_mem_degree (R := ZMod 2) (n := 1) 1
    have := degree_unique h0 h one_ne_zero
    norm_num at this

/-- An inhomogeneous polynomial cannot be assigned a single ghost number. -/
theorem mixed_not_homogeneous (k : Nat) : (1 + c 0) ∉ natDegree k := by
  have h0 : (1 : Ghosts) ∈ natDegree 0 := by simpa using scalar_mem_natDegree (R := ℚ) (n := 3) 1
  have h1 : c 0 ∈ natDegree 1 := generator_mem_natDegree 0
  have hp0 : degreeProjection 0 (1 + c 0) = 1 := by
    rw [map_add, degreeProjection_of_mem h0, degreeProjection_of_ne h1 (by decide), add_zero]
  have hp1 : degreeProjection 1 (1 + c 0) = c 0 := by
    rw [map_add, degreeProjection_of_ne h0 (by decide), degreeProjection_of_mem h1, zero_add]
  intro h
  have hk : k = 0 := by
    by_contra hk
    have hz := degreeProjection_of_ne h hk
    rw [hp0] at hz
    exact one_ne_zero hz
  subst k
  have hz := degreeProjection_of_ne h (by decide : (0 : Nat) ≠ 1)
  rw [hp1] at hz
  have hd := congrArg (derivative 0) hz
  have : (1 : Ghosts) = 0 := by simpa [c] using hd
  exact one_ne_zero this

theorem all_ring_closed_reflection {R : Type} [CommRing R] {n : Nat}
    (L : LieAlgebra R (Fin n → R)) (ω : LieCochain2 L (trivialLieModule L : LieModule L R)) :
    lieDifferential L (ghostTwo L ω) = 0 ↔ IsTwoCocycle (trivialLieModule L) ω :=
  ghostTwo_closed_iff L ω

theorem all_ring_exact_reflection {R : Type} [CommRing R] {n : Nat}
    (L : LieAlgebra R (Fin n → R)) (ω : LieCochain2 L (trivialLieModule L : LieModule L R)) :
    (∃ y, lieDifferential L y = ghostTwo L ω) ↔ IsTwoCoboundary (trivialLieModule L) ω :=
  ghostTwo_exact_iff L ω

theorem all_ring_class_reflection {R : Type} [CommRing R] {n : Nat}
    (L : LieAlgebra R (Fin n → R)) (ω η : LieCochain2 L (trivialLieModule L : LieModule L R)) :
    (integerLieBRST L).Cohomologous (ghostTwo L ω) (ghostTwo L η) ↔
      Cohomologous2 (trivialLieModule L) ω η := ghostTwo_cohomologous_iff L ω η

theorem all_ring_h2_equivalence {R : Type} [CommRing R] {n : Nat}
    (L : LieAlgebra R (Fin n → R)) :
    Nonempty (H2 (trivialLieModule L : LieModule L R) ≃ₗ[R] GhostH2 L) := ⟨h2GhostEquiv L⟩


theorem matter_nilpotency {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    {n : Nat} {L : LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M) (x : MatterGhost R n M) :
    matterDifferential 𝒨 (matterDifferential 𝒨 x) = 0 := matterDifferential_sq 𝒨 x

theorem matter_degree_shift {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    {n : Nat} {L : LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M)
    {d : Int} {x : MatterGhost R n M} (hx : x ∈ matterDegree d) :
    matterDifferential 𝒨 x ∈ matterDegree (d + 1) := matterDifferential_mem_degree 𝒨 hx

theorem matter_ce_one_bridge {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    {n : Nat} {L : LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M) (φ : LieCochain1 L 𝒨) :
    matterDifferential 𝒨 (matterOne 𝒨 φ) = matterTwo 𝒨 (differential1 𝒨 φ) := matterDifferential_one 𝒨 φ

theorem matter_invariant_vectors {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    {n : Nat} {L : LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M) (m : M) :
    matterDifferential 𝒨 (matterZero m) = 0 ↔ ∀ v, 𝒨.act v m = 0 := matterZero_closed_iff 𝒨 m

theorem matter_constant_boundaries {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    {n : Nat} {L : LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M) (m : M) :
    (∃ y, matterDifferential 𝒨 y = matterZero m) ↔ m = 0 := matterZero_exact_iff 𝒨 m

def package : TheoryPackage :=
  TheoryPackage.empty "Lie ghost research" "certified finite Lie ghost sector"
    |>.addAssumptionText "finite rational brackets"
      "the generated sl2, Heisenberg and oscillator Lie algebras over Q, with trivial scalar coefficients"
      "LeanPhy.Generated.Sl2Ghost.algebra"
    |>.addTheoremWithAssumptions "sl2 generator signs" "the three canonical quadratic images have the declared CE signs"
      "LeanPhy.Examples.LieGhostResearch.sl2_images" ["finite rational brackets"] sl2_images
    |>.addTheoremWithAssumptions "sl2 nontriviality" "the canonical ghost differential is nonzero"
      "LeanPhy.Examples.LieGhostResearch.sl2_nonzero" ["finite rational brackets"] sl2_nonzero
    |>.addTheoremWithAssumptions "sl2 polynomial nilpotency" "s squared vanishes on every ghost polynomial"
      "LeanPhy.Examples.LieGhostResearch.sl2_nilpotent" ["finite rational brackets"] sl2_nilpotent
    |>.addTheoremWithAssumptions "sl2 CE bridge" "the degree-one CE differential intertwines with the ghost differential"
      "LeanPhy.Examples.LieGhostResearch.sl2_ce_bridge" ["finite rational brackets"] sl2_ce_bridge
    |>.addTheoremWithAssumptions "sl2 signed product rule" "the polynomial differential satisfies the odd Leibniz rule"
      "LeanPhy.Examples.LieGhostResearch.sl2_leibniz" ["finite rational brackets"] sl2_leibniz
    |>.addTheoremWithAssumptions "Heisenberg generator sign" "s(c2) = -c0 c1"
      "LeanPhy.Examples.LieGhostResearch.heisenberg_image" ["finite rational brackets"] heisenberg_image
    |>.addTheoremWithAssumptions "Heisenberg nontriviality" "the central-generator image is nonzero"
      "LeanPhy.Examples.LieGhostResearch.heisenberg_nonzero" ["finite rational brackets"] heisenberg_nonzero
    |>.addTheoremWithAssumptions "oscillator polynomial nilpotency" "the four-generator differential squares to zero"
      "LeanPhy.Examples.LieGhostResearch.oscillator_nilpotent" ["finite rational brackets"] oscillator_nilpotent
    |>.addTheorem "mixed-term obstruction" "the displayed even images give a nonzero cubic square"
      "LeanPhy.Examples.LieGhostResearch.incompatible_square" incompatible_square
    |>.addTheorem "incompatible images rejected" "the candidate is not nilpotent on all polynomials"
      "LeanPhy.Examples.LieGhostResearch.incompatible_not_nilpotent" incompatible_not_nilpotent
    |>.addTheorem "Jacobi implies ghost nilpotency" "every finite coordinate Lie algebra over a commutative ring supplies its ghost differential"
      "LeanPhy.Examples.LieGhostResearch.all_ring_nilpotent" @all_ring_nilpotent
    |>.addTheorem "degree-two CE bridge" "the ghost differential intertwines CE degrees two and three over any commutative ring"
      "LeanPhy.Examples.LieGhostResearch.all_ring_two_bridge" @all_ring_two_bridge
    |>.addTheorem "parameter family nilpotency" "nilpotency holds for all weights, including degenerate parameters"
      "LeanPhy.Examples.LieGhostResearch.parameter_nilpotent" @parameter_nilpotent
    |>.addTheorem "complete ghost-pair closedness locus" "c1 c2 is closed exactly when the sum of the weights vanishes"
      "LeanPhy.Examples.LieGhostResearch.parameter_closed_iff" @parameter_closed_iff
    |>.addTheorem "characteristic two resonance" "weights one and one give a closed ghost pair in characteristic two"
      "LeanPhy.Examples.LieGhostResearch.characteristic_two_closed" characteristic_two_closed
    |>.addTheorem "polynomial parameter nilpotency" "the construction applies over a polynomial coefficient ring"
      "LeanPhy.Examples.LieGhostResearch.polynomial_parameter_nilpotent" polynomial_parameter_nilpotent
    |>.addTheorem "integer ghost degree" "the canonical Lie differential raises actual integer ghost degree by one"
      "LeanPhy.Examples.LieGhostResearch.integer_degree_shift" @integer_degree_shift
    |>.addTheorem "descending Koszul degree" "contraction lowers actual integer ghost degree by one"
      "LeanPhy.Examples.LieGhostResearch.koszul_degree_shift" @koszul_degree_shift
    |>.addTheorem "finite homogeneous decomposition" "every polynomial is a finite sum of its actual degree components"
      "LeanPhy.Examples.LieGhostResearch.finite_degree_decomposition" @finite_degree_decomposition
    |>.addTheorem "closed degree components" "every homogeneous component of a closed polynomial is closed"
      "LeanPhy.Examples.LieGhostResearch.closed_components" @closed_components
    |>.addTheorem "homogeneous primitive" "a boundary of degree k+1 admits a primitive of degree k"
      "LeanPhy.Examples.LieGhostResearch.homogeneous_boundaries" @homogeneous_boundaries
    |>.addTheorem "scalar boundary criterion" "a scalar in the pure Lie ghost complex is exact precisely when it is zero"
      "LeanPhy.Examples.LieGhostResearch.scalar_boundaries" @scalar_boundaries
    |>.addTheorem "finite ghost degree cutoff" "all components above the number of generators vanish"
      "LeanPhy.Examples.LieGhostResearch.degree_cutoff" @degree_cutoff
    |>.addTheorem "top degree closedness" "all top-degree pure ghosts are closed"
      "LeanPhy.Examples.LieGhostResearch.top_closed" @top_closed
    |>.addTheorem "characteristic two degree separation" "odd parity does not certify ghost degree one, even in characteristic two"
      "LeanPhy.Examples.LieGhostResearch.characteristic_two_degree_separation" @characteristic_two_degree_separation
    |>.addTheorem "inhomogeneous ghost polynomial" "one plus a generator has no single natural ghost degree"
      "LeanPhy.Examples.LieGhostResearch.mixed_not_homogeneous" @mixed_not_homogeneous
    |>.addTheorem "ghost closedness reflection" "ghost degree-two closedness is equivalent to the CE cocycle equation"
      "LeanPhy.Examples.LieGhostResearch.all_ring_closed_reflection" @all_ring_closed_reflection
    |>.addTheorem "ghost exactness reflection" "arbitrary polynomial primitives exist exactly for CE coboundaries"
      "LeanPhy.Examples.LieGhostResearch.all_ring_exact_reflection" @all_ring_exact_reflection
    |>.addTheorem "ghost class reflection" "ghost cohomologous pairs reflect exactly the CE class relation"
      "LeanPhy.Examples.LieGhostResearch.all_ring_class_reflection" @all_ring_class_reflection
    |>.addTheorem "actual ghost H2 equivalence" "the actual degree-two ghost quotient is linearly equivalent to scalar CE H2"
      "LeanPhy.Examples.LieGhostResearch.all_ring_h2_equivalence" @all_ring_h2_equivalence
    |>.addTheorem "Heisenberg ghost H2 dimension" "the actual Heisenberg ghost H2 has dimension two"
      "LeanPhy.Examples.GhostCohomology.heisenberg_dimension" @GhostCohomology.heisenberg_dimension
    |>.addTheorem "complete Heisenberg closedness" "every degree-two Heisenberg ghost polynomial is closed"
      "LeanPhy.Examples.GhostCohomology.heisenberg_all_degree_two_closed" @GhostCohomology.heisenberg_all_degree_two_closed
    |>.addTheorem "complete Heisenberg boundary criterion" "two extracted coefficients decide exactness for every homogeneous quadratic polynomial"
      "LeanPhy.Examples.GhostCohomology.heisenberg_all_boundaries" @GhostCohomology.heisenberg_all_boundaries
    |>.addTheorem "computed Heisenberg ghost coordinates" "the certified reduction computes the quotient class coordinates"
      "LeanPhy.Examples.GhostCohomology.heisenberg_class_coordinates" @GhostCohomology.heisenberg_class_coordinates
    |>.addTheorem "nonzero resonant ghost pair" "the resonant ghost pair defines a nonzero class over every nontrivial commutative ring"
      "LeanPhy.Examples.GhostCohomology.family_pair_class_nonzero" @GhostCohomology.family_pair_class_nonzero.{0}
    |>.addTheorem "complete parameter ghost dimension" "all weight degenerations and characteristic-dependent resonances are counted"
      "LeanPhy.Examples.GhostCohomology.family_dimension" @GhostCohomology.family_dimension.{0}
    |>.addTheorem "generic ghost H2 vanishing" "rational weights one and one give zero H2"
      "LeanPhy.Examples.GhostCohomology.family_generic" @GhostCohomology.family_generic
    |>.addTheorem "resonant ghost H2" "rational weights one and minus one give one-dimensional H2"
      "LeanPhy.Examples.GhostCohomology.family_resonant" @GhostCohomology.family_resonant
    |>.addTheorem "abelian ghost H2" "zero weights give three-dimensional H2"
      "LeanPhy.Examples.GhostCohomology.family_abelian" @GhostCohomology.family_abelian
    |>.addTheorem "characteristic two ghost H2" "weights one and one give one-dimensional H2 in characteristic two"
      "LeanPhy.Examples.GhostCohomology.characteristic_two_dimension" @GhostCohomology.characteristic_two_dimension
    |>.addTheorem "nonzero ghost class with zero divisors" "weights three and three over ZMod 6 give a nonzero ghost class"
      "LeanPhy.Examples.GhostCohomology.zero_divisor_pair_nonzero" @GhostCohomology.zero_divisor_pair_nonzero
    |>.addTheorem "matter nilpotency" "all tensor states square to zero from the representation law"
      "LeanPhy.Examples.LieGhostResearch.matter_nilpotency" @matter_nilpotency
    |>.addTheorem "matter degree shift" "matter differential raises integer ghost degree by one"
      "LeanPhy.Examples.LieGhostResearch.matter_degree_shift" @matter_degree_shift
    |>.addTheorem "matter ce one bridge" "the full matter action agrees with CE d1"
      "LeanPhy.Examples.LieGhostResearch.matter_ce_one_bridge" @matter_ce_one_bridge
    |>.addTheorem "matter invariant vectors" "constant closure is precisely gauge invariance"
      "LeanPhy.Examples.LieGhostResearch.matter_invariant_vectors" @matter_invariant_vectors
    |>.addTheorem "matter constant boundaries" "arbitrary primitives cannot produce a nonzero constant"
      "LeanPhy.Examples.LieGhostResearch.matter_constant_boundaries" @matter_constant_boundaries
    |>.addTheorem "character constant" "a character contributes its ghost times weight times vector"
      "LeanPhy.Examples.GhostMatter.character_constant" @GhostMatter.character_constant.{0}
    |>.addTheorem "character constant closed iff" "the full annihilator condition is retained over rings"
      "LeanPhy.Examples.GhostMatter.character_constant_closed_iff" @GhostMatter.character_constant_closed_iff.{0}
    |>.addTheorem "adjoint constant closed iff" "adjoint invariants recover the center for every parameter"
      "LeanPhy.Examples.GhostMatter.adjoint_constant_closed_iff" @GhostMatter.adjoint_constant_closed_iff.{0}
    |>.addTheorem "charged constant not closed" "a charged rational constant fails closure"
      "LeanPhy.Examples.GhostMatter.charged_constant_not_closed" @GhostMatter.charged_constant_not_closed
    |>.addTheorem "zero divisor constant closed" "a nonzero weight can annihilate a nonzero vector"
      "LeanPhy.Examples.GhostMatter.zero_divisor_constant_closed" @GhostMatter.zero_divisor_constant_closed
    |>.addTheorem "zero divisor constant not exact" "that torsion constant has no arbitrary primitive"
      "LeanPhy.Examples.GhostMatter.zero_divisor_constant_not_exact" @GhostMatter.zero_divisor_constant_not_exact
    |>.addTheorem "torsion adjoint closed" "the adjoint action retains torsion invariants"
      "LeanPhy.Examples.GhostMatter.torsion_adjoint_closed" @GhostMatter.torsion_adjoint_closed
    |>.addTheorem "torsion adjoint not exact" "the torsion adjoint invariant is not a boundary"
      "LeanPhy.Examples.GhostMatter.torsion_adjoint_not_exact" @GhostMatter.torsion_adjoint_not_exact
    |>.addBoundaryText "finite Lie ghost and matter complex"
      "negative-degree antighosts, all-degree CE equivalence and higher matter quotient computations remain open"
    |>.addObligationText "physical interpretation"
      "supply the physical representation, constraints and the identification of cohomology with physical observables"
      "research model"

def project : ResearchProject := ResearchProject.ofPackages "Lie ghost research" [package]

def manifest : ResearchManifest :=
  ResearchManifest.ofProject "Lie ghost research manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Examples.LieGhostResearch", "LeanPhy.GaugeTheory.GhostDerivation",
      "LeanPhy.GaugeTheory.LieGhost", "LeanPhy.GaugeTheory.LieGhostComplex",
      "LeanPhy.GaugeTheory.LieGhostFamily", "LeanPhy.GaugeTheory.GhostDegree",
      "LeanPhy.GaugeTheory.LieGhostCohomology", "LeanPhy.GaugeTheory.LieGhostMatter",
      "LeanPhy.GaugeTheory.LieGhostMatterCohomology", "LeanPhy.Examples.GhostMatter", "LeanPhy.Examples.GhostCohomology",
      "LeanPhy.Examples.HeisenbergCohomology", "LeanPhy.Mathematics.SolvableLieFamily", "LeanPhy.Examples.Generated.Sl2Ghost",
      "LeanPhy.Examples.Generated.HeisenbergGhost", "LeanPhy.Examples.Generated.OscillatorGhost",
      "scripts/lie_ghost.py", "scripts/lie_cohomology.py", "scripts/reduce_cohomology.py",
      "examples/lie-ghost/sl2.json", "examples/lie-ghost/heisenberg.json",
      "examples/lie-ghost/oscillator-four.json", "lean-toolchain", "lakefile.toml"]

example : project.claimCount = 54 := rfl
example : project.obligationCount = 1 := rfl
example : project.diagnosticCount = 0 := by decide

def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args

end LeanPhy.Examples.LieGhostResearch
