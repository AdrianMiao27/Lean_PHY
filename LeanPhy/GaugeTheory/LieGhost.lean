import LeanPhy.GaugeTheory.GhostDerivation
import LeanPhy.Mathematics.CentralExtension

/-!
# Finite Lie-algebra ghost coordinates

For a Lie algebra on `Fin n → R`, the canonical generator image is
`d cᵏ = -∑ᵢ<ⱼ [eᵢ,eⱼ]ᵏ cⁱ cʲ`. Summing only increasing pairs avoids a factor
of one half. The degree-one CE/ghost bridge is proved for arbitrary cochains
and arbitrary commutative coefficient rings, with trivial scalar coefficients.

The certificate-taking `lieBRST` constructor is retained here.
`LieGhostComplex` derives those certificates uniformly from Jacobi, proves the
degree-two bridge and supplies `canonicalLieBRST` over any commutative ring.
A full chain equivalence is not asserted.
-/

namespace LeanPhy.GaugeTheory.GhostPolynomial

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology

variable {R : Type*} [CommRing R] {n : Nat}

/-- The linear ghost polynomial representing a scalar one-cochain. -/
noncomputable def ghostOne : Module.Dual R (Fin n → R) →ₗ[R] GhostPolynomial R n where
  toFun φ := ∑ i, φ (Pi.single i 1) • generator i
  map_add' := by intro φ ψ; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intro r φ; simp [mul_smul, Finset.smul_sum]

@[simp] theorem ghostOne_proj (i : Fin n) :
    ghostOne (LinearMap.proj i : Module.Dual R (Fin n → R)) = generator i := by
  simp [ghostOne, Pi.single_apply]

/-- Increasing-pair coordinates of a scalar two-cochain in the exterior algebra. -/
noncomputable def ghostTwo (L : LieAlgebra R (Fin n → R)) :
    LieCochain2 L (trivialLieModule L : LieModule L R) →ₗ[R] GhostPolynomial R n where
  toFun ω := ∑ i, ∑ j, if i < j then
    ω (Pi.single i 1) (Pi.single j 1) • (generator i * generator j) else 0
  map_add' := by
    intro ω η
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    split_ifs <;> simp [add_smul]
  map_smul' := by intro r ω; simp [Finset.smul_sum, smul_ite, mul_smul]

theorem ghostTwo_even (L : LieAlgebra R (Fin n → R))
    (ω : LieCochain2 L (trivialLieModule L : LieModule L R)) :
    parityInvolution (ghostTwo L ω) = ghostTwo L ω := by
  simp [ghostTwo, map_sum, apply_ite, generator]

/-- Canonical quadratic generator images, with the existing CE sign convention. -/
noncomputable def lieImages (L : LieAlgebra R (Fin n → R)) (k : Fin n) :
    GhostPolynomial R n := ghostTwo L (differential1 (trivialLieModule L) (LinearMap.proj k))

theorem lieImages_formula (L : LieAlgebra R (Fin n → R)) (k : Fin n) :
    lieImages L k = ∑ i, ∑ j, if i < j then
      (-L.bracket (Pi.single i 1) (Pi.single j 1) k) •
        (generator i * generator j) else 0 := by
  simp [lieImages, ghostTwo, differential1_trivial]

theorem lieImages_even (L : LieAlgebra R (Fin n → R)) (k : Fin n) :
    parityInvolution (lieImages L k) = lieImages L k := ghostTwo_even _ _

/-- The canonical polynomial odd derivation, defined before proving nilpotency. -/
noncomputable def lieDifferential (L : LieAlgebra R (Fin n → R)) :
    GhostPolynomial R n →ₗ[R] GhostPolynomial R n := vectorField (lieImages L)

@[simp] theorem lieDifferential_generator (L : LieAlgebra R (Fin n → R)) (k : Fin n) :
    lieDifferential L (generator k) = lieImages L k := vectorField_generator _ _

theorem dual_eq_sum_proj (φ : Module.Dual R (Fin n → R)) :
    φ = ∑ i, φ (Pi.single i 1) • (LinearMap.proj i : Module.Dual R (Fin n → R)) := by
  apply LinearMap.ext; intro v
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [map_sum, mul_comm]

/-- The degree-one CE differential agrees with the polynomial ghost derivation. -/
theorem lieDifferential_ghostOne (L : LieAlgebra R (Fin n → R))
    (φ : Module.Dual R (Fin n → R)) :
    lieDifferential L (ghostOne φ) = ghostTwo L (differential1 (trivialLieModule L) φ) := by
  have hlinear : differential1 (trivialLieModule L) φ =
      ∑ i, φ (Pi.single i 1) • differential1 (trivialLieModule L) (LinearMap.proj i) := by
    change differential1Linear (trivialLieModule L) φ = _
    conv_lhs => rw [dual_eq_sum_proj φ]
    simp [map_sum, differential1Linear]
  rw [hlinear, map_sum]
  simp [ghostOne, lieDifferential, map_sum, lieImages]

theorem lieDifferential_mul (L : LieAlgebra R (Fin n → R)) (x y : GhostPolynomial R n) :
    lieDifferential L (x * y) = lieDifferential L x * y +
      parityInvolution x * lieDifferential L y :=
  vectorField_mul _ (lieImages_even L) x y

/-- Exact finite certificate boundary; checking only a subset is insufficient. -/
theorem lieDifferential_sq_iff (L : LieAlgebra R (Fin n → R)) :
    (∀ x, lieDifferential L (lieDifferential L x) = 0) ↔
      ∀ k, lieDifferential L (lieImages L k) = 0 :=
  vectorField_sq_iff _ (lieImages_even L)

noncomputable def lieBRST (L : LieAlgebra R (Fin n → R))
    (hclosed : ∀ k, lieDifferential L (lieImages L k) = 0) :
    GradedBRSTDifferential (grading (R := R) (n := n)) :=
  vectorFieldBRST (lieImages L) (lieImages_even L) hclosed

end LeanPhy.GaugeTheory.GhostPolynomial
