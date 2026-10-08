import LeanPhy.GaugeTheory.LieGhostMatter
import LeanPhy.GaugeTheory.LieGhostCohomology
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Low-degree matter cochains in ghost coordinates

Degree-zero and degree-one CE differentials agree with the tensor ghost
differential. Coefficients can be recovered without a basis or flatness
assumption on the matter module. Constant closed states are precisely the
invariant vectors, and a constant is a boundary only when it is zero.
-/

namespace LeanPhy.GaugeTheory.GhostPolynomial

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open scoped TensorProduct

set_option maxSynthPendingDepth 7

variable {R : Type*} [CommRing R] {n : Nat}
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A ghost coefficient functional applied to a matter-valued state. -/
noncomputable def matterCoefficient (f : GhostPolynomial R n →ₗ[R] R) :
    MatterGhost R n M →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id

@[simp] theorem matterCoefficient_tmul (f : GhostPolynomial R n →ₗ[R] R)
    (g : GhostPolynomial R n) (m : M) :
    matterCoefficient f (g ⊗ₜ[R] m) = f g • m := rfl

/-- Matter vectors embedded as degree-zero ghost states. -/
noncomputable def matterZero : M →ₗ[R] MatterGhost R n M :=
  TensorProduct.mk R (GhostPolynomial R n) M 1

/-- Actual linear ghost coordinates of a one-cochain. -/
noncomputable def matterOne {L : LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M) :
    LieCochain1 L 𝒨 →ₗ[R] MatterGhost R n M where
  toFun φ := ∑ i, generator i ⊗ₜ[R] φ (Pi.single i 1)
  map_add' := by intros; simp [TensorProduct.tmul_add, Finset.sum_add_distrib]
  map_smul' := by intros; simp [TensorProduct.tmul_smul, Finset.smul_sum]

/-- Alternating matter two-cochains, with increasing-pair coordinates. -/
noncomputable def matterTwo {L : LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M) :
    LieCochain2 L 𝒨 →ₗ[R] MatterGhost R n M where
  toFun ω := ∑ i, ∑ j, if i < j then
    (generator i * generator j) ⊗ₜ[R] ω (Pi.single i 1) (Pi.single j 1) else 0
  map_add' := by
    intros
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    split_ifs <;> simp [TensorProduct.tmul_add]
  map_smul' := by intros; simp [Finset.smul_sum, smul_ite, TensorProduct.tmul_smul]

/-- The first coordinate coefficient of a ghost state. -/
noncomputable def oneCoefficient (i : Fin n) : GhostPolynomial R n →ₗ[R] R :=
  ExteriorAlgebra.algebraMapInv.toLinearMap ∘ₗ derivative i

@[simp] theorem oneCoefficient_generator (i j : Fin n) :
    oneCoefficient (R := R) i (generator j) = if i = j then 1 else 0 := by
  simp [oneCoefficient, derivative_generator]

theorem matterCoefficient_one {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) (φ : LieCochain1 L 𝒨) (i : Fin n) :
    matterCoefficient (oneCoefficient i) (matterOne 𝒨 φ) = φ (Pi.single i 1) := by
  simp [matterOne, map_sum, ite_smul]

theorem matterOne_injective {L : LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M) :
    Function.Injective (matterOne 𝒨) := by
  intro φ ψ h
  apply (Pi.basisFun R (Fin n)).ext
  intro i
  simpa only [Pi.basisFun_apply, matterCoefficient_one] using
    congrArg (matterCoefficient (oneCoefficient i)) h

theorem matterCoefficient_two {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) (ω : LieCochain2 L 𝒨) (i j : Fin n) (hij : i < j) :
    matterCoefficient (pairCoefficient i j) (matterTwo 𝒨 ω) =
      ω (Pi.single i 1) (Pi.single j 1) := by
  simp only [matterTwo, LinearMap.coe_mk, AddHom.coe_mk, map_sum, apply_ite,
    map_zero, matterCoefficient_tmul]
  have term (a b : Fin n) :
      (if a < b then pairCoefficient (R := R) i j (generator a * generator b) •
        ω (Pi.single a 1) (Pi.single b 1) else 0) =
      if a = i then if b = j then ω (Pi.single i 1) (Pi.single j 1) else 0 else 0 := by
    rw [pairCoefficient_generators]
    split_ifs <;> (try omega) <;> subst_vars <;> simp_all only [sub_zero, sub_self, one_smul, zero_smul]
  simp_rw [term]
  simp

theorem matterTwo_injective {L : LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M) :
    Function.Injective (matterTwo 𝒨) := by
  intro ω η h
  have ordered (i j : Fin n) (hij : i < j) : ω (Pi.single i 1) (Pi.single j 1) =
      η (Pi.single i 1) (Pi.single j 1) := by
    simpa only [matterCoefficient_two 𝒨 _ i j hij] using
      congrArg (matterCoefficient (pairCoefficient i j)) h
  apply LieCochainCoordinates.ext_basis
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact ordered i j hij
  · simp [LieCochainCoordinates.e]
  · rw [ω.skew, η.skew]; exact congrArg Neg.neg (ordered j i hji)

/-- The matter action is exactly the degree-zero CE differential. -/
theorem matterDifferential_zero {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) (m : M) :
    matterDifferential 𝒨 (matterZero m) = matterOne 𝒨 (differential0 𝒨 m) := by
  change matterDifferential 𝒨 (1 ⊗ₜ[R] m) = _
  simp [matterOne, differential0, lieDifferential]

/-- The full representation term and the bracket term agree with CE `d₁`. -/
theorem matterDifferential_one {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) (φ : LieCochain1 L 𝒨) :
    matterDifferential 𝒨 (matterOne 𝒨 φ) = matterTwo 𝒨 (differential1 𝒨 φ) := by
  have hbracket := lieImages_tmul L φ (1 : GhostPolynomial R n)
  simp only [mul_one] at hbracket
  simp only [matterOne, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    matterDifferential_tmul, lieDifferential_generator, Finset.sum_add_distrib]
  rw [hbracket, sum_pairs (fun i j : Fin n =>
    (generator j * generator i) ⊗ₜ[R] 𝒨.act (Pi.single j 1) (φ (Pi.single i 1)))
    (by intro i; simp)]
  simp only [matterTwo, LinearMap.coe_mk, AddHom.coe_mk, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  split_ifs
  · rw [generator_swap j i, TensorProduct.neg_tmul]
    simp only [differential1, TensorProduct.tmul_sub]
    abel
  · simp

/-- A linear ghost state is closed precisely when the represented CE cochain is a cocycle. -/
theorem matterOne_closed_iff {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) (φ : LieCochain1 L 𝒨) :
    matterDifferential 𝒨 (matterOne 𝒨 φ) = 0 ↔ IsOneCocycle 𝒨 φ := by
  rw [matterDifferential_one, ← map_zero (matterTwo 𝒨), (matterTwo_injective 𝒨).eq_iff]
  constructor
  · intro h x y; exact congrArg (fun ω : LieCochain2 L 𝒨 => ω x y) h
  · intro h; ext x y; exact h x y

/-- Degree-zero closure is the actual invariant-vector condition. -/
theorem matterZero_closed_iff {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) (m : M) :
    matterDifferential 𝒨 (matterZero m) = 0 ↔ ∀ v, 𝒨.act v m = 0 := by
  rw [matterDifferential_zero, ← map_zero (matterOne 𝒨), (matterOne_injective 𝒨).eq_iff]
  constructor
  · intro h v; exact congrArg (fun φ : (Fin n → R) →ₗ[R] M => φ v) h
  · intro h; apply LinearMap.ext; intro v; exact h v

@[simp] theorem matterCoefficient_zero (m : M) :
    matterCoefficient (ExteriorAlgebra.algebraMapInv.toLinearMap :
      GhostPolynomial R n →ₗ[R] R) (matterZero m) = m := by
  change (ExteriorAlgebra.algebraMapInv (1 : GhostPolynomial R n)) • m = m
  simp

theorem matterZero_injective : Function.Injective (matterZero (R := R) (n := n) (M := M)) := by
  intro m k h
  simpa only [matterCoefficient_zero] using congrArg
    (matterCoefficient (ExteriorAlgebra.algebraMapInv.toLinearMap : GhostPolynomial R n →ₗ[R] R)) h

theorem matterZero_mem_degree (m : M) : matterZero (R := R) (n := n) m ∈ matterDegree 0 :=
  tmul_mem_matterDegree (by simpa using scalar_mem_degree (R := R) (n := n) 1) m

/-- Every actual degree-zero tensor state is a constant matter vector. -/
theorem matterDegree_zero_eq_range :
    matterDegree (R := R) (n := n) (M := M) 0 = LinearMap.range matterZero := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨g, hg, m, rfl⟩
    have hg' : g ∈ (1 : Submodule R (GhostPolynomial R n)) := hg
    rcases Submodule.mem_one.mp hg' with ⟨r, rfl⟩
    refine ⟨r • m, ?_⟩
    change (1 : GhostPolynomial R n) ⊗ₜ[R] (r • m) = _
    rw [← TensorProduct.smul_tmul]
    simp [Algebra.smul_def]
  · rintro x ⟨m, rfl⟩
    exact matterZero_mem_degree m

/-- All degree-zero cycles are uniquely represented by invariant matter vectors. -/
theorem matter_degree_zero_closed_iff {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) {x : MatterGhost R n M} (hx : x ∈ matterDegree 0) :
    matterDifferential 𝒨 x = 0 ↔ ∃! m : M, matterZero m = x ∧ ∀ v, 𝒨.act v m = 0 := by
  rw [matterDegree_zero_eq_range] at hx
  rcases hx with ⟨m, rfl⟩
  rw [matterZero_closed_iff]
  constructor
  · intro hm
    exact ⟨m, ⟨rfl, hm⟩, fun y hy => matterZero_injective hy.1⟩
  · rintro ⟨y, ⟨hy, hclosed⟩, _⟩
    exact matterZero_injective hy ▸ hclosed

private theorem augmentation_differential (L : LieAlgebra R (Fin n → R))
    (g : GhostPolynomial R n) : ExteriorAlgebra.algebraMapInv (lieDifferential L g) = 0 := by
  simp [lieDifferential, vectorField, map_sum, lieImages_formula,
    generator, ExteriorAlgebra.algebraMapInv, apply_ite]

/-- No boundary has a nonzero ghost-free coefficient, even with arbitrary primitives. -/
theorem matterCoefficient_zero_differential {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) (x : MatterGhost R n M) :
    matterCoefficient ExteriorAlgebra.algebraMapInv.toLinearMap (matterDifferential 𝒨 x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul g m =>
      simp only [matterDifferential_tmul, map_add, map_sum, matterCoefficient_tmul,
        AlgHom.toLinearMap_apply, augmentation_differential, zero_smul, zero_add]
      simp [generator, ExteriorAlgebra.algebraMapInv]

/-- A constant state is exact if and only if the matter vector itself is zero. -/
theorem matterZero_exact_iff {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) (m : M) :
    (∃ y, matterDifferential 𝒨 y = matterZero m) ↔ m = 0 := by
  constructor
  · rintro ⟨y, hy⟩
    have h := matterCoefficient_zero_differential 𝒨 y
    rwa [hy, matterCoefficient_zero] at h
  · intro h; exact ⟨0, by simp [h]⟩

/-- A trivial matter action reduces to the pure ghost differential tensored with the identity. -/
theorem matterDifferential_trivial (L : LieAlgebra R (Fin n → R)) (x : MatterGhost R n M) :
    matterDifferential (trivialLieModule L : LieModule L M) x =
      TensorProduct.map (lieDifferential L) LinearMap.id x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul g m => simp [TensorProduct.map_tmul]

end LeanPhy.GaugeTheory.GhostPolynomial

