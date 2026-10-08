import LeanPhy.GaugeTheory.GhostDegree
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Lie ghosts with matter coefficients

The Chevalley--Eilenberg ghost differential on `Λ(Rⁿ) ⊗ M` includes the
declared Lie action on `M`. Its square vanishes by Jacobi and the representation
law, over any commutative ring. Matter is only assumed to be a module; no
unavailable product on matter states is inferred.
-/

namespace LeanPhy.GaugeTheory.GhostPolynomial

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open scoped TensorProduct

set_option maxSynthPendingDepth 7

variable {R : Type*} [CommRing R] {n : Nat}
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Exterior ghost polynomials with coefficients in a matter module. -/
abbrev MatterGhost (R : Type*) [CommRing R] (n : Nat)
    (M : Type*) [AddCommGroup M] [Module R M] := GhostPolynomial R n ⊗[R] M

/-- The declared action of one Lie element, as a linear map on matter. -/
def matterAction {L : LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M)
    (v : Fin n → R) : M →ₗ[R] M where
  toFun := 𝒨.act v
  map_add' := 𝒨.act_add_right v
  map_smul' := 𝒨.act_smul_right v

/-- Left multiplication by a ghost polynomial acts on the tensor module. -/
noncomputable def matterMultiply (g : GhostPolynomial R n) :
    MatterGhost R n M →ₗ[R] MatterGhost R n M :=
  TensorProduct.map
    { toFun := fun x => g * x
      map_add' := mul_add g
      map_smul' := fun r x => mul_smul_comm r g x }
    LinearMap.id

@[simp] theorem matterMultiply_tmul (g x : GhostPolynomial R n) (m : M) :
    matterMultiply g (x ⊗ₜ[R] m) = (g * x) ⊗ₜ[R] m := rfl

/-- The matter term uses left ghost multiplication: `cⁱ g ⊗ ρ(eᵢ)m`. -/
noncomputable def matterDifferential {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) : MatterGhost R n M →ₗ[R] MatterGhost R n M :=
  TensorProduct.map (lieDifferential L) LinearMap.id +
    ∑ i : Fin n, TensorProduct.map
      { toFun := fun g => generator i * g
        map_add' := mul_add _
        map_smul' := fun r g => mul_smul_comm r _ g }
      (matterAction 𝒨 (Pi.single i 1))

@[simp] theorem matterDifferential_tmul {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) (g : GhostPolynomial R n) (m : M) :
    matterDifferential 𝒨 (g ⊗ₜ[R] m) = lieDifferential L g ⊗ₜ[R] m +
      ∑ i, (generator i * g) ⊗ₜ[R] 𝒨.act (Pi.single i 1) m := by
  simp [matterDifferential, matterAction, TensorProduct.map_tmul]

private theorem linear_coordinates (φ : (Fin n → R) →ₗ[R] M) (v : Fin n → R) :
    φ v = ∑ i, v i • φ (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp

/-- The quadratic ghost images encode the bracket on arbitrary module coefficients. -/
theorem lieImages_tmul (L : LieAlgebra R (Fin n → R))
    (φ : (Fin n → R) →ₗ[R] M) (g : GhostPolynomial R n) :
    (∑ k, (lieImages L k * g) ⊗ₜ[R] φ (Pi.single k 1)) =
      -∑ i, ∑ j, if i < j then
        ((generator i * generator j) * g) ⊗ₜ[R]
          φ (L.bracket (Pi.single i 1) (Pi.single j 1)) else 0 := by
  simp only [lieImages_formula, Finset.sum_mul, ite_mul, zero_mul,
    TensorProduct.sum_tmul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  split_ifs
  · simp only [smul_mul_assoc, TensorProduct.smul_tmul, neg_smul, neg_mul,
      TensorProduct.neg_tmul, Finset.sum_neg_distrib]
    rw [← TensorProduct.tmul_sum, ← linear_coordinates]
  · simp

private theorem action_square {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) (g : GhostPolynomial R n) (m : M) :
    (∑ i, ∑ j, (generator j * (generator i * g)) ⊗ₜ[R]
      𝒨.act (Pi.single j 1) (𝒨.act (Pi.single i 1) m)) =
      ∑ i, ∑ j, if i < j then
        ((generator i * generator j) * g) ⊗ₜ[R]
          𝒨.act (L.bracket (Pi.single i 1) (Pi.single j 1)) m else 0 := by
  rw [sum_pairs _ (by intro i; simp [← mul_assoc])]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  split_ifs
  · rw [← mul_assoc, generator_swap j i, neg_mul, TensorProduct.neg_tmul,
      ← mul_assoc, 𝒨.bracket_act, TensorProduct.tmul_sub]
    abel
  · rfl

/-- Nilpotency follows from the Lie and representation laws on all tensor states. -/
theorem matterDifferential_sq {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) (x : MatterGhost R n M) :
    matterDifferential 𝒨 (matterDifferential 𝒨 x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul g m =>
      simp only [matterDifferential_tmul, map_add, map_sum, lieDifferential_sq,
        TensorProduct.zero_tmul, zero_add, lieDifferential_mul,
        lieDifferential_generator, show ∀ i : Fin n, parityInvolution (generator (R := R) i) = -generator i from
          fun i => generator_isOdd i, neg_mul,
        TensorProduct.add_tmul, TensorProduct.neg_tmul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      have himages := lieImages_tmul L (differential0 𝒨 m) g
      simp only [differential0, LinearMap.coe_mk, AddHom.coe_mk] at himages
      rw [himages, action_square]
      abel

/-- The odd product rule for the action of the ghost algebra on matter states. -/
theorem matterDifferential_multiply {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) (g : GhostPolynomial R n) (x : MatterGhost R n M) :
    matterDifferential 𝒨 (matterMultiply g x) =
      matterMultiply (lieDifferential L g) x +
        matterMultiply (parityInvolution g) (matterDifferential 𝒨 x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | tmul h m =>
      simp only [matterMultiply_tmul, matterDifferential_tmul, lieDifferential_mul,
        TensorProduct.add_tmul, map_add, map_sum, matterMultiply_tmul, add_assoc]
      congr 1
      congr 1
      apply Finset.sum_congr rfl; intro i _
      rw [← mul_assoc, generator_mul_eq_parity_mul, mul_assoc]

/-- Integer ghost degree on the tensor module, generated by homogeneous pure tensors. -/
def matterDegree (d : Int) : Submodule R (MatterGhost R n M) :=
  Submodule.span R {x | ∃ g ∈ degree d, ∃ m : M, x = g ⊗ₜ[R] m}

theorem tmul_mem_matterDegree {d : Int} {g : GhostPolynomial R n}
    (hg : g ∈ degree d) (m : M) : g ⊗ₜ[R] m ∈ matterDegree d :=
  Submodule.subset_span ⟨g, hg, m, rfl⟩

/-- The matter action has ghost degree +1, including in characteristic two. -/
theorem matterDifferential_mem_degree {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) {d : Int} {x : MatterGhost R n M}
    (hx : x ∈ matterDegree d) : matterDifferential 𝒨 x ∈ matterDegree (d + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨g, hg, m, rfl⟩
      rw [matterDifferential_tmul]
      apply Submodule.add_mem
      · exact tmul_mem_matterDegree (lieDifferential_mem_degree L hg) m
      · apply Submodule.sum_mem; intro i _
        exact tmul_mem_matterDegree
          (by simpa [add_comm] using mul_mem_degree (generator_mem_degree i) hg) _
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

/-- Closed matter states form a submodule. -/
noncomputable def matterCycles {L : LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M) :
    Submodule R (MatterGhost R n M) := LinearMap.ker (matterDifferential 𝒨)

/-- Every exact matter state is closed; no degree restriction is needed. -/
theorem matter_boundary_closed {L : LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M)
    {x : MatterGhost R n M} (hx : ∃ y, matterDifferential 𝒨 y = x) :
    matterDifferential 𝒨 x = 0 := by
  rcases hx with ⟨y, rfl⟩
  exact matterDifferential_sq 𝒨 y

end LeanPhy.GaugeTheory.GhostPolynomial

