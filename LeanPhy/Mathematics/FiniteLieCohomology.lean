import LeanPhy.Mathematics.LieCohomologyReduction

/-!
# Finite-basis checks for Lie cohomology

The degree-two CE differential is alternating. On a finite coordinate carrier,
its vanishing can therefore be checked on strictly increasing triples of basis
vectors. These theorems support generated coordinate proofs with arbitrary
finite-dimensional coefficient modules; no representation law is omitted.
-/

namespace LeanPhy.Mathematics

namespace LieCohomology

variable {R V M : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable [AddCommGroup M] [Module R M] {L : LieAlgebra R V} (𝒨 : LieModule L M)

theorem differential2_swap_first (ω : LieCochain2 L 𝒨) (x y z : V) :
    differential2 𝒨 ω y x z = -differential2 𝒨 ω x y z := by
  simp only [differential2_apply]
  rw [L.antisymm y x, LieCochain2.neg_left, ω.skew y x, 𝒨.act_neg_right]
  abel

theorem differential2_swap_last (ω : LieCochain2 L 𝒨) (x y z : V) :
    differential2 𝒨 ω x z y = -differential2 𝒨 ω x y z := by
  simp only [differential2_apply]
  rw [ω.skew z y, 𝒨.act_neg_right, L.antisymm z y, LieCochain2.neg_left]
  abel

@[simp] theorem differential2_repeat_first (ω : LieCochain2 L 𝒨) (x z : V) :
    differential2 𝒨 ω x x z = 0 := by
  simp [differential2_apply]

@[simp] theorem differential2_repeat_last (ω : LieCochain2 L 𝒨) (x y : V) :
    differential2 𝒨 ω x y y = 0 := by
  simp [differential2_apply]

@[simp] theorem differential2_repeat_outer (ω : LieCochain2 L 𝒨) (x y : V) :
    differential2 𝒨 ω x y x = 0 := by
  rw [differential2_swap_last, differential2_repeat_first, neg_zero]

end LieCohomology

namespace LieCochainCoordinates

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Trilinear maps on a coordinate space are determined by basis triples. -/
theorem trilinear_eq_zero_of_basis {n : Nat}
    (t : (Fin n → R) →ₗ[R] (Fin n → R) →ₗ[R] (Fin n → R) →ₗ[R] M)
    (h : ∀ i j k, t (e i) (e j) (e k) = 0) : t = 0 := by
  apply (Pi.basisFun R (Fin n)).ext
  intro i
  apply (Pi.basisFun R (Fin n)).ext
  intro j
  apply (Pi.basisFun R (Fin n)).ext
  intro k
  simpa only [Pi.basisFun_apply, LinearMap.zero_apply, e] using h i j k

/-- Increasing triples suffice; repeated and permuted triples follow from
alternation, including dimensions zero, one and two. -/
theorem differential2_eq_zero_of_increasing {n : Nat}
    {L : LieAlgebra R (Fin n → R)} (𝒨 : LieModule L M) (ω : LieCochain2 L 𝒨)
    (h : ∀ i j k : Fin n, i < j → j < k →
      LieCohomology.differential2 𝒨 ω (e i) (e j) (e k) = 0) :
    LieCohomology.differential2 𝒨 ω = 0 := by
  open LieCohomology in
  have ordered (i j k : Fin n) (hij : i < j) :
      differential2 𝒨 ω (e i) (e j) (e k) = 0 := by
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · exact h i j k hij hjk
    · exact differential2_repeat_last _ _ _ _
    · rcases lt_trichotomy i k with hik | rfl | hki
      · rw [differential2_swap_last 𝒨 ω (e i) (e k) (e j), h i k j hik hkj, neg_zero]
      · exact differential2_repeat_outer _ _ _ _
      · rw [differential2_swap_last 𝒨 ω (e i) (e k) (e j),
          differential2_swap_first 𝒨 ω (e k) (e i) (e j), h k i j hki hij, neg_zero, neg_zero]
  apply trilinear_eq_zero_of_basis
  intro i j k
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact ordered i j k hij
  · exact LieCohomology.differential2_repeat_first _ _ _ _
  · rw [LieCohomology.differential2_swap_first 𝒨 ω (e j) (e i) (e k),
      ordered j i k hji, neg_zero]

end LieCochainCoordinates

end LeanPhy.Mathematics
