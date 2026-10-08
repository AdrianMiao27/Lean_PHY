import LeanPhy.GaugeTheory.LieGhost
import LeanPhy.Mathematics.LieCohomology3

/-!
# Lie ghost nilpotency from the Chevalley--Eilenberg complex

Increasing-index sums avoid division by factorials. The degree-two CE bridge
and Jacobi imply nilpotency for every finite coordinate Lie algebra over any
commutative ring, with trivial scalar coefficients.
-/

namespace LeanPhy.GaugeTheory.GhostPolynomial

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology

/-- A double sum with zero diagonal can be collected into increasing pairs. -/
theorem sum_pairs {A : Type*} [AddCommMonoid A] {n : Nat}
    (f : Fin n → Fin n → A) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = ∑ i, ∑ j, if i < j then f i j + f j i else 0 := by
  have split (i j : Fin n) : f i j =
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp [hdiag]
    · simp [h, not_lt_of_gt h]
  calc
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f i j else 0) := by
      simp only [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => split i j
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if i < j then f j i else 0) := by rw [Finset.sum_comm (f := fun i j => if j < i then f i j else 0)]
    _ = _ := by
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      split_ifs <;> simp

private theorem sum_pair_triples {A : Type*} [AddCommMonoid A] {n : Nat}
    (f : Fin n → Fin n → Fin n → A)
    (houter : ∀ i j, f i j i = 0) (hlast : ∀ i j, f i j j = 0) :
    (∑ i, ∑ j, ∑ k, if i < j then f i j k else 0) =
      ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then f i j k + f i k j + f j k i else 0 := by
  have split (i j k : Fin n) : (if i < j then f i j k else 0) =
      (if i < j ∧ j < k then f i j k else 0) +
      (if i < k ∧ k < j then f i j k else 0) +
      (if k < i ∧ i < j then f i j k else 0) := by
    by_cases hij : i < j
    · rcases lt_trichotomy k i with hki | rfl | hik
      · simp [hij, hki, show ¬j < k by omega, show ¬i < k by omega]
      · simp [houter, hij]
      · rcases lt_trichotomy k j with hkj | rfl | hjk
        · simp [hij, hik, hkj, not_lt_of_gt hkj, not_lt_of_gt hik]
        · simp [hlast, hij]
        · simp [hij, hik, hjk, not_lt_of_gt hjk, not_lt_of_gt hik]
    · simp [hij, show ¬(i < k ∧ k < j) by omega]
  calc
    _ = (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then f i j k else 0) +
        (∑ i, ∑ j, ∑ k, if i < k ∧ k < j then f i j k else 0) +
        (∑ i, ∑ j, ∑ k, if k < i ∧ i < j then f i j k else 0) := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => split i j k
    _ = (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then f i j k else 0) +
        (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then f i k j else 0) +
        (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then f j k i else 0) := by
      congr 1
      · congr 1
        apply Finset.sum_congr rfl; intro i _
        exact Finset.sum_comm
      · trans ∑ i, ∑ k, ∑ j, if k < i ∧ i < j then f i j k else 0
        · apply Finset.sum_congr rfl; intro i _
          exact Finset.sum_comm
        · exact Finset.sum_comm
    _ = _ := by
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      split_ifs <;> simp

variable {R : Type*} [CommRing R] {n : Nat}

/-- Increasing-triple coordinates, with the bracket-first CE convention. -/
noncomputable def ghostThree (L : LieAlgebra R (Fin n → R)) :
    LieCochain3 L (trivialLieModule L : LieModule L R) →ₗ[R] GhostPolynomial R n where
  toFun t := ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
    t (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) •
      (generator i * (generator j * generator k)) else 0
  map_add' := by
    intro t u
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    split_ifs <;> simp [add_smul]
  map_smul' := by intro r t; simp [Finset.smul_sum, smul_ite, mul_smul]

private theorem lieDifferential_ghostTwo_unordered (L : LieAlgebra R (Fin n → R))
    (ω : LieCochain2 L (trivialLieModule L : LieModule L R)) :
    lieDifferential L (ghostTwo L ω) =
      ∑ i, ∑ j, ω (Pi.single i 1) (Pi.single j 1) • (lieImages L i * generator j) := by
  rw [sum_pairs _ (by intro i; simp)]
  simp only [ghostTwo, LinearMap.coe_mk, AddHom.coe_mk, map_sum, apply_ite,
    map_zero, map_smul, lieDifferential_mul, lieDifferential_generator]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  split_ifs
  · rw [show parityInvolution (generator (R := R) i) = -generator i from generator_isOdd i,
      ω.skew (Pi.single j 1) (Pi.single i 1),
      even_mul_comm (lieImages_even L j) (generator i)]
    simp only [smul_add, neg_mul, smul_neg, neg_smul]
  · rfl

private theorem lieDifferential_ghostTwo_pair_sum (L : LieAlgebra R (Fin n → R))
    (ω : LieCochain2 L (trivialLieModule L : LieModule L R)) :
    lieDifferential L (ghostTwo L ω) =
      ∑ i, ∑ j, ∑ k, if i < j then
        (-ω (L.bracket (Pi.single i 1) (Pi.single j 1)) (Pi.single k 1)) •
          (generator (R := R) i * (generator j * generator k)) else 0 := by
  have slice (k : Fin n) :
      (∑ i, ω (Pi.single i 1) (Pi.single k 1) • lieImages L i) =
        ∑ i, ∑ j, if i < j then
          (-ω (L.bracket (Pi.single i 1) (Pi.single j 1)) (Pi.single k 1)) •
            (generator i * generator j) else 0 := by
    let φ : Module.Dual R (Fin n → R) := ω.toNative.val.flip (Pi.single k 1)
    have h := lieDifferential_ghostOne L φ
    simpa only [ghostOne, ghostTwo, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
      lieDifferential_generator, differential1_trivial, φ, LinearMap.flip_apply,
      LieCochain2.toNative] using h
  rw [lieDifferential_ghostTwo_unordered, Finset.sum_comm]
  calc
    _ = ∑ k, ∑ i, ∑ j, if i < j then
        (-ω (L.bracket (Pi.single i 1) (Pi.single j 1)) (Pi.single k 1)) •
          (generator (R := R) i * (generator j * generator k)) else 0 := by
      apply Finset.sum_congr rfl; intro k _
      simp_rw [← smul_mul_assoc]
      rw [← Finset.sum_mul, slice]
      simp [Finset.sum_mul, ite_mul, mul_assoc]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      exact Finset.sum_comm

theorem triple_cycle (i j k : Fin n) :
    generator (R := R) j * (generator k * generator i) =
      generator i * (generator j * generator k) := by
  rw [triple_swap_last j k i, triple_swap_first j i k, neg_neg]

/-- The degree-two CE/ghost bridge needs no invertibility of two or six. -/
theorem lieDifferential_ghostTwo (L : LieAlgebra R (Fin n → R))
    (ω : LieCochain2 L (trivialLieModule L : LieModule L R)) :
    lieDifferential L (ghostTwo L ω) =
      ghostThree L (differential2Cochain (trivialLieModule L) ω) := by
  rw [lieDifferential_ghostTwo_pair_sum, sum_pair_triples _
    (by intros; simp) (by intros; simp)]
  simp only [ghostThree, LinearMap.coe_mk, AddHom.coe_mk,
    differential2Cochain_apply, differential2_apply, trivialLieModule_act,
    sub_self, zero_add, zero_sub]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  split_ifs
  · rw [triple_swap_last i k j, triple_cycle i j k]
    simp only [smul_neg, neg_smul, neg_neg, sub_smul, add_smul]
    abel
  · rfl

/-- Jacobi, through `d₂ d₁ = 0`, supplies every finite nilpotency certificate. -/
theorem lieImages_closed (L : LieAlgebra R (Fin n → R)) (k : Fin n) :
    lieDifferential L (lieImages L k) = 0 := by
  rw [lieImages, lieDifferential_ghostTwo]
  have h : differential2Cochain (trivialLieModule L)
      (differential1 (trivialLieModule L) (LinearMap.proj k)) = 0 := by
    apply Subtype.ext
    exact differential2_differential1 _ _
  rw [h, map_zero]

/-- Canonical finite Lie ghost nilpotency, over every commutative ring. -/
theorem lieDifferential_sq (L : LieAlgebra R (Fin n → R)) (x : GhostPolynomial R n) :
    lieDifferential L (lieDifferential L x) = 0 :=
  (lieDifferential_sq_iff L).mpr (lieImages_closed L) x

/-- A Lie algebra alone now determines its pure scalar-coefficient ghost differential. -/
noncomputable def canonicalLieBRST (L : LieAlgebra R (Fin n → R)) :
    GradedBRSTDifferential (grading (R := R) (n := n)) := lieBRST L (lieImages_closed L)

@[simp] theorem canonicalLieBRST_apply (L : LieAlgebra R (Fin n → R))
    (x : GhostPolynomial R n) : canonicalLieBRST L x = lieDifferential L x := rfl

end LeanPhy.GaugeTheory.GhostPolynomial
