import LeanPhy.Mathematics.LieCohomology3

/-! Finite coordinate checks and certified reductions of the actual H³ quotient. -/
namespace LeanPhy.Mathematics

set_option maxSynthPendingDepth 7
namespace LieCohomology
variable {R V M H : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
variable {L : LieAlgebra R V} (𝒨 : LieModule L M)

/-- A reduction must check both maps, including the outgoing differential. -/
abbrev ThirdReduction (H : Type*) [AddCommGroup H] [Module R H] :=
  CohomologyReduction (differential2ToThree 𝒨) (differential3Linear 𝒨) H

noncomputable def ThirdReduction.h3Equiv (S : ThirdReduction 𝒨 H) : H3 𝒨 ≃ₗ[R] H :=
  S.quotientEquiv

@[simp] theorem ThirdReduction.h3Equiv_classOf (S : ThirdReduction 𝒨 H)
    (t : LieCochain3 L 𝒨) (ht : IsThreeCocycle 𝒨 t) :
    S.h3Equiv 𝒨 (classOfThree 𝒨 t ht) = S.project t := rfl
end LieCohomology

namespace LieCochainCoordinates
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Increasing triples determine every alternating three-cochain. -/
theorem three_ext_increasing {n : Nat} {L : LieAlgebra R (Fin n → R)}
    {𝒨 : LieModule L M} {t s : LieCochain3 L 𝒨}
    (h : ∀ i j k : Fin n, i < j → j < k → t (e i) (e j) (e k) = s (e i) (e j) (e k)) : t = s := by
  have ordered (i j k : Fin n) (hij : i < j) : t (e i) (e j) (e k) = s (e i) (e j) (e k) := by
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · exact h i j k hij hjk
    · simp
    · rcases lt_trichotomy i k with hik | rfl | hki
      · rw [LieCochain3.swap_last t (e i) (e k) (e j),
          LieCochain3.swap_last s (e i) (e k) (e j),h i k j hik hkj]
      · simp
      · rw [LieCochain3.swap_last t (e i) (e k) (e j),
          LieCochain3.swap_last s (e i) (e k) (e j),
          LieCochain3.swap_first t (e k) (e i) (e j),
          LieCochain3.swap_first s (e k) (e i) (e j),h k i j hki hij]
  apply Subtype.ext
  apply (Pi.basisFun R (Fin n)).ext; intro i
  apply (Pi.basisFun R (Fin n)).ext; intro j
  apply (Pi.basisFun R (Fin n)).ext; intro k
  simp only [Pi.basisFun_apply]
  change t (e i) (e j) (e k) = s (e i) (e j) (e k)
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact ordered i j k hij
  · simp
  · rw [LieCochain3.swap_first t (e j) (e i) (e k),
      LieCochain3.swap_first s (e j) (e i) (e k),ordered j i k hji]

/-- Four-linear maps are determined on coordinate basis vectors. -/
theorem quadrilinear_eq_zero_of_basis {n : Nat}
    (t : (Fin n → R) →ₗ[R] (Fin n → R) →ₗ[R] (Fin n → R) →ₗ[R] (Fin n → R) →ₗ[R] M)
    (h : ∀ i j k l, t (e i) (e j) (e k) (e l) = 0) : t = 0 := by
  apply (Pi.basisFun R (Fin n)).ext; intro i
  apply (Pi.basisFun R (Fin n)).ext; intro j
  apply (Pi.basisFun R (Fin n)).ext; intro k
  apply (Pi.basisFun R (Fin n)).ext; intro l
  simpa only [Pi.basisFun_apply,LinearMap.zero_apply,e] using h i j k l

open LieCohomology in
/-- Increasing quadruples suffice for closedness, including dimensions below four. -/
theorem differential3_eq_zero_of_increasing {n : Nat} {L : LieAlgebra R (Fin n → R)}
    (𝒨 : LieModule L M) (t : LieCochain3 L 𝒨)
    (h : ∀ i j k l : Fin n, i < j → j < k → k < l →
      differential3 𝒨 t (e i) (e j) (e k) (e l) = 0) : differential3 𝒨 t = 0 := by
  have ordered3 (i j k l : Fin n) (hij : i < j) (hjk : j < k) :
      differential3 𝒨 t (e i) (e j) (e k) (e l) = 0 := by
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · exact h i j k l hij hjk hkl
    · simp only [differential3_repeat_last]
    · rw [differential3_swap_last 𝒨 t (e i) (e j) (e l) (e k)]
      rcases lt_trichotomy j l with hjl | rfl | hlj
      · rw [h i j l k hij hjl hlk,neg_zero]
      · simp only [differential3_repeat_middle,neg_zero]
      · rw [differential3_swap_middle 𝒨 t (e i) (e l) (e j) (e k)]
        rcases lt_trichotomy i l with hil | rfl | hli
        · rw [h i l j k hil hlj hjk,neg_zero,neg_zero]
        · simp only [differential3_repeat_first,neg_zero]
        · rw [differential3_swap_first 𝒨 t (e l) (e i) (e j) (e k),
            h l i j k hli hij hjk,neg_zero,neg_zero,neg_zero]
  have ordered2 (i j k l : Fin n) (hij : i < j) :
      differential3 𝒨 t (e i) (e j) (e k) (e l) = 0 := by
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · exact ordered3 i j k l hij hjk
    · simp only [differential3_repeat_middle]
    · rw [differential3_swap_middle 𝒨 t (e i) (e k) (e j) (e l)]
      rcases lt_trichotomy i k with hik | rfl | hki
      · rw [ordered3 i k j l hik hkj,neg_zero]
      · simp only [differential3_repeat_first,neg_zero]
      · rw [differential3_swap_first 𝒨 t (e k) (e i) (e j) (e l),
          ordered3 k i j l hki hij,neg_zero,neg_zero]
  apply quadrilinear_eq_zero_of_basis
  intro i j k l
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact ordered2 i j k l hij
  · simp only [differential3_repeat_first]
  · rw [differential3_swap_first 𝒨 t (e j) (e i) (e k) (e l),ordered2 j i k l hji,neg_zero]

end LieCochainCoordinates
end LeanPhy.Mathematics
