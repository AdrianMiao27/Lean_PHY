import LeanPhy.Mathematics.LieDeformationThirdOrder

/-!
# Intrinsic obstructions and certified solutions at third order

The input includes a valid second-order correction. H³ classifies the next
extension obstruction for that input; this is not a canonical function on H².
Every existing certified ThirdReduction can construct a third-order model.
-/
namespace LeanPhy.Mathematics.LieDeformation
open LieCohomology
set_option maxSynthPendingDepth 7
universe u v
variable {R : Type u} {V : Type v} [CommRing R] [AddCommGroup V] [Module R V]
variable {L : LieAlgebra R V}

theorem thirdObstructionCochain_add_right (ω ν η : Cochain L) :
    thirdObstructionCochain ω (ν + η) =
      thirdObstructionCochain ω ν + thirdObstructionCochain ω η := by
  apply LieCochain3.ext
  intro x y z
  simp only [thirdObstructionCochain_apply, LieCochain3.add_apply, thirdObstruction,
    LieCochain2.add_apply, LieCochain2.map_add_right]
  abel

@[simp] theorem thirdObstructionCochain_zero_right (ω : Cochain L) :
    thirdObstructionCochain ω 0 = 0 := by
  apply LieCochain3.ext
  intro x y z
  simp only [thirdObstructionCochain_apply, LieCochain3.zero_apply, thirdObstruction,
    LieCochain2.zero_apply, LieCochain2.zero_right, add_zero]

/-- The actual H³ class for the specified second-order model. -/
def thirdObstructionClass (ω ν : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hν : secondResidual ω ν = 0) :
    H3 (adjointLieModule L) :=
  classOfThree (adjointLieModule L) (thirdObstructionCochain ω ν)
    (thirdObstruction_isThreeCocycle ω ν hω hν)

/-- Third-order extendability includes validity of both lower orders. -/
theorem thirdExtendable_lower (ω ν : Cochain L) (h : ThirdExtendable ω ν) :
    IsTwoCocycle (adjointLieModule L) ω ∧ secondResidual ω ν = 0 := by
  obtain ⟨ρ,D,hD⟩ := h
  have hc := (thirdAlgebra_exists_iff ω ν ρ).mp ⟨D,hD⟩
  exact ⟨hc.1,hc.2.1⟩

theorem thirdExtendable_iff_residual (ω ν : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hν : secondResidual ω ν = 0) :
    ThirdExtendable ω ν ↔ ∃ ρ, thirdResidual ω ν ρ = 0 := by
  constructor
  · rintro ⟨ρ,D,hD⟩
    exact ⟨ρ,((thirdAlgebra_exists_iff ω ν ρ).mp ⟨D,hD⟩).2.2⟩
  · rintro ⟨ρ,hρ⟩; exact ⟨ρ,thirdAlgebra ω ν ρ hω hν hρ,rfl⟩

/-- Vanishing detects existence of an actual third-order model, over every
possible third correction, while retaining the specified second correction. -/
theorem thirdExtendable_iff_obstructionClass_zero (ω ν : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hν : secondResidual ω ν = 0) :
    ThirdExtendable ω ν ↔ thirdObstructionClass ω ν hω hν = 0 := by
  rw [thirdExtendable_iff_residual ω ν hω hν, thirdObstructionClass,
    classOfThree_eq_zero_iff]
  constructor
  · rintro ⟨ρ,hρ⟩
    refine ⟨-ρ,?_⟩
    change (differential2ToThree (adjointLieModule L)) (-ρ) = thirdObstructionCochain ω ν
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_right hρ).symm
  · rintro ⟨ρ,hρ⟩
    refine ⟨-ρ,?_⟩
    change (differential2ToThree (adjointLieModule L)) (-ρ) + thirdObstructionCochain ω ν = 0
    rw [map_neg]
    change -differential2Cochain (adjointLieModule L) ρ + thirdObstructionCochain ω ν = 0
    rw [hρ,neg_add_cancel]

theorem thirdExtendable_of_subsingleton_h3 [Subsingleton (H3 (adjointLieModule L))]
    (ω ν : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω)
    (hν : secondResidual ω ν = 0) : ThirdExtendable ω ν :=
  (thirdExtendable_iff_obstructionClass_zero ω ν hω hν).mpr (Subsingleton.elim _ _)

/-- The difference of two third corrections is closed precisely when both
cancel the same residual. This describes all corrections, not a chosen ansatz. -/
theorem thirdCorrections_difference (ω ν ρ σ : Cochain L)
    (hρ : thirdResidual ω ν ρ = 0) :
    thirdResidual ω ν σ = 0 ↔ IsTwoCocycle (adjointLieModule L) (σ - ρ) := by
  have hdρ : differential2Cochain (adjointLieModule L) ρ = -thirdObstructionCochain ω ν :=
    eq_neg_of_add_eq_zero_left hρ
  have heq : differential2Cochain (adjointLieModule L) (σ - ρ) = thirdResidual ω ν σ := by
    change (differential2ToThree (adjointLieModule L)) (σ - ρ) = _
    rw [map_sub]
    change differential2Cochain (adjointLieModule L) σ - differential2Cochain (adjointLieModule L) ρ = _
    rw [hdρ, sub_neg_eq_add]; rfl
  constructor
  · intro hσ
    change differential2 (adjointLieModule L) (σ - ρ) = 0
    exact congrArg Subtype.val (heq.trans hσ)
  · intro hσ
    rw [← heq]
    exact LieCochain3.ext ((isTwoCocycle_iff _ _).mp hσ)

namespace ThirdReduction
variable {H : Type*} [AddCommGroup H] [Module R H]
variable (S : LieCohomology.ThirdReduction (adjointLieModule L) H)

/-- Computed coordinates of the next obstruction in the certified H³ space. -/
def thirdCoordinates (ω ν : Cochain L) : H := S.project (thirdObstructionCochain ω ν)

theorem thirdCoordinates_class (ω ν : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hν : secondResidual ω ν = 0) :
    S.h3Equiv (adjointLieModule L) (thirdObstructionClass ω ν hω hν) = thirdCoordinates S ω ν := rfl

theorem third_extendable_iff (ω ν : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hν : secondResidual ω ν = 0) :
    ThirdExtendable ω ν ↔ thirdCoordinates S ω ν = 0 := by
  rw [thirdExtendable_iff_obstructionClass_zero ω ν hω hν]
  exact (LinearEquiv.map_eq_zero_iff (S.h3Equiv (adjointLieModule L))).symm

/-- The negative certified primitive cancels the ε³ obstruction. -/
def thirdCorrection (ω ν : Cochain L) : Cochain L :=
  -S.primitive (thirdObstructionCochain ω ν)

theorem thirdCorrection_cancels (ω ν : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hν : secondResidual ω ν = 0)
    (h : thirdCoordinates S ω ν = 0) : thirdResidual ω ν (thirdCorrection S ω ν) = 0 := by
  have hb := S.normal_form (thirdObstructionCochain ω ν)
    (thirdObstruction_isThreeCocycle ω ν hω hν)
  change S.project (thirdObstructionCochain ω ν) = 0 at h
  rw [h,map_zero,add_zero] at hb
  change (differential2ToThree (adjointLieModule L)) (-S.primitive (thirdObstructionCochain ω ν)) +
    thirdObstructionCochain ω ν = 0
  rw [map_neg, hb, neg_add_cancel]

def thirdModel (ω ν : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hν : secondResidual ω ν = 0)
    (h : thirdCoordinates S ω ν = 0) : LieAlgebra R (ThirdJet V) :=
  thirdAlgebra ω ν (thirdCorrection S ω ν) hω hν (thirdCorrection_cancels S ω ν hω hν h)

@[simp] theorem thirdModel_bracket (ω ν : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hν : secondResidual ω ν = 0)
    (h : thirdCoordinates S ω ν = 0) :
    (thirdModel S ω ν hω hν h).bracket = thirdBracket ω ν (thirdCorrection S ω ν) := rfl

theorem all_third_corrections (ω ν ρ : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hν : secondResidual ω ν = 0)
    (h : thirdCoordinates S ω ν = 0) :
    thirdResidual ω ν ρ = 0 ↔
      IsTwoCocycle (adjointLieModule L) (ρ - thirdCorrection S ω ν) :=
  thirdCorrections_difference ω ν (thirdCorrection S ω ν) ρ (thirdCorrection_cancels S ω ν hω hν h)

end ThirdReduction
end LeanPhy.Mathematics.LieDeformation
