import LeanPhy.Mathematics.LieDeformationThirdObstruction

/-!
# Joint search for second- and third-order corrections

For a fixed first direction ω the two remaining equations are affine linear
in the pair (ν,ρ). A complete image certificate decides their joint solvability
and constructs an actual third-jet Lie algebra. The image quotient below is a
cokernel of a block map; it is not asserted to be a Chevalley--Eilenberg H³.
-/
namespace LeanPhy.Mathematics.LieDeformation
open LieCohomology
set_option maxSynthPendingDepth 7
universe u v
variable {R : Type u} {V : Type v} [CommRing R] [AddCommGroup V] [Module R V]
variable {L : LieAlgebra R V}

abbrev ThirdCochain (L : LieAlgebra R V) := LieCochain3 L (adjointLieModule L)

/-- For fixed ω, the mixed Jacobi term is linear in the second correction. -/
def thirdObstructionLinear (ω : Cochain L) : Cochain L →ₗ[R] ThirdCochain L where
  toFun := thirdObstructionCochain ω
  map_add' := thirdObstructionCochain_add_right ω
  map_smul' := by
    intro r ν
    apply LieCochain3.ext
    intro x y z
    simp only [thirdObstructionCochain_apply, LieCochain3.smul_apply, thirdObstruction,
      LieCochain2.smul_apply, LieCochain2.map_smul_right, smul_add, RingHom.id_apply]

/-- The block map (ν,ρ) ↦ (d₂ν, Q₃(ω,ν)+d₂ρ). -/
def jointDifferential (ω : Cochain L) :
    (Cochain L × Cochain L) →ₗ[R] (ThirdCochain L × ThirdCochain L) :=
  ((differential2ToThree (adjointLieModule L)).comp (LinearMap.fst R _ _)).prod
    (((differential2ToThree (adjointLieModule L)).comp (LinearMap.snd R _ _)) +
      (thirdObstructionLinear ω).comp (LinearMap.fst R _ _))

@[simp] theorem jointDifferential_apply (ω ν ρ : Cochain L) :
    jointDifferential ω (ν,ρ) =
      (differential2Cochain (adjointLieModule L) ν, thirdResidual ω ν ρ) := rfl

/-- The affine right-hand side contains the quadratic first-direction term. -/
def jointTarget (ω : Cochain L) : ThirdCochain L × ThirdCochain L :=
  (-obstructionCochain ω,0)

theorem joint_equation_iff (ω ν ρ : Cochain L) :
    jointDifferential ω (ν,ρ) = jointTarget ω ↔
      secondResidual ω ν = 0 ∧ thirdResidual ω ν ρ = 0 := by
  rw [jointDifferential_apply, jointTarget, Prod.mk.injEq]
  constructor
  · rintro ⟨hν,hρ⟩
    refine ⟨?_,hρ⟩
    have h := congrArg Subtype.val hν
    change differential2 (adjointLieModule L) ν = -obstructionTrilinear ω at h
    change differential2 (adjointLieModule L) ν + obstructionTrilinear ω = 0
    rw [h,neg_add_cancel]
  · rintro ⟨hν,hρ⟩
    refine ⟨?_,hρ⟩
    apply LieCochain3.ext
    intro x y z
    exact eq_neg_of_add_eq_zero_left ((secondResidual_eq_zero_iff _ _).mp hν x y z)

/-- Unlike ThirdExtendable, this predicate searches over the second correction too. -/
def ThirdDirectionExtendable (ω : Cochain L) : Prop := ∃ ν, ThirdExtendable ω ν

theorem thirdDirectionExtendable_iff_joint (ω : Cochain L) :
    ThirdDirectionExtendable ω ↔ IsTwoCocycle (adjointLieModule L) ω ∧
      ∃ q, jointDifferential ω q = jointTarget ω := by
  constructor
  · rintro ⟨ν,ρ,D,hD⟩
    have hc := (thirdAlgebra_exists_iff ω ν ρ).mp ⟨D,hD⟩
    exact ⟨hc.1,⟨(ν,ρ),(joint_equation_iff ω ν ρ).mpr hc.2⟩⟩
  · rintro ⟨hω,⟨⟨ν,ρ⟩,hq⟩⟩
    have hc := (joint_equation_iff ω ν ρ).mp hq
    exact ⟨ν,ρ,thirdAlgebra ω ν ρ hω hc.1 hc.2,rfl⟩

theorem thirdDirectionExtendable_second (ω : Cochain L) (h : ThirdDirectionExtendable ω) :
    SecondExtendable ω := by
  obtain ⟨ν,hν⟩ := h
  have hl := thirdExtendable_lower ω ν hν
  exact ⟨ν,secondAlgebra ω ν hl.1 ((secondResidual_eq_zero_iff _ _).mp hl.2),rfl⟩

/-- A split image certificate for the joint block map. Over arbitrary rings
such a certificate is an explicit premise, not an automatic existence claim. -/
abbrev JointReduction (ω : Cochain L) (H : Type*) [AddCommGroup H] [Module R H] :=
  CohomologyReduction (jointDifferential ω)
    (0 : (ThirdCochain L × ThirdCochain L) →ₗ[R] R) H

namespace JointReduction
variable {H : Type*} [AddCommGroup H] [Module R H]
variable {ω : Cochain L} (S : JointReduction ω H)

/-- These are block-image coordinates, not a purported H³ class. -/
def obstructionCoordinates : H := S.project (jointTarget ω)

/-- Both corrections are computed together, including a possible change to ν. -/
def corrections : Cochain L × Cochain L := S.primitive (jointTarget ω)

theorem corrections_solve (h : obstructionCoordinates S = 0) :
    jointDifferential ω (corrections S) = jointTarget ω := by
  have hn := S.normal_form (jointTarget ω) (by simp)
  change S.project (jointTarget ω) = 0 at h
  simpa only [corrections,h,map_zero,add_zero] using hn

theorem corrections_cancel (h : obstructionCoordinates S = 0) :
    secondResidual ω (corrections S).1 = 0 ∧
      thirdResidual ω (corrections S).1 (corrections S).2 = 0 :=
  (joint_equation_iff ω _ _).mp (corrections_solve S h)

theorem extendable_iff : ThirdDirectionExtendable ω ↔
    IsTwoCocycle (adjointLieModule L) ω ∧ obstructionCoordinates S = 0 := by
  rw [thirdDirectionExtendable_iff_joint, S.exact_iff (jointTarget ω) (by simp)]
  rfl

/-- The checked block primitive constructs a genuine third-jet Lie algebra. -/
def model (hω : IsTwoCocycle (adjointLieModule L) ω)
    (h : obstructionCoordinates S = 0) : LieAlgebra R (ThirdJet V) :=
  thirdAlgebra ω (corrections S).1 (corrections S).2 hω
    (corrections_cancel S h).1 (corrections_cancel S h).2

@[simp] theorem model_bracket (hω : IsTwoCocycle (adjointLieModule L) ω)
    (h : obstructionCoordinates S = 0) :
    (model S hω h).bracket = thirdBracket ω (corrections S).1 (corrections S).2 := rfl

/-- A nonzero block-image obstruction rules out every pair of corrections. -/
theorem no_model (h : obstructionCoordinates S ≠ 0) : ¬ThirdDirectionExtendable ω :=
  fun he => h ((extendable_iff S).mp he).2

/-- All solutions form a translate of the joint kernel, not two independent
cocycle spaces: changing ν also changes the equation for ρ. -/
theorem all_corrections_iff (ν ρ : Cochain L) (h : obstructionCoordinates S = 0) :
    secondResidual ω ν = 0 ∧ thirdResidual ω ν ρ = 0 ↔
      jointDifferential ω ((ν,ρ) - corrections S) = 0 := by
  rw [← joint_equation_iff, map_sub, corrections_solve S h, sub_eq_zero]

theorem all_models_iff (ν ρ : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (h : obstructionCoordinates S = 0) :
    (∃ D : LieAlgebra R (ThirdJet V), D.bracket = thirdBracket ω ν ρ) ↔
      jointDifferential ω ((ν,ρ) - corrections S) = 0 := by
  rw [thirdAlgebra_exists_iff, and_iff_right hω, all_corrections_iff S ν ρ h]

end JointReduction
/-- Flatten two finite coefficient arrays without dropping any coordinate. -/
def pairCoordinates (n : Nat) :
    ((Fin n → R) × (Fin n → R)) ≃ₗ[R] (Fin (n+n) → R) where
  toFun q := Fin.append q.1 q.2
  invFun a := (fun i => a (Fin.castAdd n i), fun i => a (Fin.natAdd n i))
  left_inv := by
    intro q; apply Prod.ext <;> funext i
    · exact Fin.append_left _ _ _
    · exact Fin.append_right _ _ _
  right_inv := by intro a; exact Fin.append_castAdd_natAdd
  map_add' := by
    intro q p; funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,Fin.append_left,Fin.append_right]
  map_smul' := by
    intro r q; funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [Pi.smul_apply,Fin.append_left,Fin.append_right]
    all_goals rfl

@[simp] theorem pairCoordinates_apply (n : Nat) (a b : Fin n → R) :
    pairCoordinates n (a,b) = Fin.append a b := rfl

end LeanPhy.Mathematics.LieDeformation
