import LeanPhy.Mathematics.FiniteLieCohomology3
import LeanPhy.Mathematics.LieDeformationGauge

/-!
# Intrinsic H³ obstructions to second-order Lie deformations

The quadratic Jacobi term of a closed direction is a genuine three-cocycle.
Its class in the actual H³ quotient vanishes exactly when a second-order
extension exists, and is invariant under first-order equivalence. All formulas
are valid over a commutative ring; no division by two or three is used.
-/
namespace LeanPhy.Mathematics.LieDeformation

open LieCohomology
set_option maxSynthPendingDepth 7
set_option maxRecDepth 2048

universe u v
variable {R : Type u} {V : Type v} [CommRing R] [AddCommGroup V] [Module R V]
variable {L : LieAlgebra R V}

/-- The quadratic Jacobi term in the actual alternating three-cochain space. -/
def obstructionCochain (ω : Cochain L) : LieCochain3 L (adjointLieModule L) :=
  ⟨obstructionTrilinear ω,obstruction_repeat_first ω,obstruction_repeat_last ω⟩

@[simp] theorem obstructionCochain_apply (ω : Cochain L) (x y z : V) :
    obstructionCochain ω x y z = obstruction ω x y z := rfl

/-- This auxiliary expression uses ω in both action and bracket slots. It is
not asserted to be a cochain differential or a Lie module structure. -/
def mixedDifferential3 (ω : Cochain L) (t : LieCochain3 L (adjointLieModule L)) (w x y z : V) : V :=
  ω w (t x y z) - ω x (t w y z) + ω y (t w x z) - ω z (t w x y) -
    t (ω w x) y z + t (ω w y) x z - t (ω w z) x y -
    t (ω x y) w z + t (ω x z) w y - t (ω y z) w x

/-- Polarized Jacobi/Bianchi identity. Its ninety expanded terms cancel using
only bilinearity and skew symmetry, with no characteristic restriction. -/
theorem obstruction_bianchi (ω : Cochain L) (w x y z : V) :
    differential3Expr (adjointLieModule L) (obstructionCochain ω) w x y z +
      mixedDifferential3 ω (differential2Cochain (adjointLieModule L) ω) w x y z = 0 := by
  simp only [differential3Expr,obstructionCochain_apply,mixedDifferential3,
    differential2Cochain_apply,← linearJacobi_eq_differential2]
  simp only [adjointLieModule,obstruction,linearJacobi,sub_eq_add_neg,
    LieAlgebra.bracket_add_right,
    LieCochain2.map_add_right]
  -- Concrete instances orient each swap; the generic skew rule would loop.
  simp only [L.antisymm (y) (w),
    L.antisymm (z) (w),
    L.antisymm (z) (x),
    L.antisymm (ω (w) (x)) (y),
    L.antisymm (ω (w) (y)) (x),
    L.antisymm (ω (w) (z)) (x),
    L.antisymm (ω (x) (y)) (w),
    L.antisymm (ω (x) (y)) (ω (w) (z)),
    L.antisymm (ω (x) (z)) (w),
    L.antisymm (ω (x) (z)) (ω (w) (y)),
    L.antisymm (ω (y) (z)) (w),
    L.antisymm (ω (y) (z)) (ω (w) (x)),
    ω.skew (y) (w),
    ω.skew (z) (w),
    ω.skew (z) (x),
    ω.skew (L.bracket (w) (x)) (y),
    ω.skew (L.bracket (w) (y)) (x),
    ω.skew (L.bracket (w) (z)) (x),
    ω.skew (L.bracket (x) (y)) (w),
    ω.skew (L.bracket (x) (z)) (w),
    ω.skew (L.bracket (y) (z)) (w),
    ω.skew (ω (w) (x)) (y),
    ω.skew (ω (w) (x)) (L.bracket (y) (z)),
    ω.skew (ω (w) (y)) (x),
    ω.skew (ω (w) (y)) (L.bracket (x) (z)),
    ω.skew (ω (w) (z)) (x),
    ω.skew (ω (w) (z)) (L.bracket (x) (y)),
    ω.skew (ω (x) (y)) (w),
    ω.skew (ω (x) (y)) (L.bracket (w) (z)),
    ω.skew (ω (x) (z)) (w),
    ω.skew (ω (x) (z)) (L.bracket (w) (y)),
    ω.skew (ω (y) (z)) (w),
    ω.skew (ω (y) (z)) (L.bracket (w) (x)),
    LieAlgebra.bracket_neg_right,
    LieCochain2.neg_right]
  abel

/-- Closed first-order directions always have closed quadratic obstructions. -/
theorem obstruction_isThreeCocycle (ω : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) :
    IsThreeCocycle (adjointLieModule L) (obstructionCochain ω) := by
  rw [isThreeCocycle_iff]
  intro w x y z
  have h := obstruction_bianchi ω w x y z
  simpa only [mixedDifferential3,differential2Cochain_apply,(isTwoCocycle_iff _ _).mp hω,
    LieCochain2.zero_right,sub_zero,add_zero,differential3_apply] using h

/-- The intrinsic obstruction lives in ker d₃ / im d₂, not merely coker d₂. -/
def obstructionClass (ω : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω) :
    H3 (adjointLieModule L) :=
  classOfThree (adjointLieModule L) (obstructionCochain ω) (obstruction_isThreeCocycle ω hω)

/-- The quadratic obstruction scales by the square of the scalar. -/
theorem obstructionCochain_smul (r : R) (ω : Cochain L) :
    obstructionCochain (r • ω) = (r*r) • obstructionCochain ω := by
  apply LieCochain3.ext
  intro x y z
  simp only [obstructionCochain_apply,obstruction,LieCochain2.smul_apply,
    LieCochain2.map_smul_right,LieCochain3.smul_apply,smul_add,smul_smul]

theorem obstructionClass_smul (r : R) (ω : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω)
    (hrω : IsTwoCocycle (adjointLieModule L) (r • ω)) :
    obstructionClass (r • ω) hrω = (r*r) • obstructionClass ω hω := by
  unfold obstructionClass classOfThree
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  exact obstructionCochain_smul r ω

/-- Vanishing of the intrinsic class is equivalent to an actual second-jet
Lie algebra, quantifying over every correction rather than a fixed ansatz. -/
theorem secondExtendable_iff_obstructionClass_zero (ω : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) :
    SecondExtendable ω ↔ obstructionClass ω hω = 0 := by
  rw [obstructionClass,classOfThree_eq_zero_iff]
  constructor
  · rintro ⟨ν,D,hD⟩
    have hν := ((secondAlgebra_exists_iff ω ν).mp ⟨D,hD⟩).2
    refine ⟨-ν,?_⟩
    apply LieCochain3.ext
    intro x y z
    have hn := LinearMap.congr_fun (LinearMap.congr_fun
      (LinearMap.congr_fun ((differential2Linear (adjointLieModule L)).map_neg ν) x) y) z
    change differential2 (adjointLieModule L) (-ν) x y z = obstruction ω x y z
    change differential2 (adjointLieModule L) (-ν) x y z = -differential2 (adjointLieModule L) ν x y z at hn
    rw [hn]
    exact (eq_neg_of_add_eq_zero_right (hν x y z)).symm
  · rintro ⟨ν,hν⟩
    have hc : ∀ x y z, differential2 (adjointLieModule L) (-ν) x y z + obstruction ω x y z = 0 := by
      intro x y z
      have hn := LinearMap.congr_fun (LinearMap.congr_fun
        (LinearMap.congr_fun ((differential2Linear (adjointLieModule L)).map_neg ν) x) y) z
      have hv := congrArg (fun t : LieCochain3 L (adjointLieModule L) => t x y z) hν
      change differential2 (adjointLieModule L) ν x y z = obstruction ω x y z at hv
      change differential2 (adjointLieModule L) (-ν) x y z = -differential2 (adjointLieModule L) ν x y z at hn
      rw [hn,hv,neg_add_cancel]
    exact ⟨-ν,secondAlgebra ω (-ν) hω hc,rfl⟩

/-- Equivalent first-order directions have the same H³ obstruction class. -/
theorem obstructionClass_equivalence {ω η : Cochain L} (E : Equivalence ω η) :
    obstructionClass ω E.source_cocycle = obstructionClass η E.target_cocycle := by
  apply (classOfThree_eq_iff _ _ _ _ _).mpr
  refine ⟨E.secondCorrection 0 0,?_⟩
  apply LieCochain3.ext
  intro x y z
  have h := LinearMap.congr_fun (LinearMap.congr_fun
    (LinearMap.congr_fun (E.secondCorrection_residual 0 0) x) y) z
  have hz := LinearMap.congr_fun (LinearMap.congr_fun
    (LinearMap.congr_fun ((differential2Linear (adjointLieModule L)).map_zero) x) y) z
  change differential2 (adjointLieModule L) (E.secondCorrection 0 0) x y z + obstruction η x y z =
    differential2 (adjointLieModule L) 0 x y z + obstruction ω x y z at h
  change differential2 (adjointLieModule L) 0 x y z = 0 at hz
  rw [hz,zero_add] at h
  exact eq_sub_of_add_eq h

theorem obstructionClass_of_class_eq (ω η : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hη : IsTwoCocycle (adjointLieModule L) η)
    (h : classOf (adjointLieModule L) ω hω = classOf (adjointLieModule L) η hη) :
    obstructionClass ω hω = obstructionClass η hη := by
  obtain ⟨E⟩ := (class_eq_iff_nonempty_equivalence ω η hω hη).mp h
  exact obstructionClass_equivalence E

/-- The obstruction descends to actual H². This is a function, not a claimed
linear map: the Jacobi obstruction is quadratic in the deformation direction. -/
def obstructionMap : H2 (adjointLieModule L) → H3 (adjointLieModule L) :=
  Quotient.lift (fun ω => obstructionClass ω.val ω.property) (by
    intro ω η h
    exact obstructionClass_of_class_eq ω.val η.val ω.property η.property (Quotient.sound h))

@[simp] theorem obstructionMap_classOf (ω : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) :
    obstructionMap (classOf (adjointLieModule L) ω hω) = obstructionClass ω hω := rfl

/-- Vanishing H³ suffices for extension through second order. No claim of
all-orders integrability or convergence follows from this theorem. -/
theorem secondExtendable_of_subsingleton_h3 [Subsingleton (H3 (adjointLieModule L))]
    (ω : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω) : SecondExtendable ω :=
  (secondExtendable_iff_obstructionClass_zero ω hω).mpr (Subsingleton.elim _ _)

namespace ThirdReduction
variable {H : Type*} [AddCommGroup H] [Module R H]
variable (S : LieCohomology.ThirdReduction (adjointLieModule L) H)

/-- The certified H³ primitive gives a concrete correction in the original generators. -/
def correction (ω : Cochain L) : Cochain L := -S.primitive (obstructionCochain ω)

theorem correction_cancels (ω : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω)
    (h : S.project (obstructionCochain ω) = 0) : secondResidual ω (correction S ω) = 0 := by
  have hb := S.normal_form (obstructionCochain ω) (obstruction_isThreeCocycle ω hω)
  rw [h,map_zero,add_zero] at hb
  have hv : differential2 (adjointLieModule L) (S.primitive (obstructionCochain ω)) =
      obstructionTrilinear ω := congrArg Subtype.val hb
  change (differential2Linear (adjointLieModule L)) (-S.primitive (obstructionCochain ω)) +
    obstructionTrilinear ω = 0
  rw [map_neg]
  change -differential2 (adjointLieModule L) (S.primitive (obstructionCochain ω)) + obstructionTrilinear ω = 0
  rw [hv,neg_add_cancel]

def model (ω : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω)
    (h : S.project (obstructionCochain ω) = 0) : LieAlgebra R (V × V × V) :=
  secondAlgebra ω (correction S ω) hω
    ((secondResidual_eq_zero_iff _ _).mp (correction_cancels S ω hω h))

end ThirdReduction

namespace SecondOrderSolver
variable {A B O : Type*} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup O] [Module R O]
variable (T : SecondOrderSolver L A B O)

/-- The existing finite solver decides precisely the zero locus of the true
H³ obstruction on closed directions, even when its target is a larger cokernel. -/
theorem obstructionCoordinates_zero_iff_class (ω : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) :
    T.obstructionCoordinates ω = 0 ↔ obstructionClass ω hω = 0 :=
  (T.extendable_iff ω hω).symm.trans (secondExtendable_iff_obstructionClass_zero ω hω)

end SecondOrderSolver

end LeanPhy.Mathematics.LieDeformation
