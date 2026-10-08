import LeanPhy.Mathematics.LieDeformationReduction
import LeanPhy.Mathematics.FiniteLieCohomology

/-!
# Certified second-order deformation solvers

The quadratic Jacobi term is an alternating trilinear map. Finite coordinate
solvers can therefore test its membership in the image of the adjoint CE
differential. A vanishing projected obstruction supplies an actual correction;
a nonvanishing one rules out every correction. The target is a cokernel test,
not an asserted computation of H³ or an all-orders integrability result.
-/

namespace LeanPhy.Mathematics.LieDeformation

open LieCohomology
set_option maxSynthPendingDepth 5

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable {L : LieAlgebra R V}

/-- The quadratic term, bundled with linearity in all three arguments. -/
def obstructionTrilinear (ω : Cochain L) : V →ₗ[R] V →ₗ[R] V →ₗ[R] V where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => obstruction ω x y z
          map_add' := by
            intros
            simp only [obstruction, LieCochain2.map_add_left, LieCochain2.map_add_right]
            abel
          map_smul' := by intros; simp [obstruction, smul_add] }
      map_add' := by
        intros
        apply LinearMap.ext
        intro z
        change obstruction ω x _ z = obstruction ω x _ z + obstruction ω x _ z
        simp only [obstruction, LieCochain2.map_add_left, LieCochain2.map_add_right]
        abel
      map_smul' := by
        intros
        apply LinearMap.ext
        intro z
        simp [obstruction, smul_add] }
  map_add' := by
    intros
    apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
    change obstruction ω _ y z = obstruction ω _ y z + obstruction ω _ y z
    simp only [obstruction, LieCochain2.map_add_left, LieCochain2.map_add_right]
    abel
  map_smul' := by
    intros
    apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
    simp [obstruction, smul_add]

@[simp] theorem obstructionTrilinear_apply (ω : Cochain L) (x y z : V) :
    obstructionTrilinear ω x y z = obstruction ω x y z := rfl

theorem obstruction_swap_first (ω : Cochain L) (x y z : V) :
    obstruction ω y x z = -obstruction ω x y z := by
  simp only [obstruction]
  rw [ω.skew x z, ω.skew z y, ω.skew y x]
  simp only [LieCochain2.neg_right]
  abel

theorem obstruction_swap_last (ω : Cochain L) (x y z : V) :
    obstruction ω x z y = -obstruction ω x y z := by
  simp only [obstruction]
  rw [ω.skew z y, ω.skew y x, ω.skew x z]
  simp only [LieCochain2.neg_right]
  abel

@[simp] theorem obstruction_repeat_first (ω : Cochain L) (x z : V) :
    obstruction ω x x z = 0 := by
  simp only [obstruction, LieCochain2.alternating, LieCochain2.zero_right, add_zero]
  rw [ω.skew z x, LieCochain2.neg_right, add_neg_cancel]

@[simp] theorem obstruction_repeat_last (ω : Cochain L) (x y : V) :
    obstruction ω x y y = 0 := by
  simp only [obstruction, LieCochain2.alternating, LieCochain2.zero_right, zero_add]
  rw [ω.skew y x, LieCochain2.neg_right, neg_add_cancel]

@[simp] theorem obstruction_repeat_outer (ω : Cochain L) (x y : V) :
    obstruction ω x y x = 0 := by
  rw [obstruction_swap_last, obstruction_repeat_first, neg_zero]

/-- The complete second-order Jacobi residual on constant jets. -/
def secondResidual (ω ν : Cochain L) : V →ₗ[R] V →ₗ[R] V →ₗ[R] V :=
  differential2 (adjointLieModule L) ν + obstructionTrilinear ω

@[simp] theorem secondResidual_apply (ω ν : Cochain L) (x y z : V) :
    secondResidual ω ν x y z =
      differential2 (adjointLieModule L) ν x y z + obstruction ω x y z := rfl

theorem secondResidual_eq_zero_iff (ω ν : Cochain L) :
    secondResidual ω ν = 0 ↔
      ∀ x y z, differential2 (adjointLieModule L) ν x y z + obstruction ω x y z = 0 := by
  constructor
  · intro h x y z
    exact congrArg (fun t : V →ₗ[R] V →ₗ[R] V →ₗ[R] V => t x y z) h
  · intro h
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
    exact h x y z

theorem secondResidual_swap_first (ω ν : Cochain L) (x y z : V) :
    secondResidual ω ν y x z = -secondResidual ω ν x y z := by
  simp only [secondResidual_apply]
  rw [differential2_swap_first, obstruction_swap_first]
  abel

theorem secondResidual_swap_last (ω ν : Cochain L) (x y z : V) :
    secondResidual ω ν x z y = -secondResidual ω ν x y z := by
  simp only [secondResidual_apply]
  rw [differential2_swap_last, obstruction_swap_last]
  abel

/-- Samples on increasing basis triples detect the full residual, including
zero-dimensional spaces and spaces with no increasing triples. -/
theorem secondResidual_eq_zero_of_increasing {n : Nat}
    {L : LieAlgebra R (Fin n → R)} (ω ν : Cochain L)
    (h : ∀ i j k : Fin n, i < j → j < k →
      secondResidual ω ν (LieCochainCoordinates.e i) (LieCochainCoordinates.e j)
        (LieCochainCoordinates.e k) = 0) : secondResidual ω ν = 0 := by
  open LieCochainCoordinates in
  have ordered (i j k : Fin n) (hij : i < j) :
      secondResidual ω ν (e i) (e j) (e k) = 0 := by
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · exact h i j k hij hjk
    · simp only [secondResidual_apply, differential2_repeat_last, obstruction_repeat_last, add_zero]
    · rcases lt_trichotomy i k with hik | rfl | hki
      · rw [secondResidual_swap_last ω ν (e i) (e k) (e j), h i k j hik hkj, neg_zero]
      · simp only [secondResidual_apply, differential2_repeat_outer, obstruction_repeat_outer, add_zero]
      · rw [secondResidual_swap_last ω ν (e i) (e k) (e j),
          secondResidual_swap_first ω ν (e k) (e i) (e j), h k i j hki hij, neg_zero, neg_zero]
  apply LieCochainCoordinates.trilinear_eq_zero_of_basis
  intro i j k
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact ordered i j k hij
  · simp only [secondResidual_apply, differential2_repeat_first, obstruction_repeat_first, add_zero]
  · rw [secondResidual_swap_first, ordered j i k hji, neg_zero]

variable (L) (A B H : Type*) [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup H] [Module R H]

/-- A complete image test for d₂, connected to actual adjoint cochains.
The two image identities follow from a certified reduction of `d₂ → 0`.
No closedness assumption on the supplied direction is hidden in this record. -/
structure SecondOrderSolver where
  coordinates : Cochain L ≃ₗ[R] A
  readThird : (V →ₗ[R] V →ₗ[R] V →ₗ[R] V) →ₗ[R] B
  differential : A →ₗ[R] B
  project : B →ₗ[R] H
  lift : B →ₗ[R] A
  boundary : ∀ a, project (differential a) = 0
  solve : ∀ b, project b = 0 → differential (lift b) = b
  bridge : ∀ ν, differential (coordinates ν) = readThird (differential2 (adjointLieModule L) ν)
  detect : ∀ (ω ν : Cochain L), readThird (secondResidual ω ν) = 0 → secondResidual ω ν = 0

namespace SecondOrderSolver
variable {L A B H} (S : SecondOrderSolver L A B H)

/-- Coordinates of the quadratic term modulo the entire image of d₂. -/
def obstructionCoordinates (ω : Cochain L) : H :=
  S.project (S.readThird (obstructionTrilinear ω))

/-- The sign is fixed by the equation d₂ν + Q(ω) = 0. -/
noncomputable def correction (ω : Cochain L) : Cochain L :=
  S.coordinates.symm (S.lift (-S.readThird (obstructionTrilinear ω)))

theorem correction_cancels (ω : Cochain L) (h : S.obstructionCoordinates ω = 0) :
    secondResidual ω (S.correction ω) = 0 := by
  apply S.detect
  rw [secondResidual, map_add, ← S.bridge]
  simp only [correction, LinearEquiv.apply_symm_apply]
  rw [S.solve _ (by simpa [obstructionCoordinates] using h), neg_add_cancel]

/-- All possible corrections are covered, not only the computed ansatz. -/
theorem correction_exists_iff (ω : Cochain L) :
    (∃ ν : Cochain L, secondResidual ω ν = 0) ↔ S.obstructionCoordinates ω = 0 := by
  constructor
  · rintro ⟨ν,hν⟩
    have h := congrArg (fun t => S.project (S.readThird t)) hν
    simpa only [obstructionCoordinates, secondResidual, map_add, ← S.bridge, S.boundary, zero_add, map_zero]
      using h
  · intro h; exact ⟨S.correction ω, S.correction_cancels ω h⟩

/-- The computed correction constructs the actual Lie algebra on second jets. -/
noncomputable def model (ω : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω)
    (h : S.obstructionCoordinates ω = 0) : LieAlgebra R (V × V × V) :=
  secondAlgebra ω (S.correction ω) hω
    ((secondResidual_eq_zero_iff _ _).mp (S.correction_cancels ω h))

/-- Existence of any second-order Lie model is exactly closedness plus the
computed obstruction equations. -/
theorem model_exists_iff (ω : Cochain L) :
    (∃ ν : Cochain L, ∃ D : LieAlgebra R (V × V × V), D.bracket = secondBracket ω ν) ↔
      IsTwoCocycle (adjointLieModule L) ω ∧ S.obstructionCoordinates ω = 0 := by
  constructor
  · rintro ⟨ν,D,hD⟩
    obtain ⟨hω,hν⟩ := (secondAlgebra_exists_iff ω ν).mp ⟨D,hD⟩
    exact ⟨hω,(S.correction_exists_iff ω).mp ⟨ν,(secondResidual_eq_zero_iff _ _).mpr hν⟩⟩
  · rintro ⟨hω,h⟩; exact ⟨S.correction ω,S.model ω hω h,rfl⟩

/-- Once a correction exists, all others differ from it by an adjoint cocycle. -/
theorem all_corrections_iff (ω ν : Cochain L) (h : S.obstructionCoordinates ω = 0) :
    secondResidual ω ν = 0 ↔ IsTwoCocycle (adjointLieModule L) (ν - S.correction ω) := by
  have hc := S.correction_cancels ω h
  change differential2Linear (adjointLieModule L) ν + obstructionTrilinear ω = 0 ↔ _
  change differential2Linear (adjointLieModule L) (S.correction ω) + obstructionTrilinear ω = 0 at hc
  change _ ↔ differential2Linear (adjointLieModule L) (ν - S.correction ω) = 0
  rw [map_sub, sub_eq_zero]
  exact ⟨fun hν => add_right_cancel (hν.trans hc.symm), fun hν => hν ▸ hc⟩

end SecondOrderSolver
end LeanPhy.Mathematics.LieDeformation
