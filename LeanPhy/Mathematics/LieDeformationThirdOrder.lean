import LeanPhy.Mathematics.LieDeformationObstruction

/-!
# Third-order Lie deformations

For a specified second-order correction ν, the next Jacobi obstruction is
bilinear in ω and ν. These constructions use ordinary coefficients of ε,
ε² and ε³, without factorials or characteristic restrictions.
-/
namespace LeanPhy.Mathematics.LieDeformation
open LieCohomology
set_option maxSynthPendingDepth 7
set_option maxRecDepth 4096
universe u v
variable {R : Type u} {V : Type v} [CommRing R] [AddCommGroup V] [Module R V]
variable {L : LieAlgebra R V}

/-- The ε³ Jacobi coefficient contributed by the two earlier corrections. -/
def thirdObstruction (ω ν : Cochain L) (x y z : V) : V :=
  ω x (ν y z) + ω y (ν z x) + ω z (ν x y) +
    ν x (ω y z) + ν y (ω z x) + ν z (ω x y)

/-- Polarization makes alternation available over every commutative ring. -/
def thirdObstructionCochain (ω ν : Cochain L) : LieCochain3 L (adjointLieModule L) :=
  obstructionCochain (ω + ν) - obstructionCochain ω - obstructionCochain ν

@[simp] theorem thirdObstructionCochain_apply (ω ν : Cochain L) (x y z : V) :
    thirdObstructionCochain ω ν x y z = thirdObstruction ω ν x y z := by
  simp only [thirdObstructionCochain, LieCochain3.sub_apply, obstructionCochain_apply,
    obstruction, thirdObstruction, LieCochain2.add_apply, LieCochain2.map_add_right]
  abel

theorem thirdObstructionCochain_symm (ω ν : Cochain L) :
    thirdObstructionCochain ω ν = thirdObstructionCochain ν ω := by
  ext x y z
  simp only [thirdObstructionCochain_apply, thirdObstruction]
  abel

/-- The Jacobi expression of an alternating bracket satisfies its own Bianchi
identity, even when that bracket does not satisfy Jacobi. -/
theorem obstruction_self_bianchi (ω : Cochain L) (w x y z : V) :
    mixedDifferential3 ω (obstructionCochain ω) w x y z = 0 := by
  simp only [mixedDifferential3, obstructionCochain_apply, obstruction,
    sub_eq_add_neg, LieCochain2.map_add_right]
  simp only [ω.skew (y) (w),
    ω.skew (z) (w),
    ω.skew (z) (x),
    ω.skew (ω (w) (x)) (y),
    ω.skew (ω (w) (y)) (x),
    ω.skew (ω (w) (z)) (x),
    ω.skew (ω (x) (y)) (w),
    ω.skew (ω (x) (y)) (ω (w) (z)),
    ω.skew (ω (x) (z)) (w),
    ω.skew (ω (x) (z)) (ω (w) (y)),
    ω.skew (ω (y) (z)) (w),
    ω.skew (ω (y) (z)) (ω (w) (x)), LieCochain2.neg_right]
  abel

/-- The polarized Bianchi identity controls closedness at the next order. -/
theorem thirdObstruction_bianchi (ω ν : Cochain L) (w x y z : V) :
    differential3Expr (adjointLieModule L) (thirdObstructionCochain ω ν) w x y z +
      mixedDifferential3 ω (differential2Cochain (adjointLieModule L) ν) w x y z +
      mixedDifferential3 ν (differential2Cochain (adjointLieModule L) ω) w x y z = 0 := by
  simp only [differential3Expr, thirdObstructionCochain_apply, mixedDifferential3,
    differential2Cochain_apply, ← linearJacobi_eq_differential2]
  simp only [adjointLieModule, thirdObstruction, linearJacobi, sub_eq_add_neg,
    LieAlgebra.bracket_add_right, LieCochain2.map_add_right]
  simp only [L.antisymm (y) (w),
    L.antisymm (z) (w),
    L.antisymm (z) (x),
    L.antisymm (ν (w) (x)) (y),
    L.antisymm (ν (w) (y)) (x),
    L.antisymm (ν (w) (z)) (x),
    L.antisymm (ν (x) (y)) (w),
    L.antisymm (ν (x) (z)) (w),
    L.antisymm (ν (y) (z)) (w),
    L.antisymm (ω (w) (x)) (y),
    L.antisymm (ω (w) (x)) (ν (y) (z)),
    L.antisymm (ω (w) (y)) (x),
    L.antisymm (ω (w) (y)) (ν (x) (z)),
    L.antisymm (ω (w) (z)) (x),
    L.antisymm (ω (w) (z)) (ν (x) (y)),
    L.antisymm (ω (x) (y)) (w),
    L.antisymm (ω (x) (y)) (ν (w) (z)),
    L.antisymm (ω (x) (z)) (w),
    L.antisymm (ω (x) (z)) (ν (w) (y)),
    L.antisymm (ω (y) (z)) (w),
    L.antisymm (ω (y) (z)) (ν (w) (x)),
    ν.skew (y) (w),
    ν.skew (z) (w),
    ν.skew (z) (x),
    ν.skew (L.bracket (w) (x)) (y),
    ν.skew (L.bracket (w) (y)) (x),
    ν.skew (L.bracket (w) (z)) (x),
    ν.skew (L.bracket (x) (y)) (w),
    ν.skew (L.bracket (x) (z)) (w),
    ν.skew (L.bracket (y) (z)) (w),
    ν.skew (ω (w) (x)) (y),
    ν.skew (ω (w) (x)) (L.bracket (y) (z)),
    ν.skew (ω (w) (y)) (x),
    ν.skew (ω (w) (y)) (L.bracket (x) (z)),
    ν.skew (ω (w) (z)) (x),
    ν.skew (ω (w) (z)) (L.bracket (x) (y)),
    ν.skew (ω (x) (y)) (w),
    ν.skew (ω (x) (y)) (L.bracket (w) (z)),
    ν.skew (ω (x) (z)) (w),
    ν.skew (ω (x) (z)) (L.bracket (w) (y)),
    ν.skew (ω (y) (z)) (w),
    ν.skew (ω (y) (z)) (L.bracket (w) (x)),
    ω.skew (y) (w),
    ω.skew (z) (w),
    ω.skew (z) (x),
    ω.skew (L.bracket (w) (x)) (y),
    ω.skew (L.bracket (w) (y)) (x),
    ω.skew (L.bracket (w) (z)) (x),
    ω.skew (L.bracket (x) (y)) (w),
    ω.skew (L.bracket (x) (z)) (w),
    ω.skew (L.bracket (y) (z)) (w),
    ω.skew (ν (w) (x)) (y),
    ω.skew (ν (w) (x)) (L.bracket (y) (z)),
    ω.skew (ν (w) (y)) (x),
    ω.skew (ν (w) (y)) (L.bracket (x) (z)),
    ω.skew (ν (w) (z)) (x),
    ω.skew (ν (w) (z)) (L.bracket (x) (y)),
    ω.skew (ν (x) (y)) (w),
    ω.skew (ν (x) (y)) (L.bracket (w) (z)),
    ω.skew (ν (x) (z)) (w),
    ω.skew (ν (x) (z)) (L.bracket (w) (y)),
    ω.skew (ν (y) (z)) (w),
    ω.skew (ν (y) (z)) (L.bracket (w) (x)), LieAlgebra.bracket_neg_right, LieCochain2.neg_right]
  abel

/-- The residual still to be canceled by the third-order correction. -/
def thirdResidual (ω ν ρ : Cochain L) : LieCochain3 L (adjointLieModule L) :=
  differential2Cochain (adjointLieModule L) ρ + thirdObstructionCochain ω ν

@[simp] theorem thirdResidual_apply (ω ν ρ : Cochain L) (x y z : V) :
    thirdResidual ω ν ρ x y z =
      differential2 (adjointLieModule L) ρ x y z + thirdObstruction ω ν x y z := by
  simp only [thirdResidual, LieCochain3.add_apply, differential2Cochain_apply,
    thirdObstructionCochain_apply]

theorem thirdResidual_eq_zero_iff (ω ν ρ : Cochain L) :
    thirdResidual ω ν ρ = 0 ↔ ∀ x y z,
      differential2 (adjointLieModule L) ρ x y z + thirdObstruction ω ν x y z = 0 := by
  constructor
  · intro h x y z
    simpa only [thirdResidual_apply, LieCochain3.zero_apply] using
      congrArg (fun t : LieCochain3 L (adjointLieModule L) => t x y z) h
  · intro h; apply LieCochain3.ext
    intro x y z; simpa only [thirdResidual_apply, LieCochain3.zero_apply] using h x y z

/-- Closedness uses both the first-order and the second-order Jacobi equations. -/
theorem thirdObstruction_isThreeCocycle (ω ν : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hν : secondResidual ω ν = 0) :
    IsThreeCocycle (adjointLieModule L) (thirdObstructionCochain ω ν) := by
  have hdν : differential2Cochain (adjointLieModule L) ν = -obstructionCochain ω := by
    apply LieCochain3.ext
    intro x y z
    exact eq_neg_of_add_eq_zero_left ((secondResidual_eq_zero_iff ω ν).mp hν x y z)
  have hdω : differential2Cochain (adjointLieModule L) ω = 0 :=
    LieCochain3.ext ((isTwoCocycle_iff _ _).mp hω)
  rw [isThreeCocycle_iff]
  intro w x y z
  have h := thirdObstruction_bianchi ω ν w x y z
  rw [hdν, hdω] at h
  have hm : mixedDifferential3 ω (-obstructionCochain ω) w x y z =
      -mixedDifferential3 ω (obstructionCochain ω) w x y z := by
    simp only [mixedDifferential3, LieCochain3.neg_apply, LieCochain2.neg_right]
    abel
  rw [hm, obstruction_self_bianchi] at h
  simpa only [mixedDifferential3, LieCochain3.zero_apply, LieCochain2.zero_right,
    sub_zero, add_zero, neg_zero, differential3_apply] using h


/-- The lower three coefficients and the coefficient of ε³. -/
abbrev ThirdJet (V : Type v) := (V × V × V) × V

/-- Convolution of coefficients, with ε⁴ and higher discarded. The first
component is definitionally the existing second-order bracket. -/
def thirdBracket (ω ν ρ : Cochain L) (x y : ThirdJet V) : ThirdJet V :=
  (secondBracket ω ν x.1 y.1,
   L.bracket x.1.1 y.2 + L.bracket x.1.2.1 y.1.2.2 +
   L.bracket x.1.2.2 y.1.2.1 + L.bracket x.2 y.1.1 +
   ω x.1.1 y.1.2.2 + ω x.1.2.1 y.1.2.1 + ω x.1.2.2 y.1.1 +
   ν x.1.1 y.1.2.1 + ν x.1.2.1 y.1.1 + ρ x.1.1 y.1.1)

@[simp] theorem thirdBracket_truncate (ω ν ρ : Cochain L) (x y : ThirdJet V) :
    (thirdBracket ω ν ρ x y).1 = secondBracket ω ν x.1 y.1 := rfl

/-- Full top-degree Jacobi, including the lower-order residuals on arbitrary jets. -/
theorem thirdJacobi_top (ω ν ρ : Cochain L) (x y z : ThirdJet V) :
    (thirdBracket ω ν ρ x (thirdBracket ω ν ρ y z) +
     thirdBracket ω ν ρ y (thirdBracket ω ν ρ z x) +
     thirdBracket ω ν ρ z (thirdBracket ω ν ρ x y)).2 =
      thirdResidual ω ν ρ x.1.1 y.1.1 z.1.1 +
      secondResidual ω ν x.1.1 y.1.1 z.1.2.1 +
      secondResidual ω ν x.1.1 y.1.2.1 z.1.1 +
      secondResidual ω ν x.1.2.1 y.1.1 z.1.1 +
      differential2 (adjointLieModule L) ω x.1.1 y.1.1 z.1.2.2 +
      differential2 (adjointLieModule L) ω x.1.1 y.1.2.1 z.1.2.1 +
      differential2 (adjointLieModule L) ω x.1.1 y.1.2.2 z.1.1 +
      differential2 (adjointLieModule L) ω x.1.2.1 y.1.1 z.1.2.1 +
      differential2 (adjointLieModule L) ω x.1.2.1 y.1.2.1 z.1.1 +
      differential2 (adjointLieModule L) ω x.1.2.2 y.1.1 z.1.1 := by
  let J (a b c : V) := L.bracket a (L.bracket b c) +
    L.bracket b (L.bracket c a) + L.bracket c (L.bracket a b)
  have hJ (a b c : V) : J a b c = 0 := L.jacobi a b c
  calc
    _ = J x.1.1 y.1.1 z.2 +
      J x.1.1 y.1.2.1 z.1.2.2 +
      J x.1.1 y.1.2.2 z.1.2.1 +
      J x.1.1 y.2 z.1.1 +
      J x.1.2.1 y.1.1 z.1.2.2 +
      J x.1.2.1 y.1.2.1 z.1.2.1 +
      J x.1.2.1 y.1.2.2 z.1.1 +
      J x.1.2.2 y.1.1 z.1.2.1 +
      J x.1.2.2 y.1.2.1 z.1.1 +
      J x.2 y.1.1 z.1.1 +
        linearJacobi ρ x.1.1 y.1.1 z.1.1 +
        thirdObstruction ω ν x.1.1 y.1.1 z.1.1 +
        linearJacobi ν x.1.1 y.1.1 z.1.2.1 +
      linearJacobi ν x.1.1 y.1.2.1 z.1.1 +
      linearJacobi ν x.1.2.1 y.1.1 z.1.1 +
        obstruction ω x.1.1 y.1.1 z.1.2.1 +
      obstruction ω x.1.1 y.1.2.1 z.1.1 +
      obstruction ω x.1.2.1 y.1.1 z.1.1 +
        linearJacobi ω x.1.1 y.1.1 z.1.2.2 +
      linearJacobi ω x.1.1 y.1.2.1 z.1.2.1 +
      linearJacobi ω x.1.1 y.1.2.2 z.1.1 +
      linearJacobi ω x.1.2.1 y.1.1 z.1.2.1 +
      linearJacobi ω x.1.2.1 y.1.2.1 z.1.1 +
      linearJacobi ω x.1.2.2 y.1.1 z.1.1 := by
      simp only [thirdBracket, secondBracket, Prod.snd_add,
        LieAlgebra.bracket_add_right, LieCochain2.map_add_right,
        J, linearJacobi, obstruction, thirdObstruction]
      abel
    _ = _ := by
      simp only [hJ, zero_add, linearJacobi_eq_differential2,
        thirdResidual_apply, secondResidual_apply]
      abel

/-- Testing constant jets extracts exactly the next deformation equation. -/
theorem thirdJacobi_on_constants (ω ν ρ : Cochain L) (x y z : V) :
    (thirdBracket ω ν ρ ((x,0,0),0) (thirdBracket ω ν ρ ((y,0,0),0) ((z,0,0),0)) +
     thirdBracket ω ν ρ ((y,0,0),0) (thirdBracket ω ν ρ ((z,0,0),0) ((x,0,0),0)) +
     thirdBracket ω ν ρ ((z,0,0),0) (thirdBracket ω ν ρ ((x,0,0),0) ((y,0,0),0))).2 =
      thirdResidual ω ν ρ x y z := by
  rw [thirdJacobi_top]
  simp [adjointLieModule, obstruction]

/-- All three deformation equations are necessary and sufficient for Jacobi. -/
theorem thirdJacobi_iff (ω ν ρ : Cochain L) :
    (∀ x y z, thirdBracket ω ν ρ x (thirdBracket ω ν ρ y z) +
      thirdBracket ω ν ρ y (thirdBracket ω ν ρ z x) +
      thirdBracket ω ν ρ z (thirdBracket ω ν ρ x y) = 0) ↔
    IsTwoCocycle (adjointLieModule L) ω ∧ secondResidual ω ν = 0 ∧
      thirdResidual ω ν ρ = 0 := by
  constructor
  · intro h
    have hl := (secondJacobi_iff ω ν).mp (fun x y z =>
      congrArg Prod.fst (h (x,0) (y,0) (z,0)))
    refine ⟨hl.1, (secondResidual_eq_zero_iff _ _).mpr hl.2, ?_⟩
    apply LieCochain3.ext
    intro x y z
    change thirdResidual ω ν ρ x y z = 0
    simpa only [thirdJacobi_on_constants, Prod.snd_zero] using
      congrArg Prod.snd (h ((x,0,0),0) ((y,0,0),0) ((z,0,0),0))
  · rintro ⟨hω,hν,hρ⟩ x y z
    apply Prod.ext
    · exact (secondJacobi_iff ω ν).mpr
        ⟨hω,(secondResidual_eq_zero_iff _ _).mp hν⟩ x.1 y.1 z.1
    · rw [thirdJacobi_top, hρ, hν]
      simp only [LieCochain3.zero_apply, LinearMap.zero_apply,
        (isTwoCocycle_iff _ _).mp hω, add_zero, Prod.snd_zero]

/-- A genuine Lie algebra through ε³, constructed from the checked residuals. -/
def thirdAlgebra (ω ν ρ : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hν : secondResidual ω ν = 0)
    (hρ : thirdResidual ω ν ρ = 0) : LieAlgebra R (ThirdJet V) where
  bracket := thirdBracket ω ν ρ
  add_left := by
    intros; apply Prod.ext
    · exact (secondAlgebra ω ν hω ((secondResidual_eq_zero_iff _ _).mp hν)).add_left _ _ _
    · simp [thirdBracket]; abel
  add_right := by
    intros; apply Prod.ext
    · exact (secondAlgebra ω ν hω ((secondResidual_eq_zero_iff _ _).mp hν)).add_right _ _ _
    · simp [thirdBracket]; abel
  smul_left := by
    intros; apply Prod.ext
    · exact (secondAlgebra ω ν hω ((secondResidual_eq_zero_iff _ _).mp hν)).smul_left _ _ _
    · simp [thirdBracket, smul_add]
  smul_right := by
    intros; apply Prod.ext
    · exact (secondAlgebra ω ν hω ((secondResidual_eq_zero_iff _ _).mp hν)).smul_right _ _ _
    · simp [thirdBracket, smul_add]
  zero_left := by
    intros; apply Prod.ext
    · exact (secondAlgebra ω ν hω ((secondResidual_eq_zero_iff _ _).mp hν)).zero_left _
    · simp [thirdBracket]
  alternating := by
    intro x; apply Prod.ext
    · exact (secondAlgebra ω ν hω ((secondResidual_eq_zero_iff _ _).mp hν)).alternating _
    · simp only [thirdBracket, LieCochain2.alternating, Prod.snd_zero]
      rw [L.antisymm x.2 x.1.1, L.antisymm x.1.2.2 x.1.2.1,
        ω.skew x.1.2.2 x.1.1, ν.skew x.1.2.1 x.1.1]
      abel
  antisymm := by
    intro x y; apply Prod.ext
    · exact (secondAlgebra ω ν hω ((secondResidual_eq_zero_iff _ _).mp hν)).antisymm _ _
    · simp only [thirdBracket, Prod.snd_neg]
      rw [L.antisymm x.1.1 y.2, L.antisymm x.1.2.1 y.1.2.2,
        L.antisymm x.1.2.2 y.1.2.1, L.antisymm x.2 y.1.1,
        ω.skew x.1.1 y.1.2.2, ω.skew x.1.2.1 y.1.2.1, ω.skew x.1.2.2 y.1.1,
        ν.skew x.1.1 y.1.2.1, ν.skew x.1.2.1 y.1.1, ρ.skew x.1.1 y.1.1]
      abel
  jacobi := (thirdJacobi_iff ω ν ρ).mpr ⟨hω,hν,hρ⟩

theorem thirdAlgebra_exists_iff (ω ν ρ : Cochain L) :
    (∃ D : LieAlgebra R (ThirdJet V), D.bracket = thirdBracket ω ν ρ) ↔
    IsTwoCocycle (adjointLieModule L) ω ∧ secondResidual ω ν = 0 ∧
      thirdResidual ω ν ρ = 0 := by
  constructor
  · rintro ⟨D,hD⟩
    apply (thirdJacobi_iff ω ν ρ).mp
    rw [← hD]; exact D.jacobi
  · rintro ⟨hω,hν,hρ⟩; exact ⟨thirdAlgebra ω ν ρ hω hν hρ,rfl⟩

/-- Extension of the specified second-order bracket; ν is part of the input. -/
def ThirdExtendable (ω ν : Cochain L) : Prop :=
  ∃ ρ, ∃ D : LieAlgebra R (ThirdJet V), D.bracket = thirdBracket ω ν ρ

end LeanPhy.Mathematics.LieDeformation
