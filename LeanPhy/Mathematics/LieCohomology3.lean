import LeanPhy.Mathematics.FiniteLieCohomology

/-!
# Degree-three Lie cohomology

Alternating trilinear cochains carry the next Chevalley--Eilenberg differential.
The explicit representation law and Jacobi identity prove d₃ d₂ = 0. The actual
H³ quotient is the kernel of d₃ modulo the image of d₂; it is not the cokernel
of d₂ unless the next differential vanishes.
-/
namespace LeanPhy.Mathematics

set_option maxSynthPendingDepth 7

universe u v w
variable {R : Type u} {V : Type v} {M : Type w}
variable [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup M] [Module R M]

/-- Repeated adjacent arguments vanish. Polarization then supplies all swaps
and the remaining repeated-argument case, over arbitrary commutative rings. -/
def alternatingTrilinear : Submodule R (V →ₗ[R] V →ₗ[R] V →ₗ[R] M) where
  carrier := {t | (∀ x z, t x x z = 0) ∧ ∀ x y, t x y y = 0}
  zero_mem' := by constructor <;> intros <;> rfl
  add_mem' := by
    intro a b ha hb
    constructor
    · intro x z; change a x x z + b x x z = 0; rw [ha.1,hb.1,add_zero]
    · intro x y; change a x y y + b x y y = 0; rw [ha.2,hb.2,add_zero]
  smul_mem' := by
    intro r a ha
    constructor
    · intro x z; change r • a x x z = 0; rw [ha.1,smul_zero]
    · intro x y; change r • a x y y = 0; rw [ha.2,smul_zero]

abbrev LieCochain3 (L : LieAlgebra R V) (_𝒨 : LieModule L M) : Type (max v w) :=
  ↥(alternatingTrilinear : Submodule R (V →ₗ[R] V →ₗ[R] V →ₗ[R] M))

namespace LieCochain3
variable {L : LieAlgebra R V} {𝒨 : LieModule L M}

instance : CoeFun (LieCochain3 L 𝒨) (fun _ => V → V → V → M) :=
  ⟨fun t x y z => t.val x y z⟩

@[ext] theorem ext {t s : LieCochain3 L 𝒨} (h : ∀ x y z, t x y z = s x y z) : t = s := by
  apply Subtype.ext
  apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
  exact h x y z

@[simp] theorem zero_apply (x y z : V) : (0 : LieCochain3 L 𝒨) x y z = 0 := rfl
@[simp] theorem add_apply (t s : LieCochain3 L 𝒨) (x y z : V) :
    (t+s) x y z = t x y z + s x y z := rfl
@[simp] theorem sub_apply (t s : LieCochain3 L 𝒨) (x y z : V) :
    (t-s) x y z = t x y z - s x y z := rfl
@[simp] theorem neg_apply (t : LieCochain3 L 𝒨) (x y z : V) : (-t) x y z = -t x y z := rfl
@[simp] theorem smul_apply (r : R) (t : LieCochain3 L 𝒨) (x y z : V) :
    (r • t) x y z = r • t x y z := rfl

@[simp] theorem add_first (t : LieCochain3 L 𝒨) (a b y z : V) :
    t (a+b) y z = t a y z + t b y z := by change t.val (a+b) y z = _; simp
@[simp] theorem add_middle (t : LieCochain3 L 𝒨) (x a b z : V) :
    t x (a+b) z = t x a z + t x b z := by change t.val x (a+b) z = _; simp
@[simp] theorem add_last (t : LieCochain3 L 𝒨) (x y a b : V) :
    t x y (a+b) = t x y a + t x y b := by change t.val x y (a+b) = _; simp
@[simp] theorem smul_first (t : LieCochain3 L 𝒨) (r : R) (x y z : V) :
    t (r • x) y z = r • t x y z := by change t.val (r • x) y z = _; simp
@[simp] theorem smul_middle (t : LieCochain3 L 𝒨) (r : R) (x y z : V) :
    t x (r • y) z = r • t x y z := by change t.val x (r • y) z = _; simp
@[simp] theorem smul_last (t : LieCochain3 L 𝒨) (r : R) (x y z : V) :
    t x y (r • z) = r • t x y z := by change t.val x y (r • z) = _; simp
@[simp] theorem neg_first (t : LieCochain3 L 𝒨) (x y z : V) :
    t (-x) y z = -t x y z := by change t.val (-x) y z = _; simp
@[simp] theorem neg_middle (t : LieCochain3 L 𝒨) (x y z : V) :
    t x (-y) z = -t x y z := by change t.val x (-y) z = _; simp
@[simp] theorem neg_last (t : LieCochain3 L 𝒨) (x y z : V) :
    t x y (-z) = -t x y z := by change t.val x y (-z) = _; simp

@[simp] theorem zero_first (t : LieCochain3 L 𝒨) (y z : V) : t 0 y z = 0 := by
  change t.val 0 y z = 0; simp
@[simp] theorem zero_middle (t : LieCochain3 L 𝒨) (x z : V) : t x 0 z = 0 := by
  change t.val x 0 z = 0; simp
@[simp] theorem zero_last (t : LieCochain3 L 𝒨) (x y : V) : t x y 0 = 0 := by
  change t.val x y 0 = 0; simp

@[simp] theorem repeat_first (t : LieCochain3 L 𝒨) (x z : V) : t x x z = 0 := t.property.1 x z
@[simp] theorem repeat_last (t : LieCochain3 L 𝒨) (x y : V) : t x y y = 0 := t.property.2 x y

theorem swap_first (t : LieCochain3 L 𝒨) (x y z : V) : t y x z = -t x y z := by
  have h : t (x+y) (x+y) z = 0 := t.property.1 (x+y) z
  rw [add_first,add_middle,add_middle] at h
  simp only [repeat_first,zero_add,add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem swap_last (t : LieCochain3 L 𝒨) (x y z : V) : t x z y = -t x y z := by
  have h : t x (y+z) (y+z) = 0 := t.property.2 x (y+z)
  rw [add_middle,add_last,add_last] at h
  simp only [repeat_last,zero_add,add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

@[simp] theorem repeat_outer (t : LieCochain3 L 𝒨) (x y : V) : t x y x = 0 := by
  rw [swap_last,repeat_first,neg_zero]

end LieCochain3

namespace LieCohomology
variable {L : LieAlgebra R V} (𝒨 : LieModule L M)
set_option maxSynthPendingDepth 6

/-- The previously checked differential now lands in actual three-cochains. -/
def differential2Cochain (ω : LieCochain2 L 𝒨) : LieCochain3 L 𝒨 :=
  ⟨differential2 𝒨 ω, differential2_repeat_first 𝒨 ω, differential2_repeat_last 𝒨 ω⟩

@[simp] theorem differential2Cochain_apply (ω : LieCochain2 L 𝒨) (x y z : V) :
    differential2Cochain 𝒨 ω x y z = differential2 𝒨 ω x y z := rfl

def differential2ToThree : LieCochain2 L 𝒨 →ₗ[R] LieCochain3 L 𝒨 where
  toFun := differential2Cochain 𝒨
  map_add' := by intro a b; apply Subtype.ext; exact (differential2Linear 𝒨).map_add a b
  map_smul' := by intro r a; apply Subtype.ext; exact (differential2Linear 𝒨).map_smul r a

/-- Explicit degree-three CE formula; the bracket pair is placed first. -/
def differential3Expr (t : LieCochain3 L 𝒨) (w x y z : V) : M :=
  𝒨.act w (t x y z) - 𝒨.act x (t w y z) + 𝒨.act y (t w x z) - 𝒨.act z (t w x y) -
    t (L.bracket w x) y z + t (L.bracket w y) x z - t (L.bracket w z) x y -
    t (L.bracket x y) w z + t (L.bracket x z) w y - t (L.bracket y z) w x

/-- The next differential, retaining linearity in all four arguments. -/
def differential3 (t : LieCochain3 L 𝒨) : V →ₗ[R] V →ₗ[R] V →ₗ[R] V →ₗ[R] M where
  toFun w := {
    toFun x := {
      toFun y := {
        toFun z := differential3Expr 𝒨 t w x y z
        map_add' := by intros; simp [differential3Expr]; abel
        map_smul' := by intros; simp [differential3Expr,smul_add,smul_sub] }
      map_add' := by
        intros; apply LinearMap.ext; intro z
        change differential3Expr 𝒨 t _ _ _ _ = _ + _
        simp [differential3Expr]; abel
      map_smul' := by
        intros; apply LinearMap.ext; intro z
        change differential3Expr 𝒨 t _ _ _ _ = (_ : R) • _
        simp [differential3Expr,smul_add,smul_sub] }
    map_add' := by
      intros; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
      change differential3Expr 𝒨 t _ _ _ _ = _ + _
      simp [differential3Expr]; abel
    map_smul' := by
      intros; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
      change differential3Expr 𝒨 t _ _ _ _ = (_ : R) • _
      simp [differential3Expr,smul_add,smul_sub] }
  map_add' := by
    intros; apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
    change differential3Expr 𝒨 t _ _ _ _ = _ + _
    simp [differential3Expr]; abel
  map_smul' := by
    intros; apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
    change differential3Expr 𝒨 t _ _ _ _ = (_ : R) • _
    simp [differential3Expr,smul_add,smul_sub]

@[simp] theorem differential3_apply (t : LieCochain3 L 𝒨) (w x y z : V) :
    differential3 𝒨 t w x y z = differential3Expr 𝒨 t w x y z := rfl

def differential3Linear : LieCochain3 L 𝒨 →ₗ[R] V →ₗ[R] V →ₗ[R] V →ₗ[R] V →ₗ[R] M where
  toFun := differential3 𝒨
  map_add' := by
    intro a b
    apply LinearMap.ext; intro w; apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
    simp [differential3Expr]; abel
  map_smul' := by
    intro r a
    apply LinearMap.ext; intro w; apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
    simp [differential3Expr,smul_add,smul_sub]

theorem differential3_swap_first (t : LieCochain3 L 𝒨) (w x y z : V) :
    differential3 𝒨 t x w y z = -differential3 𝒨 t w x y z := by
  simp only [differential3_apply,differential3Expr,L.antisymm x w,LieCochain3.neg_first,
    LieCochain3.swap_first t w x z,LieCochain3.swap_first t w x y,
    LieCochain3.swap_last t (L.bracket y z) w x]
  simp only [LieModule.act_neg_right]
  abel

theorem differential3_swap_middle (t : LieCochain3 L 𝒨) (w x y z : V) :
    differential3 𝒨 t w y x z = -differential3 𝒨 t w x y z := by
  simp only [differential3_apply,differential3Expr,L.antisymm y x,LieCochain3.neg_first,
    LieCochain3.swap_first t x y z,LieCochain3.swap_last t w x y,
    LieCochain3.swap_last t (L.bracket w z) x y]
  simp only [LieModule.act_neg_right]
  abel

theorem differential3_swap_last (t : LieCochain3 L 𝒨) (w x y z : V) :
    differential3 𝒨 t w x z y = -differential3 𝒨 t w x y z := by
  simp only [differential3_apply,differential3Expr,L.antisymm z y,LieCochain3.neg_first,
    LieCochain3.swap_last t x y z,LieCochain3.swap_last t w y z,
    LieCochain3.swap_last t (L.bracket w x) y z]
  simp only [LieModule.act_neg_right]
  abel

@[simp] theorem differential3_repeat_first (t : LieCochain3 L 𝒨) (x y z : V) :
    differential3 𝒨 t x x y z = 0 := by simp [differential3Expr]
@[simp] theorem differential3_repeat_middle (t : LieCochain3 L 𝒨) (x y z : V) :
    differential3 𝒨 t x y y z = 0 := by simp [differential3Expr]
@[simp] theorem differential3_repeat_last (t : LieCochain3 L 𝒨) (x y z : V) :
    differential3 𝒨 t x y z z = 0 := by simp [differential3Expr]

/-- The next chain identity follows from the representation law and Jacobi. -/
theorem differential3_differential2 (ω : LieCochain2 L 𝒨) :
    differential3 𝒨 (differential2Cochain 𝒨 ω) = 0 := by
  apply LinearMap.ext; intro w; apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
  let J (a b c : V) := L.bracket (L.bracket a b) c -
    L.bracket (L.bracket a c) b + L.bracket (L.bracket b c) a
  have hJ (a b c : V) : J a b c = 0 := by
    calc
      _ = -(L.bracket a (L.bracket b c) + L.bracket b (L.bracket c a) +
        L.bracket c (L.bracket a b)) := by
          dsimp [J]
          rw [L.antisymm (L.bracket a b) c,L.antisymm (L.bracket a c) b,
            L.antisymm (L.bracket b c) a,L.antisymm c a,LieAlgebra.bracket_neg_right]
          abel
      _ = 0 := by rw [L.jacobi,neg_zero]
  change differential3Expr 𝒨 (differential2Cochain 𝒨 ω) w x y z = 0
  calc
    _ = ω (J w x y) z - ω (J w x z) y + ω (J w y z) x - ω (J x y z) w := by
      simp only [differential3Expr,differential2Cochain_apply,differential2_apply,J,
        sub_eq_add_neg,LieModule.act_add_right,LieModule.act_neg_right,LieModule.bracket_act,
        LieCochain2.map_add_left,LieCochain2.neg_left]
      rw [ω.skew (L.bracket y z) (L.bracket w x),
        ω.skew (L.bracket x z) (L.bracket w y),
        ω.skew (L.bracket x y) (L.bracket w z)]
      abel
    _ = 0 := by simp only [hJ,LieCochain2.zero_left,sub_self,add_zero]

def IsThreeCocycle (t : LieCochain3 L 𝒨) : Prop := differential3 𝒨 t = 0

theorem isThreeCocycle_iff (t : LieCochain3 L 𝒨) :
    IsThreeCocycle 𝒨 t ↔ ∀ w x y z, differential3 𝒨 t w x y z = 0 := by
  constructor
  · intro h w x y z; rw [h]; rfl
  · intro h
    apply LinearMap.ext; intro w; apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
    exact h w x y z

def IsThreeCoboundary (t : LieCochain3 L 𝒨) : Prop :=
  ∃ ω : LieCochain2 L 𝒨, differential2Cochain 𝒨 ω = t

theorem three_coboundary_is_cocycle {t : LieCochain3 L 𝒨}
    (ht : IsThreeCoboundary 𝒨 t) : IsThreeCocycle 𝒨 t := by
  rcases ht with ⟨ω,rfl⟩
  exact differential3_differential2 𝒨 ω

def threeCocycles : Submodule R (LieCochain3 L 𝒨) := LinearMap.ker (differential3Linear 𝒨)
def threeCoboundaries : Submodule R (LieCochain3 L 𝒨) := LinearMap.range (differential2ToThree 𝒨)

theorem threeCoboundaries_le_threeCocycles : threeCoboundaries 𝒨 ≤ threeCocycles 𝒨 :=
  fun _ h => three_coboundary_is_cocycle 𝒨 h

def threeBoundariesInCycles : Submodule R (threeCocycles 𝒨) :=
  (threeCoboundaries 𝒨).comap (threeCocycles 𝒨).subtype

/-- The actual degree-three quotient, with closedness enforced in its carrier. -/
abbrev H3 := (threeCocycles 𝒨) ⧸ threeBoundariesInCycles 𝒨

def classOfThree (t : LieCochain3 L 𝒨) (ht : IsThreeCocycle 𝒨 t) : H3 𝒨 :=
  Submodule.Quotient.mk ⟨t,ht⟩

theorem classOfThree_eq_zero_iff (t : LieCochain3 L 𝒨) (ht : IsThreeCocycle 𝒨 t) :
    classOfThree 𝒨 t ht = 0 ↔ IsThreeCoboundary 𝒨 t :=
  Submodule.Quotient.mk_eq_zero (threeBoundariesInCycles 𝒨)

theorem classOfThree_eq_iff (t s : LieCochain3 L 𝒨)
    (ht : IsThreeCocycle 𝒨 t) (hs : IsThreeCocycle 𝒨 s) :
    classOfThree 𝒨 t ht = classOfThree 𝒨 s hs ↔ IsThreeCoboundary 𝒨 (t-s) :=
  Submodule.Quotient.eq (threeBoundariesInCycles 𝒨)

end LieCohomology
end LeanPhy.Mathematics
