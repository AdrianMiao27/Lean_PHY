import LeanPhy.Mathematics.LieCohomology2

/-!
# Central extensions from explicit Lie two-cocycles

For a trivial coefficient action, a two-cocycle `ω` constructs the bracket
`[(x,a),(y,b)] = ([x,y], ω(x,y))`. Its Jacobi identity follows from the proved
cocycle condition. The inclusion of the coefficient module is central and is
exactly the kernel of the surjective projection to the original algebra.

A supplied coboundary witness gives a linear shear preserving the brackets,
projection and central inclusion. No Lie-group integration, topology,
classification of all extensions, or physical anomaly interpretation is assumed.
-/

namespace LeanPhy.Mathematics

universe u v w

variable {R : Type u} {V : Type v} {M : Type w}
variable [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup M] [Module R M]

/-- The coefficient module with zero Lie action, used for central extensions. -/
def trivialLieModule (L : LieAlgebra R V) : LieModule L M where
  act := fun _ _ => 0
  act_add_left' := by intros; simp
  act_smul_left' := by intros; simp
  act_add_right' := by intros; simp
  act_smul_right' := by intros; simp
  bracket_act' := by intros; simp

@[simp] theorem trivialLieModule_act (L : LieAlgebra R V) (x : V) (m : M) :
    (trivialLieModule L).act x m = 0 := rfl

namespace LieCochain2

variable {L : LieAlgebra R V} {𝒨 : LieModule L M}

@[simp] theorem neg_left (ω : LieCochain2 L 𝒨) (x y : V) : ω (-x) y = -ω x y := by
  simpa using ω.map_smul_left (-1 : R) x y

@[simp] theorem neg_right (ω : LieCochain2 L 𝒨) (x y : V) : ω x (-y) = -ω x y := by
  simpa using ω.map_smul_right x (-1 : R) y

end LieCochain2

namespace LieCohomology

variable {L : LieAlgebra R V}

@[simp] theorem differential1_trivial (φ : V →ₗ[R] M) (x y : V) :
    differential1 (trivialLieModule L) φ x y = -φ (L.bracket x y) := by
  simp [differential1]

/-- The central-extension Jacobi equation, with the sign convention made explicit. -/
theorem twoCocycle_trivial_iff (ω : LieCochain2 L (trivialLieModule L : LieModule L M)) :
    IsTwoCocycle (trivialLieModule L) ω ↔
      ∀ x y z, ω x (L.bracket y z) + ω y (L.bracket z x) + ω z (L.bracket x y) = 0 := by
  rw [isTwoCocycle_iff]
  have heq (x y z : V) : differential2 (trivialLieModule L) ω x y z =
      ω x (L.bracket y z) + ω y (L.bracket z x) + ω z (L.bracket x y) := by
    rw [differential2_apply]
    simp only [trivialLieModule_act, sub_self, zero_add, zero_sub]
    rw [ω.skew x (L.bracket y z), ω.skew y (L.bracket z x),
      ω.skew z (L.bracket x y), L.antisymm z x, LieCochain2.neg_left]
    abel
  simp only [heq]

end LieCohomology

namespace CentralExtension

open LieCohomology

variable {L : LieAlgebra R V}

/-- The underlying central bracket; Jacobi is not asserted without a cocycle proof. -/
def bracket (ω : LieCochain2 L (trivialLieModule L : LieModule L M))
    (x y : V × M) : V × M := (L.bracket x.1 y.1, ω x.1 y.1)

/-- A cocycle constructs an actual Lie algebra, rather than assuming its Jacobi identity. -/
def algebra (ω : LieCochain2 L (trivialLieModule L : LieModule L M))
    (hω : IsTwoCocycle (trivialLieModule L) ω) : LieAlgebra R (V × M) where
  bracket := bracket ω
  add_left x y z := Prod.ext (L.add_left x.1 y.1 z.1) (ω.map_add_left x.1 y.1 z.1)
  add_right x y z := Prod.ext (L.add_right x.1 y.1 z.1) (ω.map_add_right x.1 y.1 z.1)
  smul_left r x y := Prod.ext (L.smul_left r x.1 y.1) (ω.map_smul_left r x.1 y.1)
  smul_right r x y := Prod.ext (L.smul_right r x.1 y.1) (ω.map_smul_right x.1 r y.1)
  zero_left x := Prod.ext (L.bracket_zero_left x.1) (ω.zero_left x.1)
  alternating x := Prod.ext (L.alternating x.1) (ω.alternating x.1)
  antisymm x y := Prod.ext (L.antisymm x.1 y.1) (ω.skew x.1 y.1)
  jacobi x y z := Prod.ext (L.jacobi x.1 y.1 z.1)
    ((twoCocycle_trivial_iff ω).mp hω x.1 y.1 z.1)

def inclusion : M →ₗ[R] V × M := LinearMap.inr R V M

def projection : V × M →ₗ[R] V := LinearMap.fst R V M

theorem inclusion_injective : Function.Injective (inclusion (R := R) (V := V) (M := M)) := by
  intro x y h
  exact congrArg Prod.snd h

theorem projection_surjective : Function.Surjective (projection (R := R) (V := V) (M := M)) :=
  fun x => ⟨(x, 0), rfl⟩

/-- Exactness of the central inclusion and the base projection. -/
theorem projection_eq_zero_iff (x : V × M) :
    projection (R := R) x = 0 ↔ ∃ m, inclusion (R := R) m = x := by
  constructor
  · intro h; exact ⟨x.2, Prod.ext h.symm rfl⟩
  · rintro ⟨m, rfl⟩; rfl

theorem inclusion_central (ω : LieCochain2 L (trivialLieModule L : LieModule L M))
    (m : M) (x : V × M) : bracket ω (inclusion (R := R) m) x = 0 := by
  exact Prod.ext (L.bracket_zero_left x.1) (ω.zero_left x.1)

theorem projection_bracket (ω : LieCochain2 L (trivialLieModule L : LieModule L M))
    (x y : V × M) : projection (R := R) (bracket ω x y) =
      L.bracket (projection (R := R) x) (projection (R := R) y) := rfl

/-- Change of linear section, preserving the base coordinate. -/
def shear (φ : V →ₗ[R] M) : (V × M) ≃ₗ[R] (V × M) where
  toFun x := (x.1, x.2 + φ x.1)
  invFun x := (x.1, x.2 - φ x.1)
  left_inv := by intro x; refine Prod.ext ?_ ?_; rfl; dsimp; abel
  right_inv := by intro x; refine Prod.ext ?_ ?_; rfl; dsimp; abel
  map_add' := by intro x y; refine Prod.ext ?_ ?_; rfl; simp; abel
  map_smul' := by intro r x; refine Prod.ext ?_ ?_; rfl; simp [smul_add]

/-- An extension equivalence preserves its Lie bracket, base and central inclusion. -/
structure Equivalence
    (ω η : LieCochain2 L (trivialLieModule L : LieModule L M)) where
  source_cocycle : IsTwoCocycle (trivialLieModule L) ω
  target_cocycle : IsTwoCocycle (trivialLieModule L) η
  linearEquiv : (V × M) ≃ₗ[R] (V × M)
  map_bracket : ∀ x y, linearEquiv (bracket ω x y) =
    bracket η (linearEquiv x) (linearEquiv y)
  map_projection : ∀ x, projection (R := R) (linearEquiv x) = projection (R := R) x
  map_inclusion : ∀ m, linearEquiv (inclusion (R := R) m) = inclusion (R := R) m

/-- An explicit coboundary produces an extension equivalence, with no choice of witness hidden. -/
def equivalenceOfCoboundary
    (ω η : LieCochain2 L (trivialLieModule L : LieModule L M))
    (φ : V →ₗ[R] M) (hφ : differential1 (trivialLieModule L) φ = ω - η)
    (hω : IsTwoCocycle (trivialLieModule L) ω) :
    Equivalence ω η where
  source_cocycle := hω
  target_cocycle := cocycle_of_cohomologous _ hω ⟨φ, hφ⟩
  linearEquiv := shear φ
  map_bracket := by
    intro x y
    refine Prod.ext ?_ ?_
    · rfl
    change ω x.1 y.1 + φ (L.bracket x.1 y.1) = η x.1 y.1
    have h := congrArg (fun a : LieCochain2 L (trivialLieModule L) => a x.1 y.1) hφ
    simp only [differential1_trivial, LieCochain2.sub_apply] at h
    calc
      _ = (ω x.1 y.1 - η x.1 y.1) + φ (L.bracket x.1 y.1) + η x.1 y.1 := by abel
      _ = η x.1 y.1 := by rw [← h]; abel
  map_projection := by intro x; rfl
  map_inclusion := by intro m; change (0, m + φ 0) = (0, m); simp

/-- Equality in `H²` yields an equivalence of these split-carrier central extensions. -/
theorem nonempty_equivalence_of_class_eq
    (ω η : LieCochain2 L (trivialLieModule L : LieModule L M))
    (hω : IsTwoCocycle (trivialLieModule L) ω) (hη : IsTwoCocycle (trivialLieModule L) η)
    (h : classOf (trivialLieModule L) ω hω = classOf (trivialLieModule L) η hη) :
    Nonempty (Equivalence ω η) := by
  rcases (classOf_eq_iff _ ω η hω hη).mp h with ⟨φ, hφ⟩
  exact ⟨equivalenceOfCoboundary ω η φ hφ hω⟩

namespace Equivalence

variable {ω η : LieCochain2 L (trivialLieModule L : LieModule L M)}

/-- Recover the change of section from a base- and center-preserving equivalence. -/
def sectionCochain (E : Equivalence ω η) : V →ₗ[R] M :=
  (LinearMap.snd R V M).comp (E.linearEquiv.toLinearMap.comp (LinearMap.inl R V M))

theorem snd_apply (E : Equivalence ω η) (x : V × M) :
    (E.linearEquiv x).2 = x.2 + E.sectionCochain x.1 := by
  have hx : x = (x.1, 0) + inclusion (R := R) x.2 := by
    apply Prod.ext <;> simp [inclusion]
  conv_lhs => rw [hx, map_add, E.map_inclusion]
  change (E.linearEquiv (x.1, 0)).2 + x.2 = x.2 + (E.linearEquiv (x.1, 0)).2
  exact add_comm _ _

theorem coboundary_section (E : Equivalence ω η) :
    differential1 (trivialLieModule L) E.sectionCochain = ω - η := by
  ext x y
  simp only [differential1_trivial, LieCochain2.sub_apply]
  have h := congrArg Prod.snd (E.map_bracket (x, 0) (y, 0))
  rw [E.snd_apply] at h
  change ω x y + E.sectionCochain (L.bracket x y) =
    η (projection (R := R) (E.linearEquiv (x, 0)))
      (projection (R := R) (E.linearEquiv (y, 0))) at h
  rw [E.map_projection, E.map_projection] at h
  change ω x y + E.sectionCochain (L.bracket x y) = η x y at h
  rw [← h]
  abel

end Equivalence

/-- For these split-carrier models, equal cohomology classes are exactly
equivalent central extensions with the base and center fixed. -/
theorem class_eq_iff_nonempty_equivalence
    (ω η : LieCochain2 L (trivialLieModule L : LieModule L M))
    (hω : IsTwoCocycle (trivialLieModule L) ω) (hη : IsTwoCocycle (trivialLieModule L) η) :
    classOf (trivialLieModule L) ω hω = classOf (trivialLieModule L) η hη ↔
      Nonempty (Equivalence ω η) := by
  constructor
  · exact nonempty_equivalence_of_class_eq ω η hω hη
  · rintro ⟨E⟩
    exact (classOf_eq_iff _ ω η hω hη).mpr ⟨E.sectionCochain, E.coboundary_section⟩

end CentralExtension

end LeanPhy.Mathematics
