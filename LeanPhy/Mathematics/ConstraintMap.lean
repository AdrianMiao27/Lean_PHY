import LeanPhy.Mathematics.ConstraintAlgebra

/-!
# Constraint-preserving Poisson maps

Different descriptions of a constrained system often arise from a change of
coordinates, a lattice/truncation adapter, or an effective-theory map.  This
module records the algebraic part of such a map:

* the observable map is an `AlgebraHom`;
* Poisson brackets commute with the map;
* every declared source constraint maps into the target constraint ideal;
* weak equality therefore transports to the target;
* Dirac observables transport when the target constraint ideal is covered by
  the image of the source constraint ideal.

The covering condition is deliberately explicit.  Without it, mapping source
constraints into target constraints is enough to transport weak equality, but
it is not enough to prove that an arbitrary target constraint has weakly zero
bracket with a mapped observable.  No gauge fixing, quotient regularity,
constraint classification, anomaly cancellation, or physical equivalence is
inferred here.
-/

namespace LeanPhy.Mathematics

universe u v w x y z

namespace FirstClassConstraintAlgebra

variable {R : Type u} {A : Type v} {B : Type w}
variable {ι : Type x} {κ : Type y}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable {C : FirstClassConstraintAlgebra R A ι}
variable {D : FirstClassConstraintAlgebra R B κ}

/-! ## Maps and their algebraic laws -/

/-- A Poisson map that sends each named source constraint into the target
constraint ideal.

At the syntax level an observable in `C` is sent to an observable in `D`.
This is an algebraic adapter; the structure does not assert that either model
is physically adequate or that the map is an equivalence.
-/
structure ConstraintMap
    (C : FirstClassConstraintAlgebra R A ι)
    (D : FirstClassConstraintAlgebra R B κ) where
  map : A →ₐ[R] B
  bracket_compat : ∀ x y,
    D.poisson (map x) (map y) = map (C.poisson x y)
  maps_constraint : ∀ i, map (C.constraint i) ∈ D.constraintIdeal

namespace ConstraintMap

instance : CoeFun (ConstraintMap C D) (fun _ => A → B) :=
  ⟨fun F => F.map⟩

@[simp] theorem map_zero (F : ConstraintMap C D) : F 0 = 0 :=
  F.map.map_zero

@[simp] theorem map_add (F : ConstraintMap C D) (x y : A) :
    F (x + y) = F x + F y :=
  F.map.map_add x y

@[simp] theorem map_sub (F : ConstraintMap C D) (x y : A) :
    F (x - y) = F x - F y :=
  F.map.map_sub x y

@[simp] theorem map_smul (F : ConstraintMap C D) (r : R) (x : A) :
    F (r • x) = r • F x :=
  by simp [Algebra.smul_def]

theorem map_bracket (F : ConstraintMap C D) (x y : A) :
    D.poisson (F x) (F y) = F (C.poisson x y) :=
  F.bracket_compat x y

/-- The generated source constraint ideal maps into the target ideal. -/
theorem map_constraintIdeal (F : ConstraintMap C D) {x : A}
    (hx : x ∈ C.constraintIdeal) : F x ∈ D.constraintIdeal := by
  refine Submodule.span_induction (p := fun x _ => F x ∈ D.constraintIdeal)
    ?_ ?_ ?_ ?_ hx
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    exact F.maps_constraint i
  · simp
  · intro x y _ _ hx hy
    have hmap : F (x + y) = F x + F y := F.map.map_add x y
    rw [hmap]
    exact D.constraintIdeal.add_mem hx hy
  · intro a x _ hx
    have hmap : F (a • x) = F a * F x := by
      simp
    rw [hmap]
    exact D.constraintIdeal.mul_mem_left (F a) hx

@[simp] theorem map_weaklyEqual {x y : A}
    (F : ConstraintMap C D) (h : C.WeaklyEqual x y) :
    D.WeaklyEqual (F x) (F y) := by
  change F x - F y ∈ D.constraintIdeal
  have hmap : F (x - y) = F x - F y := F.map.map_sub x y
  rw [← hmap]
  exact map_constraintIdeal F h

/-! ## Identity and composition -/

/-- The identity constraint map. -/
def id (C : FirstClassConstraintAlgebra R A ι) : ConstraintMap C C where
  map := AlgHom.id R A
  bracket_compat := by intro x y; rfl
  maps_constraint := by intro i; exact C.constraint_mem i

@[simp] theorem id_apply (C : FirstClassConstraintAlgebra R A ι) (x : A) :
    id C x = x := rfl

/-- Composition of two constraint-preserving Poisson maps. -/
def comp {E : Type z} {ι₂ : Type*} [CommRing E] [Algebra R E]
    {F : FirstClassConstraintAlgebra R E ι₂}
    (after : ConstraintMap D F) (before : ConstraintMap C D) :
    ConstraintMap C F where
  map := after.map.comp before.map
  bracket_compat := by
    intro x y
    change F.poisson (after (before x)) (after (before y)) =
      after (before (C.poisson x y))
    rw [map_bracket after, map_bracket before]
  maps_constraint := by
    intro i
    exact map_constraintIdeal after (before.maps_constraint i)

@[simp] theorem comp_apply {E : Type z} {ι₂ : Type*} [CommRing E]
    [Algebra R E] {F : FirstClassConstraintAlgebra R E ι₂}
    (after : ConstraintMap D F) (before : ConstraintMap C D) (x : A) :
    comp after before x = after (before x) := rfl

theorem comp_id_left (F : ConstraintMap C D) :
    comp (id D) F = F := by
  cases F
  rfl

theorem comp_id_right (F : ConstraintMap C D) :
    comp F (id C) = F := by
  cases F
  rfl

/-! ## Quotient-facing consequences -/

/-- The extra condition needed to transport a Dirac observable in the forward
direction.  It says that every target constraint-ideal element has a source
preimage that is itself in the source constraint ideal. -/
def CoversConstraintIdeal (F : ConstraintMap C D) : Prop :=
  ∀ ⦃c : B⦄, c ∈ D.constraintIdeal →
    ∃ x : A, x ∈ C.constraintIdeal ∧ F x = c

/-- A map that covers the target constraint ideal transports Dirac
observables.  The cover is a theorem parameter rather than an inferred
surjectivity or physical equivalence claim. -/
theorem map_diracObservable (F : ConstraintMap C D)
    (hcover : CoversConstraintIdeal F)
    {f : A} (hf : C.IsDiracObservable f) :
    D.IsDiracObservable (F f) := by
  intro c hc
  rcases hcover hc with ⟨x, hx, rfl⟩
  rw [map_bracket F]
  exact map_constraintIdeal F (hf hx)

end ConstraintMap

end FirstClassConstraintAlgebra

end LeanPhy.Mathematics
