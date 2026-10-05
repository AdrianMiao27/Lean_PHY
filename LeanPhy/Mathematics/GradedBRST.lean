import LeanPhy.Mathematics.BRST

/-!
# A graded BRST algebraic interface

Gauge-theory calculations use an odd differential and a Koszul sign in the
Leibniz rule.  The ungraded `BRST` layer is useful for constraint algebras, but
it cannot express the sign carried by ghosts.  This module adds the smallest
reusable graded interface:

* `Parity` records the even/odd part of a grading;
* `GradedRing` records homogeneous subspaces, their product grading, and the
  degree shift of the differential;
* `GradedDerivation` requires additivity, grade shifting, and the signed
  Leibniz law on homogeneous inputs;
* `GradedBRSTDifferential` adds an explicit square-zero proof and derives the
  closed/exact/cohomologous API.

The homogeneous-subspace laws are inputs.  In particular, this file does not
construct a ghost algebra, a decomposition of arbitrary elements, a BV
antibracket, a gauge-fixing fermion, a path-integral measure, or an anomaly
theorem.  A concrete model must provide those structures and its sign
conventions explicitly.
-/

namespace LeanPhy.Mathematics

universe u v

/-! ## Parity and homogeneous algebra -/

/-- The two parity classes used by the Koszul sign. -/
inductive Parity where
  | even
  | odd
deriving DecidableEq, Repr

namespace Parity

/-- Addition of parities, written as xor. -/
def add : Parity → Parity → Parity
  | .even, q => q
  | .odd, .even => .odd
  | .odd, .odd => .even

instance : Zero Parity := ⟨.even⟩

instance : Add Parity := ⟨Parity.add⟩

instance : AddMonoid Parity where
  nsmul := nsmulRec
  zero_add := by intro p; cases p <;> rfl
  add_zero := by intro p; cases p <;> rfl
  add_assoc := by intro p q r; cases p <;> cases q <;> cases r <;> rfl

@[simp] theorem add_even_left (p : Parity) : add .even p = p := by
  cases p <;> rfl

@[simp] theorem add_even_right (p : Parity) : add p .even = p := by
  cases p <;> rfl

@[simp] theorem add_odd_left (p : Parity) : add .odd p =
    match p with
    | .even => .odd
    | .odd => .even := by
  cases p <;> rfl

@[simp] theorem add_odd_right (p : Parity) : add p .odd =
    match p with
    | .even => .odd
    | .odd => .even := by
  cases p <;> rfl

/-- The sign contributed by moving an odd differential past a homogeneous
factor.  It is deliberately defined in the target ring, so no scalar-field
choice is hidden in the API. -/
def sign {A : Type u} [Ring A] : Parity → A → A
  | .even, x => x
  | .odd, x => -x

@[simp] theorem sign_even {A : Type u} [Ring A] (x : A) :
    sign .even x = x := rfl

@[simp] theorem sign_odd {A : Type u} [Ring A] (x : A) :
    sign .odd x = -x := rfl

@[simp] theorem sign_zero {A : Type u} [Ring A] (p : Parity) :
    sign p (0 : A) = 0 := by
  cases p <;> simp [sign]

end Parity

variable {G : Type u} {A : Type v} [AddMonoid G] [Ring A]

/-- A ring equipped with explicitly declared homogeneous pieces.

The structure does not require every element to be homogeneous or provide a
direct-sum decomposition.  That omission is intentional: finite ghost
polynomials, quotient algebras, and completed spaces can supply different
decomposition theorems while sharing the same derivation API.
-/
structure GradedRing (G : Type u) (A : Type v) [AddMonoid G] [Ring A] where
  homogeneous : G → Set A
  zero_mem : ∀ g, 0 ∈ homogeneous g
  add_mem : ∀ g {x y : A}, x ∈ homogeneous g → y ∈ homogeneous g →
    x + y ∈ homogeneous g
  neg_mem : ∀ g {x : A}, x ∈ homogeneous g → -x ∈ homogeneous g
  one_mem : 1 ∈ homogeneous 0
  mul_mem : ∀ {g h : G} {x y : A}, x ∈ homogeneous g → y ∈ homogeneous h →
    x * y ∈ homogeneous (g + h)
  parity : G → Parity
  parity_add : ∀ g h, parity (g + h) = Parity.add (parity g) (parity h)
  differential_degree : G
  differential_is_odd : parity differential_degree = Parity.odd

namespace GradedRing

variable (𝒜 : GradedRing G A)

/-- Membership in a declared homogeneous piece. -/
def IsHomogeneous (g : G) (x : A) : Prop := x ∈ 𝒜.homogeneous g

@[simp] theorem zero_homogeneous (g : G) : 𝒜.IsHomogeneous g 0 :=
  𝒜.zero_mem g

theorem add_homogeneous {g : G} {x y : A}
    (hx : 𝒜.IsHomogeneous g x) (hy : 𝒜.IsHomogeneous g y) :
    𝒜.IsHomogeneous g (x + y) :=
  𝒜.add_mem g hx hy

theorem neg_homogeneous {g : G} {x : A}
    (hx : 𝒜.IsHomogeneous g x) : 𝒜.IsHomogeneous g (-x) :=
  𝒜.neg_mem g hx

@[simp] theorem one_homogeneous : 𝒜.IsHomogeneous 0 1 := 𝒜.one_mem

theorem mul_homogeneous {g h : G} {x y : A}
    (hx : 𝒜.IsHomogeneous g x) (hy : 𝒜.IsHomogeneous h y) :
    𝒜.IsHomogeneous (g + h) (x * y) :=
  𝒜.mul_mem hx hy

/-- A convenience parity grading in which every element is homogeneous.  It is
useful for generic regression tests and adapters that have not yet supplied a
physical ghost decomposition. -/
def parityTrivial (A : Type v) [Ring A] : GradedRing (ZMod 2) A where
  homogeneous := fun _ => Set.univ
  zero_mem := by intro g; simp
  add_mem := by intro g x y _ _; simp
  neg_mem := by intro g x _; simp
  one_mem := by simp
  mul_mem := by intro g h x y _ _; simp
  parity := fun g => if g = 0 then Parity.even else Parity.odd
  parity_add := by
    intro g h
    fin_cases g <;> fin_cases h <;> rfl
  differential_degree := 1
  differential_is_odd := by rfl

end GradedRing

/-! ## Graded derivations -/

/-- A derivation of declared degree `𝒜.differential_degree`.

The signed Leibniz law is required only for homogeneous inputs.  This avoids
pretending that an arbitrary element has a canonical grade when the concrete
model has not supplied a decomposition theorem.
-/
structure GradedDerivation (𝒜 : GradedRing G A) where
  differential : A → A
  map_zero' : differential 0 = 0
  map_add' : ∀ x y, differential (x + y) = differential x + differential y
  map_neg' : ∀ x, differential (-x) = -differential x
  maps_grade' : ∀ {g x}, 𝒜.IsHomogeneous g x →
    𝒜.IsHomogeneous (g + 𝒜.differential_degree) (differential x)
  leibniz' : ∀ {g h x y}, 𝒜.IsHomogeneous g x → 𝒜.IsHomogeneous h y →
    differential (x * y) = differential x * y +
      Parity.sign (𝒜.parity g) (x * differential y)

namespace GradedDerivation

variable {𝒜 : GradedRing G A} (D : GradedDerivation 𝒜)

instance : CoeFun (GradedDerivation 𝒜) (fun _ => A → A) :=
  ⟨fun D => D.differential⟩

@[simp] theorem map_zero : D 0 = 0 := D.map_zero'

@[simp] theorem map_add (x y : A) : D (x + y) = D x + D y :=
  D.map_add' x y

@[simp] theorem map_neg (x : A) : D (-x) = -D x := D.map_neg' x

theorem map_sub (x y : A) : D (x - y) = D x - D y := by
  simpa [sub_eq_add_neg] using D.map_add' x (-y)

theorem maps_grade {g : G} {x : A} (hx : 𝒜.IsHomogeneous g x) :
    𝒜.IsHomogeneous (g + 𝒜.differential_degree) (D x) :=
  D.maps_grade' hx

theorem leibniz {g h : G} {x y : A}
    (hx : 𝒜.IsHomogeneous g x) (hy : 𝒜.IsHomogeneous h y) :
    D (x * y) = D x * y + Parity.sign (𝒜.parity g) (x * D y) :=
  D.leibniz' hx hy

/-- The zero graded derivation, useful as a neutral adapter and smoke witness.
Its use does not supply a physical ghost differential. -/
def zero (𝒜 : GradedRing G A) : GradedDerivation 𝒜 where
  differential := 0
  map_zero' := by simp
  map_add' := by intro x y; simp
  map_neg' := by intro x; simp
  maps_grade' := by intro g x _; exact 𝒜.zero_mem _
  leibniz' := by
    intro g h x y _ _
    cases 𝒜.parity g <;> simp [Parity.sign]

end GradedDerivation

/-! ## Nilpotent graded BRST differential -/

/-- A square-zero graded derivation.  The differential degree and all Koszul
signs remain explicit fields of the supplied `GradedRing`. -/
structure GradedBRSTDifferential (𝒜 : GradedRing G A)
    extends GradedDerivation 𝒜 where
  nilpotent : ∀ x, differential (differential x) = 0

/-- The square-zero zero differential.  This is a structural adapter for
tests and neutral maps; it carries no physical ghost dynamics. -/
def GradedBRSTDifferential.zero (𝒜 : GradedRing G A) :
  GradedBRSTDifferential 𝒜 where
  toGradedDerivation := GradedDerivation.zero 𝒜
  nilpotent := by intro x; change (0 : A) = 0; rfl

namespace GradedBRSTDifferential

variable {𝒜 : GradedRing G A} (D : GradedBRSTDifferential 𝒜)

instance : CoeFun (GradedBRSTDifferential 𝒜) (fun _ => A → A) :=
  ⟨fun D => D.differential⟩

@[simp] theorem map_zero : D 0 = 0 := D.toGradedDerivation.map_zero'

@[simp] theorem map_add (x y : A) : D (x + y) = D x + D y :=
  D.toGradedDerivation.map_add' x y

@[simp] theorem map_neg (x : A) : D (-x) = -D x :=
  D.toGradedDerivation.map_neg' x

theorem map_sub (x y : A) : D (x - y) = D x - D y :=
  D.toGradedDerivation.map_sub x y

theorem maps_grade {g : G} {x : A} (hx : 𝒜.IsHomogeneous g x) :
    𝒜.IsHomogeneous (g + 𝒜.differential_degree) (D x) :=
  D.toGradedDerivation.maps_grade' hx

theorem leibniz {g h : G} {x y : A}
    (hx : 𝒜.IsHomogeneous g x) (hy : 𝒜.IsHomogeneous h y) :
    D (x * y) = D x * y + Parity.sign (𝒜.parity g) (x * D y) :=
  D.toGradedDerivation.leibniz' hx hy

theorem nilpotent_apply (x : A) : D (D x) = 0 := D.nilpotent x

/-- A graded BRST-closed element. -/
def IsClosed (x : A) : Prop := D x = 0

/-- A graded BRST-exact element, retaining its primitive. -/
def IsExact (x : A) : Prop := ∃ y : A, D y = x

/-- Equality modulo a graded BRST-exact difference. -/
def Cohomologous (x y : A) : Prop := ∃ z : A, D z = x - y

@[simp] theorem closed_zero : D.IsClosed 0 := by
  simp [IsClosed]

theorem closed_add {x y : A} (hx : D.IsClosed x) (hy : D.IsClosed y) :
    D.IsClosed (x + y) := by
  unfold IsClosed at hx hy ⊢
  rw [D.map_add, hx, hy, add_zero]

theorem closed_neg {x : A} (hx : D.IsClosed x) : D.IsClosed (-x) := by
  unfold IsClosed at hx ⊢
  rw [D.map_neg, hx, neg_zero]

theorem closed_mul {g h : G} {x y : A}
    (hxg : 𝒜.IsHomogeneous g x) (hyh : 𝒜.IsHomogeneous h y)
    (hx : D.IsClosed x) (hy : D.IsClosed y) :
    D.IsClosed (x * y) := by
  unfold IsClosed at hx hy ⊢
  calc
    D (x * y) = D x * y + Parity.sign (𝒜.parity g) (x * D y) :=
      D.leibniz hxg hyh
    _ = 0 := by
      cases hp : 𝒜.parity g <;> simp [hx, hy, Parity.sign]

theorem exact_closed {x : A} (hx : D.IsExact x) : D.IsClosed x := by
  rcases hx with ⟨y, rfl⟩
  exact D.nilpotent_apply y

theorem exact_zero : D.IsExact 0 := ⟨0, D.map_zero⟩

theorem cohomologous_refl (x : A) : D.Cohomologous x x := by
  exact ⟨0, by simp⟩

theorem cohomologous_symm {x y : A} (h : D.Cohomologous x y) :
    D.Cohomologous y x := by
  rcases h with ⟨z, hz⟩
  refine ⟨-z, ?_⟩
  rw [D.map_neg, hz]
  abel

theorem cohomologous_trans {x y z : A}
    (hxy : D.Cohomologous x y) (hyz : D.Cohomologous y z) :
    D.Cohomologous x z := by
  rcases hxy with ⟨u, hu⟩
  rcases hyz with ⟨v, hv⟩
  refine ⟨u + v, ?_⟩
  rw [D.map_add, hu, hv]
  abel

theorem cohomologous_iff_difference_exact {x y : A} :
    D.Cohomologous x y ↔ D.IsExact (x - y) := Iff.rfl

theorem closed_of_cohomologous_left {x y : A}
    (hx : D.IsClosed x) (hxy : D.Cohomologous x y) :
    D.IsClosed y := by
  rcases hxy with ⟨z, hz⟩
  unfold IsClosed at hx ⊢
  have h := congrArg (fun t : A => D t) hz
  rw [D.nilpotent_apply, D.map_sub, hx] at h
  simpa using h

theorem closed_of_cohomologous_right {x y : A}
    (hy : D.IsClosed y) (hxy : D.Cohomologous x y) :
    D.IsClosed x :=
  D.closed_of_cohomologous_left hy (D.cohomologous_symm hxy)

end GradedBRSTDifferential

end LeanPhy.Mathematics
