import LeanPhy.Mathematics.ConstraintMap

/-!
# A delimited BRST differential layer

BRST calculations in gauge theory are often used before a full construction of
ghost fields, a BV phase space, or a path integral is available.  This module
records the algebraic core that can be checked independently:

* a BRST differential is an explicit derivation whose square is zero;
* closed, exact, and cohomologous observables are propositions;
* an optional Poisson-compatibility law transports the differential through a
  Poisson bracket;
* an optional constraint-ideal preservation law transports weak equality.

The module is intentionally ungraded.  It does not construct ghost number,
Koszul signs, a BV antibracket, a gauge-fixing fermion, a path-integral
measure, anomaly cancellation, or a physical equivalence theorem.  Those
requirements remain explicit inputs or open research obligations.
-/

namespace LeanPhy.Mathematics

universe u v w

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]

/-! ## Nilpotent derivations and algebraic cohomology -/

/-- An ungraded nilpotent derivation, the algebraic core of a BRST operator. -/
structure BRSTDifferential (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A] where
  differential : PhysicsDerivation R A
  nilpotent : ∀ x, differential (differential x) = 0

namespace BRSTDifferential

variable (D : BRSTDifferential R A)

instance : CoeFun (BRSTDifferential R A) (fun _ => A → A) :=
  ⟨fun D => D.differential⟩

@[simp] theorem map_zero : D 0 = 0 := by
  exact D.differential.map_zero

@[simp] theorem map_add (x y : A) : D (x + y) = D x + D y := by
  exact D.differential.map_add x y

@[simp] theorem map_sub (x y : A) : D (x - y) = D x - D y := by
  exact D.differential.map_sub x y

@[simp] theorem map_smul (r : R) (x : A) : D (r • x) = r • D x := by
  exact D.differential.map_smul r x

theorem map_mul (x y : A) : D (x * y) = D x * y + x * D y := by
  simpa [smul_eq_mul, mul_comm, add_comm] using D.differential.leibniz x y

theorem nilpotent_apply (x : A) : D (D x) = 0 :=
  D.nilpotent x

/-- A BRST-closed element. -/
def IsClosed (x : A) : Prop := D x = 0

/-- A BRST-exact element, with its primitive retained as a witness. -/
def IsExact (x : A) : Prop := ∃ y : A, D y = x

/-- Two elements differ by a BRST-exact element. -/
def Cohomologous (x y : A) : Prop := ∃ z : A, D z = x - y

@[simp] theorem closed_zero : D.IsClosed 0 := by
  simp [IsClosed]

theorem closed_add {x y : A} (hx : D.IsClosed x) (hy : D.IsClosed y) :
    D.IsClosed (x + y) := by
  unfold IsClosed at hx hy ⊢
  rw [D.map_add, hx, hy, add_zero]

theorem closed_smul (r : R) {x : A} (hx : D.IsClosed x) :
    D.IsClosed (r • x) := by
  unfold IsClosed at hx ⊢
  rw [D.map_smul, hx, smul_zero]

theorem closed_mul {x y : A} (hx : D.IsClosed x) (hy : D.IsClosed y) :
    D.IsClosed (x * y) := by
  unfold IsClosed at hx hy ⊢
  rw [D.map_mul, hx, hy, zero_mul, mul_zero, add_zero]

theorem exact_closed {x : A} (hx : D.IsExact x) : D.IsClosed x := by
  rcases hx with ⟨y, rfl⟩
  exact D.nilpotent_apply y

theorem exact_zero : D.IsExact 0 := by
  exact ⟨0, D.map_zero⟩

theorem cohomologous_refl (x : A) : D.Cohomologous x x := by
  exact ⟨0, by simp⟩

theorem cohomologous_symm {x y : A} (h : D.Cohomologous x y) :
    D.Cohomologous y x := by
  rcases h with ⟨z, hz⟩
  refine ⟨-z, ?_⟩
  calc
    D (-z) = -D z := D.differential.map_neg z
    _ = -(x - y) := by rw [hz]
    _ = y - x := by ring

theorem cohomologous_trans {x y z : A}
    (hxy : D.Cohomologous x y) (hyz : D.Cohomologous y z) :
    D.Cohomologous x z := by
  rcases hxy with ⟨u, hu⟩
  rcases hyz with ⟨v, hv⟩
  refine ⟨u + v, ?_⟩
  rw [D.map_add, hu, hv]
  ring

theorem cohomologous_iff_difference_exact {x y : A} :
    D.Cohomologous x y ↔ D.IsExact (x - y) := by
  rfl

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

end BRSTDifferential

/-! ## Poisson compatibility -/

/-- A nilpotent derivation compatible with a declared Poisson bracket.

The displayed law is deliberately ungraded.  A graded BRST/BV extension must
add ghost parity and the corresponding Koszul signs rather than silently
reusing this structure.
-/
structure PoissonBRSTDifferential
    (C : PoissonAlgebra R A) extends BRSTDifferential R A where
  bracket_leibniz : ∀ x y,
    differential (C x y) = C (differential x) y + C x (differential y)

namespace PoissonBRSTDifferential

variable {C : PoissonAlgebra R A}
variable (D : PoissonBRSTDifferential C)

instance : CoeFun (PoissonBRSTDifferential C) (fun _ => A → A) :=
  ⟨fun D => D.differential⟩

theorem closed_bracket {x y : A}
    (hx : D.toBRSTDifferential.IsClosed x)
    (hy : D.toBRSTDifferential.IsClosed y) :
    D.toBRSTDifferential.IsClosed (C x y) := by
  unfold BRSTDifferential.IsClosed at hx hy ⊢
  rw [D.bracket_leibniz, hx, hy]
  simp

theorem exact_bracket_closed_right {x y : A}
    (hx : D.toBRSTDifferential.IsExact x)
    (hy : D.toBRSTDifferential.IsClosed y) :
    D.toBRSTDifferential.IsExact (C x y) := by
  rcases hx with ⟨z, hz⟩
  refine ⟨C z y, ?_⟩
  rw [D.bracket_leibniz, hz, hy]
  simp

end PoissonBRSTDifferential

/-! ## Constraint-compatible BRST data -/

/-- A Poisson-compatible differential that preserves a declared constraint
ideal.  This is enough to transport weak equality through the differential.
It does not construct a quotient or identify BRST cohomology with physical
observables.
-/
structure ConstraintBRSTDifferential
    {ι : Type w} (C : FirstClassConstraintAlgebra R A ι)
    extends PoissonBRSTDifferential C.poisson where
  maps_constraintIdeal : ∀ {x : A}, x ∈ C.constraintIdeal →
    differential x ∈ C.constraintIdeal

namespace ConstraintBRSTDifferential

variable {ι : Type w} {C : FirstClassConstraintAlgebra R A ι}
variable (D : ConstraintBRSTDifferential C)

instance : CoeFun (ConstraintBRSTDifferential C) (fun _ => A → A) :=
  ⟨fun D => D.differential⟩

theorem map_constraintIdeal {x : A} (hx : x ∈ C.constraintIdeal) :
    D x ∈ C.constraintIdeal :=
  D.maps_constraintIdeal hx

theorem map_weaklyEqual {x y : A} (hxy : C.WeaklyEqual x y) :
    C.WeaklyEqual (D x) (D y) := by
  change D x - D y ∈ C.constraintIdeal
  have hmap : D (x - y) = D x - D y := by
    exact BRSTDifferential.map_sub D.toBRSTDifferential x y
  rw [← hmap]
  exact D.map_constraintIdeal hxy

end ConstraintBRSTDifferential

end LeanPhy.Mathematics
