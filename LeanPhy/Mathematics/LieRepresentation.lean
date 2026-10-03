import LeanPhy.Mathematics.Lie

/-!
# A reusable Lie-algebra and representation interface

Many LeanPhy domains use the same algebraic pattern: angular momentum,
Lorentz generators, colour generators, lattice symmetries and gauge
generators are elements of a Lie algebra, while matrices or operators give a
representation of that algebra.  The concrete files used to repeat this
pattern before this interface was introduced.  This module keeps the
structure deliberately small and finite-algebraic: it does not assert that a
formal bracket comes from a differentiable group or from a physical model.

The fields of `LieAlgebra` and `Representation` are explicit hypotheses.  A
domain module may fill them with kernel-checked matrix proofs, or expose them
as named model assumptions.  Either way, the downstream theorems below only
use the recorded laws.
-/

namespace LeanPhy.Mathematics

open LeanPhy.Quantum

universe u v w

/-- The commutator with universe-polymorphic carrier.  The older
`LeanPhy.Quantum.commutator` is kept for the existing Type-0 APIs; this
version lets the reusable interface work with large operator types too. -/
def ringCommutator {A : Type w} [Sub A] [Mul A] (x y : A) : A := x * y - y * x

theorem ringCommutator_add_left {A : Type w} [Ring A] (x y z : A) :
    ringCommutator (x + y) z = ringCommutator x z + ringCommutator y z := by
  simp [ringCommutator]
  noncomm_ring

theorem ringCommutator_add_right {A : Type w} [Ring A] (x y z : A) :
    ringCommutator x (y + z) = ringCommutator x y + ringCommutator x z := by
  simp [ringCommutator]
  noncomm_ring

theorem ringCommutator_zero_left {A : Type w} [Ring A] (x : A) :
    ringCommutator 0 x = 0 := by
  simp [ringCommutator]

theorem ringCommutator_alternating {A : Type w} [Ring A] (x : A) :
    ringCommutator x x = 0 := by
  simp [ringCommutator]

theorem ringCommutator_antisymm {A : Type w} [Ring A] (x y : A) :
    ringCommutator x y = -ringCommutator y x := by
  simp [ringCommutator]

theorem ringCommutator_jacobi {A : Type w} [Ring A] (x y z : A) :
    ringCommutator x (ringCommutator y z) +
        ringCommutator y (ringCommutator z x) +
        ringCommutator z (ringCommutator x y) = 0 := by
  simp only [ringCommutator, mul_sub, sub_mul]
  noncomm_ring

theorem ringCommutator_smul_left {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A] (r : R) (x y : A) :
    ringCommutator (r • x) y = r • ringCommutator x y := by
  simp only [ringCommutator, Algebra.smul_def]
  calc
    (algebraMap R A r * x) * y - y * (algebraMap R A r * x) =
        algebraMap R A r * (x * y) - y * (algebraMap R A r * x) := by
      noncomm_ring
    _ = algebraMap R A r * (x * y) - (y * algebraMap R A r) * x := by
      noncomm_ring
    _ = algebraMap R A r * (x * y) - (algebraMap R A r * y) * x := by
      rw [(Algebra.commutes r y).symm]
    _ = algebraMap R A r * (x * y - y * x) := by
      rw [mul_sub, mul_assoc]

theorem ringCommutator_smul_right {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A] (r : R) (x y : A) :
    ringCommutator x (r • y) = r • ringCommutator x y := by
  simp only [ringCommutator, Algebra.smul_def]
  calc
    x * (algebraMap R A r * y) - (algebraMap R A r * y) * x =
        (x * algebraMap R A r) * y - (algebraMap R A r * y) * x := by
      congr 1
      exact (mul_assoc x (algebraMap R A r) y).symm
    _ = (algebraMap R A r * x) * y - (algebraMap R A r * y) * x := by
      rw [Algebra.commutes r x]
    _ = algebraMap R A r * (x * y) - algebraMap R A r * (y * x) := by
      noncomm_ring
    _ = algebraMap R A r * (x * y - y * x) := by
      rw [mul_sub]

/-- A Lie algebra over a commutative ring, with the linearity laws made
explicit so that the interface also works for abstract symbolic generators. -/
structure LieAlgebra (R : Type u) (V : Type v)
    [CommRing R] [AddCommGroup V] [Module R V] where
  bracket : V → V → V
  add_left : ∀ x y z, bracket (x + y) z = bracket x z + bracket y z
  add_right : ∀ x y z, bracket x (y + z) = bracket x y + bracket x z
  smul_left : ∀ (r : R) x y, bracket (r • x) y = r • bracket x y
  smul_right : ∀ (r : R) x y, bracket x (r • y) = r • bracket x y
  zero_left : ∀ x, bracket 0 x = 0
  alternating : ∀ x, bracket x x = 0
  antisymm : ∀ x y, bracket x y = -bracket y x
  jacobi : ∀ x y z,
    bracket x (bracket y z) + bracket y (bracket z x) + bracket z (bracket x y) = 0

namespace LieAlgebra

variable {R : Type u} {V : Type v} [CommRing R] [AddCommGroup V] [Module R V]
variable (L : LieAlgebra R V)

@[simp] theorem bracket_zero_left (x : V) : L.bracket 0 x = 0 := L.zero_left x

@[simp] theorem bracket_zero_right (x : V) : L.bracket x 0 = 0 := by
  rw [L.antisymm, L.zero_left]
  simp

@[simp] theorem bracket_self (x : V) : L.bracket x x = 0 := by
  exact L.alternating x

theorem bracket_neg_left (x y : V) : L.bracket (-x) y = -L.bracket x y := by
  have h := L.add_left (-x) x y
  have hz : L.bracket (-x) y + L.bracket x y = 0 := by simpa using h.symm
  exact eq_neg_of_add_eq_zero_left hz

theorem bracket_neg_right (x y : V) : L.bracket x (-y) = -L.bracket x y := by
  have h := L.add_right x (-y) y
  have hz : L.bracket x (-y) + L.bracket x y = 0 := by simpa using h.symm
  exact eq_neg_of_add_eq_zero_left hz

end LieAlgebra

/-- The canonical Lie algebra carried by any associative `R`-algebra.  This
construction is the bridge that lets a concrete matrix/operator type enter
the generic representation API without restating the commutator laws. -/
def associativeLieAlgebra (R : Type u) (A : Type w)
    [CommRing R] [Ring A] [Algebra R A] : LieAlgebra R A where
  bracket := ringCommutator
  add_left := ringCommutator_add_left
  add_right := ringCommutator_add_right
  smul_left := ringCommutator_smul_left
  smul_right := ringCommutator_smul_right
  zero_left := ringCommutator_zero_left
  alternating := ringCommutator_alternating
  antisymm := ringCommutator_antisymm
  jacobi := ringCommutator_jacobi

/-- A linear representation of `L` in an associative ring.  The final field
is the only physical/model-specific compatibility condition: it says that
the matrix/operator commutator realizes the abstract Lie bracket. -/
structure Representation {R : Type u} {V : Type v}
    [CommRing R] [AddCommGroup V] [Module R V]
    (L : LieAlgebra R V) (A : Type w) [Ring A] [Algebra R A] where
  toFun : V → A
  map_zero' : toFun 0 = 0
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (r : R) x, toFun (r • x) = r • toFun x
  bracket_compat' : ∀ x y,
    ringCommutator (toFun x) (toFun y) = toFun (L.bracket x y)

namespace Representation

variable {R : Type u} {V : Type v} [CommRing R] [AddCommGroup V] [Module R V]
variable {A : Type w} [Ring A] [Algebra R A]
variable {L : LieAlgebra R V} (ρ : Representation L A)

instance : CoeFun (Representation L A) (fun _ => V → A) := ⟨Representation.toFun⟩

@[simp] theorem map_zero : ρ 0 = 0 := ρ.map_zero'

@[simp] theorem map_add (x y : V) : ρ (x + y) = ρ x + ρ y := ρ.map_add' x y

@[simp] theorem map_smul (r : R) (x : V) : ρ (r • x) = r • ρ x := ρ.map_smul' r x

theorem commutator_map (x y : V) :
    ringCommutator (ρ x) (ρ y) = ρ (L.bracket x y) :=
  ρ.bracket_compat' x y

theorem preserves_jacobi (x y z : V) :
    ringCommutator (ρ x) (ringCommutator (ρ y) (ρ z)) +
        ringCommutator (ρ y) (ringCommutator (ρ z) (ρ x)) +
        ringCommutator (ρ z) (ringCommutator (ρ x) (ρ y)) = 0 := by
  rw [commutator_map ρ, commutator_map ρ, commutator_map ρ,
    commutator_map ρ, commutator_map ρ, commutator_map ρ]
  rw [← map_add ρ, ← map_add ρ, ← map_zero ρ, L.jacobi]

end Representation

/-- The identity map is a representation of the canonical commutator Lie
algebra.  It is useful as a default adapter for matrix and operator models. -/
def associativeLieRepresentation (R : Type u) (A : Type w)
    [CommRing R] [Ring A] [Algebra R A] :
    Representation (associativeLieAlgebra R A) A where
  toFun := id
  map_zero' := rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro r x; rfl
  bracket_compat' := by intro x y; rfl

theorem associative_representation_jacobi {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A] (x y z : A) :
    ringCommutator x (ringCommutator y z) +
        ringCommutator y (ringCommutator z x) +
        ringCommutator z (ringCommutator x y) = 0 :=
  ringCommutator_jacobi x y z

end LeanPhy.Mathematics
