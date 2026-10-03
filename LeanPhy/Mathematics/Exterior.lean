import LeanPhy.Mathematics.Derivation
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite differential forms and the algebraic `d² = 0` layer

This module is a small, finite-index differential-form interface for
continuum physics.  A one-form is a finite list of coefficients, a two-form
stores antisymmetry in its type-level data, and a three-form is represented by
its coefficient function.  The exterior derivative is built from a supplied
family of derivations.  Commuting derivations are the only hypothesis needed
for the algebraic identity `d(d ω) = 0`.

The construction is deliberately independent of coordinates, smoothness,
integration, manifolds and boundary conditions.  Those analytic structures can
later provide instances of this finite interface.  The same theorem is useful
for Maxwell curvature, Abelian gauge transformations, discrete differential
forms and the local algebraic part of geometric or fluid models.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

universe u v

/-- A finite one-form with coefficients in `A`. -/
structure Form1 (n : Nat) (A : Type v) where
  value : Fin n → A

instance (n : Nat) (A : Type v) : CoeFun (Form1 n A) (fun _ => Fin n → A) :=
  ⟨Form1.value⟩

/-- A finite two-form.  Antisymmetry is stored as an invariant rather than
being left to a later simplifier. -/
structure Form2 (n : Nat) (A : Type v) [AddGroup A] where
  value : Fin n → Fin n → A
  antisymm : ∀ i j, value i j = -value j i

instance (n : Nat) (A : Type v) [AddGroup A] :
    CoeFun (Form2 n A) (fun _ => Fin n → Fin n → A) := ⟨Form2.value⟩

theorem Form2.ext {n : Nat} {A : Type v} [AddGroup A]
    {x y : Form2 n A} (h : ∀ i j, x.value i j = y.value i j) : x = y := by
  cases x with
  | mk xv xa =>
    cases y with
    | mk yv ya =>
      have hv : xv = yv := by
        funext i j
        exact h i j
      cases hv
      rfl

/-- A finite three-form coefficient function.  Its alternating laws can be
added by a later typed tensor layer; `d² = 0` only needs the cyclic component. -/
abbrev Form3 (n : Nat) (A : Type v) := Fin n → Fin n → Fin n → A

/-- The wedge of two one-forms, with the conventional factor omitted. -/
def wedge1 {n : Nat} {A : Type v} [Ring A]
    (α β : Form1 n A) : Form2 n A where
  value := fun i j => α i * β j - α j * β i
  antisymm := by
    intro i j
    change α i * β j - α j * β i = -(α j * β i - α i * β j)
    noncomm_ring

theorem wedge1_swap_apply {n : Nat} {A : Type v} [CommRing A]
    (α β : Form1 n A) (i j : Fin n) :
    wedge1 α β i j = -(wedge1 β α i j) := by
  change α i * β j - α j * β i =
    -((β i * α j - β j * α i))
  ring

theorem wedge1_self {n : Nat} {A : Type v} [CommRing A]
    (α : Form1 n A) (i j : Fin n) : wedge1 α α i j = 0 := by
  change α i * α j - α j * α i = 0
  ring

/-- The exterior derivative of a one-form, `dω_ij = D_i ω_j - D_j ω_i`. -/
def exteriorDerivative1 {n : Nat} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → PhysicsDerivation R A) (ω : Form1 n A) : Form2 n A where
  value := fun i j => D i (ω j) - D j (ω i)
  antisymm := by
    intro i j
    change D i (ω j) - D j (ω i) = -(D j (ω i) - D i (ω j))
    ring

@[simp] theorem exteriorDerivative1_apply {n : Nat} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → PhysicsDerivation R A) (ω : Form1 n A) (i j : Fin n) :
    exteriorDerivative1 D ω i j = D i (ω j) - D j (ω i) := rfl

/-- The cyclic component of the exterior derivative of a two-form. -/
def exteriorDerivative2 {n : Nat} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → PhysicsDerivation R A) (F : Form2 n A) : Form3 n A :=
  fun i j k => D i (F j k) + D j (F k i) + D k (F i j)

@[simp] theorem exteriorDerivative2_apply {n : Nat} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → PhysicsDerivation R A) (F : Form2 n A)
    (i j k : Fin n) :
    exteriorDerivative2 D F i j k =
      D i (F j k) + D j (F k i) + D k (F i j) := rfl

/-- The finite differential-form version of `d² = 0`.  The commutation
condition is explicit so a non-coordinate frame can refuse this theorem. -/
theorem exteriorDerivative2_exteriorDerivative1 {n : Nat} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → PhysicsDerivation R A) (ω : Form1 n A)
    (hcomm : ∀ i j x, D i (D j x) = D j (D i x))
    (i j k : Fin n) :
    exteriorDerivative2 D (exteriorDerivative1 D ω) i j k = 0 := by
  simp only [exteriorDerivative2, exteriorDerivative1, map_sub]
  rw [hcomm i j (ω k), hcomm i k (ω j), hcomm j k (ω i)]
  ring

/-- Adding an exact one-form to a potential leaves its exterior derivative
unchanged when the supplied derivations commute. -/
theorem exteriorDerivative1_gauge_invariant {n : Nat} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → PhysicsDerivation R A) (ω : Form1 n A) (χ : A)
    (hcomm : ∀ i j x, D i (D j x) = D j (D i x)) :
    exteriorDerivative1 D
        ⟨fun i => ω i + D i χ⟩ = exteriorDerivative1 D ω := by
  apply Form2.ext
  intro i j
  change D i (ω j + D j χ) - D j (ω i + D i χ) =
    D i (ω j) - D j (ω i)
  rw [map_add, map_add]
  simp only [sub_eq_add_neg]
  rw [hcomm i j χ]
  ring

end LeanPhy.Mathematics
