import Mathlib.Tactic

/-!
# A finite/combinatorial cochain layer

Many lattice and band-theory calculations use the same local identity as
ordinary differential forms: a vertex potential produces an edge field, and
the oriented sum around every triangle vanishes.  This module records that
identity without choosing a lattice, a metric, a dimension or a continuum
limit.  A physical mesh supplies the vertex/edge/triangle labels and may add
boundary conditions or topology later.

The coefficient type is an additive commutative group.  This covers additive
Abelian gauge fields, discrete one-forms, phase angles and velocity one-forms.
Non-Abelian link variables belong to `Mathematics.Holonomy` instead.
-/

namespace LeanPhy.Mathematics

namespace DiscreteCochain

universe u v

open scoped BigOperators

abbrev Cochain0 (V : Type u) (A : Type v) := V → A
abbrev Cochain1 (V : Type u) (A : Type v) := V → V → A
abbrev Cochain2 (V : Type u) (A : Type v) := V → V → V → A

/-- The combinatorial exterior derivative of a vertex potential. -/
def d0 {V : Type u} {A : Type v} [AddCommGroup A]
    (φ : Cochain0 V A) (x y : V) : A := φ y - φ x

/-- The oriented triangle sum of an edge field. -/
def d1 {V : Type u} {A : Type v} [AddCommGroup A]
    (α : Cochain1 V A) (x y z : V) : A := α x y + α y z + α z x

@[simp] theorem d0_apply {V : Type u} {A : Type v} [AddCommGroup A]
    (φ : Cochain0 V A) (x y : V) : d0 φ x y = φ y - φ x := rfl

@[simp] theorem d1_apply {V : Type u} {A : Type v} [AddCommGroup A]
    (α : Cochain1 V A) (x y z : V) : d1 α x y z = α x y + α y z + α z x := rfl

theorem d0_swap {V : Type u} {A : Type v} [AddCommGroup A]
    (φ : Cochain0 V A) (x y : V) : d0 φ y x = -d0 φ x y := by
  simp [d0]

theorem d1_cyclic {V : Type u} {A : Type v} [AddCommGroup A]
    (α : Cochain1 V A) (x y z : V) :
    d1 α y z x = d1 α x y z := by
  simp [d1]
  abel

theorem d1_d0 {V : Type u} {A : Type v} [AddCommGroup A]
    (φ : Cochain0 V A) (x y z : V) : d1 (d0 φ) x y z = 0 := by
  simp [d1, d0]

/-- Add an exact vertex potential to an edge field. -/
def gaugeShift {V : Type u} {A : Type v} [AddCommGroup A]
    (α : Cochain1 V A) (φ : Cochain0 V A) : Cochain1 V A :=
  fun x y => α x y + d0 φ x y

theorem d1_gaugeShift {V : Type u} {A : Type v} [AddCommGroup A]
    (α : Cochain1 V A) (φ : Cochain0 V A) (x y z : V) :
    d1 (gaugeShift α φ) x y z = d1 α x y z := by
  simp only [d1, gaugeShift, d0]
  abel

theorem d1_gaugeShift_eq (V : Type u) (A : Type v) [AddCommGroup A]
    (α : Cochain1 V A) (φ : Cochain0 V A) :
    d1 (gaugeShift α φ) = d1 α := by
  funext x y z
  exact d1_gaugeShift α φ x y z

/-- A field is exact when it is the derivative of a vertex potential. -/
def IsExact {V : Type u} {A : Type v} [AddCommGroup A]
    (α : Cochain1 V A) : Prop := ∃ φ, α = d0 φ

theorem exact_isClosed {V : Type u} {A : Type v} [AddCommGroup A]
    {α : Cochain1 V A} (hα : IsExact α) : ∀ x y z, d1 α x y z = 0 := by
  rcases hα with ⟨φ, rfl⟩
  intro x y z
  exact d1_d0 φ x y z

/-! A finite cyclic sum is the cochain version of a lattice flux or a
one-dimensional winding certificate.  The step is an explicit permutation,
so the theorem does not assume that a chosen successor function is bijective.
-/

def cycleSum {V : Type u} {A : Type v} [Fintype V] [AddCommMonoid A]
    (link : V → A) : A := ∑ x, link x

def cycleGauge {V : Type u} {A : Type v} [AddCommGroup A]
    (g link : V → A) (step : Equiv.Perm V) : V → A :=
  fun x => g x + link x - g (step x)

theorem cycleGauge_sum_invariant {V : Type u} {A : Type v}
    [Fintype V] [AddCommGroup A]
    (g link : V → A) (step : Equiv.Perm V) :
    cycleSum (cycleGauge g link step) = cycleSum link := by
  unfold cycleSum cycleGauge
  simp only [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hstep : (∑ x : V, g (step x)) = ∑ x : V, g x := Equiv.sum_comp step g
  rw [hstep]
  abel

end DiscreteCochain

end LeanPhy.Mathematics
