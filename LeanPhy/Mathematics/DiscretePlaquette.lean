import LeanPhy.Mathematics.DiscreteCochain
import Mathlib.Tactic

/-!
# Oriented quadrilateral fluxes

Many finite calculations attach a one-form to the edges of an oriented
quadrilateral.  The same four-term boundary sum appears as a lattice gauge
plaquette, a Berry flux on a rectangular mesh, a finite-difference curl, or a
circulation in a network.  This file keeps that common algebra in one place.

The theorem is deliberately combinatorial.  It does not identify a plaquette
flux with a continuum integral or a Chern number; a mesh, orientation and any
quantisation statement remain explicit inputs.
-/

namespace LeanPhy.Mathematics

universe u v

open DiscreteCochain

namespace Plaquette

abbrev EdgeField (V : Type u) (A : Type v) := V → V → A

/-- The oriented boundary sum of the quadrilateral `x → y → z → w → x`. -/
def flux {V : Type u} {A : Type v} [AddCommGroup A]
    (α : EdgeField V A) (x y z w : V) : A :=
  α x y + α y z + α z w + α w x

@[simp] theorem flux_apply {V : Type u} {A : Type v} [AddCommGroup A]
    (α : EdgeField V A) (x y z w : V) :
    flux α x y z w = α x y + α y z + α z w + α w x := rfl

/-- Reversing the orientation changes the sign when the edge field is
antisymmetric.  Antisymmetry is a hypothesis because an arbitrary function on
ordered pairs need not represent an oriented one-form. -/
theorem flux_reverse {V : Type u} {A : Type v} [AddCommGroup A]
    (α : EdgeField V A)
    (hanti : ∀ a b, α b a = -α a b)
    (x y z w : V) :
    flux α w z y x = -flux α x y z w := by
  simp only [flux]
  rw [hanti z w, hanti y z, hanti x y, hanti w x]
  abel

/-! The exact vertex-potential shift used by Abelian lattice gauge fields. -/

def gaugeShift {V : Type u} {A : Type v} [AddCommGroup A]
    (α : EdgeField V A) (φ : V → A) : EdgeField V A :=
  fun x y => α x y + (φ y - φ x)

theorem flux_gaugeShift {V : Type u} {A : Type v} [AddCommGroup A]
    (α : EdgeField V A) (φ : V → A) (x y z w : V) :
    flux (gaugeShift α φ) x y z w = flux α x y z w := by
  simp only [flux, gaugeShift]
  abel

theorem flux_gaugeShift_eq {V : Type u} {A : Type v} [AddCommGroup A]
    (α : EdgeField V A) (φ : V → A) :
    flux (gaugeShift α φ) = flux α := by
  funext x y z w
  exact flux_gaugeShift α φ x y z w

/-- A four-edge field is closed when every plaquette boundary sum vanishes. -/
def IsPlaquetteClosed {V : Type u} {A : Type v} [AddCommGroup A]
    (α : EdgeField V A) : Prop :=
  ∀ x y z w, flux α x y z w = 0

theorem exact_isPlaquetteClosed {V : Type u} {A : Type v} [AddCommGroup A]
    (φ : V → A) : IsPlaquetteClosed (fun x y => φ y - φ x) := by
  intro x y z w
  simp [flux]

end Plaquette

/-! Domain vocabulary aliases.  All of them reduce to the same checked
boundary sum, so adapters can exchange certificates without re-proving the
telescoping identity. -/

namespace GaugeTheory
abbrev PlaquetteFlux {V : Type u} {A : Type v} [AddCommGroup A] :=
  Plaquette.flux (V := V) (A := A)
end GaugeTheory

namespace Condensed
abbrev BerryPlaquetteFlux {V : Type u} {A : Type v} [AddCommGroup A] :=
  Plaquette.flux (V := V) (A := A)
end Condensed

namespace Classical
abbrev CirculationPlaquette {V : Type u} {A : Type v} [AddCommGroup A] :=
  Plaquette.flux (V := V) (A := A)
end Classical

namespace StatMech
abbrev LatticePlaquetteFlux {V : Type u} {A : Type v} [AddCommGroup A] :=
  Plaquette.flux (V := V) (A := A)
end StatMech

end LeanPhy.Mathematics
