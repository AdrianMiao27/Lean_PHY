import Mathlib.Tactic

/-!
# Periodic finite plaquettes

Two commuting finite translations are the algebraic skeleton of a periodic
two-dimensional lattice.  The oriented plaquette curl below is shared by
Berry-curvature meshes, lattice gauge fields, periodic finite differences and
discrete fluid vorticity.  We prove exact vertex-gauge invariance and the
telescoping identity that the sum of a globally defined periodic curl vanishes.

The module does **not** call that sum a Chern number: nontrivial Chern data
requires patches, transition functions and a quantisation theorem, all of
which remain explicit higher-level inputs.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

namespace PeriodicPlaquette

universe u v

variable {V : Type u} {A : Type v} [Fintype V] [AddCommGroup A]

/-- The oriented curl on the plaquette based at `x`.  `s₁` and `s₂` are the
two periodic translations; the commutation condition is needed for a gauge
shift to cancel around the plaquette. -/
def flux (s₁ s₂ : Equiv.Perm V) (a b : V → A) (x : V) : A :=
  a x + b (s₁ x) - a (s₂ x) - b x

@[simp] theorem flux_apply (s₁ s₂ : Equiv.Perm V) (a b : V → A) (x : V) :
    flux s₁ s₂ a b x = a x + b (s₁ x) - a (s₂ x) - b x := rfl

/-- Add the exact vertex potential differences to the two directional link
fields. -/
def shift (s : Equiv.Perm V) (a φ : V → A) : V → A :=
  fun x => a x + φ (s x) - φ x

theorem flux_gauge_invariant (s₁ s₂ : Equiv.Perm V)
    (hcomm : Function.Commute s₁ s₂) (a b φ : V → A) (x : V) :
    flux s₁ s₂ (shift s₁ a φ) (shift s₂ b φ) x =
      flux s₁ s₂ a b x := by
  unfold flux shift
  rw [hcomm x]
  abel

theorem total_flux_zero (s₁ s₂ : Equiv.Perm V) (a b : V → A) :
    ∑ x, flux s₁ s₂ a b x = 0 := by
  unfold flux
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Equiv.sum_comp s₁ b, Equiv.sum_comp s₂ a]
  abel

theorem exact_flux_zero (s₁ s₂ : Equiv.Perm V)
    (hcomm : Function.Commute s₁ s₂) (φ : V → A) (x : V) :
    flux s₁ s₂ (shift s₁ (fun _ => 0) φ)
      (shift s₂ (fun _ => 0) φ) x = 0 := by
  rw [flux_gauge_invariant s₁ s₂ hcomm (fun _ => 0) (fun _ => 0) φ]
  simp [flux]

theorem total_flux_gauge_invariant (s₁ s₂ : Equiv.Perm V)
    (hcomm : Function.Commute s₁ s₂) (a b φ : V → A) :
    (∑ x, flux s₁ s₂ (shift s₁ a φ) (shift s₂ b φ) x) =
      ∑ x, flux s₁ s₂ a b x := by
  apply Finset.sum_congr rfl
  intro x hx
  exact flux_gauge_invariant s₁ s₂ hcomm a b φ x

end PeriodicPlaquette

/-! Domain names for adapters.  They reduce to the same checked finite curl. -/

namespace GaugeTheory

abbrev PeriodicPlaquetteFlux {V : Type u} {A : Type v}
    [Fintype V] [AddCommGroup A] :=
  PeriodicPlaquette.flux (V := V) (A := A)

end GaugeTheory

namespace Condensed

abbrev BerryMeshFlux {V : Type u} {A : Type v}
    [Fintype V] [AddCommGroup A] :=
  PeriodicPlaquette.flux (V := V) (A := A)

end Condensed

namespace Classical

abbrev PeriodicVorticity {V : Type u} {A : Type v}
    [Fintype V] [AddCommGroup A] :=
  PeriodicPlaquette.flux (V := V) (A := A)

end Classical

end LeanPhy.Mathematics
