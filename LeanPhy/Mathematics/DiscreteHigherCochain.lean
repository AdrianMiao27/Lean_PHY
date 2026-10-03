import LeanPhy.Mathematics.DiscreteCochain
import Mathlib.Tactic

/-!
# Alternating finite 2- and 3-cochains

The cyclic triangle sum in `DiscreteCochain` is convenient for oriented edge
tables.  For mesh and topological calculations it is also useful to expose the
standard alternating coboundary explicitly:

`(d₁ α)(x,y,z) = α(x,y) + α(y,z) - α(x,z)`

and

`(d₂ β)(w,x,y,z) = β(x,y,z) - β(w,y,z) + β(w,x,z) - β(w,x,y)`.

The finite theorem `d₂ d₁ = 0` is the algebraic boundary-of-boundary identity
used by discrete Maxwell, Berry curvature, finite-element and lattice models.
No manifold, orientation atlas, integral or Chern theorem is hidden here.
-/

namespace LeanPhy.Mathematics

namespace HigherCochain

universe u v

abbrev EdgeField (V : Type u) (A : Type v) := V → V → A
abbrev FaceField (V : Type u) (A : Type v) := V → V → V → A

def d1Alt {V : Type u} {A : Type v} [AddCommGroup A]
    (α : EdgeField V A) (x y z : V) : A :=
  α x y + α y z - α x z

def d2 {V : Type u} {A : Type v} [AddCommGroup A]
    (β : FaceField V A) (w x y z : V) : A :=
  β x y z - β w y z + β w x z - β w x y

@[simp] theorem d1Alt_apply {V : Type u} {A : Type v} [AddCommGroup A]
    (α : EdgeField V A) (x y z : V) :
    d1Alt α x y z = α x y + α y z - α x z := rfl

@[simp] theorem d2_apply {V : Type u} {A : Type v} [AddCommGroup A]
    (β : FaceField V A) (w x y z : V) :
    d2 β w x y z = β x y z - β w y z + β w x z - β w x y := rfl

theorem d1Alt_d0 {V : Type u} {A : Type v} [AddCommGroup A]
    (φ : V → A) (x y z : V) :
    d1Alt (fun a b => φ b - φ a) x y z = 0 := by
  simp [d1Alt]

theorem d2_d1Alt {V : Type u} {A : Type v} [AddCommGroup A]
    (α : EdgeField V A) (w x y z : V) :
    d2 (d1Alt α) w x y z = 0 := by
  simp only [d2, d1Alt]
  abel

theorem d2_d1Alt_eq {V : Type u} {A : Type v} [AddCommGroup A]
    (α : EdgeField V A) :
    d2 (d1Alt α) = 0 := by
  funext w x y z
  exact d2_d1Alt α w x y z

/-- Sum a face field over a finite mesh.  The mesh labels remain abstract; a
physical model supplies the finite face type and any orientation convention. -/
def faceSum {F : Type u} {A : Type v} [Fintype F] [AddCommMonoid A]
    (β : F → A) : A := ∑ f, β f

theorem faceSum_congr {F : Type u} {A : Type v} [Fintype F] [AddCommMonoid A]
    {β γ : F → A} (h : ∀ f, β f = γ f) :
    faceSum β = faceSum γ := by
  unfold faceSum
  exact Finset.sum_congr rfl (fun f _ => h f)

end HigherCochain

/-! Physics vocabulary aliases for the alternating finite complex. -/

namespace GaugeTheory
abbrev AlternatingCurvature {V : Type u} {A : Type v} [AddCommGroup A] :=
  HigherCochain.d1Alt (V := V) (A := A)
abbrev BianchiFace {V : Type u} {A : Type v} [AddCommGroup A] :=
  HigherCochain.d2 (V := V) (A := A)
end GaugeTheory

namespace Condensed
abbrev BerryTriangle {V : Type u} {A : Type v} [AddCommGroup A] :=
  HigherCochain.d1Alt (V := V) (A := A)
abbrev BerryBianchiFace {V : Type u} {A : Type v} [AddCommGroup A] :=
  HigherCochain.d2 (V := V) (A := A)
end Condensed

namespace Classical
abbrev FluidCurlFace {V : Type u} {A : Type v} [AddCommGroup A] :=
  HigherCochain.d1Alt (V := V) (A := A)
end Classical

namespace StatMech
abbrev LatticeFaceFlux {F : Type u} {A : Type v} [Fintype F] [AddCommMonoid A] :=
  HigherCochain.faceSum (F := F) (A := A)
end StatMech

end LeanPhy.Mathematics
