import LeanPhy.Mathematics.Exterior
import LeanPhy.Mathematics.DiscreteCochain

/-!
# Finite vorticity adapter

This file packages the algebraic part of a finite/discrete fluid calculation:
the vorticity of a velocity one-form is its exterior derivative.  Commuting
derivations then give the closedness identity `d(d u) = 0`.  No Navier--Stokes
equation, smoothness, boundary condition, Hodge decomposition or continuum
limit is inferred here; those are separate analysis and modelling inputs.
-/

namespace LeanPhy.Classical

open LeanPhy.Mathematics

universe u v

/-- Finite/discrete vorticity as the exterior derivative of a velocity one-form. -/
def vorticity {n : Nat} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → PhysicsDerivation R A) (velocity : Form1 n A) : Form2 n A :=
  exteriorDerivative1 D velocity

@[simp] theorem vorticity_apply {n : Nat} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → PhysicsDerivation R A) (velocity : Form1 n A)
    (i j : Fin n) :
    vorticity D velocity i j = D i (velocity j) - D j (velocity i) := rfl

/-- The finite/discrete vorticity is closed when the supplied derivatives commute. -/
theorem vorticity_closed {n : Nat} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → PhysicsDerivation R A) (velocity : Form1 n A)
    (hcomm : ∀ i j x, D i (D j x) = D j (D i x))
    (i j k : Fin n) :
    exteriorDerivative2 D (vorticity D velocity) i j k = 0 :=
  exteriorDerivative2_exteriorDerivative1 D velocity hcomm i j k

/-- Adding a discrete exact potential to velocity leaves its vorticity unchanged. -/
theorem vorticity_potential_shift {n : Nat} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → PhysicsDerivation R A) (velocity : Form1 n A) (χ : A)
    (hcomm : ∀ i j x, D i (D j x) = D j (D i x)) :
    vorticity D ⟨fun i => velocity i + D i χ⟩ = vorticity D velocity :=
  exteriorDerivative1_gauge_invariant D velocity χ hcomm

/-! A combinatorial sibling uses only edge values on an arbitrary finite graph.
It is useful for lattice fluids, network models and finite-difference tests
where no coordinate derivation has yet been introduced. -/

def discreteVorticity {V A : Type} [AddCommGroup A]
    (velocity : LeanPhy.Mathematics.DiscreteCochain.Cochain1 V A)
    (x y z : V) : A :=
  LeanPhy.Mathematics.DiscreteCochain.d1 velocity x y z

theorem discreteVorticity_potential_shift {V A : Type} [AddCommGroup A]
    (velocity : LeanPhy.Mathematics.DiscreteCochain.Cochain1 V A)
    (potential : LeanPhy.Mathematics.DiscreteCochain.Cochain0 V A)
    (x y z : V) :
    discreteVorticity
      (LeanPhy.Mathematics.DiscreteCochain.gaugeShift velocity potential) x y z =
      discreteVorticity velocity x y z := by
  exact LeanPhy.Mathematics.DiscreteCochain.d1_gaugeShift velocity potential x y z

end LeanPhy.Classical
