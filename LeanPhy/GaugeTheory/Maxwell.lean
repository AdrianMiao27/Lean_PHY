import LeanPhy.Mathematics.Derivation
import LeanPhy.Mathematics.Exterior
import LeanPhy.Mathematics.DiscreteCochain
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LeanPhy.GaugeTheory

open LeanPhy.Mathematics

/-! ## Discrete/finite-difference Maxwell adapter

The continuous-looking component API below has a direct combinatorial sibling:
an edge potential on an arbitrary vertex set has a triangle curvature `d1`.
The cochain theorem proves gauge invariance and `d1 d0 = 0` without assuming a
coordinate chart or a continuum limit. -/

def discreteFieldStrength {V A : Type} [AddCommGroup A]
    (potential : LeanPhy.Mathematics.DiscreteCochain.Cochain1 V A)
    (x y z : V) : A :=
  LeanPhy.Mathematics.DiscreteCochain.d1 potential x y z

theorem discreteFieldStrength_gauge_invariant {V A : Type} [AddCommGroup A]
    (potential : LeanPhy.Mathematics.DiscreteCochain.Cochain1 V A)
    (chi : LeanPhy.Mathematics.DiscreteCochain.Cochain0 V A)
    (x y z : V) :
    discreteFieldStrength
      (LeanPhy.Mathematics.DiscreteCochain.gaugeShift potential chi) x y z =
      discreteFieldStrength potential x y z := by
  exact LeanPhy.Mathematics.DiscreteCochain.d1_gaugeShift potential chi x y z

theorem discretePotentialFieldStrength_zero {V A : Type} [AddCommGroup A]
    (chi : LeanPhy.Mathematics.DiscreteCochain.Cochain0 V A)
    (x y z : V) :
    discreteFieldStrength
      (fun i j => LeanPhy.Mathematics.DiscreteCochain.d0 chi i j) x y z = 0 := by
  exact LeanPhy.Mathematics.DiscreteCochain.d1_d0 chi x y z

/-- The Abelian field strength built from a potential and commuting directional
  derivations: `F_mu nu = D_mu A_nu - D_nu A_mu`.  This is the algebraic
  Maxwell interface; coordinates, smoothness and boundary conditions stay
  outside the definition. -/
def abelianFieldStrength {R : Type} {A : Type}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin 4 → PhysicsDerivation R A) (potential : Fin 4 → A)
    (mu nu : Fin 4) : A :=
  D mu (potential nu) - D nu (potential mu)

/-! The Maxwell adapter is definitionally the shared finite exterior derivative.
This bridge lets downstream developments use either the familiar component
notation or the reusable `Form1`/`Form2` interface. -/
theorem abelianFieldStrength_eq_exteriorDerivative1 {R : Type} {A : Type}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin 4 → PhysicsDerivation R A) (potential : Fin 4 → A)
    (mu nu : Fin 4) :
    abelianFieldStrength D potential mu nu =
      exteriorDerivative1 D (⟨potential⟩ : Form1 4 A) mu nu := rfl

theorem abelianFieldStrength_bianchi_via_exterior {R : Type} {A : Type}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin 4 → PhysicsDerivation R A) (potential : Fin 4 → A)
    (hcomm : ∀ i j x, D i (D j x) = D j (D i x))
    (mu nu rho : Fin 4) :
    D mu (abelianFieldStrength D potential nu rho) +
        D nu (abelianFieldStrength D potential rho mu) +
        D rho (abelianFieldStrength D potential mu nu) = 0 := by
  have h := exteriorDerivative2_exteriorDerivative1 D
    (⟨potential⟩ : Form1 4 A) hcomm mu nu rho
  simpa [abelianFieldStrength, exteriorDerivative1, exteriorDerivative2] using h

/-- Abelian field strength is antisymmetric. -/
theorem abelianFieldStrength_antisym {R : Type} {A : Type}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin 4 → PhysicsDerivation R A) (potential : Fin 4 → A)
    (mu nu : Fin 4) :
    abelianFieldStrength D potential mu nu =
      -abelianFieldStrength D potential nu mu := by
  simp only [abelianFieldStrength]
  ring

/-- Commuting derivations act in either order on a scalar field. -/
theorem commuting_derivations_apply {R : Type} {A : Type}
    [CommRing R] [CommRing A] [Algebra R A]
    (D E : PhysicsDerivation R A)
    (hcomm : derivationCommutator D E = 0) (f : A) :
    D (E f) = E (D f) := by
  have h := congrArg (fun X : PhysicsDerivation R A => X f) hcomm
  have hz : D (E f) - E (D f) = 0 := by
    simpa [derivationCommutator_apply] using h
  exact sub_eq_zero.mp hz

/-- Gauge transformation `A_mu -> A_mu + D_mu chi` leaves the Abelian field
strength unchanged whenever the directional derivations commute. -/
theorem abelianFieldStrength_gauge_invariant {R : Type} {A : Type}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin 4 → PhysicsDerivation R A) (potential : Fin 4 → A)
    (chi : A) (hcomm : ∀ mu nu, derivationCommutator (D mu) (D nu) = 0)
    (mu nu : Fin 4) :
    abelianFieldStrength D (fun k => potential k + D k chi) mu nu =
      abelianFieldStrength D potential mu nu := by
  unfold abelianFieldStrength
  have hmn := commuting_derivations_apply (D mu) (D nu) (hcomm mu nu) chi
  have hnm := commuting_derivations_apply (D nu) (D mu) (hcomm nu mu) chi
  rw [map_add, map_add]
  rw [hmn]
  ring

/-- The cyclic Bianchi identity for the Abelian curvature. -/
theorem abelianFieldStrength_bianchi {R : Type} {A : Type}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin 4 → PhysicsDerivation R A) (potential : Fin 4 → A)
    (hcomm : ∀ mu nu, derivationCommutator (D mu) (D nu) = 0)
    (mu nu rho : Fin 4) :
    D mu (abelianFieldStrength D potential nu rho) +
        D nu (abelianFieldStrength D potential rho mu) +
        D rho (abelianFieldStrength D potential mu nu) = 0 := by
  unfold abelianFieldStrength
  have hmn := commuting_derivations_apply (D mu) (D nu) (hcomm mu nu) (potential rho)
  have hmr := commuting_derivations_apply (D mu) (D rho) (hcomm mu rho) (potential nu)
  have hnr := commuting_derivations_apply (D nu) (D rho) (hcomm nu rho) (potential mu)
  have hnm := commuting_derivations_apply (D nu) (D mu) (hcomm nu mu) (potential rho)
  have hrm := commuting_derivations_apply (D rho) (D mu) (hcomm rho mu) (potential nu)
  have hrn := commuting_derivations_apply (D rho) (D nu) (hcomm rho nu) (potential mu)
  rw [map_sub, map_sub, map_sub]
  rw [hmn, hmr, hnr, hnm, hrm, hrn]
  ring

end LeanPhy.GaugeTheory
