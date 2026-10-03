import Mathlib.Algebra.Group.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import LeanPhy.Mathematics.Holonomy

/-!
# Lattice gauge theory: Wilson loops

Lattice gauge theory is where a gauge theory is finite and combinatorial, so the
algebra is decidable and kernel-checkable.  This module covers the lowest layer:
the parallel transport around one plaquette and the Wilson loop built from it.

The physical content is standard and small enough to be checked exactly.

- A link variable `U_i` transforms as `U_i -> g_i U_i g_{i+1}^{-1}`; the ordered
  product around a closed loop then transforms in the adjoint representation,
  `W -> g W g^{-1}` (theorem `loop_conj`).
- For an abelian gauge group the conjugation is trivial and the Wilson loop is
  gauge invariant (`wilson_loop_invariant`); additively this is the statement
  that the plaquette flux is unchanged by a gauge transformation
  (`plaquette_flux_gauge_invariant`), with a concrete finite-field witness.
- Any representation of the gauge group respects the loop product (`loop_map`),
  so a class function of the loop, the shape every gauge-invariant observable
  takes, is automatically gauge invariant (`classFunction_invariant`).

Everything is a genuine kernel-checked statement over an abstract group or ring.
The nonabelian and continuum pieces (lattice action, strong-coupling expansion,
the continuum limit) are not attempted here; the group-level covariance proved
below is the input those constructions consume.
-/

namespace LeanPhy.GaugeTheory

open scoped BigOperators

/-- Parallel transport around a four-plaquette: the gauge field on the links of
one plaquette, with the link variable at position `i` and the gauge parameter `g`. -/
def gaugeTransform {G : Type} [Group G] (g U : Fin 4 → G) (i : Fin 4) : G :=
  g i * U i * (g (i + 1))⁻¹

/-- The ordered product of the four link variables around the loop, the group-valued
Wilson loop before taking a trace in a representation. -/
def loopProduct {G : Type} [Group G] (U : Fin 4 → G) : G := U 0 * U 1 * U 2 * U 3

/-- **Gauge covariance of the Wilson loop.**  Under a lattice gauge transformation
the loop product conjugates by the gauge parameter at the basepoint: the loop
transforms in the adjoint representation.  This is the lattice analogue of the
continuum statement that a Wilson loop is a gauge-invariant object once traced. -/
theorem loop_conj {G : Type} [Group G] (g U : Fin 4 → G) :
    loopProduct (gaugeTransform g U) = g 0 * loopProduct U * (g 0)⁻¹ := by
  simp only [loopProduct, gaugeTransform,
    show ((0:Fin 4)+1)=1 from rfl, show ((1:Fin 4)+1)=2 from rfl,
    show ((2:Fin 4)+1)=3 from rfl, show ((3:Fin 4)+1)=0 from rfl]
  group

section Abelian

variable {G : Type} [CommGroup G]

/-- For an abelian gauge group the adjoint action is trivial, so the Wilson loop is
gauge invariant.  This is the U(1) lattice-electromagnetism statement. -/
theorem wilson_loop_invariant (g U : Fin 4 → G) :
    loopProduct (gaugeTransform g U) = loopProduct U := by
  rw [loop_conj]
  simp only [mul_inv_cancel_comm]

end Abelian

section Representation

variable {G H : Type} [Group G] [Group H]

/-- A group homomorphism (a representation on a representation space) sends the
loop product of the image configuration to the image of the loop product, so a
representation cannot change the group-level loop relation. -/
theorem loop_map (rho : G →* H) (U : Fin 4 → G) :
    loopProduct (fun i => rho (U i)) = rho (loopProduct U) := by
  simp only [loopProduct, map_mul]

end Representation

section ClassFunction

variable {G : Type} [Group G] {R : Type}

/-- **Gauge invariance of any class function of the loop.**  Every gauge-invariant
observable built from a loop is a class function of it (a trace in some
representation, for instance).  Such an observable is invariant for free, because
the loop only changes by conjugation. -/
theorem classFunction_invariant (f : G → R) (hf : ∀ a b : G, f (a * b * a⁻¹) = f b)
    (g U : Fin 4 → G) :
    f (loopProduct (gaugeTransform g U)) = f (loopProduct U) := by
  have h : loopProduct (gaugeTransform g U) = g 0 * loopProduct U * (g 0)⁻¹ := loop_conj g U
  rw [h, hf]

end ClassFunction

section MatrixRepresentation

/-- The trace is a class function for a finite matrix representation.  The
invertibility hypothesis is explicit because a gauge transformation must be
an element of the matrix group, not an arbitrary square matrix. -/
theorem matrix_trace_conjugate {n : Type} [Fintype n] [DecidableEq n]
    (g W : Matrix n n ℂ) (hg : IsUnit g) :
    Matrix.trace (g * W * g⁻¹) = Matrix.trace W := by
  rw [Matrix.trace_mul_cycle]
  rw [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_mul_cancel g hg, Matrix.one_mul]

/-! The same result can be used as the matrix-valued class function in
Wilson-loop calculations.  No choice of Lie group or representation is
hidden in this theorem; those are supplied by the caller. -/

end MatrixRepresentation

section Additive

variable {A : Type} [AddCommGroup A]

/-- The additive (log) gauge transformation of a link, the finite-difference of the
scalar gauge parameter. -/
def fluxGauge (g U : Fin 4 → A) (i : Fin 4) : A := g i + U i - g (i + 1)

/-- The plaquette flux, the additive loop product. -/
def plaquetteFlux (U : Fin 4 → A) : A := U 0 + U 1 + U 2 + U 3

/-- The plaquette flux is gauge invariant: the two gauge-parameter endpoints
cancel because they are equal around a closed loop. -/
theorem plaquette_flux_gauge_invariant (g U : Fin 4 → A) :
    plaquetteFlux (fluxGauge g U) = plaquetteFlux U := by
  simp only [plaquetteFlux, fluxGauge,
    show ((0:Fin 4)+1)=1 from rfl, show ((1:Fin 4)+1)=2 from rfl,
    show ((2:Fin 4)+1)=3 from rfl, show ((3:Fin 4)+1)=0 from rfl]
  abel

/-- A concrete finite-field witness over `ZMod 7`: four unit links give the
plaquette flux `4 = 1 + 1 + 1 + 1`, computed by the kernel. -/
example : plaquetteFlux (fluxGauge (fun _ => (5:ZMod 7)) (fun _ => (1:ZMod 7))) = 4 := by
  decide

end Additive

section NonAbelianWitness

/-- The loop covariance is not vacuous: conjugation genuinely moves a loop in a
nonabelian group.  Here the 3-cycle `(0 1)(1 2)` conjugates the transposition `(0 1)` to
a different transposition, so the abelian invariance above is not a triviality. -/
example :
    (Equiv.swap (0:Fin 3) 1 * Equiv.swap 1 2) * Equiv.swap 0 1
        * (Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹ ≠ Equiv.swap (0:Fin 3) 1 := by
  decide

end NonAbelianWitness

/-! ## Generic finite-path adapter

The fixed four-link API above is kept for compatibility with existing lattice
examples.  The following definitions identify it with the endpoint-indexed
path interface, so larger graphs and differently shaped loops can reuse the
same transport and gauge-covariance theorems.
-/

def plaquettePath : LeanPhy.Mathematics.FinitePath (Fin 4) 0 0 :=
  .edge 0 1 0 (.edge 1 2 0 (.edge 2 3 0 (.edge 3 0 0 (.refl 0))))

def plaquetteLink {G : Type} [Group G] (U : Fin 4 → G) : Fin 4 → Fin 4 → G :=
  fun i _ => U i

theorem plaquette_transport_eq_loopProduct {G : Type} [Group G] (U : Fin 4 → G) :
    LeanPhy.Mathematics.FinitePath.transport (plaquetteLink U) plaquettePath =
      loopProduct U := by
  simp [LeanPhy.Mathematics.FinitePath.transport, plaquettePath,
    plaquetteLink, loopProduct]
  group

theorem plaquette_transport_gauge_covariant {G : Type} [Group G]
    (g U : Fin 4 → G) :
    LeanPhy.Mathematics.FinitePath.transport
        (LeanPhy.Mathematics.FinitePath.gaugeLink g (plaquetteLink U)) plaquettePath =
      g 0 * loopProduct U * (g 0)⁻¹ := by
  rw [LeanPhy.Mathematics.FinitePath.transport_gauge]
  rw [plaquette_transport_eq_loopProduct]

theorem plaquette_wilson_from_generic_classFunction {G R : Type} [Group G]
    (f : G → R) (hf : ∀ a b : G, f (a * b * a⁻¹) = f b)
    (g U : Fin 4 → G) :
    f (LeanPhy.Mathematics.FinitePath.transport
        (LeanPhy.Mathematics.FinitePath.gaugeLink g (plaquetteLink U)) plaquettePath) =
      f (loopProduct U) := by
  have h := LeanPhy.Mathematics.FinitePath.classFunction_transport_invariant
    f hf g (plaquetteLink U) plaquettePath
  simpa only [plaquette_transport_eq_loopProduct] using h

/-! The additive plaquette flux is also a direct instance of the generic
endpoint-indexed additive transport.  This is the bridge used by Abelian
Maxwell, discrete differential-form and angle-valued Berry adapters. -/

def plaquetteAdditiveLink {A : Type} [AddCommGroup A] (U : Fin 4 → A) :
    Fin 4 → Fin 4 → A := fun i _ => U i

theorem plaquette_additive_transport_eq_flux {A : Type} [AddCommGroup A]
    (U : Fin 4 → A) :
    LeanPhy.Mathematics.AdditivePath.transport
        (plaquetteAdditiveLink U) plaquettePath = plaquetteFlux U := by
  simp [LeanPhy.Mathematics.AdditivePath.transport, plaquettePath,
    plaquetteAdditiveLink, plaquetteFlux]
  abel

theorem plaquette_additive_transport_gauge_invariant {A : Type} [AddCommGroup A]
    (g U : Fin 4 → A) :
    LeanPhy.Mathematics.AdditivePath.transport
        (LeanPhy.Mathematics.AdditivePath.gaugeLink g (plaquetteAdditiveLink U))
        plaquettePath = plaquetteFlux U := by
  rw [LeanPhy.Mathematics.AdditivePath.closed_gauge_invariant]
  exact plaquette_additive_transport_eq_flux U

end LeanPhy.GaugeTheory
