import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

/-!
# Finite path transport and holonomy

This module is the common finite/combinatorial interface for several physics
domains.  A path has typed endpoints, so the same transport product can be
used for lattice gauge links, discrete Berry phases, graph connections and
finite-state parallel transport.  It deliberately proves only algebraic
facts: continuum limits, smoothness, path ordering for analytic connections
and topological quantisation remain explicit inputs at higher layers.

The endpoint-indexed path type makes a useful invariant visible in the API:
an open transport transforms by conjugation at its two endpoints, while a
closed transport transforms by conjugation at one base point.  Consequently
abelian holonomy, or any class function such as a trace, is gauge invariant.
-/

namespace LeanPhy.Mathematics

universe u

/-! A finite path is a sequence of abstract edges with typed endpoints. -/

inductive FinitePath (V : Type u) : V → V → Type u
  | refl (x : V) : FinitePath V x x
  | edge (x y z : V) : FinitePath V y z → FinitePath V x z

namespace FinitePath

variable {V : Type u}

/-! Concatenation is typed at the shared endpoint. -/

def comp {x y z : V} : FinitePath V x y → FinitePath V y z → FinitePath V x z
  | .refl _, q => q
  | .edge a b _ p, q => .edge a b _ (comp p q)

@[simp] theorem comp_refl {x y : V} (p : FinitePath V x y) :
    comp p (.refl y) = p := by
  induction p with
  | refl x => rfl
  | edge x y z p ih =>
      simp only [comp, ih]

@[simp] theorem refl_comp {x y : V} (p : FinitePath V x y) :
    comp (.refl x) p = p := rfl

theorem comp_assoc {w x y z : V}
    (p : FinitePath V w x) (q : FinitePath V x y) (r : FinitePath V y z) :
    comp (comp p q) r = comp p (comp q r) := by
  induction p with
  | refl x => rfl
  | edge w x z p ih =>
      simp only [comp, ih]

/-! A link field assigns a group element to every oriented edge. -/

def transport {G : Type u} [Group G] (link : V → V → G)
    {x y : V} : FinitePath V x y → G
  | .refl _ => 1
  | .edge a b _ p => link a b * transport link p

@[simp] theorem transport_refl {G : Type u} [Group G] (link : V → V → G) (x : V) :
    transport link (.refl x) = 1 := rfl

@[simp] theorem transport_edge {G : Type u} [Group G] (link : V → V → G)
    {x y z : V} (p : FinitePath V y z) :
    transport link (.edge x y z p) = link x y * transport link p := rfl

theorem transport_comp {G : Type u} [Group G] (link : V → V → G)
    {x y z : V} (p : FinitePath V x y) (q : FinitePath V y z) :
    transport link (comp p q) = transport link p * transport link q := by
  induction p with
  | refl x => simp [transport]
  | edge x y z p ih =>
      simp only [comp, transport, ih, mul_assoc]

/-! Gauge transformations of edge variables and their endpoint covariance. -/

def gaugeLink {G : Type u} [Group G] (g : V → G) (link : V → V → G)
    (x y : V) : G := g x * link x y * (g y)⁻¹

theorem transport_gauge {G : Type u} [Group G] (g : V → G) (link : V → V → G)
    {x y : V} (p : FinitePath V x y) :
    transport (gaugeLink g link) p =
      g x * transport link p * (g y)⁻¹ := by
  induction p with
  | refl x => simp [transport]
  | edge x y z p ih =>
      simp only [transport, gaugeLink, ih]
      group

theorem transport_gauge_open {G : Type u} [Group G] (g : V → G)
    (link : V → V → G) {x y : V} (p : FinitePath V x y) :
    transport (gaugeLink g link) p =
      g x * transport link p * (g y)⁻¹ :=
  transport_gauge g link p

theorem holonomy_gauge_conj {G : Type u} [Group G] (g : V → G)
    (link : V → V → G) {x : V} (p : FinitePath V x x) :
    transport (gaugeLink g link) p =
      g x * transport link p * (g x)⁻¹ :=
  transport_gauge g link p

section Invariants

variable {G R : Type u} [Group G]

theorem classFunction_transport_invariant (f : G → R)
    (hf : ∀ a b : G, f (a * b * a⁻¹) = f b)
    (g : V → G) (link : V → V → G) {x : V} (p : FinitePath V x x) :
    f (transport (gaugeLink g link) p) = f (transport link p) := by
  rw [holonomy_gauge_conj]
  exact hf (g x) (transport link p)

end Invariants

section Abelian

variable {G : Type u} [CommGroup G]

theorem abelian_transport_invariant (g : V → G) (link : V → V → G)
    {x : V} (p : FinitePath V x x) :
    transport (gaugeLink g link) p = transport link p := by
  rw [holonomy_gauge_conj]
  simp only [mul_inv_cancel_comm]

end Abelian

end FinitePath

/-! The additive version is useful for lattice fluxes, discrete one-forms and
angle-valued Berry phases.  It is kept next to the multiplicative interface so
the two conventions can be connected by a model-specific exponential map. -/

namespace AdditivePath

variable {V : Type u}

def transport {A : Type u} [AddCommGroup A] (link : V → V → A)
    {x y : V} : FinitePath V x y → A
  | .refl _ => 0
  | .edge a b _ p => link a b + transport link p

@[simp] theorem transport_refl {A : Type u} [AddCommGroup A]
    (link : V → V → A) (x : V) : transport link (.refl x) = 0 := rfl

theorem transport_comp {A : Type u} [AddCommGroup A] (link : V → V → A)
    {x y z : V} (p : FinitePath V x y) (q : FinitePath V y z) :
    transport link (FinitePath.comp p q) = transport link p + transport link q := by
  induction p with
  | refl x => simp [transport]
  | edge x y z p ih =>
      simp only [FinitePath.comp, transport, ih, add_assoc]

def gaugeLink {A : Type u} [AddCommGroup A] (g : V → A) (link : V → V → A)
    (x y : V) : A := g x + link x y - g y

theorem transport_gauge {A : Type u} [AddCommGroup A] (g : V → A)
    (link : V → V → A) {x y : V} (p : FinitePath V x y) :
    transport (gaugeLink g link) p =
      g x + transport link p - g y := by
  induction p with
  | refl x => simp [transport]
  | edge x y z p ih =>
      simp only [transport, gaugeLink, ih]
      abel

theorem closed_gauge_invariant {A : Type u} [AddCommGroup A] (g : V → A)
    (link : V → V → A) {x : V} (p : FinitePath V x x) :
    transport (gaugeLink g link) p = transport link p := by
  rw [transport_gauge]
  abel

end AdditivePath

/-! Generic names are convenient in domain adapters and tutorials. -/

abbrev Path := FinitePath

def holonomy {V G : Type} [Group G] (link : V → V → G)
    {x y : V} (p : FinitePath V x y) : G :=
  FinitePath.transport link p

theorem holonomy_comp {V G : Type} [Group G] (link : V → V → G)
    {x y z : V} (p : FinitePath V x y) (q : FinitePath V y z) :
    holonomy link (FinitePath.comp p q) = holonomy link p * holonomy link q :=
  FinitePath.transport_comp link p q

end LeanPhy.Mathematics
