import LeanPhy.Mathematics.FiniteProcess

/-!
# Constrained dynamics and symmetry reduction

Gauge fixing, constrained Hamiltonian systems, lattice symmetries and quantum
error models all share the same proof boundary: a transformation must preserve
the declared physical state predicate, observables must be insensitive to the
declared orbit relation, and an evolution must intertwine with the action.

This file supplies that boundary without choosing a particular gauge group,
constraint equation or quotient implementation.  A constraint is represented
by a proposition, so users can state equations, positivity conditions,
boundary conditions or a conjunction of them.  The library proves only the
consequences of the supplied preservation and equivariance fields; it does not
construct a gauge slice, assert that a quotient is a manifold, or identify
gauge-equivalent states with equal physical states by fiat.
-/

namespace LeanPhy.Mathematics

universe u v w

/-! ## Physical states and orbit equivalence -/

structure ConstrainedSymmetry (G : Type u) (S : Type v)
    [Group G] [MulAction G S] where
  /-- A model-level predicate, such as finite energy or a chosen domain. -/
  admissible : S → Prop
  /-- The constraint surface, including equations and side conditions. -/
  constrained : S → Prop
  admissible_preserved : ∀ (g : G) (s : S), admissible s → admissible (g • s)
  constrained_preserved : ∀ (g : G) (s : S), constrained s → constrained (g • s)

/-! A value-valued constraint is useful when a gauge condition transforms
covariantly.  The zero-fibre constructor below records that covariance and the
fact that zero is fixed; it then produces the proposition-valued interface
above.  This keeps Gauss, moment-map and BRST-style constraints from being
encoded as an unexplained predicate while preserving the same downstream API. -/

structure EquivariantConstraint (G : Type u) (S : Type v) (Q : Type w)
    [Group G] [MulAction G S] [MulAction G Q] [Zero Q] where
  value : S → Q
  equivariant : ∀ (g : G) (s : S), value (g • s) = g • value s
  zero_fixed : ∀ g : G, g • (0 : Q) = 0

namespace EquivariantConstraint

variable {G : Type u} {S : Type v} {Q : Type w}
  [Group G] [MulAction G S] [MulAction G Q] [Zero Q]

def satisfied (C : EquivariantConstraint G S Q) (s : S) : Prop :=
  C.value s = 0

theorem satisfied_preserved (C : EquivariantConstraint G S Q)
    (g : G) {s : S} (hs : C.satisfied s) : C.satisfied (g • s) := by
  change C.value (g • s) = 0
  change C.value s = 0 at hs
  rw [C.equivariant g s, hs, C.zero_fixed]

def toConstrainedSymmetry (C : EquivariantConstraint G S Q)
    (admissible : S → Prop)
    (admissible_preserved : ∀ (g : G) (s : S),
      admissible s → admissible (g • s)) :
    ConstrainedSymmetry G S where
  admissible := admissible
  constrained := C.satisfied
  admissible_preserved := admissible_preserved
  constrained_preserved := C.satisfied_preserved

end EquivariantConstraint

namespace ConstrainedSymmetry

variable {G : Type u} {S : Type v} [Group G] [MulAction G S]

def physical (X : ConstrainedSymmetry G S) (s : S) : Prop :=
  X.admissible s ∧ X.constrained s

theorem physical_preserved (X : ConstrainedSymmetry G S)
    (g : G) {s : S} (hs : X.physical s) : X.physical (g • s) := by
  exact ⟨X.admissible_preserved g s hs.1,
    X.constrained_preserved g s hs.2⟩

def orbitEquivalent (_X : ConstrainedSymmetry G S) (s t : S) : Prop :=
  ∃ g : G, g • s = t

theorem orbitEquivalent_refl (X : ConstrainedSymmetry G S) (s : S) :
    X.orbitEquivalent s s := by
  exact ⟨1, one_smul G s⟩

theorem orbitEquivalent_symm (X : ConstrainedSymmetry G S)
    {s t : S} (h : X.orbitEquivalent s t) : X.orbitEquivalent t s := by
  rcases h with ⟨g, rfl⟩
  refine ⟨g⁻¹, ?_⟩
  simp [smul_smul]

theorem orbitEquivalent_trans (X : ConstrainedSymmetry G S)
    {s t u : S} (hst : X.orbitEquivalent s t)
    (htu : X.orbitEquivalent t u) : X.orbitEquivalent s u := by
  rcases hst with ⟨g, hg⟩
  rcases htu with ⟨h, hh⟩
  refine ⟨h * g, ?_⟩
  rw [mul_smul, hg, hh]

theorem physical_of_orbitEquivalent (X : ConstrainedSymmetry G S)
    {s t : S} (hs : X.physical s) (h : X.orbitEquivalent s t) :
    X.physical t := by
  rcases h with ⟨g, rfl⟩
  exact X.physical_preserved g hs

/-! A quotient is exposed only for the declared physical states.  The
`Setoid` proof below is generated from the group action, so a downstream
development can use `Quotient` when it really wants reduced states without
silently assuming that arbitrary representatives are interchangeable. -/

abbrev PhysicalState (X : ConstrainedSymmetry G S) :=
  {s : S // X.physical s}

def physicalOrbitEquivalent (X : ConstrainedSymmetry G S)
    (s t : PhysicalState X) : Prop :=
  X.orbitEquivalent s.1 t.1

def physicalOrbitSetoid (X : ConstrainedSymmetry G S) :
    Setoid (PhysicalState X) where
  r := X.physicalOrbitEquivalent
  iseqv := by
    refine { refl := ?_, symm := ?_, trans := ?_ }
    · intro s
      exact ConstrainedSymmetry.orbitEquivalent_refl X s.1
    · intro s t h
      exact ConstrainedSymmetry.orbitEquivalent_symm X h
    · intro s t u hst htu
      exact ConstrainedSymmetry.orbitEquivalent_trans X hst htu

def physicalQuotient (X : ConstrainedSymmetry G S) : Type _ :=
  Quotient X.physicalOrbitSetoid

/-! ## Observables that descend to the declared physical orbit -/

structure ConstrainedObservable (X : ConstrainedSymmetry G S) (R : Type w) where
  eval : S → R
  invariant_on_physical : ∀ (g : G) (s : S), X.physical s →
    eval (g • s) = eval s

namespace ConstrainedObservable

variable {X : ConstrainedSymmetry G S} {R : Type w} {V : Type*}

def map (O : ConstrainedObservable X R) (f : R → V) :
    ConstrainedObservable X V where
  eval := fun s => f (O.eval s)
  invariant_on_physical := by
    intro g s hs
    exact congrArg f (O.invariant_on_physical g s hs)

/- The quotient lift is the formal version of “an observable is gauge
   invariant”.  The proof of well-definedness consumes the observable's
   invariance field and the representative's physical-state witness. -/
noncomputable def descend (O : ConstrainedObservable X R) :
    physicalQuotient X → R :=
  Quotient.lift (fun s : PhysicalState X => O.eval s.1) (by
    intro s t hst
    rcases hst with ⟨g, hg⟩
    calc
      O.eval s.1 = O.eval (g • s.1) :=
        (O.invariant_on_physical g s.1 s.2).symm
      _ = O.eval t.1 := by rw [hg])

@[simp] theorem descend_mk (O : ConstrainedObservable X R)
    (s : PhysicalState X) :
    O.descend (Quotient.mk _ s) = O.eval s.1 := rfl

theorem eval_eq_of_orbitEquivalent (O : ConstrainedObservable X R)
    {s t : S} (hs : X.physical s) (h : X.orbitEquivalent s t) :
    O.eval t = O.eval s := by
  rcases h with ⟨g, hg⟩
  calc
    O.eval t = O.eval (g • s) := by rw [hg]
    _ = O.eval s := O.invariant_on_physical g s hs

theorem eval_eq_of_orbitEquivalent_of_physical (O : ConstrainedObservable X R)
    {s t : S} (hs : X.physical s)
    (h : X.orbitEquivalent s t) : O.eval s = O.eval t := by
  exact (O.eval_eq_of_orbitEquivalent hs h).symm

end ConstrainedObservable

/-! ## Equivariant constrained dynamics -/

structure ConstrainedDynamics (X : ConstrainedSymmetry G S) where
  step : S → S
  preserves_physical : ∀ s, X.physical s → X.physical (step s)
  equivariant : ∀ (g : G) (s : S), step (g • s) = g • step s

namespace ConstrainedDynamics

variable {X : ConstrainedSymmetry G S}

def toProcess (D : ConstrainedDynamics X) : Process S X.physical where
  toFun := D.step
  preserves := D.preserves_physical

def evolve (D : ConstrainedDynamics X) (n : Nat) (s : S) : S :=
  Process.iterate D.toProcess n s

theorem evolve_zero (D : ConstrainedDynamics X) (s : S) :
    D.evolve 0 s = s := rfl

theorem evolve_succ (D : ConstrainedDynamics X) (n : Nat) (s : S) :
    D.evolve (n + 1) s = D.step (D.evolve n s) := rfl

theorem evolve_physical (D : ConstrainedDynamics X) (n : Nat)
    {s : S} (hs : X.physical s) : X.physical (D.evolve n s) :=
  Process.iterate_valid D.toProcess n hs

theorem evolve_equivariant (D : ConstrainedDynamics X) (n : Nat)
    (g : G) (s : S) :
    D.evolve n (g • s) = g • D.evolve n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [D.evolve_succ, D.evolve_succ, ih, D.equivariant]

theorem orbitEquivalent_evolve (D : ConstrainedDynamics X) (n : Nat)
    {s t : S} (h : X.orbitEquivalent s t) :
    X.orbitEquivalent (D.evolve n s) (D.evolve n t) := by
  rcases h with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  calc
    g • D.evolve n s = D.evolve n (g • s) :=
      (D.evolve_equivariant n g s).symm
    _ = D.evolve n t := by rw [hg]

theorem observable_evolve_eq (D : ConstrainedDynamics X)
    (O : ConstrainedObservable X R) (n : Nat) {s t : S}
    (hs : X.physical s) (h : X.orbitEquivalent s t) :
    O.eval (D.evolve n t) = O.eval (D.evolve n s) := by
  exact O.eval_eq_of_orbitEquivalent (D.evolve_physical n hs)
    (D.orbitEquivalent_evolve n h)

end ConstrainedDynamics

end ConstrainedSymmetry

/-! Names used in common physics subfields.  They are aliases, so all domains
share the same preservation and quotient-facing theorems. -/

namespace GaugeTheory
abbrev ConstraintSystem (G : Type u) (S : Type v)
    [Group G] [MulAction G S] := ConstrainedSymmetry G S
abbrev GaugeInvariantObservable (G : Type u) (S : Type v)
    [Group G] [MulAction G S]
    (X : ConstrainedSymmetry G S) (R : Type w) :=
  ConstrainedSymmetry.ConstrainedObservable X R
abbrev GaugeEquivariantDynamics (G : Type u) (S : Type v)
    [Group G] [MulAction G S] (X : ConstrainedSymmetry G S) :=
  ConstrainedSymmetry.ConstrainedDynamics X
end GaugeTheory

namespace Classical
abbrev ConstrainedHamiltonianSystem (G : Type u) (S : Type v)
    [Group G] [MulAction G S] := ConstrainedSymmetry G S
abbrev DiracObservable (G : Type u) (S : Type v)
    [Group G] [MulAction G S]
    (X : ConstrainedSymmetry G S) (R : Type w) :=
  ConstrainedSymmetry.ConstrainedObservable X R
end Classical

namespace Quantum
abbrev PhysicalSymmetrySystem (G : Type u) (S : Type v)
    [Group G] [MulAction G S] := ConstrainedSymmetry G S
abbrev SymmetryObservable (G : Type u) (S : Type v)
    [Group G] [MulAction G S]
    (X : ConstrainedSymmetry G S) (R : Type w) :=
  ConstrainedSymmetry.ConstrainedObservable X R
end Quantum

end LeanPhy.Mathematics
