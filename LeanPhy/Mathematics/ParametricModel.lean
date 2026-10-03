import LeanPhy.Mathematics.Model
import LeanPhy.Mathematics.ApproximateModel

/-!
# Parameterised physical models

Most research models are not single endomorphisms.  A Hamiltonian depends on a
coupling, a Markov kernel on temperature, and a lattice model on its mesh
parameter.  This module gives those families one typed interface.  The
parameter itself carries no physical interpretation: assumptions about its
range, units, limits, or calibration remain ordinary Lean hypotheses or open
research obligations.

`ParametricModel` keeps the state and observable representations fixed while
allowing admissibility, evolution, and readout to depend on a parameter.  A
`ParametricModelMap` is a pointwise `ModelMap` whose composition and finite-time
laws are proved once here.  `ParametricApproximateMap` lifts the same idea to
the explicit finite error budget in `ApproximateModelMap`.
-/

namespace LeanPhy.Mathematics

universe u v w z

structure ParametricModel (P : Type w) (R : Type z) where
  State : Type u
  valid : P → State → Prop
  step : ∀ p, Process State (valid p)
  Observable : Type v
  evaluate : ∀ p : P, State → Observable → R

namespace ParametricModel

variable {P : Type w} {R : Type z}

def modelAt (M : ParametricModel P R) (p : P) : PhysicalModel R where
  State := M.State
  valid := M.valid p
  step := M.step p
  Observable := M.Observable
  evaluate := M.evaluate p

instance stateMetricAt (M : ParametricModel P R)
    [PseudoMetricSpace M.State] (p : P) :
    PseudoMetricSpace (M.modelAt p).State := by
  change PseudoMetricSpace M.State
  infer_instance

def evolve (M : ParametricModel P R) (p : P) (n : Nat) (s : M.State) : M.State :=
  Process.iterate (M.step p) n s

@[simp] theorem evolve_zero (M : ParametricModel P R) (p : P) (s : M.State) :
    M.evolve p 0 s = s := rfl

@[simp] theorem evolve_succ (M : ParametricModel P R) (p : P) (n : Nat)
    (s : M.State) : M.evolve p (n + 1) s = M.step p (M.evolve p n s) := rfl

theorem evolve_valid (M : ParametricModel P R) (p : P) (n : Nat)
    {s : M.State} (hs : M.valid p s) : M.valid p (M.evolve p n s) :=
  Process.iterate_valid (M.step p) n hs

theorem evolve_add (M : ParametricModel P R) (p : P) (m n : Nat)
    (s : M.State) :
    M.evolve p (m + n) s = M.evolve p m (M.evolve p n s) :=
  Process.iterate_add (M.step p) m n s

/- Reindexing is useful when a discretisation uses a derived parameter.  It
   changes only the parameter labels; the state, observable, and proof terms
   remain those of the original family. -/
def reindex {Q : Type*} (M : ParametricModel P R) (f : Q → P) :
    ParametricModel Q R where
  State := M.State
  valid := fun q => M.valid (f q)
  step := fun q => M.step (f q)
  Observable := M.Observable
  evaluate := fun q => M.evaluate (f q)

instance reindexStateMetric {Q : Type*} (M : ParametricModel P R)
    (f : Q → P) [PseudoMetricSpace M.State] :
    PseudoMetricSpace (M.reindex f).State := by
  change PseudoMetricSpace M.State
  infer_instance

@[simp] theorem reindex_modelAt {Q : Type*} (M : ParametricModel P R) (f : Q → P)
    (q : Q) : (M.reindex f).modelAt q = M.modelAt (f q) := rfl

end ParametricModel

structure ParametricModelMap {P : Type w} {R : Type z}
    (M N : ParametricModel P R) where
  state : ∀ p, StateMap M.State N.State (M.valid p) (N.valid p)
  pullback : ∀ p, N.Observable → M.Observable
  step_commutes : ∀ p s, M.valid p s →
    state p (M.step p s) = N.step p (state p s)
  evaluate_commutes : ∀ p s, M.valid p s → ∀ o,
    N.evaluate p (state p s) o = M.evaluate p s (pullback p o)

namespace ParametricModelMap

variable {P : Type w} {R : Type z}
variable {M N O : ParametricModel P R}

def modelAt (F : ParametricModelMap M N) (p : P) :
    ModelMap (M.modelAt p) (N.modelAt p) where
  state := F.state p
  pullback := F.pullback p
  step_commutes := F.step_commutes p
  evaluate_commutes := F.evaluate_commutes p

def identity (M : ParametricModel P R) : ParametricModelMap M M where
  state := fun p => StateMap.identity M.State (M.valid p)
  pullback := fun _ => id
  step_commutes := by intro p s _; rfl
  evaluate_commutes := by intro p s _ o; rfl

theorem map_valid (F : ParametricModelMap M N) (p : P)
    {s : M.State} (hs : M.valid p s) : N.valid p (F.state p s) :=
  (F.state p).preserves s hs

def compose (after : ParametricModelMap N O)
    (before : ParametricModelMap M N) : ParametricModelMap M O where
  state := fun p => StateMap.compose (after.state p) (before.state p)
  pullback := fun p o => before.pullback p (after.pullback p o)
  step_commutes := by
    intro p s hs
    change after.state p (before.state p (M.step p s)) =
      O.step p (after.state p (before.state p s))
    rw [before.step_commutes p s hs]
    exact after.step_commutes p (before.state p s)
      ((before.state p).preserves s hs)
  evaluate_commutes := by
    intro p s hs o
    change O.evaluate p (after.state p (before.state p s)) o =
      M.evaluate p s (before.pullback p (after.pullback p o))
    rw [after.evaluate_commutes p (before.state p s)
      ((before.state p).preserves s hs) o]
    exact before.evaluate_commutes p s hs (after.pullback p o)

theorem compose_state_apply (after : ParametricModelMap N O)
    (before : ParametricModelMap M N) (p : P) (s : M.State) :
    (compose after before).state p s = after.state p (before.state p s) := rfl

theorem compose_pullback_apply (after : ParametricModelMap N O)
    (before : ParametricModelMap M N) (p : P) (o : O.Observable) :
    (compose after before).pullback p o = before.pullback p (after.pullback p o) := rfl

theorem identity_left (F : ParametricModelMap M N) :
    compose (identity N) F = F := by
  cases F
  rfl

theorem identity_right (F : ParametricModelMap M N) :
    compose F (identity M) = F := by
  cases F
  rfl

theorem iterate_commutes (F : ParametricModelMap M N) (p : P) (n : Nat)
    (s : M.State) (hs : M.valid p s) :
    F.state p (M.evolve p n s) = N.evolve p n (F.state p s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [ParametricModel.evolve_succ, ParametricModel.evolve_succ]
      rw [F.step_commutes p (M.evolve p n s)
        (M.evolve_valid p n hs)]
      exact congrArg (N.step p) ih

theorem evaluate_after_iterate (F : ParametricModelMap M N) (p : P)
    (n : Nat) (s : M.State) (hs : M.valid p s) (o : N.Observable) :
    N.evaluate p (F.state p (M.evolve p n s)) o =
      M.evaluate p (M.evolve p n s) (F.pullback p o) :=
  F.evaluate_commutes p (M.evolve p n s) (M.evolve_valid p n hs) o

theorem trajectory_evaluate (F : ParametricModelMap M N) (p : P)
    (n : Nat) (s : M.State) (hs : M.valid p s) (o : N.Observable) :
    N.evaluate p (N.evolve p n (F.state p s)) o =
      M.evaluate p (M.evolve p n s) (F.pullback p o) := by
  rw [← F.iterate_commutes p n s hs]
  exact F.evaluate_after_iterate p n s hs o

theorem compose_assoc {X : ParametricModel P R}
    (third : ParametricModelMap O X)
    (second : ParametricModelMap N O)
    (first : ParametricModelMap M N) :
    compose third (compose second first) =
      compose (compose third second) first := by
  cases third
  cases second
  cases first
  rfl

end ParametricModelMap

/- A family of approximate maps reuses all quantitative checks from the single
   parameter instance.  The state and scalar representations are fixed by
   `ParametricModel`, so ordinary metric instances are sufficient. -/
structure ParametricApproximateMap {P : Type w} {R : Type z}
    (M N : ParametricModel P R)
    [PseudoMetricSpace M.State] [PseudoMetricSpace N.State]
    [PseudoMetricSpace R] where
  modelAt : ∀ p, ApproximateModelMap (M.modelAt p) (N.modelAt p)

namespace ParametricApproximateMap

variable {P : Type w} {R : Type z}
variable {M N O : ParametricModel P R}
variable [PseudoMetricSpace M.State] [PseudoMetricSpace N.State]
variable [PseudoMetricSpace O.State] [PseudoMetricSpace R]

def compose (after : ParametricApproximateMap N O)
    (before : ParametricApproximateMap M N) :
    ParametricApproximateMap M O where
  modelAt := fun p => ApproximateModelMap.compose (after.modelAt p) (before.modelAt p)

theorem iterate_distance (F : ParametricApproximateMap M N) (p : P)
    (n : Nat) (s : M.State) (hs : M.valid p s) :
    dist ((F.modelAt p).state (M.evolve p n s))
      ((N.evolve p n) ((F.modelAt p).state s)) ≤
      (F.modelAt p).stateRadius s n :=
  ApproximateModelMap.iterate_distance (F.modelAt p) n s hs

theorem evaluate_distance (F : ParametricApproximateMap M N) (p : P)
    (n : Nat) (s : M.State) (hs : M.valid p s) (o : N.Observable) :
    dist
      ((N.modelAt p).evaluate ((N.evolve p n) ((F.modelAt p).state s)) o)
      ((M.modelAt p).evaluate ((M.evolve p n) s) ((F.modelAt p).pullback o)) ≤
      (F.modelAt p).observableModulus o * (F.modelAt p).stateRadius s n +
        (F.modelAt p).observableRadius (M.evolve p n s) o :=
  ApproximateModelMap.evaluate_distance (F.modelAt p) n s hs o

def reindex {Q : Type*} (F : ParametricApproximateMap M N) (f : Q → P) :
    ParametricApproximateMap (M.reindex f) (N.reindex f) where
  modelAt := fun q => by
    simpa [ParametricModel.reindex_modelAt] using F.modelAt (f q)

/- A uniform budget is the finite-parameter analogue of a stability envelope.
   It is deliberately a separate certificate: a pointwise family of bounds
   does not imply a common bound without this supplied witness. -/
structure UniformBudget (F : ParametricApproximateMap M N) where
  stateRadius : Nat → ℝ
  stateRadius_nonneg : ∀ n, 0 ≤ stateRadius n
  state_bound : ∀ (p : P) (s : M.State) (n : Nat),
    (F.modelAt p).stateRadius s n ≤ stateRadius n
  observableRadius : N.Observable → Nat → ℝ
  observableRadius_nonneg : ∀ o n, 0 ≤ observableRadius o n
  observable_bound : ∀ (p : P) (s : M.State) (n : Nat) (o : N.Observable),
    (F.modelAt p).observableModulus o * (F.modelAt p).stateRadius s n +
        (F.modelAt p).observableRadius (M.evolve p n s) o ≤
      observableRadius o n

theorem UniformBudget.iterate_distance
    (B : UniformBudget F) (p : P) (n : Nat) (s : M.State)
    (hs : M.valid p s) :
    dist ((F.modelAt p).state (M.evolve p n s))
      ((N.evolve p n) ((F.modelAt p).state s)) ≤ B.stateRadius n := by
  exact (ParametricApproximateMap.iterate_distance F p n s hs).trans
    (B.state_bound p s n)

theorem UniformBudget.evaluate_distance
    (B : UniformBudget F) (p : P) (n : Nat) (s : M.State)
    (hs : M.valid p s) (o : N.Observable) :
    dist
      ((N.modelAt p).evaluate ((N.evolve p n) ((F.modelAt p).state s)) o)
      ((M.modelAt p).evaluate ((M.evolve p n) s) ((F.modelAt p).pullback o)) ≤
      B.observableRadius o n := by
  exact (ParametricApproximateMap.evaluate_distance F p n s hs o).trans
    (B.observable_bound p s n o)

end ParametricApproximateMap

end LeanPhy.Mathematics
