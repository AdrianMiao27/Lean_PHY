import LeanPhy.Mathematics.Model
import LeanPhy.Mathematics.FiniteEvolution

/-!
# Approximate model maps

`ModelMap` expresses an exact finite simulation.  Numerical meshes, truncated
Fock spaces and finite-volume models usually have a local residual instead.
`ApproximateModelMap` makes that residual, the stability modulus of the target
step, and the observable error explicit.  The kernel then propagates them to
any finite time horizon.  No limit, convergence rate, or physical equivalence
is inferred from this contract.
-/

namespace LeanPhy.Mathematics

universe u v w

structure ApproximateModelMap {R : Type w} (M N : PhysicalModel R)
    [PseudoMetricSpace M.State] [PseudoMetricSpace N.State]
    [PseudoMetricSpace R] where
  state : StateMap M.State N.State M.valid N.valid
  stateModulus : ℝ
  stateModulus_nonneg : 0 ≤ stateModulus
  state_lipschitz : ∀ x y,
    dist (state x) (state y) ≤ stateModulus * dist x y
  pullback : N.Observable → M.Observable
  modulus : ℝ
  modulus_nonneg : 0 ≤ modulus
  target_lipschitz : ∀ x y,
    dist (N.step x) (N.step y) ≤ modulus * dist x y
  oneStepRadius : M.State → ℝ
  oneStepRadius_nonneg : ∀ s, 0 ≤ oneStepRadius s
  oneStep_error : ∀ s, M.valid s →
    ErrorCertificate (state (M.step s)) (N.step (state s))
      (oneStepRadius s)
  observableRadius : M.State → N.Observable → ℝ
  observableRadius_nonneg : ∀ s o, 0 ≤ observableRadius s o
  observable_error : ∀ s, M.valid s → ∀ o,
    ErrorCertificate (N.evaluate (state s) o)
      (M.evaluate s (pullback o)) (observableRadius s o)
  observableModulus : N.Observable → ℝ
  observableModulus_nonneg : ∀ o, 0 ≤ observableModulus o
  observable_lipschitz : ∀ o,
    ErrorCertificate.LipschitzCertificate
      (fun x : N.State => N.evaluate x o) (observableModulus o)

namespace ApproximateModelMap

variable {R : Type w} {M N : PhysicalModel R}
variable [PseudoMetricSpace M.State] [PseudoMetricSpace N.State]
variable [PseudoMetricSpace R]

def stabilityStep (F : ApproximateModelMap M N) :
    FiniteEvolutionStep N.State where
  step := N.step
  modulus := F.modulus
  modulus_nonneg := F.modulus_nonneg
  lipschitz := F.target_lipschitz

def stateRadius (F : ApproximateModelMap M N) (s : M.State) (n : ℕ) : ℝ :=
  F.stabilityStep.propagatedRadius 0
    (fun k => F.oneStepRadius (M.evolve k s)) n

@[simp] theorem stateRadius_zero (F : ApproximateModelMap M N)
    (s : M.State) : F.stateRadius s 0 = 0 := rfl

theorem stateRadius_nonneg (F : ApproximateModelMap M N)
    (s : M.State) (n : ℕ) : 0 ≤ F.stateRadius s n := by
  unfold stateRadius
  exact F.stabilityStep.propagatedRadius_nonneg (by norm_num)
    (fun k => F.oneStepRadius_nonneg (M.evolve k s)) n

/-! Approximate adapters compose with an explicit error budget.  The state
   Lipschitz certificate is what transports the first adapter's local residual
   through the second state map; omitting it would make composition unsound. -/
def compose {O : PhysicalModel R}
    [PseudoMetricSpace O.State]
    (after : ApproximateModelMap N O)
    (before : ApproximateModelMap M N) : ApproximateModelMap M O where
  state := StateMap.compose after.state before.state
  stateModulus := after.stateModulus * before.stateModulus
  stateModulus_nonneg := mul_nonneg after.stateModulus_nonneg
    before.stateModulus_nonneg
  state_lipschitz := by
    intro x y
    change dist (after.state (before.state x))
      (after.state (before.state y)) ≤ _
    calc
      dist (after.state (before.state x))
          (after.state (before.state y)) ≤
          after.stateModulus * dist (before.state x) (before.state y) :=
        after.state_lipschitz _ _
      _ ≤ after.stateModulus *
          (before.stateModulus * dist x y) :=
        mul_le_mul_of_nonneg_left (before.state_lipschitz _ _)
          after.stateModulus_nonneg
      _ = (after.stateModulus * before.stateModulus) * dist x y := by ring
  pullback := fun o => before.pullback (after.pullback o)
  modulus := after.modulus
  modulus_nonneg := after.modulus_nonneg
  target_lipschitz := after.target_lipschitz
  oneStepRadius := fun s =>
    after.stateModulus * before.oneStepRadius s +
      after.oneStepRadius (before.state s)
  oneStepRadius_nonneg := by
    intro s
    exact add_nonneg
      (mul_nonneg after.stateModulus_nonneg (before.oneStepRadius_nonneg s))
      (after.oneStepRadius_nonneg (before.state s))
  oneStep_error := by
    intro s hs
    have hbefore := before.oneStep_error s hs
    have hstateLipschitz :
        ErrorCertificate.LipschitzCertificate after.state
          after.stateModulus :=
      { nonneg := after.stateModulus_nonneg
        bound := after.state_lipschitz }
    have htransport := ErrorCertificate.map hstateLipschitz hbefore
    have hafter := after.oneStep_error (before.state s)
      (before.state.preserves s hs)
    change ErrorCertificate
      (after.state (before.state (M.step s)))
      (O.step (after.state (before.state s))) _
    exact htransport.trans hafter
  observableRadius := fun s o =>
    after.observableRadius (before.state s) o +
      before.observableRadius s (after.pullback o)
  observableRadius_nonneg := by
    intro s o
    exact add_nonneg
      (after.observableRadius_nonneg (before.state s) o)
      (before.observableRadius_nonneg s (after.pullback o))
  observable_error := by
    intro s hs o
    have hafter := after.observable_error (before.state s)
      (before.state.preserves s hs) o
    have hbefore := before.observable_error s hs (after.pullback o)
    exact hafter.trans hbefore
  observableModulus := after.observableModulus
  observableModulus_nonneg := after.observableModulus_nonneg
  observable_lipschitz := after.observable_lipschitz

@[simp] theorem compose_state_apply {O : PhysicalModel R}
    [PseudoMetricSpace O.State]
    (after : ApproximateModelMap N O)
    (before : ApproximateModelMap M N) (s : M.State) :
    (compose after before).state s = after.state (before.state s) := rfl

@[simp] theorem compose_pullback_apply {O : PhysicalModel R}
    [PseudoMetricSpace O.State]
    (after : ApproximateModelMap N O)
    (before : ApproximateModelMap M N) (o : O.Observable) :
    (compose after before).pullback o = before.pullback (after.pullback o) := rfl

/- The exact target trajectory and the mapped source trajectory form a
   `TrajectoryCertificate`: the target recurrence is exact, while its local
   residual is the reversed one-step error supplied by the adapter. -/
theorem trajectoryCertificate (F : ApproximateModelMap M N)
    (s : M.State) (hs : M.valid s) :
    F.stabilityStep.TrajectoryCertificate
      (fun n => N.evolve n (F.state s))
      (fun n => F.state (M.evolve n s))
      0 (fun n => F.oneStepRadius (M.evolve n s)) where
  initial_nonneg := by norm_num
  step_nonneg := by intro n; exact F.oneStepRadius_nonneg _
  initial := ErrorCertificate.of_eq rfl
  exact_step := by intro n; rfl
  step := by
    intro n
    exact (F.oneStep_error (M.evolve n s)
      (M.evolve_valid n hs)).symmetric

theorem iterate_error (F : ApproximateModelMap M N)
    (n : ℕ) (s : M.State) (hs : M.valid s) :
    ErrorCertificate (F.state (M.evolve n s))
      (N.evolve n (F.state s)) (F.stateRadius s n) := by
  exact (F.trajectoryCertificate s hs).bound n |>.symmetric

theorem iterate_distance (F : ApproximateModelMap M N)
    (n : ℕ) (s : M.State) (hs : M.valid s) :
    dist (F.state (M.evolve n s))
      (N.evolve n (F.state s)) ≤ F.stateRadius s n :=
  (F.iterate_error n s hs).bound

theorem evaluate_error (F : ApproximateModelMap M N)
    (n : ℕ) (s : M.State) (hs : M.valid s) (o : N.Observable) :
    ErrorCertificate
      (N.evaluate (N.evolve n (F.state s)) o)
      (M.evaluate (M.evolve n s) (F.pullback o))
      (F.observableModulus o * F.stateRadius s n +
        F.observableRadius (M.evolve n s) o) := by
  have hstate := (F.iterate_error n s hs).symmetric
  have hobservable := ErrorCertificate.map
    (F.observable_lipschitz o) hstate
  have hlocal := F.observable_error (M.evolve n s)
    (M.evolve_valid n hs) o
  exact hobservable.trans hlocal

theorem evaluate_distance (F : ApproximateModelMap M N)
    (n : ℕ) (s : M.State) (hs : M.valid s) (o : N.Observable) :
    dist (N.evaluate (N.evolve n (F.state s)) o)
      (M.evaluate (M.evolve n s) (F.pullback o)) ≤
      F.observableModulus o * F.stateRadius s n +
        F.observableRadius (M.evolve n s) o :=
  (F.evaluate_error n s hs o).bound

/- A zero-radius approximate adapter can be upgraded to an exact dynamical
   adapter after separately supplying the zero observable error.  This is a
   useful boundary when a finite implementation is later proven exact. -/
def toExact (F : ApproximateModelMap M N)
    (hstate : ∀ s, F.oneStepRadius s = 0)
    (hobs : ∀ (s : M.State) (o : N.Observable),
      F.observableRadius s o = 0)
    (hN : ∀ x y : N.State, dist x y = 0 → x = y)
    (hR : ∀ x y : R, dist x y = 0 → x = y) : ModelMap M N where
  state := F.state
  pullback := F.pullback
  step_commutes := by
    intro s hs
    have h := F.oneStep_error s hs
    apply hN
    apply le_antisymm
    · simpa [hstate s] using h.bound
    · exact dist_nonneg
  evaluate_commutes := by
    intro s hs o
    have h := F.observable_error s hs o
    apply hR
    apply le_antisymm
    · simpa [hobs s o] using h.bound
    · exact dist_nonneg

end ApproximateModelMap

/- Domain names make the shared contract discoverable without creating
   separate theorem families. -/
namespace Quantum
abbrev TruncatedModelMap {R : Type*} (M N : PhysicalModel R)
    [PseudoMetricSpace M.State] [PseudoMetricSpace N.State]
    [PseudoMetricSpace R] := ApproximateModelMap M N
end Quantum

namespace FieldTheory
abbrev TruncatedModelMap {R : Type*} (M N : PhysicalModel R)
    [PseudoMetricSpace M.State] [PseudoMetricSpace N.State]
    [PseudoMetricSpace R] := ApproximateModelMap M N
end FieldTheory

namespace Condensed
abbrev DiscretizedModelMap {R : Type*} (M N : PhysicalModel R)
    [PseudoMetricSpace M.State] [PseudoMetricSpace N.State]
    [PseudoMetricSpace R] := ApproximateModelMap M N
end Condensed

namespace StatMech
abbrev FiniteVolumeModelMap {R : Type*} (M N : PhysicalModel R)
    [PseudoMetricSpace M.State] [PseudoMetricSpace N.State]
    [PseudoMetricSpace R] := ApproximateModelMap M N
end StatMech

namespace Classical
abbrev DiscretizedModelMap {R : Type*} (M N : PhysicalModel R)
    [PseudoMetricSpace M.State] [PseudoMetricSpace N.State]
    [PseudoMetricSpace R] := ApproximateModelMap M N
end Classical

end LeanPhy.Mathematics
