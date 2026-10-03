import LeanPhy.Minimal
import Mathlib.Tactic

/-!
# Public regression for parameterised models

This is an API regression for a family of finite evolutions.  The proof uses
only the shared parameterised contracts, so a client can replace the scalar
family by a quantum coupling, temperature, lattice spacing, or truncation
index without changing the downstream finite-time theorems.
-/

namespace LeanPhy.Examples.ParametricModel

open LeanPhy.Mathematics

abbrev identityFamily : ParametricModel Nat ℝ where
  State := ℝ
  valid := fun _ _ => True
  step := fun _ => {
    toFun := id
    preserves := by intro _ _; trivial }
  Observable := Unit
  evaluate := fun _ x _ => x

abbrev shiftedFamily : ParametricModel Nat ℝ where
  State := ℝ
  valid := fun _ _ => True
  step := fun p => {
    toFun := fun x => x + p
    preserves := by intro _ _; trivial }
  Observable := Unit
  evaluate := fun _ x _ => x

noncomputable def identityMap : ParametricModelMap identityFamily identityFamily where
  state := fun _ => StateMap.identity ℝ (fun _ => True)
  pullback := fun _ => id
  step_commutes := by intro p s _; rfl
  evaluate_commutes := by intro p s _ o; rfl

theorem identity_trajectory (p : Nat) (n : Nat) (x : ℝ) :
    identityFamily.evolve p n x = x := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [ParametricModel.evolve_succ] using ih

theorem identity_map_trajectory (p : Nat) (n : Nat) (x : ℝ) :
    (identityMap.modelAt p).state (identityFamily.evolve p n x) =
      identityFamily.evolve p n ((identityMap.modelAt p).state x) :=
  ParametricModelMap.iterate_commutes identityMap p n x (by trivial)

noncomputable def shiftedApproximation :
    ParametricApproximateMap identityFamily shiftedFamily where
  modelAt := fun p => {
    state := StateMap.identity ℝ (fun _ => True)
    stateModulus := 1
    stateModulus_nonneg := by norm_num
    state_lipschitz := by
      intro x y
      dsimp [ParametricModel.modelAt, StateMap.identity] at x y ⊢
      simpa [mul_one] using (le_rfl : dist x y ≤ dist x y)
    pullback := id
    modulus := 1
    modulus_nonneg := by norm_num
    target_lipschitz := by
      intro x y
      dsimp [ParametricModel.modelAt, shiftedFamily] at x y ⊢
      rw [dist_eq_norm, dist_eq_norm]
      have h : (x + (p : ℝ)) - (y + (p : ℝ)) = x - y := by ring
      rw [h]
      simpa [mul_one] using (le_rfl : ‖x - y‖ ≤ ‖x - y‖)
    oneStepRadius := fun _ => p
    oneStepRadius_nonneg := by intro _; positivity
    oneStep_error := by
      intro x _
      refine ⟨by positivity, ?_⟩
      simp [ParametricModel.modelAt, identityFamily, shiftedFamily,
        StateMap.identity, dist_eq_norm, abs_of_nonneg]
    observableRadius := fun _ _ => 0
    observableRadius_nonneg := by intro _ _; norm_num
    observable_error := by
      intro x _ _
      exact ErrorCertificate.of_eq rfl
    observableModulus := fun _ => 1
    observableModulus_nonneg := by intro _; norm_num
    observable_lipschitz := by
      intro _
      exact { nonneg := by norm_num
              bound := by
                intro x y
                dsimp [ParametricModel.modelAt, shiftedFamily] at x y ⊢
                simpa [mul_one] using (le_rfl : dist x y ≤ dist x y) }
  }

theorem shifted_family_distance (p : Nat) (n : Nat) (x : ℝ) :
    dist ((shiftedApproximation.modelAt p).state (identityFamily.evolve p n x))
      (shiftedFamily.evolve p n ((shiftedApproximation.modelAt p).state x)) ≤
      (shiftedApproximation.modelAt p).stateRadius x n :=
  ParametricApproximateMap.iterate_distance shiftedApproximation p n x (by trivial)

theorem shifted_family_observable (p : Nat) (n : Nat) (x : ℝ) :
    dist
      ((shiftedFamily.modelAt p).evaluate
        (shiftedFamily.evolve p n ((shiftedApproximation.modelAt p).state x)) Unit.unit)
      ((identityFamily.modelAt p).evaluate (identityFamily.evolve p n x) Unit.unit) ≤
      (shiftedApproximation.modelAt p).stateRadius x n := by
  have h := ParametricApproximateMap.evaluate_distance
    shiftedApproximation p n x (by trivial) Unit.unit
  simpa [shiftedApproximation, ParametricModel.modelAt] using h

theorem reindex_preserves_identity (q : Fin 3) (n : Nat) (x : ℝ) :
    (identityFamily.reindex (fun _ : Fin 3 => 0)).evolve q n x = x := by
  change identityFamily.evolve 0 n x = x
  exact identity_trajectory 0 n x

/- A genuinely uniform parameter certificate over a finite coupling range.
   The pointwise `shiftedApproximation` is indexed by all naturals, so no
   common finite bound exists there.  Reindexing to `Fin 3` makes the range
   explicit; the proof below still has to supply the common bound rather than
   getting one from the parameter type automatically. -/
noncomputable def finiteShiftApprox :
    ParametricApproximateMap (identityFamily.reindex (fun p : Fin 3 => p.val))
      (shiftedFamily.reindex (fun p : Fin 3 => p.val)) :=
  shiftedApproximation.reindex (fun p : Fin 3 => p.val)

private theorem sum_two_le (n : Nat) :
    (∑ _k ∈ Finset.range n, (2 : ℝ)) ≤ 2 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Finset.sum_range_succ, Finset.sum_const_zero, Nat.cast_add,
        Nat.cast_one]
      nlinarith

private theorem finiteShift_state_bound (p : Fin 3) (s : ℝ) (n : Nat) :
    (finiteShiftApprox.modelAt p).stateRadius s n ≤ 2 * n := by
  unfold finiteShiftApprox ParametricApproximateMap.reindex
  change (FiniteEvolutionStep.propagatedRadius
    (FiniteEvolutionStep.mk (X := ℝ) (fun x => x + (p.val : ℝ)) 1 (by norm_num) (by
      intro x y
      simpa using (le_rfl : dist x y ≤ dist x y)))
    0 (fun _ => (p.val : ℝ)) n) ≤ 2 * n
  have hp : (p.val : ℝ) ≤ 2 := by
    have hpNat : p.val ≤ 2 := by omega
    exact_mod_cast hpNat
  have hp0 : (0 : ℝ) ≤ p.val := by positivity
  have hsum := FiniteEvolutionStep.propagatedRadius_le_add_sum
    (S := FiniteEvolutionStep.mk (X := ℝ) (fun x => x + (p.val : ℝ)) 1 (by norm_num) (by
      intro x y
      simpa using (le_rfl : dist x y ≤ dist x y)))
    (initial := (0 : ℝ)) (stepRadius := fun _ => (p.val : ℝ))
    (hi := by norm_num) (hs := by intro k; exact hp0)
    (hcontract := by norm_num) n
  simp only [zero_add, one_mul] at hsum
  calc
    _ ≤ ∑ k ∈ Finset.range n, (p.val : ℝ) := hsum
    _ ≤ ∑ _k ∈ Finset.range n, (2 : ℝ) := by
      gcongr with k hk
    _ ≤ 2 * n := sum_two_le n

def finiteShiftUniformBudget :
    ParametricApproximateMap.UniformBudget finiteShiftApprox where
  stateRadius := fun n => 2 * n
  stateRadius_nonneg := by intro n; positivity
  state_bound := by
    intro p s n
    exact finiteShift_state_bound p s n
  observableRadius := fun _ n => 2 * n
  observableRadius_nonneg := by intro o n; positivity
  observable_bound := by
    intro p s n o
    change (finiteShiftApprox.modelAt p).observableModulus o *
        (finiteShiftApprox.modelAt p).stateRadius s n +
        (finiteShiftApprox.modelAt p).observableRadius
          ((identityFamily.reindex (fun p : Fin 3 => p.val)).evolve p n s) o ≤
      2 * n
    have hs := finiteShift_state_bound p s n
    simpa [finiteShiftApprox, ParametricApproximateMap.reindex,
      shiftedApproximation, ParametricModel.modelAt] using hs

theorem finite_shift_uniform_distance (p : Fin 3) (n : Nat) (x : ℝ) :
    dist ((finiteShiftApprox.modelAt p).state
      ((identityFamily.reindex (fun p : Fin 3 => p.val)).evolve p n x))
      ((shiftedFamily.reindex (fun p : Fin 3 => p.val)).evolve p n
        ((finiteShiftApprox.modelAt p).state x)) ≤ 2 * n :=
  finiteShiftUniformBudget.iterate_distance p n x (by trivial)

theorem finite_shift_uniform_observable (p : Fin 3) (n : Nat) (x : ℝ) (o : Unit) :
    dist
      (((shiftedFamily.reindex (fun p : Fin 3 => p.val)).modelAt p).evaluate
        (((shiftedFamily.reindex (fun p : Fin 3 => p.val)).evolve p n
          ((finiteShiftApprox.modelAt p).state x))) o)
      (((identityFamily.reindex (fun p : Fin 3 => p.val)).modelAt p).evaluate
        (((identityFamily.reindex (fun p : Fin 3 => p.val)).evolve p n x)) o) ≤ 2 * n := by
  have h := finiteShiftUniformBudget.evaluate_distance p n x (by trivial) o
  simpa [finiteShiftUniformBudget, finiteShiftApprox,
    ParametricApproximateMap.reindex,
    shiftedApproximation, ParametricModel.modelAt] using h

end LeanPhy.Examples.ParametricModel
