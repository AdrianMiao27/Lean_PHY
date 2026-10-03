import LeanPhy.Minimal
import Mathlib.Tactic

/-!
# Public regression for approximate model maps

This file exercises the reusable approximation contract with ordinary Lean
models.  The same construction applies to a finite-volume step, a truncated
Fock basis or a lattice Markov update; no domain-specific case is hidden in
the API.
-/

namespace LeanPhy.Examples.ApproximateModel

open LeanPhy.Mathematics

def identityProcess : Process ℝ (fun _ => True) where
  toFun := id
  preserves := by intro _ _; trivial

def shiftProcess : Process ℝ (fun _ => True) where
  toFun := fun x => x + 1
  preserves := by intro _ _; trivial

abbrev identityModel : PhysicalModel ℝ where
  State := ℝ
  valid := fun _ => True
  step := identityProcess
  Observable := Unit
  evaluate := fun x _ => x

abbrev shiftedModel : PhysicalModel ℝ where
  State := ℝ
  valid := fun _ => True
  step := shiftProcess
  Observable := Unit
  evaluate := fun x _ => x

noncomputable def shiftedAdapter : ApproximateModelMap identityModel shiftedModel where
  state := StateMap.identity ℝ (fun _ => True)
  stateModulus := 1
  stateModulus_nonneg := by norm_num
  state_lipschitz := by
    intro x y
    simpa [StateMap.identity] using (show dist x y ≤ dist x y from le_rfl)
  pullback := id
  modulus := 1
  modulus_nonneg := by norm_num
  target_lipschitz := by
    intro x y
    simpa [shiftedModel, shiftProcess] using
      (show dist x y ≤ dist x y from le_rfl)
  oneStepRadius := fun _ => 1
  oneStepRadius_nonneg := by intro _; norm_num
  oneStep_error := by
    intro x _
    refine ⟨by norm_num, ?_⟩
    simp [identityModel, shiftedModel, identityProcess, shiftProcess,
      StateMap.identity, dist_eq_norm]
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
            bound := by intro x y; simpa [shiftedModel] using
              (show dist x y ≤ dist x y from le_rfl) }

theorem shifted_state_radius_three (x : ℝ) :
    shiftedAdapter.stateRadius x 3 = 3 := by
  norm_num [ApproximateModelMap.stateRadius,
    ApproximateModelMap.stabilityStep, FiniteEvolutionStep.propagatedRadius,
    shiftedAdapter, identityModel, identityProcess]

theorem shifted_iterate_distance (x : ℝ) :
    dist (shiftedAdapter.state (identityModel.evolve 3 x))
      (shiftedModel.evolve 3 (shiftedAdapter.state x)) ≤ 3 := by
  calc
    dist (shiftedAdapter.state (identityModel.evolve 3 x))
        (shiftedModel.evolve 3 (shiftedAdapter.state x)) ≤
        shiftedAdapter.stateRadius x 3 :=
      ApproximateModelMap.iterate_distance (F := shiftedAdapter) 3 x (by trivial)
    _ = 3 := shifted_state_radius_three x

theorem shifted_observable_distance (x : ℝ) :
    dist (shiftedModel.evaluate (shiftedModel.evolve 3
      (shiftedAdapter.state x)) Unit.unit)
      (identityModel.evaluate (identityModel.evolve 3 x)
        (shiftedAdapter.pullback Unit.unit)) ≤ 3 := by
  have h := ApproximateModelMap.evaluate_distance (F := shiftedAdapter)
    3 x (by trivial) Unit.unit
  norm_num [shiftedAdapter, identityModel, shiftedModel, identityProcess,
    shiftProcess, ApproximateModelMap.stateRadius,
    ApproximateModelMap.stabilityStep, FiniteEvolutionStep.propagatedRadius] at h ⊢
  exact h

noncomputable def exactAdapter : ApproximateModelMap identityModel identityModel where
  state := StateMap.identity ℝ (fun _ => True)
  stateModulus := 1
  stateModulus_nonneg := by norm_num
  state_lipschitz := by
    intro x y
    simpa [StateMap.identity] using (show dist x y ≤ dist x y from le_rfl)
  pullback := id
  modulus := 1
  modulus_nonneg := by norm_num
  target_lipschitz := by
    intro x y
    simpa [identityModel, identityProcess] using
      (show dist x y ≤ dist x y from le_rfl)
  oneStepRadius := fun _ => 0
  oneStepRadius_nonneg := by intro _; norm_num
  oneStep_error := by intro x _; exact ErrorCertificate.of_eq rfl
  observableRadius := fun _ _ => 0
  observableRadius_nonneg := by intro _ _; norm_num
  observable_error := by intro x _ _; exact ErrorCertificate.of_eq rfl
  observableModulus := fun _ => 1
  observableModulus_nonneg := by intro _; norm_num
  observable_lipschitz := by
    intro _
    exact { nonneg := by norm_num
            bound := by intro x y; simpa [identityModel, identityProcess] using
              (show dist x y ≤ dist x y from le_rfl) }

noncomputable def exact_adapter_to_model_map :
    ModelMap identityModel identityModel := by
  exact exactAdapter.toExact (by intro; rfl) (by intro _ _; rfl)
    (by intro x y h; exact eq_of_dist_eq_zero h)
    (by intro x y h; exact eq_of_dist_eq_zero h)

theorem composed_radius_three (x : ℝ) :
    (ApproximateModelMap.compose shiftedAdapter exactAdapter).stateRadius x 3 = 3 := by
  norm_num [ApproximateModelMap.stateRadius,
    ApproximateModelMap.compose, ApproximateModelMap.stabilityStep,
    FiniteEvolutionStep.propagatedRadius, shiftedAdapter, exactAdapter,
    identityModel, identityProcess]

end LeanPhy.Examples.ApproximateModel
