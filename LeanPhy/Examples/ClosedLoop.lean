import LeanPhy.Examples.Oscillator
import LeanPhy.Mathematics.FinitePathReflection
import LeanPhy.Mathematics.FiniteEnergy
import LeanPhy.Mathematics.FiniteParabolic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Closed-loop prototype

This is a deliberately small end-to-end artifact.  A user can inspect one
finite oscillator statement, one stable evolution/energy certificate and one
finite Euclidean reflection certificate in a single imported module.  The
definitions are ordinary Lean structures and the conclusions are ordinary
theorems, so this is a workflow prototype rather than a second proof language.
-/

namespace LeanPhy.Examples.ClosedLoop

open LeanPhy.Mathematics
open LeanPhy.Examples
open scoped BigOperators

/-! A scalar contraction gives both a trajectory modulus and a quadratic
energy bound.  The same step map is stored in both structures. -/

noncomputable def contractionEnergy : FiniteEvolutionEnergyStep ℝ where
  evolution :=
    { step := fun x => x / 2
      modulus := 1 / 2
      modulus_nonneg := by norm_num
      lipschitz := by
        intro u v
        calc
          dist (u / 2) (v / 2) = dist u v / 2 := by
            rw [dist_eq_norm]
            calc
              ‖u / 2 - v / 2‖ = ‖(u - v) / 2‖ := by
                congr 1
                ring
              _ = ‖u - v‖ / ‖(2 : ℝ)‖ := by rw [norm_div]
              _ = dist u v / 2 := by
                rw [dist_eq_norm]
                norm_num
          _ = (1 / 2 : ℝ) * dist u v := by ring
          _ ≤ (1 / 2 : ℝ) * dist u v := le_rfl }
  energy :=
    { step := fun x => x / 2
      energy := fun x => x ^ 2
      energy_nonneg := by intro x; exact sq_nonneg x
      factor := 1 / 4
      factor_nonneg := by norm_num
      one_step := by
        intro x
        ring_nf
        exact le_rfl }
  step_eq := by intro x; rfl

theorem contraction_energy_bound (n : ℕ) (x : ℝ) :
    contractionEnergy.energy.energy
        (contractionEnergy.evolution.evolve n x) ≤
      contractionEnergy.energy.factor ^ n *
        contractionEnergy.energy.energy x :=
  contractionEnergy.energy_bound n x

/-! A concrete two-node finite-difference heat step.  Each row averages the
two nodes, so the generic positive-step API supplies the discrete maximum
principle and the explicit column-sum certificate supplies mass conservation.
This is the first non-abstract PDE-shaped model in the closed loop. -/

noncomputable def heatKernel : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

noncomputable def heatStep : FinitePositiveStep (Fin 2) where
  kernel := heatKernel
  nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [heatKernel]
  row_sum := by
    intro i
    fin_cases i <;> norm_num [heatKernel]

theorem heat_mass_certificate :
    FinitePositiveStep.MassConservationCertificate heatStep := by
  constructor
  intro j
  fin_cases j <;> norm_num [heatStep, heatKernel]

theorem heat_step_preserves_bounds (u : Fin 2 → ℝ)
    (lower upper : ℝ) (hlo : ∀ j, lower ≤ u j)
    (hhi : ∀ j, u j ≤ upper) :
    ∀ i, lower ≤ heatStep.step u i ∧ heatStep.step u i ≤ upper :=
  heatStep.step_bounds u lower upper hlo hhi

theorem heat_iterate_preserves_mass (u : Fin 2 → ℝ) (n : ℕ) :
    ∑ i, heatStep.iterate n u i = ∑ i, u i :=
  heatStep.iterate_sum_preserved heat_mass_certificate u n

/-! A two-state positive Euclidean weight and a swap reflection. -/

def pathWeights : Fin 2 → ℝ := fun i => if i = 0 then 1 else 2

noncomputable def positivePath : FinitePositivePathIntegral (Fin 2) where
  weight := pathWeights
  weight_nonneg := by
    intro i
    fin_cases i <;> norm_num [pathWeights]
  partition_pos := by norm_num [pathWeights]

def pathFeature : Fin 2 → Fin 2 → ℝ :=
  fun i a => if i = a then 1 else 0

def pathReflection : Equiv.Perm (Fin 2) := Equiv.swap 0 1

theorem pathReflection_involutive :
    ∀ i, pathReflection (pathReflection i) = i := by
  intro i
  fin_cases i <;> rfl

noncomputable def reflectionCertificate :
    FiniteWeightedReflectionCertificate (Fin 2) (Fin 2) :=
  FiniteWeightedReflectionCertificate.fromPath positivePath pathFeature
    pathReflection pathReflection_involutive

theorem reflection_positive (f : Fin 2 → ℝ) :
    0 ≤ reflectionCertificate.reflectedKernelQuadratic f :=
  reflectionCertificate.reflectedKernelQuadratic_nonneg f

/-! One bundle is enough for a client or a small adapter to carry the entire
prototype's proof obligations. -/

structure VerifiedPrototype where
  oscillator : truncN * truncAdag - truncAdag * truncN = truncAdag
  energy : ∀ (n : ℕ) (x : ℝ),
    contractionEnergy.energy.energy
        (contractionEnergy.evolution.evolve n x) ≤
      contractionEnergy.energy.factor ^ n *
        contractionEnergy.energy.energy x
  heat_bounds : ∀ (u : Fin 2 → ℝ) (lower upper : ℝ),
    (∀ j, lower ≤ u j) → (∀ j, u j ≤ upper) →
      ∀ i, lower ≤ heatStep.step u i ∧ heatStep.step u i ≤ upper
  heat_mass : ∀ (u : Fin 2 → ℝ) (n : ℕ),
    ∑ i, heatStep.iterate n u i = ∑ i, u i
  reflection : ∀ (f : Fin 2 → ℝ),
    0 ≤ reflectionCertificate.reflectedKernelQuadratic f

theorem verifiedPrototype : VerifiedPrototype where
  oscillator := truncN_ladder
  energy := contraction_energy_bound
  heat_bounds := heat_step_preserves_bounds
  heat_mass := heat_iterate_preserves_mass
  reflection := reflection_positive

end LeanPhy.Examples.ClosedLoop
