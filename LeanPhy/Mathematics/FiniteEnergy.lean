import Mathlib.Tactic
import LeanPhy.Mathematics.FiniteEvolution

/-!
# Finite energy stability and conservation

Hyperbolic PDEs, wave equations, Maxwell updates, lattice dynamics and finite
mode truncations are often validated by an energy estimate.  A one-step
residual bound is not enough: the numerical step must also supply an
amplification factor for the chosen energy.  This module records that fact in
a reusable Lean-style structure.

The state space is abstract on purpose.  A finite-difference, finite-element,
lattice or modal adapter supplies its state, step map and energy estimate; the
kernel then propagates the estimate to every finite number of steps.  Exact
energy conservation is represented by a factor-one certificate.  No
continuous energy identity, CFL theorem, well-posedness result, mesh
convergence or infinite-dimensional limit is inferred.
-/

namespace LeanPhy.Mathematics

universe u

/-- A finite numerical step with an explicit nonnegative energy and a
one-step amplification factor.  The factor is part of the certificate rather
than inferred from the name of the scheme. -/
structure FiniteEnergyStep (X : Type u) where
  step : X → X
  energy : X → ℝ
  energy_nonneg : ∀ x, 0 ≤ energy x
  factor : ℝ
  factor_nonneg : 0 ≤ factor
  one_step : ∀ x, energy (step x) ≤ factor * energy x

namespace FiniteEnergyStep

variable {X : Type u}

/-- Iterate the same finite step a natural number of times. -/
def iterate (S : FiniteEnergyStep X) : ℕ → X → X :=
  fun n x => Nat.rec x (fun _ y => S.step y) n

@[simp] theorem iterate_zero (S : FiniteEnergyStep X) (x : X) :
    S.iterate 0 x = x := rfl

@[simp] theorem iterate_succ (S : FiniteEnergyStep X) (n : ℕ) (x : X) :
    S.iterate (n + 1) x = S.step (S.iterate n x) := by
  rfl

/-- The one-step certificate propagates to an explicit finite-time energy
bound.  The exponent records every amplification factor and therefore cannot
be silently dropped by a downstream numerical adapter. -/
theorem iterate_energy_bound (S : FiniteEnergyStep X) (n : ℕ) (x : X) :
    S.energy (S.iterate n x) ≤ S.factor ^ n * S.energy x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [S.iterate_succ]
      calc
        S.energy (S.step (S.iterate n x)) ≤
            S.factor * S.energy (S.iterate n x) := S.one_step _
        _ ≤ S.factor * (S.factor ^ n * S.energy x) := by
          exact mul_le_mul_of_nonneg_left ih S.factor_nonneg
        _ = S.factor ^ (n + 1) * S.energy x := by ring

/-- If the supplied amplification factor is at most one, the finite-time
energy never exceeds its initial value. -/
theorem iterate_energy_nonincreasing (S : FiniteEnergyStep X)
    (hfactor : S.factor ≤ 1) (n : ℕ) (x : X) :
    S.energy (S.iterate n x) ≤ S.energy x := by
  have hp : S.factor ^ n ≤ 1 := pow_le_one₀ S.factor_nonneg hfactor
  have hE := S.iterate_energy_bound n x
  have hmul : S.factor ^ n * S.energy x ≤ 1 * S.energy x :=
    mul_le_mul_of_nonneg_right hp (S.energy_nonneg x)
  exact hE.trans (by simpa using hmul)

/-- A supplied exact one-step energy identity yields exact conservation at
every finite iterate. -/
theorem iterate_energy_eq_of_conserved (S : FiniteEnergyStep X)
    (hconserve : ∀ x, S.energy (S.step x) = S.energy x)
    (n : ℕ) (x : X) :
    S.energy (S.iterate n x) = S.energy x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [S.iterate_succ, hconserve, ih]

/-- Construct the factor-one form from an exact one-step conservation proof.
This constructor makes the proof obligation visible at the solver/adapter
boundary while exposing the resulting stability API to later users. -/
def ofConserved (step : X → X) (energy : X → ℝ)
    (energy_nonneg : ∀ x, 0 ≤ energy x)
    (hconserve : ∀ x, energy (step x) = energy x) :
    FiniteEnergyStep X where
  step := step
  energy := energy
  energy_nonneg := energy_nonneg
  factor := 1
  factor_nonneg := by norm_num
  one_step := by
    intro x
    rw [hconserve]
    simp

end FiniteEnergyStep

/-! A coupled evolution/energy adapter keeps the state-error ledger and the
energy ledger on the same step map.  Numerical PDE and truncated-field
adapters can therefore submit one object and expose both kinds of finite-time
guarantee without duplicating a stability proof. -/

structure FiniteEvolutionEnergyStep (X : Type u) [PseudoMetricSpace X] where
  evolution : FiniteEvolutionStep X
  energy : FiniteEnergyStep X
  step_eq : ∀ x, evolution.step x = energy.step x

namespace FiniteEvolutionEnergyStep

variable {X : Type u} [PseudoMetricSpace X]

theorem evolve_eq_iterate (C : FiniteEvolutionEnergyStep X)
    (n : ℕ) (x : X) :
    C.evolution.evolve n x = C.energy.iterate n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [C.evolution.evolve_succ, C.energy.iterate_succ, ih,
        C.step_eq]

theorem energy_bound (C : FiniteEvolutionEnergyStep X)
    (n : ℕ) (x : X) :
    C.energy.energy (C.evolution.evolve n x) ≤
      C.energy.factor ^ n * C.energy.energy x := by
  rw [C.evolve_eq_iterate]
  exact C.energy.iterate_energy_bound n x

theorem energy_nonincreasing (C : FiniteEvolutionEnergyStep X)
    (hfactor : C.energy.factor ≤ 1) (n : ℕ) (x : X) :
    C.energy.energy (C.evolution.evolve n x) ≤ C.energy.energy x := by
  rw [C.evolve_eq_iterate]
  exact C.energy.iterate_energy_nonincreasing hfactor n x

/-! The structure below is the reusable cross-ledger boundary.  Its
`trajectory` field contains initial and per-step residual certificates, while
the coupled object supplies the independent energy amplification factor. -/

structure EnergyTrajectoryCertificate
    (C : FiniteEvolutionEnergyStep X)
    (exact approximate : ℕ → X)
    (initialRadius : ℝ) (stepRadius : ℕ → ℝ)
    (initialState : X) where
  trajectory : C.evolution.TrajectoryCertificate
    exact approximate initialRadius stepRadius
  exact_initial : exact 0 = initialState

namespace EnergyTrajectoryCertificate

variable {C : FiniteEvolutionEnergyStep X}
variable {exact approximate : ℕ → X}
variable {initialRadius : ℝ} {stepRadius : ℕ → ℝ} {initialState : X}

theorem state_error
    (T : C.EnergyTrajectoryCertificate exact approximate
      initialRadius stepRadius initialState) (n : ℕ) :
    ErrorCertificate (exact n) (approximate n)
      (C.evolution.propagatedRadius initialRadius stepRadius n) :=
  T.trajectory.bound n

theorem exact_eq_evolve
    (T : C.EnergyTrajectoryCertificate exact approximate
      initialRadius stepRadius initialState) (n : ℕ) :
    exact n = C.evolution.evolve n initialState := by
  induction n with
  | zero => simpa [T.exact_initial]
  | succ n ih =>
      rw [T.trajectory.exact_step n, ih, C.evolution.evolve_succ]

theorem exact_energy_bound
    (T : C.EnergyTrajectoryCertificate exact approximate
      initialRadius stepRadius initialState) (n : ℕ) :
    C.energy.energy (exact n) ≤
      C.energy.factor ^ n * C.energy.energy initialState := by
  rw [T.exact_eq_evolve]
  exact C.energy_bound n initialState

theorem exact_energy_nonincreasing
    (T : C.EnergyTrajectoryCertificate exact approximate
      initialRadius stepRadius initialState)
    (hfactor : C.energy.factor ≤ 1) (n : ℕ) :
    C.energy.energy (exact n) ≤ C.energy.energy initialState := by
  rw [T.exact_eq_evolve]
  exact C.energy_nonincreasing hfactor n initialState

end EnergyTrajectoryCertificate

end FiniteEvolutionEnergyStep

/-! Physics-facing aliases.  They intentionally expose the same certificate
contract to different research adapters instead of duplicating stability
proofs for each field. -/

namespace Classical
abbrev FiniteWaveEnergyStep := FiniteEnergyStep
abbrev FiniteODEEnergyStep := FiniteEnergyStep
end Classical

namespace GaugeTheory
abbrev FiniteMaxwellEnergyStep := FiniteEnergyStep
abbrev FiniteLatticeGaugeEnergyStep := FiniteEnergyStep
end GaugeTheory

namespace FieldTheory
abbrev FiniteModeEnergyStep := FiniteEnergyStep
end FieldTheory

namespace Condensed
abbrev FiniteLatticeEnergyStep := FiniteEnergyStep
abbrev FiniteBdGEnergyStep := FiniteEnergyStep
end Condensed

namespace StatMech
abbrev FiniteDissipativeEnergyStep := FiniteEnergyStep
end StatMech

namespace Classical
abbrev FiniteStableEvolutionEnergyStep := FiniteEvolutionEnergyStep
end Classical

namespace FieldTheory
abbrev FiniteStableModeEvolution := FiniteEvolutionEnergyStep
end FieldTheory

namespace GaugeTheory
abbrev FiniteStableMaxwellEvolution := FiniteEvolutionEnergyStep
end GaugeTheory

namespace Condensed
abbrev FiniteStableLatticeEvolution := FiniteEvolutionEnergyStep
end Condensed

end LeanPhy.Mathematics
