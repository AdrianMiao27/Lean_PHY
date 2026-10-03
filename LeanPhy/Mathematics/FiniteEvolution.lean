import LeanPhy.Mathematics.Approximation
import LeanPhy.Mathematics.CertifiedResidual
import Mathlib.Tactic

/-!
# Finite-step evolution and residual propagation

Time discretisations of a PDE, ODE, master equation or truncated field model
need a stability ledger.  A small residual at one step does not by itself
give a small error at a later time: the amplification modulus and the initial
error must also be recorded.  This module packages exactly those obligations.

The state space is intentionally abstract.  A concrete finite PDE, lattice
equation or quantum integrator supplies its step map and a Lipschitz bound;
the kernel then proves a finite discrete Grönwall estimate.  No existence,
regularity, convergence or continuum-time claim is hidden in the interface.
-/

namespace LeanPhy.Mathematics

universe u

variable {X : Type u} [PseudoMetricSpace X]

/-! A one-step stability certificate. -/

structure FiniteEvolutionStep (X : Type u) [PseudoMetricSpace X] where
  step : X → X
  modulus : ℝ
  modulus_nonneg : 0 ≤ modulus
  lipschitz : ∀ u v, dist (step u) (step v) ≤ modulus * dist u v

namespace FiniteEvolutionStep

variable (S : FiniteEvolutionStep X)

/-- The iterated finite step map.  The time variable is a natural number, so
this definition represents an explicitly finite time horizon. -/
def evolve (S : FiniteEvolutionStep X) : ℕ → X → X
  | 0, x => x
  | n + 1, x => S.step (S.evolve n x)

@[simp] theorem evolve_zero (x : X) : S.evolve 0 x = x := rfl

@[simp] theorem evolve_succ (n : ℕ) (x : X) :
    S.evolve (n + 1) x = S.step (S.evolve n x) := rfl

/-- The Lipschitz certificate exposed in the common approximation API. -/
def lipschitzCertificate :
    ErrorCertificate.LipschitzCertificate S.step S.modulus :=
  { nonneg := S.modulus_nonneg
    bound := S.lipschitz }

/-! A recursively defined error budget.  At each step the old error is
multiplied by the stability modulus and the newly certified step residual is
added. -/

def propagatedRadius (S : FiniteEvolutionStep X)
    (initial : ℝ) (stepRadius : ℕ → ℝ) : ℕ → ℝ
  | 0 => initial
  | n + 1 => S.modulus * S.propagatedRadius initial stepRadius n + stepRadius n

@[simp] theorem propagatedRadius_zero (initial : ℝ) (stepRadius : ℕ → ℝ) :
    S.propagatedRadius initial stepRadius 0 = initial := rfl

@[simp] theorem propagatedRadius_succ (initial : ℝ) (stepRadius : ℕ → ℝ)
    (n : ℕ) :
    S.propagatedRadius initial stepRadius (n + 1) =
      S.modulus * S.propagatedRadius initial stepRadius n + stepRadius n := rfl

theorem propagatedRadius_nonneg {initial : ℝ} {stepRadius : ℕ → ℝ}
    (hi : 0 ≤ initial) (hs : ∀ n, 0 ≤ stepRadius n) :
    ∀ n, 0 ≤ S.propagatedRadius initial stepRadius n := by
  intro n
  induction n with
  | zero => exact hi
  | succ n ih =>
      simp only [propagatedRadius_succ]
      exact add_nonneg (mul_nonneg S.modulus_nonneg ih) (hs n)

theorem propagatedRadius_zero_steps {initial : ℝ} (n : ℕ) :
    S.propagatedRadius initial (fun _ => 0) n = S.modulus ^ n * initial := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [S.propagatedRadius_succ, ih]
      simp only [Pi.zero_apply, add_zero, pow_succ]
      ring

/-! A trajectory certificate keeps the exact recurrence and the approximate
one-step residual separate.  This makes a missing equation or missing error
bound visible at elaboration time. -/

structure TrajectoryCertificate
    (exact approximate : ℕ → X)
    (initialRadius : ℝ) (stepRadius : ℕ → ℝ) where
  initial_nonneg : 0 ≤ initialRadius
  step_nonneg : ∀ n, 0 ≤ stepRadius n
  initial : ErrorCertificate (exact 0) (approximate 0) initialRadius
  exact_step : ∀ n, exact (n + 1) = S.step (exact n)
  step : ∀ n,
    ErrorCertificate (S.step (approximate n)) (approximate (n + 1))
      (stepRadius n)

namespace TrajectoryCertificate

variable {S}
variable {exact approximate : ℕ → X}
variable {initialRadius : ℝ} {stepRadius : ℕ → ℝ}

theorem bound
    (C : S.TrajectoryCertificate exact approximate initialRadius stepRadius)
    (n : ℕ) :
    ErrorCertificate (exact n) (approximate n)
      (S.propagatedRadius initialRadius stepRadius n) := by
  induction n with
  | zero =>
      simpa using C.initial
  | succ n ih =>
      have hprop :
          ErrorCertificate (S.step (exact n)) (S.step (approximate n))
            (S.modulus * S.propagatedRadius initialRadius stepRadius n) :=
        ErrorCertificate.map S.lipschitzCertificate ih
      have hnext := hprop.trans (C.step n)
      rw [C.exact_step n]
      simpa [S.propagatedRadius_succ] using hnext

theorem finiteApproximation
    (C : S.TrajectoryCertificate exact approximate initialRadius stepRadius)
    (n : ℕ) :
    FiniteApproximation (exact n) (approximate n)
      (S.propagatedRadius initialRadius stepRadius n) :=
  ⟨C.bound n⟩

end TrajectoryCertificate

/-! If the step is a contraction/non-expansive map, the recursively generated
budget is bounded by the initial error plus the sum of all local residuals.
This is the finite form used for stable heat, diffusion and dissipative RG
iterations. -/

theorem propagatedRadius_le_add_sum
    {initial : ℝ} {stepRadius : ℕ → ℝ}
    (hi : 0 ≤ initial) (hs : ∀ n, 0 ≤ stepRadius n)
    (hcontract : S.modulus ≤ 1) (n : ℕ) :
    S.propagatedRadius initial stepRadius n ≤
      initial + ∑ k ∈ Finset.range n, stepRadius k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev_nonneg := S.propagatedRadius_nonneg hi hs n
      have hmul :
          S.modulus * S.propagatedRadius initial stepRadius n ≤
            S.propagatedRadius initial stepRadius n := by
        nlinarith
      rw [S.propagatedRadius_succ]
      calc
        S.modulus * S.propagatedRadius initial stepRadius n + stepRadius n ≤
            S.propagatedRadius initial stepRadius n + stepRadius n :=
          by nlinarith [hmul]
        _ ≤ (initial + ∑ k ∈ Finset.range n, stepRadius k) + stepRadius n := by
          nlinarith [ih]
        _ = initial + ∑ k ∈ Finset.range (n + 1), stepRadius k := by
          rw [Finset.sum_range_succ]
          ring

end FiniteEvolutionStep

/-! Physics-facing aliases.  They preserve the generic contract while making
the intended use visible in a theorem statement and in diagnostics. -/

namespace Classical
abbrev FiniteODETimeStep := FiniteEvolutionStep
end Classical

namespace Quantum
abbrev FiniteSchrodingerTimeStep := FiniteEvolutionStep
abbrev FiniteMasterEquationStep := FiniteEvolutionStep
end Quantum

namespace FieldTheory
abbrev FiniteFieldEvolutionStep := FiniteEvolutionStep
end FieldTheory

namespace Condensed
abbrev FiniteLatticeEvolutionStep := FiniteEvolutionStep
end Condensed

namespace StatMech
abbrev FiniteMarkovEvolutionStep := FiniteEvolutionStep
end StatMech

end LeanPhy.Mathematics
