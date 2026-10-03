import LeanPhy.HighEnergy.Trace
import LeanPhy.HighEnergy.Gamma5
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Ring

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Dirac (Feynman-slash) bilinear algebra

The Feynman slash of a four-vector,  a-slash = gamma^mu a_mu, is the object
every Dirac-algebra manipulation is written in terms of.  Its trace with a
second slash is the workhorse of QED cross-section algebra, and it is exactly
the place a metric-signature slip silently flips a result, so it is worth
checking in the kernel rather than by hand.

Everything is proved from the explicit chiral gamma matrices and the
gamma-trace module, never assumed.  Proved (no sorry, no axiom):

- the bilinear expansion  a-slash b-slash = sum_{mu nu} a_mu b_nu gamma^mu gamma^nu;
- the two-point trace  tr (a-slash b-slash) = 4 (a . b);
- an odd number of slashes is traceless,  tr (a-slash) = 0;
- a single gamma^5 with one slash is traceless,  tr (gamma^5 a-slash) = 0.
-/

namespace LeanPhy.HighEnergy

open LeanPhy.Quantum
open scoped BigOperators

local notation "M4" => Matrix (Fin 4) (Fin 4) ℂ

/-- The Feynman slash  a-slash = sum_mu a_mu gamma^mu. -/
noncomputable def slash (a : Fin 4 → ℂ) : M4 :=
  ∑ μ : Fin 4, a μ • gammaFin μ

/-- The Minkowski inner product  a . b = sum_{mu nu} eta^{mu nu} a_mu b_nu. -/
noncomputable def minkowskiDot (a b : Fin 4 → ℂ) : ℂ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, etaFin μ ν * (a μ * b ν)

/-- Bilinear expansion of a slash product: this is the identity that turns every
Dirac-algebra manipulation into index algebra. -/
theorem slash_mul_expand (a b : Fin 4 → ℂ) :
    slash a * slash b
      = ∑ μ : Fin 4, ∑ ν : Fin 4, (a μ * b ν) • (gammaFin μ * gammaFin ν) := by
  rw [slash, slash, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [smul_mul_smul_comm]

/-- The QED workhorse:  tr (a-slash b-slash) = 4 (a . b). -/
theorem tr4_slash_mul (a b : Fin 4 → ℂ) :
    tr4 (slash a * slash b) = 4 * minkowskiDot a b := by
  rw [slash_mul_expand, minkowskiDot]
  simp only [tr4, Matrix.trace_sum, Matrix.trace_smul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [show (gammaFin μ * gammaFin ν).trace = etaFin μ ν * 4 from by
        have h := tr4_gammaFin_two μ ν; rw [tr4] at h; rw [h]; ring]
  ring

/-- An odd number of slashes is traceless:  tr (a-slash) = 0. -/
theorem tr4_slash (a : Fin 4 → ℂ) : tr4 (slash a) = 0 := by
  rw [slash, tr4, Matrix.trace_sum]
  refine Finset.sum_eq_zero fun μ _ => ?_
  rw [Matrix.trace_smul]
  have h := tr4_gammaFin μ
  rw [tr4] at h
  rw [h, smul_zero]

/-- A single gamma^5 together with one slash is traceless:
tr (gamma^5 a-slash) = 0. -/
theorem tr4_gamma5_slash (a : Fin 4 → ℂ) : tr4 (gamma5 * slash a) = 0 := by
  rw [slash, Finset.mul_sum, tr4, Matrix.trace_sum]
  refine Finset.sum_eq_zero fun μ _ => ?_
  rw [mul_smul_comm, Matrix.trace_smul]
  have h := tr4_gamma5_gammaFin μ
  rw [tr4] at h
  rw [h, smul_zero]

end LeanPhy.HighEnergy
