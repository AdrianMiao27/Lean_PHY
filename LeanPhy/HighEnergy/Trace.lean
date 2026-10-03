import LeanPhy.HighEnergy.Gamma5
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Gamma-matrix trace identities

The trace identities for Dirac gamma matrices are the algebra where a single
sign error silently invalidates a cross-section computation, so they are worth
checking exactly.  Everything here is proved entrywise on the explicit 4x4
chiral representation in `LeanPhy.HighEnergy.Gamma`, never assumed:

- every single gamma matrix is traceless;
- `tr (γ^μ γ^ν) = 4 η^{μν}`;
- `tr (γ^μ γ^ν γ^ρ γ^σ) = 4 (η^{μν} η^{ρσ} - η^{μρ} η^{νσ} + η^{μσ} η^{νρ})`;
- the chiral traces `tr γ^5 = 0` and `tr (γ^5 γ^μ γ^ν) = 0`.

The trace is taken with mathlib's `Matrix.trace`; the left-hand side is
written through the physics alias `tr4` so a reader sees the shape of the
identity at a glance.
-/

namespace LeanPhy.HighEnergy

open LeanPhy.Quantum

local notation "𝕚" => Complex.I
local notation "M4" => Matrix (Fin 4) (Fin 4) ℂ

/-- The Dirac trace of a 4x4 matrix, named for physics reading. -/
def tr4 (M : M4) : ℂ := M.trace

@[simp] theorem tr4_one : tr4 (1 : M4) = 4 := by
  simp [tr4, Matrix.trace, Matrix.one_apply, Fin.sum_univ_four]

/-! ## Odd traces vanish -/

theorem tr4_gamma0 : tr4 gamma0 = 0 := by
  simp [tr4, Matrix.trace, Matrix.diag, gamma0, Fin.sum_univ_four]

theorem tr4_gamma1 : tr4 gamma1 = 0 := by
  simp [tr4, Matrix.trace, Matrix.diag, gamma1, Fin.sum_univ_four]

theorem tr4_gamma2 : tr4 gamma2 = 0 := by
  simp [tr4, Matrix.trace, Matrix.diag, gamma2, Fin.sum_univ_four]

theorem tr4_gamma3 : tr4 gamma3 = 0 := by
  simp [tr4, Matrix.trace, Matrix.diag, gamma3, Fin.sum_univ_four]

/-- Every gamma matrix is traceless, in the indexed form used in derivations. -/
theorem tr4_gammaFin (mu : Fin 4) : tr4 (gammaFin mu) = 0 := by
  fin_cases mu <;> simp [gammaFin, tr4_gamma0, tr4_gamma1, tr4_gamma2, tr4_gamma3]

/-! ## Two-point trace: tr (γ^μ γ^ν) = 4 η^{μν} -/

theorem tr4_gammaFin_two (mu nu : Fin 4) :
    tr4 (gammaFin mu * gammaFin nu) = 4 * etaFin mu nu := by
  fin_cases mu <;> fin_cases nu <;>
    simp [gammaFin, etaFin, tr4, Matrix.trace, Matrix.diag, gamma0, gamma1, gamma2, gamma3,
      Matrix.mul_apply, Fin.sum_univ_four] <;>
    (try ring_nf) <;> (try simp only [Complex.I_mul_I]) <;> (try ring)

/-! ## Four-point trace -/

theorem tr4_gammaFin_four (mu nu rho sig : Fin 4) :
    tr4 (gammaFin mu * gammaFin nu * gammaFin rho * gammaFin sig)
      = 4 * (etaFin mu nu * etaFin rho sig - etaFin mu rho * etaFin nu sig
              + etaFin mu sig * etaFin nu rho) := by
  fin_cases mu <;> fin_cases nu <;> fin_cases rho <;> fin_cases sig <;>
    simp [gammaFin, etaFin, tr4, Matrix.trace, Matrix.diag, gamma0, gamma1, gamma2, gamma3,
      Matrix.mul_apply, Fin.sum_univ_four] <;>
    (try ring_nf) <;> (try simp only [Complex.I_mul_I, Complex.I_sq]) <;> (try ring)

/-! ## Chiral traces -/

theorem tr4_gamma5 : tr4 gamma5 = 0 := by
  simp [tr4, Matrix.trace, Matrix.diag, gamma5, gamma0, gamma1, gamma2, gamma3,
    Matrix.mul_apply, Fin.sum_univ_four] <;>
    (try ring_nf) <;> (try simp only [Complex.I_mul_I, Complex.I_sq]) <;> (try ring)

/-- The trace with a single gamma^5 and two gammas vanishes. -/
theorem tr4_gamma5_gammaFin_two (mu nu : Fin 4) :
    tr4 (gamma5 * gammaFin mu * gammaFin nu) = 0 := by
  fin_cases mu <;> fin_cases nu <;>
    simp [gammaFin, tr4, Matrix.trace, Matrix.diag, gamma5, gamma0, gamma1, gamma2, gamma3,
      Matrix.mul_apply, Fin.sum_univ_four] <;>
    (try ring_nf) <;> (try simp only [Complex.I_mul_I, Complex.I_sq]) <;> (try ring)

/-- A single gamma^5 with one gamma is traceless:  tr (gamma^5 gamma^mu) = 0. -/
theorem tr4_gamma5_gammaFin (mu : Fin 4) : tr4 (gamma5 * gammaFin mu) = 0 := by
  fin_cases mu <;>
    simp [gammaFin, tr4, Matrix.trace, Matrix.diag, gamma5, gamma0, gamma1, gamma2, gamma3,
      Matrix.mul_apply, Fin.sum_univ_four]

end LeanPhy.HighEnergy
