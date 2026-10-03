import LeanPhy.HighEnergy.Ward
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Spinor kinematics: the slash square and the mass-shell condition

Lorentz-invariant amplitudes are built from the two facts that a Dirac spinor
carries: the Feynman slash squares to the invariant mass squared,

    a-slash p * a-slash p = (p . p) 1,

and the Dirac equation therefore forces the on-shell relation.  Both are
proved here on the explicit chiral gamma matrices (never assumed), and they are
the algebraic content of every mass-shell statement a derivation uses.  The
module is stated at the spinor level, so it sits directly on top of the
`LeanPhy.HighEnergy.Ward` vertex algebra: `ward_identity` supplies the on-shell
hypotheses, this module shows what those hypotheses mean.

Proved (no sorry, no axiom):

- `slash_sq`: `a-slash p * a-slash p = (p . p) • 1`;
- `mass_shell`: from the Dirac equation `a-slash p u = m u` for an eigenvalue
  `m`, the momentum is on shell, `(p . p - m m) • u = 0`;
- `massless_lightlike`: a massless on-shell spinor has lightlike momentum;
- `slash_sq_trace`: the trace form `tr (a-slash p * a-slash p) = 4 (p . p)`,
  tying the spinor statement back to `tr4_slash_mul`.
-/

namespace LeanPhy.HighEnergy

open LeanPhy.Quantum
open scoped BigOperators

local notation "M4" => Matrix (Fin 4) (Fin 4) ℂ

/-- **The slash square.**  The Feynman slash squares to the Lorentz invariant
`p . p`, so `a-slash^2` is a multiple of the identity.  This is the identity
that makes every spinor mass-shell statement algebraic. -/
theorem slash_sq (p : Fin 4 → ℂ) :
    slash p * slash p = (minkowskiDot p p) • (1 : M4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [slash, minkowskiDot, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.one_apply, Fin.sum_univ_four, gammaFin, gamma0, gamma1, gamma2, gamma3,
      etaFin, Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply] <;>
    norm_num <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring_nf

/-- The trace shadow of the slash square: applying the trace to `slash_sq`
reproduces `tr (a-slash p * a-slash p) = 4 (p . p)`, the two-point function of
the Dirac bilinear algebra. -/
theorem slash_sq_trace (p : Fin 4 → ℂ) :
    tr4 (slash p * slash p) = 4 * minkowskiDot p p := by
  rw [slash_sq, tr4, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  ring

/-- **The mass-shell condition.**  If a spinor satisfies the Dirac equation
`a-slash p u = m u` for an eigenvalue `m`, then `(p . p - m m) • u = 0`: the
momentum lies on the mass shell.  In particular a nonzero eigenvector forces
`p . p = m m`. -/
theorem mass_shell (p u : Fin 4 → ℂ) (m : ℂ) (h : (slash p).mulVec u = m • u) :
    (minkowskiDot p p - m * m) • u = 0 := by
  have e2 : (slash p * slash p).mulVec u = (m * m) • u := by
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, h, smul_smul]
  rw [slash_sq, Matrix.smul_mulVec, Matrix.one_mulVec] at e2
  rw [sub_smul, e2, sub_self]

/-- A massless on-shell spinor has lightlike momentum: if `a-slash p u = 0`
then `(p . p) • u = 0`. -/
theorem massless_lightlike (p u : Fin 4 → ℂ) (h : (slash p).mulVec u = 0) :
    (minkowskiDot p p) • u = 0 := by
  have h0 := mass_shell p u 0 (by rw [h, zero_smul])
  simpa using h0

end LeanPhy.HighEnergy
