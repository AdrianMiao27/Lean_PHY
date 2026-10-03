import LeanPhy.HighEnergy.Gamma5
import LeanPhy.HighEnergy.Trace
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000

/-!
# Spinor covariants: the antisymmetric tensor sigma^{mu nu}

A Dirac bilinear `ubar Gamma u` is classified by the Dirac matrix `Gamma`, and
the five independent ones are the scalar `1`, the vector `gamma^mu`, the tensor
`sigma^{mu nu}`, the pseudovector `gamma^mu gamma^5`, and the pseudoscalar
`gamma^5`.  Since `LeanPhy.HighEnergy.DiracBilinear` and
`LeanPhy.HighEnergy.Spinor` already provide the gamma and slash layers, this
module adds the tensor generator

    sigma^{mu nu} = (i/2) [gamma^mu, gamma^nu],

namely the two facts that fix its place in the Clifford algebra: it is
antisymmetric in its indices, and it commutes with `gamma^5` (because `gamma^5`
anticommutes with every `gamma^mu`, so the anticommutators cancel in the
commutator).  That commutation is exactly why the tensor is a genuine covariant
rather than mixing with the pseudotensor, and it is the algebraic input the
standard decomposition of a Dirac bilinear into covariants consumes.

Everything is checked entrywise on the explicit `4 x 4` chiral representation.
The completeness of the five-covariant basis (the Fierz expansion) is not proved
here; it needs a `± 4` weighting of each covariant, which is left as a future
step.
-/

namespace LeanPhy.HighEnergy

open scoped BigOperators Matrix

/-- The antisymmetric tensor generator `sigma^{mu nu} = (i/2) [gamma^mu, gamma^nu]`. -/
noncomputable def sigma (mu nu : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  (Complex.I / 2) • (gammaFin mu * gammaFin nu - gammaFin nu * gammaFin mu)

/-- `sigma^{mu nu}` is antisymmetric: `sigma^{nu mu} = -sigma^{mu nu}`. -/
theorem sigma_antisym (mu nu : Fin 4) : sigma nu mu = -sigma mu nu := by
  simp only [sigma]
  rw [show gammaFin nu * gammaFin mu - gammaFin mu * gammaFin nu
        = -(gammaFin mu * gammaFin nu - gammaFin nu * gammaFin mu) from by abel]
  rw [smul_neg]

/-- On the diagonal `sigma^{mu mu} = 0`; the content of the antisymmetry. -/
theorem sigma_self (mu : Fin 4) : sigma mu mu = 0 := by
  simp only [sigma, sub_self, smul_zero]

/-- `gamma^5` commutes with `sigma^{mu nu}`: the tensor is a genuine Lorentz
covariant (it does not mix with the pseudotensor). -/
theorem gamma5_commute_sigma (mu nu : Fin 4) : gamma5 * sigma mu nu = sigma mu nu * gamma5 := by
  simp only [sigma]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [gammaFin]
  fin_cases mu <;> fin_cases nu <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [gamma5, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply, Matrix.sub_apply,
        Fin.sum_univ_four] <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring_nf))

end LeanPhy.HighEnergy

