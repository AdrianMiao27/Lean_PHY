import LeanPhy.Mathematics.Poisson
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-!
# A checked polynomial phase-space model

The abstract Poisson interface is useful only when concrete observable models
can inhabit it.  This file supplies the smallest nontrivial canonical model:
polynomials in two variables `q` and `p` over `ℝ`.  Mathlib's formal partial
derivatives provide the two commuting derivations, so the canonical bracket

    `{f,g} = (∂q f)(∂p g) - (∂p f)(∂q g)`

is constructed rather than postulated.  The commutation proof is checked on
the polynomial generators and extended by `MvPolynomial.derivation_ext`.
This is still an algebraic polynomial model: smooth functions, convergence,
boundary conditions and Hamiltonian flow existence remain separate layers.
-/

namespace LeanPhy.Classical

open LeanPhy.Mathematics
open LeanPhy.Mathematics.PoissonAlgebra

/-- The polynomial algebra in two canonical coordinates. -/
abbrev PhasePolynomial := MvPolynomial (Fin 2) ℝ

/-- Formal partial derivatives commute for every pair of variables in a
multivariate polynomial algebra.  The proof only checks the polynomial
generators, which is the algebraic analogue of equality of mixed partials. -/
theorem mvPolynomial_pderiv_commute {σ : Type} [DecidableEq σ] (i j : σ) :
    ⁅(MvPolynomial.pderiv i : PhysicsDerivation ℝ (MvPolynomial σ ℝ)),
      (MvPolynomial.pderiv j : PhysicsDerivation ℝ (MvPolynomial σ ℝ))⁆ = 0 := by
  apply MvPolynomial.derivation_ext
  intro k
  by_cases hij : i = j
  · subst j
    simp
  · by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [Derivation.commutator_apply, hki, hkj, hij]

/-- The canonical Poisson structure associated with any selected pair of
polynomial coordinates.  The ambient polynomial algebra may contain many
additional variables; the bracket differentiates only in `i` and `j`.
-/
noncomputable def polynomialPairPoisson {σ : Type} [DecidableEq σ]
    (i j : σ) : PoissonAlgebra ℝ (MvPolynomial σ ℝ) :=
  derivationPoissonAlgebra (MvPolynomial.pderiv i) (MvPolynomial.pderiv j)
    (mvPolynomial_pderiv_commute i j)

/-- Formal partial derivative with respect to `q` (variable `0`). -/
noncomputable def qDerivative : PhysicsDerivation ℝ PhasePolynomial :=
  MvPolynomial.pderiv 0

/-- Formal partial derivative with respect to `p` (variable `1`). -/
noncomputable def pDerivative : PhysicsDerivation ℝ PhasePolynomial :=
  MvPolynomial.pderiv 1

/-! The two coordinate derivatives commute on all polynomials. -/
theorem phase_derivatives_commute : ⁅qDerivative, pDerivative⁆ = 0 := by
  exact mvPolynomial_pderiv_commute 0 1

/-- The canonical polynomial Poisson algebra, constructed from `∂q` and `∂p`.
The Jacobi identity comes from the proved commutation of these derivations. -/
noncomputable def canonicalPolynomialPoisson : PoissonAlgebra ℝ PhasePolynomial :=
  derivationPoissonAlgebra qDerivative pDerivative phase_derivatives_commute

theorem canonical_q_p :
    canonicalPolynomialPoisson (MvPolynomial.X 0) (MvPolynomial.X 1) = 1 := by
  simp [canonicalPolynomialPoisson, derivationPoissonAlgebra,
    derivationBracket, qDerivative, pDerivative]

theorem canonical_p_q :
    canonicalPolynomialPoisson (MvPolynomial.X 1) (MvPolynomial.X 0) = -1 := by
  simp [canonicalPolynomialPoisson, derivationPoissonAlgebra,
    derivationBracket, qDerivative, pDerivative]

theorem canonical_q_q :
    canonicalPolynomialPoisson (MvPolynomial.X 0) (MvPolynomial.X 0) = 0 := by
  simp [canonicalPolynomialPoisson, derivationPoissonAlgebra,
    qDerivative, pDerivative]

theorem canonical_hamiltonian_is_derivation (H f g : PhasePolynomial) :
    hamiltonianDerivation canonicalPolynomialPoisson H (f * g) =
      f * hamiltonianDerivation canonicalPolynomialPoisson H g +
        g * hamiltonianDerivation canonicalPolynomialPoisson H f := by
  exact hamiltonianDerivation_product canonicalPolynomialPoisson H f g

/-- Canonical polynomial coordinates and the normalized oscillator Hamiltonian
`H = (q²+p²)/2`. -/
noncomputable def qPolynomial : PhasePolynomial := MvPolynomial.X 0
noncomputable def pPolynomial : PhasePolynomial := MvPolynomial.X 1
noncomputable def oscillatorPolynomialHamiltonian : PhasePolynomial :=
  (1 / 2 : ℝ) • (qPolynomial * qPolynomial + pPolynomial * pPolynomial)

theorem oscillator_hamiltonian_q :
    canonicalPolynomialPoisson oscillatorPolynomialHamiltonian qPolynomial =
      -pPolynomial := by
  simp [canonicalPolynomialPoisson, derivationPoissonAlgebra, derivationBracket,
    oscillatorPolynomialHamiltonian, qPolynomial, pPolynomial, qDerivative,
    pDerivative, div_eq_mul_inv]
  module

theorem oscillator_hamiltonian_p :
    canonicalPolynomialPoisson oscillatorPolynomialHamiltonian pPolynomial =
      qPolynomial := by
  simp [canonicalPolynomialPoisson, derivationPoissonAlgebra, derivationBracket,
    oscillatorPolynomialHamiltonian, qPolynomial, pPolynomial, qDerivative,
    pDerivative, div_eq_mul_inv]
  module

theorem oscillator_hamiltonian_conserved :
    Conserved canonicalPolynomialPoisson oscillatorPolynomialHamiltonian
      oscillatorPolynomialHamiltonian := by
  change canonicalPolynomialPoisson oscillatorPolynomialHamiltonian
      oscillatorPolynomialHamiltonian = 0
  exact bracket_self canonicalPolynomialPoisson oscillatorPolynomialHamiltonian

end LeanPhy.Classical
