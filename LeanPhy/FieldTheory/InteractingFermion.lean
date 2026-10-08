import LeanPhy.FieldTheory.FermionPolynomial
import LeanPhy.FieldTheory.FiniteFermion
import LeanPhy.Quantum.DynamicalResponse

set_option autoImplicit false

/-!
# Interacting expressions in actual occupation representations

Arbitrary finite fermion polynomials give operators, Hermitian Hamiltonians and
thermal states on the existing occupation construction. A checked normal-form
identity is transferred to actual matrices and to the derivative of an actual
Heisenberg observable. This is exact finite-mode algebra; no Gaussian closure,
mean-field factorization or thermodynamic approximation is implicit.
-/

namespace LeanPhy.FieldTheory.InteractingFermion

open FermionPolynomial LeanPhy.Quantum
open scoped Matrix Matrix.Norms.Operator

variable {R ι σ : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [Fintype σ] [DecidableEq σ]
variable (S : FiniteFermion.Representation ι σ) (f : R →+* ℂ)

noncomputable def operator (p : Expression R ι) : Matrix σ σ ℂ := eval f S.car p

theorem operator_normalOrder (p : Expression R ι) :
    operator S f (normalOrder p) = operator S f p := eval_normalOrder f S.car p

theorem operator_compile [DecidableEq R] (p : Expression R ι) :
    operator S f (compile p) = operator S f p := eval_compile f S.car p

theorem operator_eq_of_certificate [DecidableEq R] (p q : Expression R ι)
    (h : compile (sub p q) = []) : operator S f p = operator S f q :=
  eq_of_compile_sub_eq_nil f S.car p q h

theorem operator_adjoint [StarRing R] (hf : ∀ c, f (star c) = star (f c))
    (p : Expression R ι) : operator S f (adjoint p) = (operator S f p)ᴴ :=
  eval_adjoint f S.car hf S.adjoint p

/-- Adding the adjoint gives a Hermitian interaction, with no implicit half factor. -/
theorem withAdjoint_hermitian [StarRing R] (hf : ∀ c, f (star c) = star (f c))
    (p : Expression R ι) : (operator S f (withAdjoint p)).IsHermitian :=
  withAdjoint_selfAdjoint f S.car hf S.adjoint p

/-- A symbolic Hermiticity check applies after any star-compatible specialization. -/
theorem hermitian_of_certificate [StarRing R] [DecidableEq R]
    (hf : ∀ c, f (star c) = star (f c)) (p : Expression R ι)
    (h : compile (sub (adjoint p) p) = []) : (operator S f p).IsHermitian := by
  rw [Matrix.IsHermitian, ← operator_adjoint S f hf]
  exact operator_eq_of_certificate S f _ _ h

noncomputable def thermalState [Nonempty σ] (p : Expression R ι)
    (h : (operator S f p).IsHermitian) (β : ℝ) : FiniteDensity σ :=
  finiteThermalState (operator S f p) h β

noncomputable def expectation (ρ : FiniteDensity σ) (p : Expression R ι) : ℂ :=
  Matrix.trace (ρ.rho * operator S f p)

theorem expectation_normalOrder (ρ : FiniteDensity σ) (p : Expression R ι) :
    expectation S f ρ (normalOrder p) = expectation S f ρ p := by
  rw [expectation, operator_normalOrder, expectation]

/-- An exact symbolic commutator computes the derivative of a physical unitary
observable. The Hamiltonian's Hermiticity remains an explicit checked premise. -/
theorem observable_derivative_of_certificate [DecidableEq R]
    (H O D : Expression R ι) (hH : (operator S f H).IsHermitian)
    (h : compile (sub (FermionPolynomial.commutator H O) D) = []) :
    HasDerivAt (fun t : ℝ =>
      (finiteHamiltonianFlow (operator S f H) hH t).conjugate (operator S f O))
      (Complex.I • operator S f D) 0 := by
  have hc : operator S f H * operator S f O - operator S f O * operator S f H =
      operator S f D := by
    have he := operator_eq_of_certificate S f _ _ h
    simpa only [operator, eval_commutator, LeanPhy.Quantum.commutator] using he
  have hd := Dynamics.heisenberg_derivative (operator S f H) (operator S f O) 0
  simp only [Dynamics.heisenberg_zero, hc] at hd
  have he : Dynamics.heisenberg (operator S f H) (operator S f O) =
      (fun t => (finiteHamiltonianFlow (operator S f H) hH t).conjugate (operator S f O)) :=
    funext (Dynamics.heisenberg_eq_conjugate _ _ hH)
  rw [he] at hd
  exact hd

/-- The same checked equation gives the actual initial-state readout derivative;
the density may be interacting or non-Gaussian. -/
theorem expectation_derivative_of_certificate [DecidableEq R]
    (ρ : FiniteDensity σ) (H O D : Expression R ι)
    (hH : (operator S f H).IsHermitian)
    (h : compile (sub (FermionPolynomial.commutator H O) D) = []) :
    HasDerivAt (fun t : ℝ => Matrix.trace (ρ.rho *
      (finiteHamiltonianFlow (operator S f H) hH t).conjugate (operator S f O)))
      (Matrix.trace (ρ.rho * (Complex.I • operator S f D))) 0 := by
  exact Dynamics.hasDerivAt_trace
    ((observable_derivative_of_certificate S f H O D hH h).const_mul ρ.rho)

end LeanPhy.FieldTheory.InteractingFermion
