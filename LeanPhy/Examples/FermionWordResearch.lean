import LeanPhy.FieldTheory.InteractingFermion
import LeanPhy.FieldTheory.FermionEmbedding
import LeanPhy.Workflow.Core

set_option autoImplicit false

/-! A client for variable interactions, selected local modes, and an actual
quartic Heisenberg equation. All rearrangements consume the shared compiler. -/

namespace LeanPhy.Examples.FermionWordResearch

open LeanPhy.FieldTheory LeanPhy.Quantum LeanPhy.Workflow
open FermionWord FermionPolynomial FiniteFermion
open scoped Matrix Matrix.Norms.Operator

def interaction : Expression ℤ (Fin 2) :=
  term 1 [cre 0, ann 0, cre 1, ann 1]

def probe : Expression ℤ (Fin 2) := letter (ann 0)

def interactionEquation : Expression ℤ (Fin 2) := term (-1) [ann 0, cre 1, ann 1]

theorem quartic_equation_checked :
    compile (sub (FermionPolynomial.commutator interaction probe) interactionEquation) = [] := by
  decide

theorem quartic_hermitian_checked :
    compile (sub (FermionPolynomial.adjoint interaction) interaction) = [] := by
  decide

/-- The local quartic identity applies to any injectively selected pair of modes. -/
theorem local_interaction_equation (n : ℕ) (g : Fin 2 → Fin n) (hg : Function.Injective g) :
    eval (Int.castRingHom ℂ) (modes n).car
      (rename g (FermionPolynomial.commutator interaction probe)) =
    eval (Int.castRingHom ℂ) (modes n).car (rename g interactionEquation) :=
  eq_of_local_certificate (Int.castRingHom ℂ) (modes n).car g hg _ _ quartic_equation_checked

/-- Any complex finite interaction, including non-Gaussian terms, can be reordered. -/
theorem arbitrary_interaction_normalOrder (n : ℕ) (p : Expression ℂ (Fin n)) :
    InteractingFermion.operator (modes n) (RingHom.id ℂ) (normalOrder p) =
      InteractingFermion.operator (modes n) (RingHom.id ℂ) p :=
  InteractingFermion.operator_normalOrder (modes n) (RingHom.id ℂ) p

/-- Coupling tables plus their adjoints construct actual Hermitian operators. -/
theorem arbitrary_interaction_hermitian (n : ℕ) (p : Expression ℂ (Fin n)) :
    (InteractingFermion.operator (modes n) (RingHom.id ℂ) (withAdjoint p)).IsHermitian :=
  InteractingFermion.withAdjoint_hermitian (modes n) (RingHom.id ℂ) (fun _ => rfl) p

theorem arbitrary_thermal_stationary (n : ℕ) (p : Expression ℂ (Fin n)) (β t : ℝ) :
    (finiteHamiltonianFlow
      (InteractingFermion.operator (modes n) (RingHom.id ℂ) (withAdjoint p))
      (arbitrary_interaction_hermitian n p) t).conjugate
      (InteractingFermion.thermalState (modes n) (RingHom.id ℂ) (withAdjoint p)
        (arbitrary_interaction_hermitian n p) β).rho =
      (InteractingFermion.thermalState (modes n) (RingHom.id ℂ) (withAdjoint p)
        (arbitrary_interaction_hermitian n p) β).rho :=
  finiteThermalState_stationary _ _ β t

theorem quartic_hermitian :
    (InteractingFermion.operator (modes 2) (Int.castRingHom ℂ) interaction).IsHermitian :=
  InteractingFermion.hermitian_of_certificate (modes 2) (Int.castRingHom ℂ)
    (by intro c; simp) interaction quartic_hermitian_checked

/-- The checked cubic equation is the derivative of the actual unitary evolution. -/
theorem quartic_observable_derivative :
    HasDerivAt (fun t : ℝ =>
      (finiteHamiltonianFlow
        (InteractingFermion.operator (modes 2) (Int.castRingHom ℂ) interaction)
        quartic_hermitian t).conjugate
        (InteractingFermion.operator (modes 2) (Int.castRingHom ℂ) probe))
      (Complex.I • InteractingFermion.operator (modes 2) (Int.castRingHom ℂ) interactionEquation) 0 :=
  InteractingFermion.observable_derivative_of_certificate (modes 2) (Int.castRingHom ℂ)
    interaction probe interactionEquation quartic_hermitian quartic_equation_checked

theorem contraction_cannot_be_deleted :
    compile (sub (term (1 : ℤ) [ann (0 : Fin 1), cre 0])
      (term (-1) [cre 0, ann 0])) ≠ [] := by decide

theorem repeated_creation_vanishes :
    compile (term (1 : ℤ) [cre (0 : Fin 3), cre 2, cre 0, ann 1]) = [] := by decide

def package : TheoryPackage :=
  (TheoryPackage.empty "interacting fermion expressions" "condensed matter and finite-mode field theory")
    |>.addTheorem "general interaction normalization" "arbitrary complex interaction tables retain their represented operator"
      "LeanPhy.Examples.FermionWordResearch.arbitrary_interaction_normalOrder" arbitrary_interaction_normalOrder
    |>.addTheorem "general Hermitian interactions" "adding the adjoint preserves complex conjugation and reversed order"
      "LeanPhy.Examples.FermionWordResearch.arbitrary_interaction_hermitian" arbitrary_interaction_hermitian
    |>.addTheorem "interacting thermal stationarity" "the exact many-body Gibbs density is stationary"
      "LeanPhy.Examples.FermionWordResearch.arbitrary_thermal_stationary" arbitrary_thermal_stationary
    |>.addTheorem "local quartic equation" "a certified local identity embeds in any selected distinct modes"
      "LeanPhy.Examples.FermionWordResearch.local_interaction_equation" local_interaction_equation
    |>.addTheorem "quartic dynamics" "the cubic commutator is the actual initial Heisenberg derivative"
      "LeanPhy.Examples.FermionWordResearch.quartic_observable_derivative" quartic_observable_derivative
    |>.addTheorem "contraction retained" "dropping the scalar contraction fails the exact check"
      "LeanPhy.Examples.FermionWordResearch.contraction_cannot_be_deleted" contraction_cannot_be_deleted
    |>.addTheorem "Pauli cancellation" "repeated equal creation generators cancel even when separated"
      "LeanPhy.Examples.FermionWordResearch.repeated_creation_vanishes" repeated_creation_vanishes
    |>.addObligationText "actual-state Wick theorem" "normal ordering alone supplies no Gaussian moment factorization"
      "derive contractions from an actual state"
    |>.addObligationText "bosonic cutoff boundaries" "fermion nilpotence does not implement bosonic truncated CCR"
      "construct boson occupation operators and retain boundary corrections"
    |>.addObligationText "large-system performance and limits" "finite exact identities do not prove scalable many-body dynamics or thermodynamic limits"
      "benchmark symbolic and represented operations; prove model-specific limiting bounds"

end LeanPhy.Examples.FermionWordResearch
