import LeanPhy.FieldTheory.FiniteFermion
import LeanPhy.FieldTheory.FermionBasis
import LeanPhy.FieldTheory.PhysicalMajorana
import LeanPhy.FieldTheory.FermionVacuumWick
import LeanPhy.FieldTheory.FermionUnitaryWick
import LeanPhy.Condensed.ComplexPairing
import LeanPhy.Workflow.Core

set_option autoImplicit false

/-! Integration clients use variable mode counts and coupling tables. Small
counterexamples protect representation and convention boundaries. -/

namespace LeanPhy.Examples.FermionResearch

open LeanPhy.Quantum LeanPhy.FieldTheory LeanPhy.FieldTheory.FiniteFermion
open LeanPhy.FieldTheory.FermionBdG LeanPhy.Condensed LeanPhy.Workflow
open LeanPhy.FieldTheory.SingleModeVacuum
open LeanPhy.FieldTheory.TwoModeVacuum
open scoped Matrix Kronecker

theorem constructed_car (n : ℕ) (i j : Fin n) :
    ⟪(modes n).car.ann i, (modes n).car.cre j⟫ = if i = j then 1 else 0 :=
  (modes n).car.car_ann_cre i j

theorem constructed_equation (n : ℕ) (K : Coefficients (Fin n)) (i : Fin n ⊕ Fin n) :
    ⟦nambu (modes n).car i, (modes n).hamiltonian K⟧ =
      act K.matrix (nambu (modes n).car) i :=
  nambu_equation (modes n).car (modes n).adjoint K i

theorem constructed_energy (n : ℕ) (K : Coefficients (Fin n)) :
    (modes n).hamiltonian K = (1 / 2 : ℂ) •
      (nambuQuadratic (modes n).car K + Matrix.trace K.normal • 1) :=
  nambu_energy (modes n).car (modes n).adjoint K

theorem thermal_stationarity (n : ℕ) (K : Coefficients (Fin n)) (β t : ℝ) :
    (finiteHamiltonianFlow ((modes n).hamiltonian K)
      ((modes n).hamiltonian_hermitian K) t).conjugate ((modes n).thermalState K β).rho =
        ((modes n).thermalState K β).rho :=
  finiteThermalState_stationary _ _ β t

theorem orbital_invariance (n : ℕ) (K : Coefficients (Fin n)) (U : FiniteUnitary (Fin n)) :
    ((modes n).car.rotate U).quadratic (K.rotate U).normal (K.rotate U).pairing =
      (modes n).hamiltonian K := quadratic_rotate (modes n).car K U

theorem majorana_occupation (n : ℕ) (i : Fin n) :
    (modes n).car.numberOp i = (1 / 2 : ℂ) •
      (1 + Complex.I • ((modes n).car.majoranaX i * (modes n).car.majoranaY i)) :=
  (modes n).car.occupation_majorana i

/-- An actual finite vacuum state satisfies the ordered four-point Wick identity.
The ordered contraction keeps CAR contact terms separate from the antisymmetric
Pfaffian slots used by the shared Wick kernel. -/
theorem single_mode_vacuum_wick (a b c d : Fin 2) :
    SingleModeVacuum.expectation
      (SingleModeVacuum.generator a * SingleModeVacuum.generator b *
        SingleModeVacuum.generator c * SingleModeVacuum.generator d) =
      FermionicWick.fourPoint
        (SingleModeVacuum.orderedContraction (SingleModeVacuum.slots a b c d))
        0 1 2 3 :=
  SingleModeVacuum.vacuum_fourPoint a b c d

/-! The two-mode regression uses the actual four-dimensional occupation space
and both Jordan--Wigner strings.  It is intentionally a fixed certificate
readout: arbitrary mode labels and thermal covariances remain a separate
adapter obligation below. -/
theorem two_mode_vacuum_wick :
    OrderedQuasiFreeCertificate.expectation TwoModeVacuum.certificate
      (TwoModeVacuum.generator 0 * TwoModeVacuum.generator 1 *
        TwoModeVacuum.generator 2 * TwoModeVacuum.generator 3) =
      FermionicWick.fourPoint
        (TwoModeVacuum.orderedContraction (TwoModeVacuum.slots 0 1 2 3)) 0 1 2 3 :=
  TwoModeVacuum.certificate_readout

/-- Coefficient data and mode count determine an actual vacuum four-point trace. -/
theorem multimode_vacuum_wick (n : ℕ) (p q r s : FermionProbe (Fin n)) :
    (vacuumState n).expectation
      (p.operator (modes n).car * q.operator (modes n).car *
        r.operator (modes n).car * s.operator (modes n).car) =
      p.contraction q * r.contraction s - p.contraction r * q.contraction s +
        p.contraction s * q.contraction r :=
  (vacuumState n).fourPoint p q r s

theorem multimode_vacuum_twoPoint (n : ℕ) (p q : FermionProbe (Fin n)) :
    (vacuumState n).expectation (p.operator (modes n).car * q.operator (modes n).car) =
      p.contraction q := (vacuumState n).twoPoint p q

theorem arbitrary_vacuum_moment (n : ℕ) (ps : List (FermionProbe (Fin n))) :
    (vacuumState n).moment ps = FermionicWick.moment FermionProbe.contraction ps :=
  (vacuumState n).moment_eq ps

/-- A common many-body orbital rotation transports the constructed vacuum and
    preserves every ordered probe moment.  This is the finite bridge used for
    free-fermion quenches and basis changes. -/
theorem unitary_transported_vacuum_moment (n : ℕ)
    (U : FiniteUnitary (Occupation n))
    (ps : List (FermionProbe (Fin n))) :
    (FermionVacuum.transport U (vacuumState n)).moment ps =
      FermionicWick.moment FermionProbe.contraction ps := by
  exact FermionVacuum.transport_moment_eq U (vacuumState n) ps

theorem odd_vacuum_moment (n : ℕ) (ps : List (FermionProbe (Fin n)))
    (hodd : ps.length % 2 = 1) : (vacuumState n).moment ps = 0 :=
  (vacuumState n).moment_odd ps hodd

theorem vacuum_contact (n : ℕ) (before after : List (FermionProbe (Fin n)))
    (p q : FermionProbe (Fin n)) :
    (vacuumState n).moment (before ++ p :: q :: after) +
        (vacuumState n).moment (before ++ q :: p :: after) =
      (p.contraction q + q.contraction p) * (vacuumState n).moment (before ++ after) :=
  (vacuumState n).moment_exchange before after p q

theorem interaction_vacuum_readout {R : Type} [CommRing R] (n : ℕ)
    (f : R →+* ℂ) (p : FermionPolynomial.Expression R (Fin n)) :
    (vacuumState n).expectation (FermionPolynomial.eval f (modes n).car p) =
      f (FermionPolynomial.vacuumValue p) :=
  (vacuumState n).expression_expectation f p

/-- Three physical modes have eight occupation states but six Nambu indices. -/
theorem distinct_spaces : Fintype.card (Occupation 3) = 8 ∧
    Fintype.card (Fin 3 ⊕ Fin 3) = 6 := by
  constructor
  · norm_num [occupation_card]
  · decide

/-- Dropping the Jordan-Wigner string violates cross-mode CAR. -/
theorem parity_string_required :
    ⟪smMat ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ), 1 ⊗ₖ smMat⟫ ≠ 0 := by
  intro h
  have he := congrArg (fun A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ =>
    A (0, 0) (1, 1)) h
  norm_num [anticommutator, ← Matrix.mul_kronecker_mul, smMat,
    Matrix.kronecker_apply] at he

/-- A complex-symmetric legacy block is not the Hermitian complex-pairing block. -/
theorem conjugate_entry_required : ComplexPairing.block 0 Complex.I ≠ bdg 0 Complex.I := by
  intro h
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 1 0).im) h
  norm_num [ComplexPairing.block, bdg] at he

/-- Normal ordering cannot remove the trace term, even before a state is chosen. -/
theorem trace_constant_required :
    (modes 1).car.antiNormal (1 : Matrix (Fin 1) (Fin 1) ℂ) ≠
      -(modes 1).car.normal 1 := by
  rw [MultiModeCAR.antiNormal_eq]
  simp only [Matrix.trace_one, Fintype.card_fin, Nat.cast_one, one_smul,
    Matrix.transpose_one]
  intro h
  have hz : (1 : Matrix (Occupation 1) (Occupation 1) ℂ) = 0 := by
    simpa using (sub_eq_iff_eq_add).mp h
  exact one_ne_zero hz

def package : TheoryPackage :=
  TheoryPackage.empty "finite fermion research" "condensed matter and finite-mode field theory"
    |>.addTheorem "constructed CAR" "arbitrary mode count obtains an actual occupation representation"
      "constructed_car" constructed_car
    |>.addTheorem "many-body Nambu equation" "the coefficient matrix is derived from the actual CAR Hamiltonian"
      "constructed_equation" constructed_equation
    |>.addTheorem "normal-ordering energy" "the Nambu representation retains its half factor and trace constant"
      "constructed_energy" constructed_energy
    |>.addTheorem "many-body thermal state" "the constructed occupation-space Gibbs state is stationary"
      "thermal_stationarity" thermal_stationarity
    |>.addTheorem "orbital basis transport" "transporting generators and coefficients preserves the Hamiltonian"
      "orbital_invariance" orbital_invariance
    |>.addTheorem "Majorana occupation" "the occupation sign follows the explicit phase convention"
      "majorana_occupation" majorana_occupation
    |>.addTheorem "actual vacuum Wick identity"
      "an explicit finite vacuum satisfies the ordered four-point contraction rule"
      "single_mode_vacuum_wick" single_mode_vacuum_wick
    |>.addTheorem "two-mode vacuum Wick identity"
      "an explicit Jordan-Wigner two-mode vacuum satisfies a cross-mode four-point rule"
      "two_mode_vacuum_wick" two_mode_vacuum_wick
    |>.addTheorem "multimode vacuum four-point function"
      "arbitrary finite mode counts and linear probes give a derived actual vacuum four-point trace"
      "multimode_vacuum_wick" multimode_vacuum_wick
    |>.addTheorem "multimode vacuum two-point function"
      "the constructed vacuum derives ordered two-point contractions from complex probe coefficients"
      "multimode_vacuum_twoPoint" multimode_vacuum_twoPoint
    |>.addTheorem "arbitrary ordered vacuum moments"
      "CAR and the actual density derive terminating contractions for any probe list"
      "arbitrary_vacuum_moment" arbitrary_vacuum_moment
    |>.addTheorem "unitary-transported vacuum moments"
      "a common finite many-body rotation preserves all ordered vacuum contractions"
      "unitary_transported_vacuum_moment" unitary_transported_vacuum_moment
    |>.addTheorem "odd vacuum moments"
      "odd ordered products vanish in the supplied actual vacuum"
      "odd_vacuum_moment" odd_vacuum_moment
    |>.addTheorem "vacuum contact terms"
      "adjacent exchanges retain their CAR contact term in any surrounding product"
      "vacuum_contact" vacuum_contact
    |>.addTheorem "interaction vacuum readout"
      "exact integer word moments evaluate symbolic expressions before coefficient specialization"
      "interaction_vacuum_readout" (@interaction_vacuum_readout)
    |>.addTheorem "complex pairing square" "general complex pairing uses its norm squared"
      "LeanPhy.Condensed.ComplexPairing.square" ComplexPairing.square
    |>.addTheorem "particle-hole partner" "full Nambu conjugation maps the eigen-equation"
      "LeanPhy.FieldTheory.FermionBdG.Coefficients.partner_equation"
      (@Coefficients.partner_equation.{0})
    |>.addTheorem "representation dimensions" "Nambu and occupation spaces have different dimensions"
      "distinct_spaces" distinct_spaces
    |>.addTheorem "parity string" "naive tensor-local fermions do not satisfy cross-mode CAR"
      "parity_string_required" parity_string_required
    |>.addObligationText "interacting self-consistency" "derive state-dependent mean-field equations and their validity"
      "model-dependent approximation and fixed-point evidence"
    |>.addObligationText "dynamical correlations" "connect time derivatives, time ordering and actual-state Wick contractions"
      "dynamics and quasi-free state analysis"
    |>.addObligationText "continuum and topology" "supply limits and band/projector invariants for the target model"
      "spectral and continuum analysis"

example : package.claimCount = 19 := rfl
example : package.obligationCount = 3 := rfl
example : package.hasErrors = false := by decide

end LeanPhy.Examples.FermionResearch
