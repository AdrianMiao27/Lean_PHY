import LeanPhy.Quantum.Basic
import Mathlib.Tactic.NoncommRing

/-!
# A single Hubbard site: two fermionic modes with spin

The Hubbard model is the canonical playground of strongly correlated electrons:
one site hosts an up-spin and a down-spin fermion, and the characteristic
physics (Mott gap, local moments, superconductivity) already lives in the local
algebra of the two modes.  This file states exactly that local algebra as
explicit hypotheses in a ring, so no operator-domain or Hilbert-space input is
assumed.

For one site we have creation and annihilation operators cU, cD and their
daggers, subject to the canonical anticommutation relations
{c_a, c_b^dagger} = delta_ab, {c_a, c_b} = 0, and nilpotency c_a^2 = 0.

Proved here (absence of any sorry or axiom):

- the spin-resolved number operators nUp = cUp^dagger cUp and
  nDn = cDn^dagger cDn are commuting projectors;
- the double occupancy D = nUp nDn is also a projector, and nUp, nDn both act
  on it trivially;
- the pair (Cooper-pair) operator P = cUp^dagger cDn^dagger is nilpotent, and
  D shifts it: [D, P] = P;
- the total number operator raises the up mode, [nUp + nDn, cUp^dagger] = cUp^dagger.

These are the algebraic facts that later phases (BCS mean-field, Nagaoka
ferromagnetism, dynamical mean-field theory) build on.
-/

namespace LeanPhy.Condensed

open LeanPhy.Quantum

/-- The local algebraic data of a single Hubbard site: one up and one down
fermionic mode with the full canonical anticommutation relations. -/
structure HubbardSite where
  /-- Carrier ring of operators. -/
  A : Type
  [ringA : Ring A]
  /-- Up-spin annihilation operator. -/
  cUp : A
  /-- Up-spin creation operator. -/
  cUpDag : A
  /-- Down-spin annihilation operator. -/
  cDn : A
  /-- Down-spin creation operator. -/
  cDnDag : A
  /-- Same-mode canonical relation for the up spin, {cUp, cUp^dagger} = 1. -/
  car_up : cUp * cUpDag + cUpDag * cUp = 1
  /-- Same-mode canonical relation for the down spin, {cDn, cDn^dagger} = 1. -/
  car_dn : cDn * cDnDag + cDnDag * cDn = 1
  /-- Cross relation {cUp, cDn} = 0. -/
  ac_up_dn : cUp * cDn + cDn * cUp = 0
  /-- Cross relation {cUp, cDn^dagger} = 0. -/
  ac_up_dndag : cUp * cDnDag + cDnDag * cUp = 0
  /-- Cross relation {cUp^dagger, cDn} = 0. -/
  ac_updag_dn : cUpDag * cDn + cDn * cUpDag = 0
  /-- Cross relation {cUp^dagger, cDn^dagger} = 0. -/
  ac_updag_dndag : cUpDag * cDnDag + cDnDag * cUpDag = 0
  /-- Annihilation of up spin is nilpotent. -/
  sq_up : cUp * cUp = 0
  /-- Creation of up spin is nilpotent. -/
  sq_updag : cUpDag * cUpDag = 0
  /-- Annihilation of down spin is nilpotent. -/
  sq_dn : cDn * cDn = 0
  /-- Creation of down spin is nilpotent. -/
  sq_dndag : cDnDag * cDnDag = 0

attribute [instance] HubbardSite.ringA

namespace HubbardSite

variable (M : HubbardSite)

local notation "cU" => M.cUp
local notation "cUd" => M.cUpDag
local notation "cD" => M.cDn
local notation "cDd" => M.cDnDag

/-! ## Anticommutation relations in subtractive form -/

theorem car_up_sub : cU * cUd = 1 - cUd * cU := by
  rw [eq_sub_iff_add_eq]; exact M.car_up

theorem car_dn_sub : cD * cDd = 1 - cDd * cD := by
  rw [eq_sub_iff_add_eq]; exact M.car_dn

theorem ac_up_dn_sub : cU * cD = -(cD * cU) :=
  eq_neg_of_add_eq_zero_left M.ac_up_dn

theorem ac_up_dndag_sub : cU * cDd = -(cDd * cU) :=
  eq_neg_of_add_eq_zero_left M.ac_up_dndag

theorem ac_updag_dn_sub : cUd * cD = -(cD * cUd) :=
  eq_neg_of_add_eq_zero_left M.ac_updag_dn

theorem ac_updag_dndag_sub : cUd * cDd = -(cDd * cUd) :=
  eq_neg_of_add_eq_zero_left M.ac_updag_dndag

theorem ac_dn_updag_sub : cD * cUd = -(cUd * cD) :=
  eq_neg_of_add_eq_zero_right M.ac_updag_dn

theorem ac_dndag_updag_sub : cDd * cUd = -(cUd * cDd) :=
  eq_neg_of_add_eq_zero_right M.ac_updag_dndag

/-! ## Number operators are commuting projectors -/

/-- The up-spin number operator nUp = cUp^dagger cUp. -/
def nUp : M.A := M.cUpDag * M.cUp

/-- The down-spin number operator nDn = cDn^dagger cDn. -/
def nDn : M.A := M.cDnDag * M.cDn

/-- The up-spin number operator is a projector: nUp^2 = nUp. -/
theorem nUp_idempotent : M.nUp * M.nUp = M.nUp := by
  have hdup : M.cUpDag * (M.cUpDag * (M.cUp * M.cUp)) = 0 := by
    rw [show M.cUpDag * (M.cUpDag * (M.cUp * M.cUp))
          = (M.cUpDag * M.cUpDag) * (M.cUp * M.cUp) from by noncomm_ring]
    simp only [M.sq_updag, zero_mul]
  rw [nUp, show (M.cUpDag * M.cUp) * (M.cUpDag * M.cUp)
        = M.cUpDag * (M.cUp * M.cUpDag) * M.cUp from by noncomm_ring, M.car_up_sub]
  rw [show M.cUpDag * (1 - M.cUpDag * M.cUp) * M.cUp
        = M.cUpDag * M.cUp - M.cUpDag * (M.cUpDag * (M.cUp * M.cUp)) from by noncomm_ring]
  simp only [hdup, sub_zero]

/-- The down-spin number operator is a projector: nDn^2 = nDn. -/
theorem nDn_idempotent : M.nDn * M.nDn = M.nDn := by
  have hdd : M.cDnDag * (M.cDnDag * (M.cDn * M.cDn)) = 0 := by
    rw [show M.cDnDag * (M.cDnDag * (M.cDn * M.cDn))
          = (M.cDnDag * M.cDnDag) * (M.cDn * M.cDn) from by noncomm_ring]
    simp only [M.sq_dndag, zero_mul]
  rw [nDn, show (M.cDnDag * M.cDn) * (M.cDnDag * M.cDn)
        = M.cDnDag * (M.cDn * M.cDnDag) * M.cDn from by noncomm_ring, M.car_dn_sub]
  rw [show M.cDnDag * (1 - M.cDnDag * M.cDn) * M.cDn
        = M.cDnDag * M.cDn - M.cDnDag * (M.cDnDag * (M.cDn * M.cDn)) from by noncomm_ring]
  simp only [hdd, sub_zero]

/-- Up and down number operators commute: [nUp, nDn] = 0.  The two spins are
genuinely independent; there is no spin-flipping term in the local algebra. -/
theorem nUp_commutes_nDn : M.nUp * M.nDn = M.nDn * M.nUp := by
  have hL : (M.cUpDag * M.cUp) * (M.cDnDag * M.cDn) = M.cUpDag * M.cDnDag * M.cDn * M.cUp := by
    rw [show (M.cUpDag * M.cUp) * (M.cDnDag * M.cDn)
          = M.cUpDag * (M.cUp * M.cDnDag) * M.cDn from by noncomm_ring, M.ac_up_dndag_sub]
    rw [show M.cUpDag * (-(M.cDnDag * M.cUp)) * M.cDn
          = -(M.cUpDag * M.cDnDag * (M.cUp * M.cDn)) from by noncomm_ring]
    rw [M.ac_up_dn_sub]
    noncomm_ring
  have hR : (M.cDnDag * M.cDn) * (M.cUpDag * M.cUp) = M.cUpDag * M.cDnDag * M.cDn * M.cUp := by
    rw [show (M.cDnDag * M.cDn) * (M.cUpDag * M.cUp)
          = M.cDnDag * (M.cDn * M.cUpDag) * M.cUp from by noncomm_ring, M.ac_dn_updag_sub]
    rw [show M.cDnDag * (-(M.cUpDag * M.cDn)) * M.cUp
          = -((M.cDnDag * M.cUpDag) * (M.cDn * M.cUp)) from by noncomm_ring]
    rw [M.ac_dndag_updag_sub]
    noncomm_ring
  rw [nUp, nDn, hL, hR]

/-! ## Double occupancy -/

/-- The double-occupancy operator D = nUp nDn. -/
def doubleOcc : M.A := M.nUp * M.nDn

/-- Double occupancy is a projector: D^2 = D. -/
theorem doubleOcc_idempotent : M.doubleOcc * M.doubleOcc = M.doubleOcc := by
  rw [doubleOcc, show (M.nUp * M.nDn) * (M.nUp * M.nDn)
        = (M.nUp * (M.nDn * M.nUp)) * M.nDn from by noncomm_ring]
  rw [← M.nUp_commutes_nDn]
  rw [show (M.nUp * (M.nUp * M.nDn)) * M.nDn
        = (M.nUp * M.nUp) * (M.nDn * M.nDn) from by noncomm_ring,
      M.nUp_idempotent, M.nDn_idempotent]

/-! ## The Cooper-pair operator -/

/-- The local pair operator P = cUp^dagger cDn^dagger, which creates a
field-aligned pair on the site. -/
def pairOp : M.A := M.cUpDag * M.cDnDag

/-- The pair operator is nilpotent: P^2 = 0 (Pauli exclusion forbids two pairs
on one site). -/
theorem pairOp_nilpotent : M.pairOp * M.pairOp = 0 := by
  rw [pairOp, show (M.cUpDag * M.cDnDag) * (M.cUpDag * M.cDnDag)
        = M.cUpDag * (M.cDnDag * M.cUpDag) * M.cDnDag from by noncomm_ring,
      M.ac_dndag_updag_sub]
  rw [show M.cUpDag * (-(M.cUpDag * M.cDnDag)) * M.cDnDag
        = -((M.cUpDag * M.cUpDag) * (M.cDnDag * M.cDnDag)) from by noncomm_ring]
  simp only [M.sq_updag, M.sq_dndag, mul_zero, neg_zero]

/-- nUp leaves the pair operator invariant: nUp P = P. -/
theorem nUp_mul_pairOp : M.nUp * M.pairOp = M.pairOp := by
  rw [nUp, pairOp, show (M.cUpDag * M.cUp) * (M.cUpDag * M.cDnDag)
        = M.cUpDag * (M.cUp * M.cUpDag) * M.cDnDag from by noncomm_ring, M.car_up_sub]
  rw [show M.cUpDag * (1 - M.cUpDag * M.cUp) * M.cDnDag
        = M.cUpDag * M.cDnDag - M.cUpDag * (M.cUpDag * (M.cUp * M.cDnDag)) from by noncomm_ring]
  rw [show M.cUpDag * (M.cUpDag * (M.cUp * M.cDnDag))
        = (M.cUpDag * M.cUpDag) * (M.cUp * M.cDnDag) from by noncomm_ring]
  simp only [M.sq_updag, zero_mul, sub_zero]

/-- nDn leaves the pair operator invariant: nDn P = P. -/
theorem nDn_mul_pairOp : M.nDn * M.pairOp = M.pairOp := by
  rw [nDn, pairOp, show (M.cDnDag * M.cDn) * (M.cUpDag * M.cDnDag)
        = M.cDnDag * (M.cDn * M.cUpDag) * M.cDnDag from by noncomm_ring, M.ac_dn_updag_sub]
  rw [show M.cDnDag * (-(M.cUpDag * M.cDn)) * M.cDnDag
        = -((M.cDnDag * M.cUpDag) * (M.cDn * M.cDnDag)) from by noncomm_ring]
  rw [M.ac_dndag_updag_sub]
  rw [show -((-(M.cUpDag * M.cDnDag)) * (M.cDn * M.cDnDag))
        = (M.cUpDag * M.cDnDag) * (M.cDn * M.cDnDag) from by noncomm_ring]
  rw [show (M.cUpDag * M.cDnDag) * (M.cDn * M.cDnDag)
        = M.cUpDag * (M.cDnDag * (M.cDn * M.cDnDag)) from by noncomm_ring, M.car_dn_sub]
  rw [show M.cUpDag * (M.cDnDag * (1 - M.cDnDag * M.cDn))
        = M.cUpDag * M.cDnDag - M.cUpDag * (M.cDnDag * (M.cDnDag * M.cDn)) from by noncomm_ring]
  rw [show M.cUpDag * (M.cDnDag * (M.cDnDag * M.cDn))
        = M.cUpDag * (M.cDnDag * M.cDnDag) * M.cDn from by noncomm_ring]
  simp only [M.sq_dndag, mul_zero, zero_mul, sub_zero]

/-- The pair operator lowers double occupancy from the left: P D = 0. -/
theorem pairOp_mul_doubleOcc : M.pairOp * M.doubleOcc = 0 := by
  rw [pairOp, doubleOcc, nUp, nDn,
      show (M.cUpDag * M.cDnDag) * ((M.cUpDag * M.cUp) * (M.cDnDag * M.cDn))
        = ((M.cUpDag * M.cDnDag) * (M.cUpDag * M.cUp)) * (M.cDnDag * M.cDn) from by noncomm_ring]
  have h : (M.cUpDag * M.cDnDag) * (M.cUpDag * M.cUp) = 0 := by
    rw [show (M.cUpDag * M.cDnDag) * (M.cUpDag * M.cUp)
          = (M.cUpDag * (M.cDnDag * M.cUpDag)) * M.cUp from by noncomm_ring]
    rw [M.ac_dndag_updag_sub]
    rw [show M.cUpDag * (-(M.cUpDag * M.cDnDag)) * M.cUp
          = -((M.cUpDag * M.cUpDag) * (M.cDnDag * M.cUp)) from by noncomm_ring]
    simp only [M.sq_updag, zero_mul, neg_zero]
  rw [h, zero_mul]

/-- Double occupancy shifts the pair operator: [D, P] = P. -/
theorem doubleOcc_commutator_pairOp : ⟦M.doubleOcc, M.pairOp⟧ = M.pairOp := by
  have hDP : M.doubleOcc * M.pairOp = M.pairOp := by
    rw [doubleOcc, show (M.nUp * M.nDn) * M.pairOp
          = M.nUp * (M.nDn * M.pairOp) from by noncomm_ring, M.nDn_mul_pairOp, M.nUp_mul_pairOp]
  have hPD : M.pairOp * M.doubleOcc = 0 := M.pairOp_mul_doubleOcc
  rw [commutator, hDP, hPD, sub_zero]

/-! ## The total number operator is a ladder -/

/-- The total number operator of the site, N = nUp + nDn. -/
def totalNumber : M.A := M.nUp + M.nDn

/-- The up number operator raises the up mode: [nUp, cUp^dagger] = cUp^dagger. -/
theorem nUp_commutator_cUpDag : ⟦M.nUp, M.cUpDag⟧ = M.cUpDag := by
  have hkey : M.cUpDag * (M.cUpDag * M.cUp) = 0 := by
    rw [show M.cUpDag * (M.cUpDag * M.cUp)
          = (M.cUpDag * M.cUpDag) * M.cUp from by noncomm_ring]
    simp only [M.sq_updag, zero_mul]
  have hdcd : M.cUpDag * (M.cUp * M.cUpDag) = M.cUpDag := by
    rw [M.car_up_sub]
    rw [show M.cUpDag * (1 - M.cUpDag * M.cUp)
          = M.cUpDag - M.cUpDag * (M.cUpDag * M.cUp) from by noncomm_ring]
    simp only [hkey, sub_zero]
  rw [nUp, commutator, show (M.cUpDag * M.cUp) * M.cUpDag
        = M.cUpDag * (M.cUp * M.cUpDag) from by noncomm_ring, hdcd, hkey, sub_zero]

/-- The down number operator commutes with the up creation operator. -/
theorem nDn_commutator_cUpDag : ⟦M.nDn, M.cUpDag⟧ = 0 := by
  have h1 : (M.cDnDag * M.cDn) * M.cUpDag = M.cUpDag * (M.cDnDag * M.cDn) := by
    rw [show (M.cDnDag * M.cDn) * M.cUpDag
          = M.cDnDag * (M.cDn * M.cUpDag) from by noncomm_ring, M.ac_dn_updag_sub]
    rw [show M.cDnDag * (-(M.cUpDag * M.cDn))
          = -((M.cDnDag * M.cUpDag) * M.cDn) from by noncomm_ring]
    rw [M.ac_dndag_updag_sub]
    rw [show -((-(M.cUpDag * M.cDnDag)) * M.cDn)
          = M.cUpDag * (M.cDnDag * M.cDn) from by noncomm_ring]
  rw [nDn, commutator, h1, sub_self]

/-- The total number operator raises the up mode: [nUp + nDn, cUp^dagger] = cUp^dagger. -/
theorem totalNumber_commutator_cUpDag :
    ⟦M.totalNumber, M.cUpDag⟧ = M.cUpDag := by
  rw [totalNumber, commutator_add_left, M.nUp_commutator_cUpDag,
      M.nDn_commutator_cUpDag, add_zero]

end HubbardSite

end LeanPhy.Condensed
