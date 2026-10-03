import LeanPhy.Quantum.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Wick's theorem for a free bosonic mode (highest-risk tier)

This module formalises the algebraic core of Wick's theorem for one free
bosonic mode.  Everything is stated as pure ring algebra with explicit
hypotheses, so no analysis (unbounded operators, domains, convergence) enters.

The honest scope statement, which is the point of this file:

* PROVED here: the recursion that drives Wick's theorem, together with the
  general closed form that every even-point function equals a double factorial,
  omega (phi^(2k)) = (2k-1)!!, and the small cases as instances.  The recursion
  and the closed form are genuine theorems, not axioms.  The statement that all
  odd-point functions vanish is also proved, which is the other half of the
  textbook form of Wick's theorem for a free field.

* PROVED also (in LeanPhy/FieldTheory/Pairing): the combinatorial pairing
  statement.  The set of perfect matchings is built as a concrete executable
  list (`pairings`), and `numMatchings_eq` proves that for a list of even
  length 2n the number of pairings is exactly the double factorial (2n-1)!!.
  `wick_pairing_count` then ties the two together: the (2k)-point function of
  a free mode equals the number of perfect matchings of 2k objects.  With the
  unit two-point function of a free mode every pairing contributes the same
  product, so the sum over pairings collapses to the pairing count; the
  sign/ordering bookkeeping that a multi-field or fermionic statement would
  need is not exercised here.
-/

namespace LeanPhy.FieldTheory

open LeanPhy.Quantum

/-- A free bosonic mode together with a vacuum expectation functional.

The functional omega is additive and normalised (omega 1 = 1); it annihilates
the vacuum on both sides (omega (a * x) = 0 and omega (d * x) = 0), which is
exactly the statement that a lowers the vacuum and d raises into a state
orthogonal to it. -/
structure FreeMode where
  A : Type
  [ringA : Ring A]
  a : A
  adag : A
  /-- The canonical commutation relation, [a, a†] = 1. -/
  ccr : a * adag - adag * a = 1
  /-- The vacuum expectation functional. -/
  omega : A →+ ℂ
  omega_one : omega 1 = 1
  omega_right_ann : ∀ x, omega (x * a) = 0
  omega_left_cre : ∀ x, omega (adag * x) = 0

attribute [instance] FreeMode.ringA

namespace FreeMode

variable (M : FreeMode)

/-- The double factorial (2n-1)!!, the number of pairings of 2n objects. -/
def doubleFact : ℕ → ℕ
  | 0 => 1
  | (n+1) => (2*n+1) * doubleFact n

@[simp] theorem doubleFact_zero : doubleFact 0 = 1 := rfl

theorem doubleFact_succ (n : ℕ) : doubleFact (n+1) = (2*n+1) * doubleFact n := rfl

@[simp] theorem doubleFact_one : doubleFact 1 = 1 := by simp [doubleFact]
@[simp] theorem doubleFact_two : doubleFact 2 = 3 := by simp [doubleFact]
@[simp] theorem doubleFact_three : doubleFact 3 = 15 := by simp [doubleFact]
@[simp] theorem doubleFact_four : doubleFact 4 = 105 := by simp [doubleFact]

local notation "ω" => M.omega
local notation "𝕒" => M.a
local notation "𝕕" => M.adag
local notation "φ" => M.a + M.adag

/-- The CCR in the additive normal form used throughout. -/
theorem ccr' : 𝕒 * 𝕕 = 𝕕 * 𝕒 + 1 := by
  have h := M.ccr
  rw [sub_eq_iff_eq_add] at h
  rw [add_comm] at h
  exact h

/-- The free field commutes with its lowering operator up to 1. -/
theorem commutator_phi : ⟦𝕒, φ⟧ = 1 := by
  rw [commutator, mul_add, add_mul, ccr' M]
  noncomm_ring

/-- [a, φ^n] = n φ^(n-1): the seed of the Wick recursion. -/
theorem commutator_pow_succ (m : ℕ) : ⟦𝕒, φ ^ (m+1)⟧ = (m+1) • φ ^ m := by
  induction m with
  | zero => rw [Nat.zero_add, pow_one, commutator_phi M]; simp
  | succ k ih =>
      rw [pow_succ, commutator_mul_right, ih, commutator_phi M, mul_one]
      rw [nsmul_eq_mul, nsmul_eq_mul, pow_succ]
      push_cast
      noncomm_ring

/-- Antisymmetry of the commutator, in the direction used to move a past a
power of the field. -/
theorem mul_eq_mul_add_commutator (n : ℕ) :
    𝕒 * φ ^ n = φ ^ n * 𝕒 + ⟦𝕒, φ ^ n⟧ := by
  rw [commutator]; abel

/-- The Wick recurrence: the (2k+2)-point function is (2k+1) times the
(2k)-point function.  This is the single contraction that all later pairings
encode. -/
theorem wick_rec (k : ℕ) :
    ω (φ ^ (2*k + 2)) = ((2*k+1 : ℕ) : ℂ) * ω (φ ^ (2*k)) := by
  have hp : φ ^ (2*k+2) = (𝕒 + 𝕕) * φ ^ (2*k+1) := by
    rw [show 2*k+2 = 1 + (2*k+1) from by ring, pow_add, pow_one]
  rw [hp, add_mul, map_add, M.omega_left_cre, add_zero]
  rw [mul_eq_mul_add_commutator M (2*k+1), map_add, commutator_pow_succ M (2*k),
    M.omega_right_ann, zero_add, map_nsmul, nsmul_eq_mul]

/-- The one-step recursion in its general (not just even) form:
`ω (φ^(n+2)) = (n+1) ω (φ^n)`.  This is the contraction recursion without
the parity restriction, from which both the even closed form and the vanishing
of odd moments follow. -/
theorem phi_step (n : ℕ) : ω (φ ^ (n+2)) = ((n+1 : ℕ) : ℂ) * ω (φ ^ n) := by
  have hp : φ ^ (n+2) = (𝕒 + 𝕕) * φ ^ (n+1) := by
    rw [show n+2 = 1 + (n+1) from by ring, pow_add, pow_one]
  rw [hp, add_mul, map_add, M.omega_left_cre, add_zero]
  rw [mul_eq_mul_add_commutator M (n+1), map_add, commutator_pow_succ M n,
    M.omega_right_ann, zero_add, map_nsmul, nsmul_eq_mul]

/-- The vacuum annihilates the field itself, `ω φ = 0`. -/
theorem phi_odd_one : ω φ = 0 := by
  rw [add_comm]
  simp only [map_add]
  rw [show ω 𝕒 = 0 from by have h := M.omega_right_ann 1; simpa using h,
      show ω 𝕕 = 0 from by have h := M.omega_left_cre 1; simpa using h, add_zero]

/-- Every odd-point function vanishes: `ω (φ^(2k+1)) = 0`.  Together with
`wick_even_moment` this is the textbook statement of Wick's theorem for a
single free field: odd moments vanish, even moments are the pairing count. -/
theorem phi_odd (k : ℕ) : ω (φ ^ (2*k+1)) = 0 := by
  induction k with
  | zero =>
      rw [Nat.mul_zero, zero_add, pow_one]
      exact phi_odd_one M
  | succ k ih =>
      rw [show 2*(k+1)+1 = (2*k+1)+2 from by ring, phi_step M (2*k+1), ih, mul_zero]

/-- The two-point function is 1. -/
theorem phi_two : ω (φ ^ 2) = 1 := by
  have h := wick_rec M 0
  norm_num at h
  rw [M.omega_one] at h
  simpa using h

/-- Every even moment of the free field has a closed form: the (2k)-point
function is the double factorial (2k-1)!!
`ω (φ^(2k)) = (2k-1)!!`.

This is the numerical content of Wick's theorem for a single free mode: it says
the (2k)-point function equals the number of distinct pairings of 2k objects,
which is exactly `(2k-1)!!`.  The recursion `wick_rec` is the induction step
that `(2k+1) (2k-1)!! = (2k+1)!!` encodes. -/
theorem wick_even_moment (k : ℕ) : ω (φ ^ (2*k)) = (doubleFact k : ℂ) := by
  induction k with
  | zero =>
      rw [Nat.mul_zero, pow_zero]
      simp [doubleFact, M.omega_one]
  | succ k ih =>
      rw [show 2*(k+1) = 2*k + 2 from by ring, wick_rec M k, ih, doubleFact_succ, Nat.cast_mul]

/-- The four-point function is 3 = 3!!. -/
theorem phi_four : ω (φ ^ 4) = 3 := by
  simpa using wick_even_moment M 2

/-- The six-point function is 15 = 5!!. -/
theorem phi_six : ω (φ ^ 6) = 15 := by
  simpa using wick_even_moment M 3

/-- The eight-point function is 105 = 7!!. -/
theorem phi_eight : ω (φ ^ 8) = 105 := by
  simpa using wick_even_moment M 4

end FreeMode

end LeanPhy.FieldTheory
