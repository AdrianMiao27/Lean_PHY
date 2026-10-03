import LeanPhy.Quantum.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Algebraic symmetries and conserved observables

Many derivations in quantum mechanics, QFT and condensed matter repeatedly use
the same inference: if an observable commutes with a Hamiltonian, then sums,
products and powers of commuting observables are also conserved.  This module
packages those rules without choosing a representation or invoking an
exponential/time-evolution construction.  The result is useful as a common
interface for spin, number, gauge and lattice symmetries.
-/

namespace LeanPhy.Quantum

universe u

/-- An observable is conserved by `H` when its algebraic commutator with `H`
vanishes.  In a concrete model this is the finite-dimensional shadow of the
Heisenberg equation; no differentiability is assumed here. -/
def Conserved {A : Type u} [Ring A] (H O : A) : Prop := ⟦H, O⟧ = 0

theorem conserved_iff {A : Type u} [Ring A] (H O : A) :
    Conserved H O ↔ ⟦H, O⟧ = 0 := Iff.rfl

theorem conserved_zero {A : Type u} [Ring A] (H : A) : Conserved H 0 := by
  simp [Conserved, commutator]

theorem conserved_one {A : Type u} [Ring A] (H : A) : Conserved H 1 := by
  simp [Conserved, commutator]

theorem conserved_add {A : Type u} [Ring A] (H O P : A)
    (hO : Conserved H O) (hP : Conserved H P) :
    Conserved H (O + P) := by
  unfold Conserved at hO hP ⊢
  rw [commutator_add_right, hO, hP, add_zero]

theorem conserved_mul {A : Type u} [Ring A] (H O P : A)
    (hO : Conserved H O) (hP : Conserved H P) :
    Conserved H (O * P) := by
  unfold Conserved at hO hP ⊢
  rw [commutator_mul_right, hO, hP, zero_mul, mul_zero, add_zero]

/-- Multiplication by a coefficient is safe when that coefficient is central
with respect to the Hamiltonian.  This is the explicit condition behind the
usual scalar-linear-combination rule in operator algebras. -/
theorem conserved_left_mul_of_central {A : Type u} [Ring A] (H c O : A)
    (hc : Conserved H c) (hO : Conserved H O) :
    Conserved H (c * O) :=
  conserved_mul H c O hc hO

theorem conserved_linear_combination {A : Type u} [Ring A] (H a b O P : A)
    (ha : Conserved H a) (hb : Conserved H b)
    (hO : Conserved H O) (hP : Conserved H P) :
    Conserved H (a * O + b * P) := by
  exact conserved_add H (a * O) (b * P)
    (conserved_left_mul_of_central H a O ha hO)
    (conserved_left_mul_of_central H b P hb hP)

theorem conserved_commutator {A : Type u} [Ring A] (H O P : A)
    (hO : Conserved H O) (hP : Conserved H P) :
    Conserved H ⟦O, P⟧ := by
  unfold Conserved at hO hP ⊢
  have hsub : ⟦H, O * P - P * O⟧ = ⟦H, O * P⟧ - ⟦H, P * O⟧ := by
    simp only [commutator, mul_sub, sub_mul]
    noncomm_ring
  change ⟦H, O * P - P * O⟧ = 0
  rw [hsub, commutator_mul_right, commutator_mul_right, hO, hP]
  simp

theorem conserved_pow {A : Type u} [Ring A] (H O : A) (n : Nat)
    (hO : Conserved H O) : Conserved H (O ^ n) := by
  induction n with
  | zero => simpa [pow_zero] using conserved_one H
  | succ n ih =>
      rw [pow_succ]
      exact conserved_mul H (O ^ n) O ih hO

theorem commuting_of_conserved {A : Type u} [Ring A] (H O : A)
    (hO : Conserved H O) : H * O = O * H := by
  exact sub_eq_zero.mp hO

/- A natural linear combination is always safe in a noncommutative algebra. -/
theorem conserved_nsmul {A : Type u} [Ring A] (H O : A) (n : Nat)
    (hO : Conserved H O) : Conserved H (n • O) := by
  induction n with
  | zero => simpa using conserved_zero H
  | succ n ih =>
      rw [succ_nsmul]
      exact conserved_add H (n • O) O ih hO

end LeanPhy.Quantum
