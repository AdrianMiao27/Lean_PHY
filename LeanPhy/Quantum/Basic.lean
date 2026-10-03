import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing

/-!
# Finite-dimensional quantum objects

The finite-dimensional layer is deliberately represented by mathlib's matrices
and finite functions.  This means the kernel checks ordinary matrix proofs,
while the physics-facing names (`Ket`, `Bra`, `Operator`, `commutator`) make
the statements readable to physicists.
-/

namespace LeanPhy.Quantum

universe u

abbrev Ket (n : Nat) := Fin n → ℂ
abbrev Bra (n : Nat) := Fin n → ℂ
abbrev Operator (n : Nat) := Matrix (Fin n) (Fin n) ℂ

def identity {n : Nat} : Operator n := 1

def commutator {A : Type u} [Sub A] [Mul A] (x y : A) : A := x * y - y * x

def anticommutator {A : Type u} [Add A] [Mul A] (x y : A) : A := x * y + y * x

scoped notation "⟦" A "," B "⟧" => commutator A B
scoped notation "⟪" A "," B "⟫" => anticommutator A B


@[simp] theorem commutator_self {A : Type u} [Ring A] (x : A) : ⟦x, x⟧ = 0 := by
  simp [commutator]

theorem commutator_mul_left {A : Type u} [Ring A] (x y z : A) :
    ⟦x * y, z⟧ = x * ⟦y, z⟧ + ⟦x, z⟧ * y := by
  simp only [commutator, mul_sub, sub_mul]
  noncomm_ring

theorem commutator_mul_right {A : Type u} [Ring A] (x y z : A) :
    ⟦x, y * z⟧ = ⟦x, y⟧ * z + y * ⟦x, z⟧ := by
  simp only [commutator, mul_sub, sub_mul]
  noncomm_ring

theorem anticommutator_comm {A : Type u} [AddCommMagma A] [Mul A] (x y : A) :
    ⟪x, y⟫ = ⟪y, x⟫ := by
  simp only [anticommutator, add_comm]

theorem commutator_skew {A : Type u} [Ring A] (x y : A) :
    ⟦x, y⟧ = -⟦y, x⟧ := by
  simp only [commutator]
  noncomm_ring

theorem commutator_add_left {A : Type u} [Ring A] (x y z : A) :
    ⟦x + y, z⟧ = ⟦x, z⟧ + ⟦y, z⟧ := by
  simp only [commutator, add_mul, mul_add, sub_add, add_sub]
  noncomm_ring

theorem commutator_add_right {A : Type u} [Ring A] (x y z : A) :
    ⟦x, y + z⟧ = ⟦x, y⟧ + ⟦x, z⟧ := by
  simp only [commutator, add_mul, mul_add, sub_add, add_sub]
  noncomm_ring

end LeanPhy.Quantum
