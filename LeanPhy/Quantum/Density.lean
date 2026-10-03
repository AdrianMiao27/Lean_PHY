import LeanPhy.Quantum.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Complex.Basic

/-! Finite-dimensional states and measurements. -/

namespace LeanPhy.Quantum

open scoped Matrix

open scoped ComplexOrder
open scoped BigOperators

abbrev State (n : Nat) := Matrix (Fin n) (Fin n) ℂ
abbrev Observable (n : Nat) := Operator n

def trace {n : Nat} (ρ : State n) : ℂ := Matrix.trace ρ

def IsDensity {n : Nat} (ρ : State n) : Prop :=
  ρ.IsHermitian ∧ ρ.PosSemidef ∧ trace ρ = 1

def expectation {n : Nat} (ρ : State n) (A : Observable n) : ℂ := trace (ρ * A)

theorem expectation_add {n : Nat} (ρ : State n) (A B : Observable n) :
    expectation ρ (A + B) = expectation ρ A + expectation ρ B := by
  simp only [expectation, trace, mul_add, Matrix.trace_add]

theorem expectation_smul {n : Nat} (ρ : State n) (A : Observable n) (c : ℂ) :
    expectation ρ (c • A) = c * expectation ρ A := by
  rw [expectation, trace, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, expectation, trace]

def projector {n : Nat} (v : Ket n) : State n :=
  fun i j => v i * star (v j)

theorem projector_apply {n : Nat} (v : Ket n) (i j : Fin n) :
    projector v i j = v i * star (v j) := rfl

theorem trace_projector {n : Nat} (v : Ket n) :
    trace (projector v) = ∑ i, v i * star (v i) := by
  simp only [trace, Matrix.trace, projector, Matrix.diag_apply]

end LeanPhy.Quantum
