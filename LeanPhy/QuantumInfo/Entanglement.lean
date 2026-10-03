import LeanPhy.QuantumInfo.Bell
import LeanPhy.Quantum.Density
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Entanglement measures: purity and the Renyi-2 entropy

The von Neumann entropy needs a logarithm, which is analysis; the Renyi-2
entropy does not.  For a state rho the purity is tr (rho^2) and the Renyi-2
entropy is -log tr (rho^2), so the algebraic content is entirely in the purity.
This file proves that content exactly over the complex matrices: the maximally
mixed qubit has purity 1/2 (the value that signals maximal entanglement of a
purifying pair), a pure projector has purity 1, and purity scales as the square
under  c . rho.

Everything is checked by the kernel; no logarithm and no analysis enters.
-/

namespace LeanPhy.QuantumInfo

open LeanPhy.Quantum
open scoped BigOperators Matrix

/-- The purity of a state, tr (rho^2), the algebraic core of the Renyi-2
entropy. -/
noncomputable def purity {n : Nat} (rho : State n) : ℂ := Matrix.trace (rho * rho)

/-- The maximally mixed qubit I/2. -/
noncomputable def halfIdentity : State 2 := fun i j => if i = j then (1/2 : ℂ) else 0

/-- The pure qubit state |0><0|. -/
noncomputable def groundProjector : State 2 :=
  fun i j => if i = 0 ∧ j = 0 then (1 : ℂ) else 0

/-- The maximally mixed qubit I/2 has purity 1/2.  For a two-level system this
is the smallest purity of a normalised state, and it is the value that signals
maximal entanglement of a pair that purifies it. -/
theorem purity_maximallyMixed : purity halfIdentity = 1/2 := by
  simp only [purity, Matrix.trace, Matrix.diag, halfIdentity, Matrix.mul_apply,
    Fin.sum_univ_two]
  norm_num

/-- The purity of the pure state |0><0| is 1. -/
theorem purity_pure_projector : purity groundProjector = 1 := by
  simp only [purity, Matrix.trace, Matrix.diag, groundProjector, Matrix.mul_apply,
    Fin.sum_univ_two]
  norm_num

/-- Purity scales as the square: purity (c . rho) = c * c * purity rho. -/
theorem purity_smul {n : Nat} (c : ℂ) (rho : State n) :
    purity (c • rho) = c * c * purity rho := by
  simp only [purity, smul_mul_smul_comm, Matrix.trace_smul, smul_eq_mul]

/-- The reduced state of the (unnormalised) Bell pair is the identity, whose
purity is 2.  For a two-level reduction the minimum purity at trace 2 is
2^2/dim = 2, so the Bell reduction saturates it: the pair is maximally
entangled. -/
theorem purity_bell_marginal : purity (partialTraceRight bellState) = 2 := by
  rw [partialTrace_bell_marginal]
  simp only [purity, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

end LeanPhy.QuantumInfo
