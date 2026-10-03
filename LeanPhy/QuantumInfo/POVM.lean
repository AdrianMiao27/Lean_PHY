import LeanPhy.Quantum.Density
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
# Finite-dimensional POVMs

This module packages a finite positive-operator-valued measure.  The effects
are positive semidefinite matrices and their finite sum is the identity.  The
kernel-checked result supplied here is the part of a measurement rule that is
purely algebraic: the outcome weights sum to the trace of the input state, and
therefore to one for a density matrix.

The weights are deliberately returned as complex numbers, matching the rest of
the finite matrix API.  A future order bridge can add the theorem that these
weights are real and nonnegative under the usual Hermiticity assumptions; it is
not silently treated as an axiom in this layer.
-/

namespace LeanPhy.QuantumInfo

open LeanPhy.Quantum
open scoped BigOperators Matrix
open scoped ComplexOrder
open scoped MatrixOrder

/-- A finite POVM on an `n`-dimensional system. -/
structure POVM (n : Nat) (ι : Type) [Fintype ι] where
  effect : ι → Operator n
  positive : ∀ i, (effect i).PosSemidef
  complete : (∑ i, effect i) = 1

instance {n : Nat} {ι : Type} [Fintype ι] : CoeFun (POVM n ι) (fun _ => ι → Operator n) :=
  ⟨POVM.effect⟩

/-- The algebraic outcome weight `tr (rho E_i)`. -/
noncomputable def weight {n : Nat} {ι : Type} [Fintype ι]
    (M : POVM n ι) (rho : State n) (i : ι) : ℂ :=
  Matrix.trace (rho * M.effect i)

/-- A POVM's outcome weights add up to the input trace. -/
theorem weight_sum {n : Nat} {ι : Type} [Fintype ι]
    (M : POVM n ι) (rho : State n) :
    (∑ i, weight M rho i) = Matrix.trace rho := by
  unfold weight
  calc
    (∑ i, Matrix.trace (rho * M.effect i)) =
        Matrix.trace (∑ i, rho * M.effect i) := by
      rw [Matrix.trace_sum]
    _ = Matrix.trace (rho * (∑ i, M.effect i)) := by
      congr 1
      rw [Finset.mul_sum]
    _ = Matrix.trace rho := by
      rw [M.complete, Matrix.mul_one]

/-- A POVM on a density matrix has normalized total weight. -/
theorem weight_sum_is_one {n : Nat} {ι : Type} [Fintype ι]
    (M : POVM n ι) (rho : State n) (hrho : IsDensity rho) :
    (∑ i, weight M rho i) = 1 :=
  (weight_sum M rho).trans hrho.2.2

/-! ## The order bridge for Born probabilities

`Matrix.PosSemidef.trace_mul_nonneg` is the finite-dimensional fact that turns
two positive operators into a nonnegative real trace.  It is proved here from
the matrix square-root theorem rather than imported as an application axiom.
-/

theorem trace_mul_posSemidef_nonneg {n : Nat} (A B : Operator n)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  obtain ⟨sqrtB, rfl⟩ : ∃ sqrtB : Operator n,
      B = sqrtBᴴ * sqrtB := by
    classical
    apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    exact Matrix.nonneg_iff_posSemidef.mpr hB
  simp only [← Matrix.mul_assoc, ← Matrix.trace_mul_comm sqrtB]
  have h : (sqrtB * A * sqrtBᴴ).PosSemidef := by
    convert hA.conjTranspose_mul_mul_same sqrtBᴴ using 1
    simp [Matrix.mul_assoc]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at h
  simpa [Matrix.mulVec, dotProduct, Matrix.trace, Pi.single_apply] using
    Finset.sum_nonneg fun i _ ↦ h.2 (Pi.single i 1)

/-- A Born probability, represented in the real scalar field. -/
noncomputable def probability {n : Nat} {ι : Type} [Fintype ι]
    (M : POVM n ι) (rho : State n) (i : ι) : ℝ :=
  (weight M rho i).re

theorem probability_nonneg {n : Nat} {ι : Type} [Fintype ι]
    (M : POVM n ι) (rho : State n) (hrho : IsDensity rho) (i : ι) :
    0 ≤ probability M rho i := by
  exact (Complex.nonneg_iff.mp
    (trace_mul_posSemidef_nonneg rho (M.effect i) hrho.2.1 (M.positive i))).1

theorem weight_eq_ofReal_probability {n : Nat} {ι : Type} [Fintype ι]
    (M : POVM n ι) (rho : State n) (hrho : IsDensity rho) (i : ι) :
    weight M rho i = (probability M rho i : ℂ) := by
  have h := Complex.nonneg_iff.mp
    (trace_mul_posSemidef_nonneg rho (M.effect i) hrho.2.1 (M.positive i))
  apply Complex.ext
  · simp [probability]
  · simpa [weight] using h.2.symm

theorem probability_sum_is_one {n : Nat} {ι : Type} [Fintype ι]
    (M : POVM n ι) (rho : State n) (hrho : IsDensity rho) :
    (∑ i, probability M rho i) = 1 := by
  have hweight : (∑ i, weight M rho i) = (1 : ℂ) := weight_sum_is_one M rho hrho
  have hreal : ∀ i, weight M rho i = (probability M rho i : ℂ) :=
    fun i ↦ weight_eq_ofReal_probability M rho hrho i
  rw [Finset.sum_congr rfl (fun i _ ↦ hreal i)] at hweight
  simpa using congrArg Complex.re hweight

/-- The two computational-basis effects on a qubit. -/
noncomputable def computationalQubitEffect0 : Operator 2 := Matrix.diagonal ![1, 0]

noncomputable def computationalQubitEffect1 : Operator 2 := Matrix.diagonal ![0, 1]

theorem computationalQubitEffect0_pos : computationalQubitEffect0.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [computationalQubitEffect0]

theorem computationalQubitEffect1_pos : computationalQubitEffect1.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [computationalQubitEffect1]

noncomputable def computationalQubit : POVM 2 (Fin 2) where
  effect := ![computationalQubitEffect0, computationalQubitEffect1]
  positive := by
    intro i
    fin_cases i
    · exact computationalQubitEffect0_pos
    · exact computationalQubitEffect1_pos
  complete := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [computationalQubitEffect0, computationalQubitEffect1, Fin.sum_univ_two]

theorem computationalQubit_weight_sum (rho : State 2) :
    weight computationalQubit rho 0 + weight computationalQubit rho 1 =
      Matrix.trace rho := by
  simpa [Fin.sum_univ_two] using (weight_sum computationalQubit rho)

end LeanPhy.QuantumInfo
