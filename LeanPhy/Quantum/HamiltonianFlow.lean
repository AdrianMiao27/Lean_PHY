import LeanPhy.Quantum.Unitary
import LeanPhy.Quantum.Symmetry
import LeanPhy.Mathematics.LinearFlow
import LeanPhy.Mathematics.FlowInvariant
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-!
# Finite-dimensional Hamiltonian flow

This module connects a finite Hermitian Hamiltonian to the matrix exponential
used by quantum mechanics.  The analytic existence theory is already supplied
by mathlib's convergent matrix exponential; the physics layer checks the
algebraic consequences: `exp (i t H)` is unitary, times add under composition,
and conjugation preserves finite density-state invariants.  It is intentionally
finite-dimensional and makes no Stone theorem or unbounded-operator claim.
-/

namespace LeanPhy.Quantum

open NormedSpace
open scoped Matrix Matrix.Norms.Operator ComplexOrder BigOperators

noncomputable def hamiltonianGenerator {ι : Type*}
    (t : ℝ) (H : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (t : ℂ) • (Complex.I • H)

theorem hamiltonianGenerator_skewAdjoint {ι : Type*} [Fintype ι]
    [DecidableEq ι] (t : ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    hamiltonianGenerator t H ∈ skewAdjoint (Matrix ι ι ℂ) := by
  unfold hamiltonianGenerator
  rw [skewAdjoint.mem_iff]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul]
  rw [hH]
  simp

/-- `exp (i t H)` as a generic finite-index unitary. -/
noncomputable def finiteHamiltonianFlow {ι : Type*} [Fintype ι]
    [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (t : ℝ) :
    FiniteUnitary ι := by
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  let G := hamiltonianGenerator t H
  have hG : G ∈ skewAdjoint (Matrix ι ι ℂ) :=
    hamiltonianGenerator_skewAdjoint t H hH
  have hstar : Gᴴ = -G := by
    have hs := (skewAdjoint.mem_iff.mp hG)
    simpa [Matrix.star_eq_conjTranspose] using hs
  have hunit : (NormedSpace.exp G)ᴴ * NormedSpace.exp G = 1 := by
    rw [← Matrix.exp_conjTranspose G, hstar, Matrix.exp_neg]
    have hu : IsUnit (NormedSpace.exp G) := Matrix.isUnit_exp G
    rw [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_of_isUnit hu]
    exact Units.inv_mul hu.unit
  exact { op := NormedSpace.exp G, unitary := hunit }

@[simp] theorem finiteHamiltonianFlow_op {ι : Type*} [Fintype ι]
    [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (finiteHamiltonianFlow H hH t).op =
      NormedSpace.exp (hamiltonianGenerator t H) := by
  rfl

theorem finiteHamiltonianFlow_zero {ι : Type*} [Fintype ι]
    [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (finiteHamiltonianFlow H hH 0).op = 1 := by
  rw [finiteHamiltonianFlow_op]
  simp [hamiltonianGenerator]

theorem hamiltonianGenerator_add {ι : Type*} [Fintype ι]
    [DecidableEq ι] (H : Matrix ι ι ℂ) (t s : ℝ) :
    hamiltonianGenerator (t + s) H =
      hamiltonianGenerator t H + hamiltonianGenerator s H := by
  unfold hamiltonianGenerator
  simp only [Complex.ofReal_add, add_smul]

theorem hamiltonianGenerator_commute {ι : Type*} [Fintype ι]
    [DecidableEq ι] (H : Matrix ι ι ℂ) (t s : ℝ) :
    Commute (hamiltonianGenerator t H) (hamiltonianGenerator s H) := by
  unfold hamiltonianGenerator
  change (((t : ℂ) • (Complex.I • H)) * ((s : ℂ) • (Complex.I • H))) =
    (((s : ℂ) • (Complex.I • H)) * ((t : ℂ) • (Complex.I • H)))
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  ring

theorem finiteHamiltonianFlow_add_op {ι : Type*} [Fintype ι]
    [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (t s : ℝ) :
    (finiteHamiltonianFlow H hH (t + s)).op =
      (finiteHamiltonianFlow H hH t).op *
        (finiteHamiltonianFlow H hH s).op := by
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  rw [finiteHamiltonianFlow_op, hamiltonianGenerator_add]
  rw [Matrix.exp_add_of_commute _ _ (hamiltonianGenerator_commute H t s)]
  rw [finiteHamiltonianFlow_op, finiteHamiltonianFlow_op]

theorem finiteHamiltonianFlow_add {ι : Type*} [Fintype ι]
    [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (t s : ℝ) :
    finiteHamiltonianFlow H hH (t + s) =
      (finiteHamiltonianFlow H hH t).compose (finiteHamiltonianFlow H hH s) := by
  apply FiniteUnitary.ext
  exact finiteHamiltonianFlow_add_op H hH t s

/-- If an observable commutes with a finite Hamiltonian, its Heisenberg
    conjugate is exactly constant along the checked matrix-exponential flow.
    This is the finite algebraic shadow of the Heisenberg conservation law;
    no differentiability or infinite-dimensional Stone theorem is assumed. -/
theorem finiteHamiltonianFlow_conjugate_of_conserved {ι : Type*} [Fintype ι]
    [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (t : ℝ) (O : Matrix ι ι ℂ) (hO : Conserved H O) :
    (finiteHamiltonianFlow H hH t).conjugate O = O := by
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  let G := hamiltonianGenerator t H
  have hHO : Commute H O := (commute_iff_eq H O).2 (sub_eq_zero.mp hO)
  have hGO : Commute G O := by
    exact (hHO.smul_left (Complex.I)).smul_left (t : ℂ)
  have hExp : Commute (NormedSpace.exp G) O := hGO.exp_left
  have hGstar : Gᴴ = -G := by
    have hGmem := hamiltonianGenerator_skewAdjoint t H hH
    have hs := (skewAdjoint.mem_iff.mp hGmem)
    simpa [Matrix.star_eq_conjTranspose] using hs
  have hconj : (NormedSpace.exp G)ᴴ = (NormedSpace.exp G)⁻¹ := by
    rw [← Matrix.exp_conjTranspose G, hGstar, Matrix.exp_neg]
  have hu : IsUnit (NormedSpace.exp G) := Matrix.isUnit_exp G
  rw [FiniteUnitary.conjugate, finiteHamiltonianFlow_op]
  change NormedSpace.exp G * O * (NormedSpace.exp G)ᴴ = O
  rw [hconj, hExp.eq]
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_eq_ringInverse,
    Ring.mul_inverse_cancel _ hu, Matrix.mul_one]

theorem finiteHamiltonianFlow_conjugate_trace {ι : Type*} [Fintype ι]
    [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (t : ℝ) (rho : Matrix ι ι ℂ) :
    Matrix.trace ((finiteHamiltonianFlow H hH t).conjugate rho) =
      Matrix.trace rho := by
  exact FiniteUnitary.conjugate_trace (finiteHamiltonianFlow H hH t) rho

theorem finiteHamiltonianFlow_conjugate_posSemidef {ι : Type*} [Fintype ι]
    [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (t : ℝ) (rho : Matrix ι ι ℂ) (hrho : rho.PosSemidef) :
    ((finiteHamiltonianFlow H hH t).conjugate rho).PosSemidef := by
  exact FiniteUnitary.conjugate_posSemidef (finiteHamiltonianFlow H hH t) rho hrho

/-! The Hamiltonian construction also instantiates the domain-neutral finite
linear-flow interface.  This is the reusable entry point for later adapters
to BdG, linear response and finite-volume evolution. -/

noncomputable def finiteHamiltonianEvolution {ι : Type*} [Fintype ι]
    [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    LeanPhy.Mathematics.FiniteMatrixFlow (𝕜 := ℂ) ι where
  flow := fun t => (finiteHamiltonianFlow H hH t).op
  zero := finiteHamiltonianFlow_zero H hH
  add := finiteHamiltonianFlow_add_op H hH

@[simp] theorem finiteHamiltonianEvolution_flow {ι : Type*} [Fintype ι]
    [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (finiteHamiltonianEvolution H hH).flow t =
      (finiteHamiltonianFlow H hH t).op := rfl

/-! The Hamiltonian adapter also consumes the domain-neutral flow-invariant
theorem.  This keeps the physical commutator assumption visible while making
the resulting statement available to all modules that only know a
`FiniteMatrixFlow`. -/

theorem finiteHamiltonianEvolution_isInvariant {ι : Type*} [Fintype ι]
    [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (O : Matrix ι ι ℂ) (hO : Conserved H O) :
    (finiteHamiltonianEvolution H hH).IsInvariant O := by
  have hHO : Commute H O := (commute_iff_eq H O).2 (sub_eq_zero.mp hO)
  have hGO : Commute (Complex.I • H) O := hHO.smul_left Complex.I
  have h := LeanPhy.Mathematics.FiniteMatrixFlow.exponential_isInvariant_of_commute
    (Complex.I • H) O hGO
  intro t
  exact h t

end LeanPhy.Quantum
