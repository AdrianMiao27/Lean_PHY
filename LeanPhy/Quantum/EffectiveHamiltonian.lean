import LeanPhy.Mathematics.BlockElimination
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option autoImplicit false

/-!
# Energy-dependent effective Hamiltonians and effective observables

An invertible heavy resolvent `D - z I` eliminates the heavy component of an
actual finite block eigenvalue equation. The resulting `H_eff(z)` is generally
energy dependent. Reconstruction is not assumed unitary: quadratic probes
become `F† O F` and the state norm becomes `F† F`. Keeping this metric avoids
silently normalizing a reconstructed eigenstate by its light component alone.
No small parameter, spectral gap estimate, or truncation error is inferred.
-/

namespace LeanPhy.Quantum.EnergyElimination

open LeanPhy.Mathematics.BlockElimination
open scoped Matrix

variable {L H : Type*} [Fintype L] [Fintype H] [DecidableEq L] [DecidableEq H]

/-- A supplied heavy resolvent inverse, bound to the actual heavy block and energy. -/
structure Model (L H : Type*) [Fintype H] [DecidableEq H] where
  light : Matrix L L ℂ
  toLight : Matrix L H ℂ
  toHeavy : Matrix H L ℂ
  heavy : Matrix H H ℂ
  energy : ℂ
  resolvent : (Matrix H H ℂ)ˣ
  resolvent_eq : (resolvent : Matrix H H ℂ) = heavy - energy • 1

namespace Model

variable (M : Model L H)

def system : System ℂ L H where
  light := M.light - M.energy • 1
  toLight := M.toLight
  toHeavy := M.toHeavy
  heavy := M.resolvent

def hamiltonian : Matrix (L ⊕ H) (L ⊕ H) ℂ :=
  Matrix.fromBlocks M.light M.toLight M.toHeavy M.heavy

def effectiveHamiltonian : Matrix L L ℂ :=
  M.light - M.toLight * (↑(M.resolvent⁻¹) : Matrix H H ℂ) * M.toHeavy

/-- Reconstruction matrix, including the sign from the heavy equation. -/
def liftMatrix : Matrix (L ⊕ H) L ℂ :=
  Matrix.fromRows 1 (-(↑(M.resolvent⁻¹) : Matrix H H ℂ) * M.toHeavy)

theorem liftMatrix_mulVec (x : L → ℂ) :
    M.liftMatrix.mulVec x = Sum.elim x (M.system.reconstruct x 0) := by
  simp [liftMatrix, Matrix.fromRows_mulVec, System.reconstruct, system,
    Matrix.neg_mulVec, Matrix.mulVec_neg, Matrix.mulVec_mulVec]

/-- Exact equivalence of the full and reduced eigenvalue equations. This
theorem allows the zero vector; nonzero states are handled separately below. -/
theorem eigen_equation_iff (x : L → ℂ) (y : H → ℂ) :
    M.hamiltonian.mulVec (Sum.elim x y) = M.energy • Sum.elim x y ↔
      M.effectiveHamiltonian.mulVec x = M.energy • x ∧
        y = M.system.reconstruct x 0 := by
  have hblock :
      M.hamiltonian.mulVec (Sum.elim x y) = M.energy • Sum.elim x y ↔
        M.system.Satisfies x y 0 0 := by
    rw [hamiltonian, Matrix.fromBlocks_mulVec]
    simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
    constructor
    · intro h
      have hL := congrArg (fun f i => f (Sum.inl i)) h
      have hH := congrArg (fun f i => f (Sum.inr i)) h
      change M.light.mulVec x + M.toLight.mulVec y = M.energy • x at hL
      change M.toHeavy.mulVec x + M.heavy.mulVec y = M.energy • y at hH
      change _ ∧ _
      simp only [system, M.resolvent_eq, Matrix.sub_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec]
      exact ⟨by simpa only [sub_add_eq_add_sub] using sub_eq_zero.mpr hL,
        by simpa only [add_sub_assoc] using sub_eq_zero.mpr hH⟩
    · rintro ⟨hL, hH⟩
      simp only [system, M.resolvent_eq, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec] at hL hH
      funext i
      cases i with
      | inl i =>
        have hi := congrFun hL i
        simpa using (show M.light.mulVec x i + M.toLight.mulVec y i =
          M.energy * x i by dsimp at hi ⊢; linear_combination hi)
      | inr i =>
        have hi := congrFun hH i
        simpa using (show M.toHeavy.mulVec x i + M.heavy.mulVec y i =
          M.energy * y i by dsimp at hi ⊢; linear_combination hi)
  rw [hblock, M.system.satisfies_iff]
  have heff : M.system.effective = M.effectiveHamiltonian - M.energy • 1 := by
    unfold system System.effective effectiveHamiltonian
    simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  rw [heff]
  simp [System.effectiveSource, Matrix.sub_mulVec, Matrix.smul_mulVec, sub_eq_zero]

theorem liftMatrix_injective : Function.Injective M.liftMatrix.mulVec := by
  intro x y h
  rw [M.liftMatrix_mulVec, M.liftMatrix_mulVec] at h
  exact congrArg (fun f i => f (Sum.inl i)) h

theorem lifted_ne_zero_iff (x : L → ℂ) : M.liftMatrix.mulVec x ≠ 0 ↔ x ≠ 0 := by
  rw [← Matrix.mulVec_zero M.liftMatrix]
  exact not_congr M.liftMatrix_injective.eq_iff

/-- Every quadratic probe, including density and current probes, must be
pulled back with the reconstruction map. -/
def effectiveObservable (O : Matrix (L ⊕ H) (L ⊕ H) ℂ) : Matrix L L ℂ :=
  M.liftMatrixᴴ * O * M.liftMatrix

def normMetric : Matrix L L ℂ := M.liftMatrixᴴ * M.liftMatrix

theorem quadratic_readout (O : Matrix (L ⊕ H) (L ⊕ H) ℂ) (x : L → ℂ) :
    dotProduct (star (M.liftMatrix.mulVec x)) (O.mulVec (M.liftMatrix.mulVec x)) =
      dotProduct (star x) ((M.effectiveObservable O).mulVec x) := by
  simp [effectiveObservable, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem norm_readout (x : L → ℂ) :
    dotProduct (star (M.liftMatrix.mulVec x)) (M.liftMatrix.mulVec x) =
      dotProduct (star x) (M.normMetric.mulVec x) := by
  simpa [effectiveObservable, normMetric] using M.quadratic_readout 1 x

/-- Heavy admixture changes the normalization metric even before truncation. -/
theorem normMetric_eq :
    M.normMetric = 1 +
      ((↑(M.resolvent⁻¹) : Matrix H H ℂ) * M.toHeavy)ᴴ *
        ((↑(M.resolvent⁻¹) : Matrix H H ℂ) * M.toHeavy) := by
  simp [normMetric, liftMatrix, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows]

theorem effectiveObservable_isHermitian (O : Matrix (L ⊕ H) (L ⊕ H) ℂ)
    (hO : O.IsHermitian) : (M.effectiveObservable O).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_mul M.liftMatrix hO

/-- In a Hermitian block problem at a real off-spectrum energy the resolvent
block is Hermitian; its inverse then preserves Hermiticity of the effective H. -/
theorem effectiveHamiltonian_isHermitian (hA : M.light.IsHermitian)
    (hC : M.toHeavy = M.toLightᴴ)
    (hR : (M.resolvent : Matrix H H ℂ).IsHermitian) :
    M.effectiveHamiltonian.IsHermitian := by
  have hi : (↑(M.resolvent⁻¹) : Matrix H H ℂ).IsHermitian := by
    simpa only [Matrix.coe_units_inv] using hR.inv
  unfold effectiveHamiltonian
  rw [hC]
  exact hA.sub (Matrix.isHermitian_mul_mul_conjTranspose M.toLight hi)

end Model
end LeanPhy.Quantum.EnergyElimination
