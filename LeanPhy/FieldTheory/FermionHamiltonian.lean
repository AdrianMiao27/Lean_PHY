import LeanPhy.FieldTheory.FermionBilinear
import LeanPhy.FieldTheory.FermionBdG
import LeanPhy.Quantum.FiniteThermalState

set_option autoImplicit false

/-! Bridge coefficient matrices to actual many-body operators. The Nambu
equation is a commutator identity, with no unstated time-evolution convention.
A Gibbs density is constructed on a supplied many-body CAR representation;
the Nambu coefficient matrix is not substituted for that Hilbert space. -/

namespace LeanPhy.FieldTheory.FermionBdG

open LeanPhy.Quantum
open scoped Matrix

variable {ι A : Type} [Fintype ι] [DecidableEq ι]
variable [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

def nambu (M : MultiModeCAR ι A) : ι ⊕ ι → A := Sum.elim M.ann M.cre

noncomputable def act (B : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (ψ : ι ⊕ ι → A)
    (i : ι ⊕ ι) : A := ∑ j, B i j • ψ j

noncomputable def nambuQuadratic (M : MultiModeCAR ι A) (K : Coefficients ι) : A :=
  ∑ i, ∑ j, K.matrix i j • (star (nambu M i) * nambu M j)

/-- Exact energy relation retains the trace constant from normal ordering. -/
theorem nambu_energy (M : MultiModeCAR ι A) (hstar : ∀ i, M.cre i = star (M.ann i))
    (K : Coefficients ι) :
    M.quadratic K.normal K.pairing =
      (1 / 2 : ℂ) • (nambuQuadratic M K + Matrix.trace K.normal • (1 : A)) := by
  have hsc (j : ι) : star (M.cre j) = M.ann j := by rw [hstar, star_star]
  have he : nambuQuadratic M K =
      M.normal K.normal + M.creationPair K.pairing +
        M.annihilationPair K.pairingᴴ - M.antiNormal K.normal.transpose := by
    simp only [nambuQuadratic, Fintype.sum_sum_type, nambu, Coefficients.matrix,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Sum.elim_inl, Sum.elim_inr, ← hstar, hsc,
      Matrix.neg_apply, neg_smul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    simp only [MultiModeCAR.normal, MultiModeCAR.creationPair,
      MultiModeCAR.annihilationPair, MultiModeCAR.antiNormal]
    abel
  rw [he, M.antiNormal_eq, Matrix.transpose_transpose, Matrix.trace_transpose,
    ← M.star_creationPair hstar]
  simp only [MultiModeCAR.quadratic]
  module

/-- The coefficient matrix is derived from the actual quadratic CAR operator. -/
theorem nambu_equation (M : MultiModeCAR ι A) (hstar : ∀ i, M.cre i = star (M.ann i))
    (K : Coefficients ι) (i : ι ⊕ ι) :
    ⟦nambu M i, M.quadratic K.normal K.pairing⟧ = act K.matrix (nambu M) i := by
  cases i with
  | inl k =>
    simpa [act, nambu, Coefficients.matrix, Fintype.sum_sum_type,
      MultiModeCAR.annihilation, MultiModeCAR.creation] using
      M.annihilation_equation hstar K.normal K.pairing K.pairing_skew k
  | inr k =>
    have hsc (j : ι) : star (M.cre j) = M.ann j := by rw [hstar, star_star]
    have hs := congrArg star
      (M.annihilation_equation hstar K.normal K.pairing K.pairing_skew k)
    simp only [LeanPhy.Quantum.commutator, star_sub, star_mul,
      M.quadratic_selfAdjoint hstar _ _ K.normal_hermitian, ← hstar,
      MultiModeCAR.annihilation, MultiModeCAR.creation, star_add, star_sum, star_smul,
      hsc, K.normal_hermitian_apply] at hs
    have hp (j : ι) : star (K.pairing j k) = -star (K.pairing k j) := by
      rw [K.pairing_skew_apply k j, star_neg]
    simp only [act, nambu, Coefficients.matrix, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr,
      Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.transpose_apply,
      hp, neg_smul, Finset.sum_neg_distrib]
    unfold LeanPhy.Quantum.commutator
    calc
      _ = -(M.quadratic K.normal K.pairing * M.cre k -
          M.cre k * M.quadratic K.normal K.pairing) := by abel
      _ = _ := by rw [hs]; abel

section MatrixRepresentation

variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem manyBody_hermitian (M : MultiModeCAR ι (Matrix σ σ ℂ))
    (hstar : ∀ i, M.cre i = (M.ann i)ᴴ) (K : Coefficients ι) :
    (M.quadratic K.normal K.pairing).IsHermitian :=
  M.quadratic_selfAdjoint hstar _ _ K.normal_hermitian

/-- The physical finite thermal state lives on the many-body representation. -/
noncomputable def manyBodyThermalState [Nonempty σ]
    (M : MultiModeCAR ι (Matrix σ σ ℂ)) (hstar : ∀ i, M.cre i = (M.ann i)ᴴ)
    (K : Coefficients ι) (β : ℝ) : FiniteDensity σ :=
  finiteThermalState (M.quadratic K.normal K.pairing) (manyBody_hermitian M hstar K) β

end MatrixRepresentation
end LeanPhy.FieldTheory.FermionBdG
