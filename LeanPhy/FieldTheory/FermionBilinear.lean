import LeanPhy.FieldTheory.MultiCAR
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Star.Module
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Quadratic fermion operators from actual CAR generators

Arbitrary finite mode labels and complex coefficient tables define quadratic
operators without expanding a many-body matrix. The operator identities are
derived from the supplied CAR representation. Adjoint statements additionally
require the creation operators to be the star of annihilation operators.
-/

namespace LeanPhy.FieldTheory.MultiModeCAR

open LeanPhy.Quantum
open scoped Matrix

variable {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A]
variable (M : MultiModeCAR ι A)

/-- A coefficient vector acting on annihilation operators. -/
noncomputable def annihilation (f : ι → ℂ) : A := ∑ i, f i • M.ann i

/-- A coefficient vector acting on creation operators, without implicit conjugation. -/
noncomputable def creation (f : ι → ℂ) : A := ∑ i, f i • M.cre i

/-- Number-conserving quadratic operator, with no Hermiticity presumed. -/
noncomputable def normal (h : Matrix ι ι ℂ) : A :=
  ∑ i, ∑ j, h i j • (M.cre i * M.ann j)

noncomputable def antiNormal (h : Matrix ι ι ℂ) : A :=
  ∑ i, ∑ j, h i j • (M.ann i * M.cre j)

/-- Reordering a quadratic form produces the trace constant as well as a sign. -/
theorem antiNormal_eq (h : Matrix ι ι ℂ) :
    M.antiNormal h = Matrix.trace h • (1 : A) - M.normal h.transpose := by
  simp only [antiNormal, M.ann_cre_rewrite, smul_sub, Finset.sum_sub_distrib]
  congr 1
  · simp [Matrix.trace, smul_ite, Finset.sum_smul]
  · unfold normal
    rw [Finset.sum_comm]
    rfl

noncomputable def creationPair (Δ : Matrix ι ι ℂ) : A :=
  ∑ i, ∑ j, Δ i j • (M.cre i * M.cre j)

noncomputable def annihilationPair (Δ : Matrix ι ι ℂ) : A :=
  ∑ i, ∑ j, Δ i j • (M.ann i * M.ann j)

/-- The mixed CAR in the opposite order, retaining the index convention. -/
theorem cre_ann (i j : ι) : ⟪M.cre i, M.ann j⟫ = if i = j then 1 else 0 := by
  rw [anticommutator_comm, M.car_ann_cre]
  simp only [eq_comm]

private theorem product_commutator (x y z : A) :
    ⟦x * y, z⟧ = x * ⟪y, z⟫ - ⟪x, z⟫ * y := by
  unfold LeanPhy.Quantum.commutator anticommutator
  noncomm_ring

theorem bilinear_commutator_ann (i j k : ι) :
    ⟦M.cre i * M.ann j, M.ann k⟧ = -(if i = k then M.ann j else 0) := by
  rw [product_commutator, M.car_ann_ann, M.cre_ann]
  split_ifs <;> simp

theorem bilinear_commutator_cre (i j k : ι) :
    ⟦M.cre i * M.ann j, M.cre k⟧ = if j = k then M.cre i else 0 := by
  rw [product_commutator, M.car_ann_cre, M.car_cre_cre]
  split_ifs <;> simp

theorem pair_commutator_ann (i j k : ι) :
    ⟦M.cre i * M.cre j, M.ann k⟧ =
      (if j = k then M.cre i else 0) - (if i = k then M.cre j else 0) := by
  rw [product_commutator, M.cre_ann, M.cre_ann]
  split_ifs <;> simp

theorem annihilationPair_commutator_ann (Δ : Matrix ι ι ℂ) (k : ι) :
    ⟦M.annihilationPair Δ, M.ann k⟧ = 0 := by
  have hz (i j : ι) : ⟦M.ann i * M.ann j, M.ann k⟧ = 0 := by
    rw [product_commutator, M.car_ann_ann, M.car_ann_ann]
    simp
  simp only [annihilationPair, commutator_sum_left]
  simp only [LeanPhy.Quantum.commutator, smul_mul_assoc, mul_smul_comm, ← smul_sub] at hz ⊢
  simp [hz]

private theorem smul_commutator (c : ℂ) (x y : A) :
    ⟦c • x, y⟧ = c • ⟦x, y⟧ := by
  simp [LeanPhy.Quantum.commutator, smul_sub, smul_mul_assoc, mul_smul_comm]

theorem normal_commutator_ann (h : Matrix ι ι ℂ) (k : ι) :
    ⟦M.normal h, M.ann k⟧ = -M.annihilation (h k) := by
  simp only [normal, commutator_sum_left, smul_commutator, M.bilinear_commutator_ann]
  simp [annihilation, Finset.sum_neg_distrib]

theorem normal_commutator_cre (h : Matrix ι ι ℂ) (k : ι) :
    ⟦M.normal h, M.cre k⟧ = M.creation (fun i => h i k) := by
  simp only [normal, commutator_sum_left, smul_commutator, M.bilinear_commutator_cre]
  simp [creation]

/-- Antisymmetric pairing gives the factor two before the Nambu half factor. -/
theorem creationPair_commutator_ann (Δ : Matrix ι ι ℂ)
    (hΔ : Δ.transpose = -Δ) (k : ι) :
    ⟦M.creationPair Δ, M.ann k⟧ = (-2 : ℂ) • M.creation (Δ k) := by
  have hskew (i j : ι) : Δ i j = -Δ j i := by
    simpa using congrArg (fun D : Matrix ι ι ℂ => D j i) hΔ
  simp only [creationPair, commutator_sum_left, smul_commutator,
    M.pair_commutator_ann, smul_sub, Finset.sum_sub_distrib]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [show (∑ i, Δ i k • M.cre i) = -M.creation (Δ k) by
    simp only [creation, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hskew i k, neg_smul]]
  simp [creation, sub_eq_add_neg, two_smul]

section Adjoint

variable [StarRing A] [StarModule ℂ A]
variable (hstar : ∀ i, M.cre i = star (M.ann i))

include hstar

theorem star_normal (h : Matrix ι ι ℂ) : star (M.normal h) = M.normal hᴴ := by
  have hs (i : ι) : star (M.cre i) = M.ann i := by rw [hstar, star_star]
  simp only [normal, star_sum, star_smul, star_mul, hs, ← hstar,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

theorem star_creationPair (Δ : Matrix ι ι ℂ) :
    star (M.creationPair Δ) = M.annihilationPair Δᴴ := by
  have hs (i : ι) : star (M.cre i) = M.ann i := by rw [hstar, star_star]
  simp only [creationPair, annihilationPair, star_sum, star_smul, star_mul, hs,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

/-- Physical pairing includes the adjoint and the double-counting half factor. -/
noncomputable def quadratic (h Δ : Matrix ι ι ℂ) : A :=
  M.normal h + (1 / 2 : ℂ) • (M.creationPair Δ + star (M.creationPair Δ))

theorem quadratic_selfAdjoint (h Δ : Matrix ι ι ℂ) (hh : hᴴ = h) :
    star (M.quadratic h Δ) = M.quadratic h Δ := by
  simp [quadratic, M.star_normal hstar, hh, add_comm]

/-- Exact annihilation equation generated by the actual many-body operator. -/
theorem annihilation_equation (h Δ : Matrix ι ι ℂ)
    (hΔ : Δ.transpose = -Δ) (k : ι) :
    ⟦M.ann k, M.quadratic h Δ⟧ =
      M.annihilation (h k) + M.creation (Δ k) := by
  rw [commutator_skew]
  simp only [quadratic, commutator_add_left, smul_commutator,
    M.normal_commutator_ann, M.creationPair_commutator_ann Δ hΔ,
    M.star_creationPair hstar, M.annihilationPair_commutator_ann, add_zero, smul_smul]
  norm_num [add_comm]

end Adjoint
end LeanPhy.FieldTheory.MultiModeCAR
