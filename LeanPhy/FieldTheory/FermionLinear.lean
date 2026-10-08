import LeanPhy.FieldTheory.FermionBilinear
import LeanPhy.Quantum.Unitary

set_option autoImplicit false

/-! Linear mode transformations preserve CAR only when their coefficient rows
are orthonormal. Creation coefficients are conjugated. Rectangular isometries
select a canonical subfamily; a full orbital change uses a square unitary. -/

namespace LeanPhy.FieldTheory.MultiModeCAR

open LeanPhy.Quantum
open scoped Matrix

variable {ι κ A : Type} [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ] [Ring A] [Algebra ℂ A]

private theorem anticommutator_linear (v : ι → A) (w : κ → A)
    (f : ι → ℂ) (g : κ → ℂ) :
    ⟪∑ i, f i • v i, ∑ j, g j • w j⟫ =
      ∑ i, ∑ j, (f i * g j) • ⟪v i, w j⟫ := by
  simp only [anticommutator, Finset.sum_mul, Finset.mul_sum,
    smul_mul_smul_comm, smul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

variable (M : MultiModeCAR ι A)

theorem annihilation_creation (f g : ι → ℂ) :
    ⟪M.annihilation f, M.creation g⟫ = (∑ i, f i * g i) • (1 : A) := by
  rw [annihilation, creation, anticommutator_linear]
  simp [M.car_ann_cre, Finset.sum_smul]

theorem annihilation_annihilation (f g : ι → ℂ) :
    ⟪M.annihilation f, M.annihilation g⟫ = 0 := by
  rw [annihilation, annihilation, anticommutator_linear]
  simp [M.car_ann_ann]

theorem creation_creation (f g : ι → ℂ) :
    ⟪M.creation f, M.creation g⟫ = 0 := by
  rw [creation, creation, anticommutator_linear]
  simp [M.car_cre_cre]

/-- Orthonormal coefficient rows construct actual transformed CAR generators. -/
noncomputable def mix (U : Matrix κ ι ℂ) (hU : U * Uᴴ = 1) : MultiModeCAR κ A where
  ann := fun k => M.annihilation (U k)
  cre := fun k => M.creation (fun i => star (U k i))
  car_ann_cre := by
    intro i j
    rw [M.annihilation_creation]
    have hij := congrArg (fun D : Matrix κ κ ℂ => D i j) hU
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hij
    rw [hij]
    split_ifs <;> simp
  car_ann_ann := fun _ _ => M.annihilation_annihilation _ _
  car_cre_cre := fun _ _ => M.creation_creation _ _

/-- A finite orbital unitary supplies the orthonormal-row certificate. -/
noncomputable def rotate (U : FiniteUnitary ι) : MultiModeCAR ι A :=
  M.mix U.op U.right_unitary

theorem annihilation_mix (U : Matrix κ ι ℂ) (hU : U * Uᴴ = 1) (f : κ → ℂ) :
    (M.mix U hU).annihilation f = M.annihilation (fun j => ∑ i, f i * U i j) := by
  simp only [annihilation, mix, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem rotate_inverse_ann (U : FiniteUnitary ι) (i : ι) :
    ((M.rotate U).rotate U.adjoint).ann i = M.ann i := by
  change (M.mix U.op U.right_unitary).annihilation (U.opᴴ i) = M.ann i
  rw [M.annihilation_mix]
  have hrow : (fun j => ∑ k, U.opᴴ i k * U.op k j) = (fun j => (1 : Matrix ι ι ℂ) i j) := by
    funext j
    exact congrArg (fun D : Matrix ι ι ℂ => D i j) U.unitary
  rw [hrow]
  simp [annihilation, Matrix.one_apply]

/-- The coefficient table transforms together with the orbital generators. -/
theorem normal_mix (U : Matrix κ ι ℂ) (hU : U * Uᴴ = 1) (h : Matrix κ κ ℂ) :
    (M.mix U hU).normal h = M.normal (Uᴴ * h * U) := by
  simp only [normal, mix, creation, annihilation, Finset.sum_mul, Finset.mul_sum,
    Finset.smul_sum, smul_mul_smul_comm, smul_smul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_smul, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext i
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [Complex.star_def]
  ring

theorem creationPair_mix (U : Matrix κ ι ℂ) (hU : U * Uᴴ = 1) (Δ : Matrix κ κ ℂ) :
    (M.mix U hU).creationPair Δ =
      M.creationPair (Uᴴ * Δ * U.map (starRingEnd ℂ)) := by
  simp only [creationPair, mix, creation, Finset.sum_mul, Finset.mul_sum,
    Finset.smul_sum, smul_mul_smul_comm, smul_smul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_smul, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext i
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [Complex.star_def]
  ring

section Adjoint

variable [StarRing A] [StarModule ℂ A]
variable (hstar : ∀ i, M.cre i = star (M.ann i))
include hstar

theorem star_annihilation (f : ι → ℂ) :
    star (M.annihilation f) = M.creation (fun i => star (f i)) := by
  simp only [annihilation, creation, star_sum, star_smul, ← hstar]

theorem mix_cre_eq_star (U : Matrix κ ι ℂ) (hU : U * Uᴴ = 1) (i : κ) :
    (M.mix U hU).cre i = star ((M.mix U hU).ann i) :=
  (M.star_annihilation hstar (U i)).symm

end Adjoint
end LeanPhy.FieldTheory.MultiModeCAR
