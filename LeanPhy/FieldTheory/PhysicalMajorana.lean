import LeanPhy.FieldTheory.FermionLinear

set_option autoImplicit false

/-! Physical Majorana operators with explicit adjoints and phase convention.
For γx = c + c† and γy = -i(c-c†), occupation is
`n = (1 + i γx γy)/2`. The sign follows this convention and is proved below. -/

namespace LeanPhy.FieldTheory.MultiModeCAR

open LeanPhy.Quantum

variable {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A]
variable (M : MultiModeCAR ι A)

theorem ann_sq_zero (i : ι) : M.ann i * M.ann i = 0 := by
  have h := congrArg (fun x : A => (1 / 2 : ℂ) • x) (M.car_ann_ann i i)
  simp only [anticommutator, smul_add, smul_zero, ← add_smul] at h
  norm_num at h
  exact h

theorem cre_sq_zero (i : ι) : M.cre i * M.cre i = 0 := by
  have h := congrArg (fun x : A => (1 / 2 : ℂ) • x) (M.car_cre_cre i i)
  simp only [anticommutator, smul_add, smul_zero, ← add_smul] at h
  norm_num at h
  exact h

def majoranaX (i : ι) : A := M.ann i + M.cre i
def majoranaY (i : ι) : A := (-Complex.I) • (M.ann i - M.cre i)

theorem majoranaX_sq (i : ι) : M.majoranaX i * M.majoranaX i = 1 := by
  have h := M.car_ann_cre i i
  simp only [anticommutator, ite_true] at h
  unfold majoranaX
  calc
    _ = (M.ann i * M.ann i + M.cre i * M.cre i) +
        (M.ann i * M.cre i + M.cre i * M.ann i) := by noncomm_ring
    _ = 1 := by rw [M.ann_sq_zero, M.cre_sq_zero, h]; simp

theorem majoranaY_sq (i : ι) : M.majoranaY i * M.majoranaY i = 1 := by
  have h := M.car_ann_cre i i
  simp only [anticommutator, ite_true] at h
  have hs : (M.ann i - M.cre i) * (M.ann i - M.cre i) = -(1 : A) := by
    calc
      _ = (M.ann i * M.ann i + M.cre i * M.cre i) -
          (M.ann i * M.cre i + M.cre i * M.ann i) := by noncomm_ring
      _ = -1 := by rw [M.ann_sq_zero, M.cre_sq_zero, h]; simp
  simp only [majoranaY, smul_mul_smul_comm, hs]
  norm_num

/-- In this phase convention the occupation formula has a plus sign. -/
theorem occupation_majorana (i : ι) :
    M.numberOp i = (1 / 2 : ℂ) •
      (1 + Complex.I • (M.majoranaX i * M.majoranaY i)) := by
  have h := M.car_ann_cre i i
  simp only [anticommutator, ite_true] at h
  have hc : (M.ann i + M.cre i) * (M.ann i - M.cre i) =
      (2 : ℂ) • (M.cre i * M.ann i) - 1 := by
    simp only [two_smul]
    calc
      _ = (M.ann i * M.ann i - M.cre i * M.cre i) +
          (M.cre i * M.ann i + M.cre i * M.ann i) -
          (M.ann i * M.cre i + M.cre i * M.ann i) := by noncomm_ring
      _ = _ := by rw [M.ann_sq_zero, M.cre_sq_zero, h]; simp
  rw [majoranaX, majoranaY, mul_smul_comm, hc, smul_smul]
  norm_num
  simp [numberOp, smul_add, smul_sub, smul_smul]

section Adjoint

variable [StarRing A] [StarModule ℂ A]
variable (hstar : ∀ i, M.cre i = star (M.ann i))
include hstar

theorem majoranaX_selfAdjoint (i : ι) : star (M.majoranaX i) = M.majoranaX i := by
  simp [majoranaX, hstar, add_comm]

theorem majoranaY_selfAdjoint (i : ι) : star (M.majoranaY i) = M.majoranaY i := by
  simp only [majoranaY, star_smul, star_sub, ← hstar]
  rw [hstar i, star_star]
  simp only [star_neg, Complex.star_def, Complex.conj_I, neg_neg]
  rw [← neg_sub (M.ann i) (star (M.ann i)), smul_neg, neg_smul]

end Adjoint
end LeanPhy.FieldTheory.MultiModeCAR
