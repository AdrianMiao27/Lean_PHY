import LeanPhy.HighEnergy.SpinorCovariant
import Mathlib.Tactic

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# The 16 Dirac covariant matrices and Fierz completeness

A Dirac bilinear `ubar Gamma u` is built from sixteen independent matrices:
the identity, `gamma^5`, the four `gamma^mu`, the four `gamma^mu gamma^5`, and the
six `sigma^{mu nu}`.  These span the full `4 x 4` matrix algebra, and their
completeness is the algebraic heart of every Fierz rearrangement in QED and QCD.
This module writes the sixteen covariants out explicitly and proves their
defining properties on the kernel:

- **trace orthogonality** `tr (Gamma_A Gamma_B) = 4 w_A delta_AB` with the weight
  `w_A = tr (Gamma_A Gamma_A) / 4`, which is `+1` for the scalar, pseudoscalar,
  vector and tensor families and `-1` for the axial-vector family;
- **Fierz completeness**, entrywise,
  `sum_A w_A (Gamma_A)_{ij} (Gamma_A)_{kl} = 4 delta_il delta_jk`,
  the statement that the weighted covariants are a complete orthogonal basis of
  the `4 x 4` matrices;
- the **closure form** `sum_A w_A tr (Gamma_A M) Gamma_A = 4 M` for any `4 x 4`
  matrix `M`, the identity a Fierz rearrangement of an operator product is read
  off from.

Everything is checked entrywise on the explicit chiral representation; the
weights are the kernel-evaluated traces, never assumed.  The sign bookkeeping of
the axial-vector family (the `w_A = -1` cases) is where a Fierz computation is
most often done wrong, so it is worth having the kernel confirm each sign.
-/

namespace LeanPhy.HighEnergy

open LeanPhy.Quantum
open scoped BigOperators Matrix

/-- The sixteen Dirac covariants: `1`, `gamma^5`, the four `gamma^mu`, the four
`gamma^mu gamma^5`, and the six `sigma^{mu nu}`, in the chiral representation. -/
noncomputable def cov : Fin 16 → Matrix (Fin 4) (Fin 4) Complex :=
  ![1, !![-1,0,0,0;0,-1,0,0;0,0,1,0;0,0,0,1],
    !![0,0,1,0;0,0,0,1;1,0,0,0;0,1,0,0],
    !![0,0,0,1;0,0,1,0;0,-1,0,0;-1,0,0,0],
    !![0,0,0,-Complex.I;0,0,Complex.I,0;0,Complex.I,0,0;-Complex.I,0,0,0],
    !![0,0,1,0;0,0,0,-1;-1,0,0,0;0,1,0,0],
    !![0,0,1,0;0,0,0,1;-1,0,0,0;0,-1,0,0],
    !![0,0,0,1;0,0,1,0;0,1,0,0;1,0,0,0],
    !![0,0,0,-Complex.I;0,0,Complex.I,0;0,-Complex.I,0,0;Complex.I,0,0,0],
    !![0,0,1,0;0,0,0,-1;1,0,0,0;0,-1,0,0],
    !![0,-Complex.I,0,0;-Complex.I,0,0,0;0,0,0,Complex.I;0,0,Complex.I,0],
    !![0,-1,0,0;1,0,0,0;0,0,0,1;0,0,-1,0],
    !![-Complex.I,0,0,0;0,Complex.I,0,0;0,0,Complex.I,0;0,0,0,-Complex.I],
    !![1,0,0,0;0,-1,0,0;0,0,1,0;0,0,0,-1],
    !![0,Complex.I,0,0;-Complex.I,0,0,0;0,0,0,Complex.I;0,0,-Complex.I,0],
    !![0,1,0,0;1,0,0,0;0,0,0,1;0,0,1,0]]

/-- The Fierz weights `w_A = tr (Gamma_A Gamma_A) / 4`: `+1` on the scalar,
pseudoscalar, vector and tensor families and `-1` on the axial-vector family. -/
noncomputable def covW : Fin 16 → Complex :=
  ![1, 1, 1, -1, -1, -1, -1, 1, 1, 1, -1, -1, -1, 1, 1, 1]

/-- **Trace-orthogonality of the covariants**: distinct covariants are
trace-orthogonal and each has weight `w_A = tr (Gamma_A^2)/4`,
`tr (Gamma_A Gamma_B) = 4 w_A delta_AB`. -/
theorem cov_trace_orthonormal (a b : Fin 16) :
    (cov a * cov b).trace = 4 * covW a * (if a = b then 1 else 0) := by
  fin_cases a <;> fin_cases b <;>
    simp only [cov, covW, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.cons_val_succ, Matrix.head_cons, Matrix.of_apply, Fin.sum_univ_four] <;>
    norm_num <;> (try simp only [Complex.I_mul_I]) <;> norm_num

/-- **Fierz completeness**, entrywise: the weighted covariants resolve the
identity on the `4 x 4` matrices,
`sum_A w_A (Gamma_A)_{ij} (Gamma_A)_{kl} = 4 delta_il delta_jk`. -/
theorem cov_fierz (i j k l : Fin 4) :
    (∑ a : Fin 16, covW a * cov a i j * cov a k l)
      = 4 * (if i = l then (1 : Complex) else 0) * (if j = k then 1 else 0) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, cov, covW,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num <;> (try simp only [Complex.I_mul_I]) <;> norm_num

/-- Collapse of a doubled Kronecker-delta weighted sum over `Fin 4`. -/
theorem cov_collapse (M : Matrix (Fin 4) (Fin 4) Complex) (i j : Fin 4) :
    (∑ p : Fin 4, ∑ q : Fin 4,
        4 * (if i = q then (1 : Complex) else 0) * (if j = p then 1 else 0) * M q p)
      = 4 * M i j := by
  have h1 : ∀ p : Fin 4,
      (∑ q : Fin 4,
        4 * (if i = q then (1 : Complex) else 0) * (if j = p then 1 else 0) * M q p)
      = 4 * (if j = p then (1 : Complex) else 0) * M i p := by
    intro p
    rw [Finset.sum_eq_single i]
    · simp
    · intro q _ hq; rw [ite_eq_right (Ne.symm hq)]; simp
    · intro h; simp at h
  simp only [h1]
  rw [Finset.sum_eq_single j]
  · simp
  · intro p _ hp
    rw [show (if j = p then (1 : Complex) else 0) = 0 from by rw [ite_eq_right]; exact fun h => hp h.symm]
    simp
  · intro h; simp at h

/-- **Closure form of Fierz completeness**: for any `4 x 4` matrix `M`,
`sum_A w_A tr (Gamma_A M) Gamma_A = 4 M`.  A Fierz rearrangement is nothing more
than this identity read off a product of two Dirac bilinears. -/
theorem cov_fierz_expansion (M : Matrix (Fin 4) (Fin 4) Complex) :
    (∑ a : Fin 16, (covW a * (cov a * M).trace) • cov a) = (4 : Complex) • M := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have htr : ∀ a : Fin 16,
      (cov a * M).trace = ∑ p : Fin 4, ∑ q : Fin 4, cov a p q * M q p := by
    intro a; simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have hstep : ∀ a : Fin 16, covW a * (cov a * M).trace * cov a i j
      = ∑ p : Fin 4, ∑ q : Fin 4, (covW a * cov a i j * cov a p q) * M q p := by
    intro a
    rw [htr a]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring
  simp only [hstep]
  rw [Finset.sum_comm]
  rw [show (∑ p : Fin 4, ∑ a : Fin 16, ∑ q : Fin 4,
        (covW a * cov a i j * cov a p q) * M q p)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ a : Fin 16,
        (covW a * cov a i j * cov a p q) * M q p from by
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.sum_comm]]
  rw [show (∑ p : Fin 4, ∑ q : Fin 4, ∑ a : Fin 16,
        (covW a * cov a i j * cov a p q) * M q p)
      = ∑ p : Fin 4, ∑ q : Fin 4,
        (∑ a : Fin 16, covW a * cov a i j * cov a p q) * M q p from by
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    rw [←Finset.sum_mul]]
  simp only [cov_fierz, Matrix.smul_apply, smul_eq_mul]
  exact cov_collapse M i j

end LeanPhy.HighEnergy