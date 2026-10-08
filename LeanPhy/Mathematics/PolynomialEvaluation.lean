import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Polynomial densities evaluated on differentiable fields

The finite chain rule is derived from the polynomial, including every field
and derivative slot. This supplies analytic derivatives of actual evaluated
densities; polynomial partial derivatives are not merely named physical ones.
-/

namespace LeanPhy.Mathematics.PolynomialEvaluation

open scoped BigOperators ContDiff

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasFDerivAt_eval (P : MvPolynomial ι ℝ) (g : ι → E → ℝ)
    (g' : ι → E →L[ℝ] ℝ) (x : E) (hg : ∀ i, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt (fun y => MvPolynomial.eval (fun i => g i y) P)
      (∑ i, MvPolynomial.eval (fun j => g j x) (MvPolynomial.pderiv i P) • g' i) x := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simpa using (hasFDerivAt_const r x)
  | add P Q hP hQ =>
      simpa only [map_add, add_smul, Finset.sum_add_distrib, Pi.add_apply] using! hP.add hQ
  | mul_X P j hP =>
      convert! hP.mul (hg j) using 1
      · funext y
        simp
      · simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul,
          MvPolynomial.eval_X, MvPolynomial.pderiv_X, Pi.single_apply,
          apply_ite, map_zero, mul_one, mul_zero, add_smul, ite_smul,
          zero_smul, Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        simp only [mul_smul, Finset.smul_sum]

theorem hasDerivAt_eval (P : MvPolynomial ι ℝ) (g : ι → ℝ → ℝ)
    (g' : ι → ℝ) (t : ℝ) (hg : ∀ i, HasDerivAt (g i) (g' i) t) :
    HasDerivAt (fun s => MvPolynomial.eval (fun i => g i s) P)
      (∑ i, MvPolynomial.eval (fun j => g j t) (MvPolynomial.pderiv i P) * g' i) t := by
  classical
  have h := hasFDerivAt_eval P g (fun i => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (g' i)) t hg
  simpa using! h.hasDerivAt

omit [Fintype ι] in
theorem contDiff_eval (P : MvPolynomial ι ℝ) (g : ι → E → ℝ) (n : ℕ∞ω)
    (hg : ∀ i, ContDiff ℝ n (g i)) :
    ContDiff ℝ n (fun x => MvPolynomial.eval (fun i => g i x) P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simpa using (contDiff_const (c := r) : ContDiff ℝ n (fun _ : E => r))
  | add P Q hP hQ => simpa using hP.add hQ
  | mul_X P i hP => simpa using hP.mul (hg i)

end LeanPhy.Mathematics.PolynomialEvaluation
