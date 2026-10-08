import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Differentiating finite normalized ensembles

A shared quotient/score rule for real thermal ensembles and complex finite
path sums. The observable may itself depend on the parameter: its derivative
is retained as a contact term. The nonzero partition hypothesis is local at
the differentiation point; no global absence of complex partition zeros is
assumed. The raw functions use Lean's total division, so physical normalized
claims are made only with an explicit nonzero partition hypothesis.

These are analytic `HasDerivAt` statements proved from the derivatives of the
individual finite weights and insertions. They do not postulate a response
identity, replace an infinite sum by a finite one, or give quantum dynamical
linear response. Domain adapters identify these functions with the project's
existing probability and path-integral expectations.
-/

namespace LeanPhy.Mathematics.FiniteWeighted

open scoped BigOperators

variable {ι 𝕜 : Type*} [Fintype ι] [NontriviallyNormedField 𝕜]

noncomputable def partition (w : ι → 𝕜) : 𝕜 := ∑ i, w i

noncomputable def insertion (w O : ι → 𝕜) : 𝕜 := ∑ i, w i * O i

noncomputable def expectation (w O : ι → 𝕜) : 𝕜 := insertion w O / partition w

noncomputable def connected (w O A : ι → 𝕜) : 𝕜 :=
  expectation w (fun i => O i * A i) - expectation w O * expectation w A

/-- A direct quotient rule, including parameter-dependent observables. -/
theorem hasDerivAt_expectation (w O : 𝕜 → ι → 𝕜) (w' O' : ι → 𝕜) (t : 𝕜)
    (hw : ∀ i, HasDerivAt (fun s => w s i) (w' i) t)
    (hO : ∀ i, HasDerivAt (fun s => O s i) (O' i) t)
    (hZ : partition (w t) ≠ 0) :
    HasDerivAt (fun s => expectation (w s) (O s))
      (((∑ i, (w' i * O t i + w t i * O' i)) * partition (w t) -
        insertion (w t) (O t) * ∑ i, w' i) / partition (w t) ^ 2) t := by
  have hnum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hw i).mul (hO i))
  have hden := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hw i)
  convert! hnum.fun_div hden hZ using 1

/-- If `w'_i = w_i score_i`, differentiating normalization produces the
connected correlator, not just the unnormalized insertion. Individual weights
may vanish: no pointwise division by `w_i` is performed. -/
theorem hasDerivAt_expectation_score (w O : 𝕜 → ι → 𝕜) (score O' : ι → 𝕜) (t : 𝕜)
    (hw : ∀ i, HasDerivAt (fun s => w s i) (w t i * score i) t)
    (hO : ∀ i, HasDerivAt (fun s => O s i) (O' i) t)
    (hZ : partition (w t) ≠ 0) :
    HasDerivAt (fun s => expectation (w s) (O s))
      (expectation (w t) O' + connected (w t) (O t) score) t := by
  convert hasDerivAt_expectation w O (fun i => w t i * score i) O' t hw hO hZ using 1
  simp only [connected, expectation, insertion]
  simp only [Finset.sum_add_distrib]
  have h : (∑ i, w t i * score i * O t i) = ∑ i, w t i * (O t i * score i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h]
  field_simp
  ring

/-- Fixed observables have no contact term. -/
theorem hasDerivAt_expectation_fixed (w : 𝕜 → ι → 𝕜) (O score : ι → 𝕜) (t : 𝕜)
    (hw : ∀ i, HasDerivAt (fun s => w s i) (w t i * score i) t)
    (hZ : partition (w t) ≠ 0) :
    HasDerivAt (fun s => expectation (w s) O) (connected (w t) O score) t := by
  simpa [expectation, insertion] using
    hasDerivAt_expectation_score w (fun _ => O) score (fun _ => 0) t hw
      (fun i => hasDerivAt_const t (O i)) hZ

/-- Source-independent rescaling leaves the normalized expectation unchanged. -/
theorem expectation_scale (w O : ι → 𝕜) (c : 𝕜) (hc : c ≠ 0) :
    expectation (fun i => c * w i) O = expectation w O := by
  unfold expectation insertion partition
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc

end LeanPhy.Mathematics.FiniteWeighted
