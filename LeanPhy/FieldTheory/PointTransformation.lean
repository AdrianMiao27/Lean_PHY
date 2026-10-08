import LeanPhy.FieldTheory.PolynomialAction
import LeanPhy.Mathematics.PolynomialEvaluation

/-!
# Composable point transformations of polynomial field densities

A map `F` expresses old fields as polynomials in new fields. Gradient slots
transform by its full Jacobian. Pullback acts on the entire density, including
source terms, and respects composition. No inverse is inferred for a singular
or non-injective field map. Coefficients describe real commuting fields.
-/

set_option autoImplicit false

namespace LeanPhy.FieldTheory.PointTransformation

open FirstOrderLagrangian
open LeanPhy.Mathematics.PolynomialEvaluation
open scoped BigOperators ContDiff

variable {Old New Dir E : Type*} [Fintype Old] [Fintype New] [Fintype Dir]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def coordinate (F : Old → MvPolynomial New ℝ) (p : Old × Option Dir) :
    FirstOrderLagrangian ℝ New Dir :=
  p.2.elim (potential (F p.1))
    (fun μ => ∑ b, potential (MvPolynomial.pderiv b (F p.1)) * gradient b μ)

noncomputable def pullback (F : Old → MvPolynomial New ℝ) :
    FirstOrderLagrangian ℝ Old Dir →ₐ[ℝ] FirstOrderLagrangian ℝ New Dir :=
  MvPolynomial.aeval (coordinate F)

omit [Fintype Old] [Fintype Dir] in
theorem pderiv_substitution (F : New → MvPolynomial Old ℝ) (P : MvPolynomial New ℝ)
    (j : Old) :
    MvPolynomial.pderiv j (MvPolynomial.aeval F P) =
      ∑ i, MvPolynomial.aeval F (MvPolynomial.pderiv i P) * MvPolynomial.pderiv j (F i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P a hP =>
    have hx (i : New) : MvPolynomial.aeval F (MvPolynomial.pderiv i (MvPolynomial.X a : MvPolynomial New ℝ)) =
        if a = i then 1 else 0 := by
      simp only [MvPolynomial.pderiv_X, Pi.single_apply]
      split_ifs <;> simp
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.pderiv_mul, hP,
      map_add, hx, mul_ite, mul_one, mul_zero, add_mul, ite_mul, zero_mul,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [Finset.mul_sum, mul_left_comm, mul_comm]

omit [Fintype Old] [Fintype Dir] in
theorem pullback_potential (F : Old → MvPolynomial New ℝ) (P : MvPolynomial Old ℝ) :
    pullback F (potential P : FirstOrderLagrangian ℝ Old Dir) =
      potential (MvPolynomial.aeval F P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [pullback, potential]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P a hP =>
    simp only [map_mul, hP]
    congr 1
    simp [pullback, potential, coordinate]

omit [Fintype Old] [Fintype Dir] in
theorem pullback_gradient (F : Old → MvPolynomial New ℝ) (a : Old) (μ : Dir) :
    pullback F (gradient a μ) =
      ∑ b, potential (MvPolynomial.pderiv b (F a)) * gradient b μ := by
  simp [pullback, gradient, coordinate]

omit [Fintype Old] [Fintype Dir] in
theorem pullback_sources {Label : Type*} [Fintype Label] (F : Old → MvPolynomial New ℝ)
    (L : FirstOrderLagrangian ℝ Old Dir) (J : Label → ℝ)
    (V : Label → FirstOrderLagrangian ℝ Old Dir) :
    pullback F (L + ∑ a, J a • V a) = pullback F L + ∑ a, J a • pullback F (V a) := by
  simp only [map_add, map_sum, map_smul]

noncomputable def compose {Third : Type*} (F : Old → MvPolynomial New ℝ)
    (G : New → MvPolynomial Third ℝ) : Old → MvPolynomial Third ℝ :=
  fun a => MvPolynomial.aeval G (F a)

omit [Fintype Old] [Fintype Dir] in
theorem coordinate_compose {Third : Type*} [Fintype Third]
    (F : Old → MvPolynomial New ℝ) (G : New → MvPolynomial Third ℝ)
    (p : Old × Option Dir) :
    pullback G (coordinate F p) = coordinate (compose F G) p := by
  obtain ⟨a, μ⟩ := p
  cases μ with
  | none => simp only [coordinate, Option.elim_none, pullback_potential, compose]
  | some μ =>
    simp only [coordinate, Option.elim_some, map_sum, map_mul, pullback_potential,
      pullback_gradient, compose, pderiv_substitution, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc]

omit [Fintype Old] [Fintype Dir] in
theorem pullback_compose {Third : Type*} [Fintype Third]
    (F : Old → MvPolynomial New ℝ) (G : New → MvPolynomial Third ℝ)
    (L : FirstOrderLagrangian ℝ Old Dir) :
    pullback G (pullback F L) = pullback (compose F G) L := by
  induction L using MvPolynomial.induction_on with
  | C r => simp [pullback]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P a hP =>
    simp only [map_mul, hP]
    congr 1
    simpa only [pullback, MvPolynomial.aeval_X] using coordinate_compose F G a

omit [Fintype Old] [Fintype Dir] in
@[simp] theorem pullback_identity (L : FirstOrderLagrangian ℝ New Dir) :
    pullback (fun b => MvPolynomial.X b) L = L := by
  classical
  have hc (p : New × Option Dir) :
      coordinate (fun b => MvPolynomial.X b) p = MvPolynomial.X p := by
    obtain ⟨b, μ⟩ := p
    cases μ with
    | none => simp [coordinate, potential]
    | some μ => simp [coordinate, potential, gradient, MvPolynomial.pderiv_X, Pi.single_apply]
  induction L using MvPolynomial.induction_on with
  | C r => simp [pullback]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P a hP =>
    simp only [map_mul, hP]
    congr 1
    simpa only [pullback, MvPolynomial.aeval_X] using hc a

omit [Fintype Dir] in
/-- Returning a density to its original fields requires an actual polynomial
composition identity. An arbitrary point map does not give equivalence. -/
theorem pullback_inverse (F : Old → MvPolynomial New ℝ) (G : New → MvPolynomial Old ℝ)
    (hFG : ∀ a, MvPolynomial.aeval G (F a) = MvPolynomial.X a)
    (L : FirstOrderLagrangian ℝ Old Dir) : pullback G (pullback F L) = L := by
  rw [pullback_compose]
  have hc : compose F G = fun a => MvPolynomial.X a := funext hFG
  rw [hc, pullback_identity]

end LeanPhy.FieldTheory.PointTransformation
