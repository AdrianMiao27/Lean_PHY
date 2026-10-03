import LeanPhy.Mathematics.FinitePathIntegral
import Mathlib.Tactic

/-!
# Finite source insertions and Schwinger--Dyson identities

The continuum Schwinger--Dyson equation involves a functional derivative and
an integration-by-parts argument.  Those analytic ingredients are not hidden
here.  Instead this file exposes the exact finite analogue:

* a truncated source generating polynomial whose coefficients are finite
  moments;
* a finite involutive change of variables with an explicit weight/Jacobian
  balance certificate;
* the resulting weighted difference identity and its normalized expectation
  form.

The certificate is useful for lattice and truncated-field calculations.  It
does not assert a continuum measure, differentiability, boundary decay, or a
non-perturbative Schwinger--Dyson equation.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

universe u

namespace FinitePathIntegral

variable {ι : Type u} [Fintype ι]

/-! ## Sources and finite generating polynomials -/

/-- A source insertion for a field and a configuration-dependent source. -/
noncomputable def sourceInsertion (P : FinitePathIntegral ι)
    (field source : ι → ℂ) : ℂ :=
  P.expectation (fun i => source i * field i)

/-- The finite n-th moment used as a source-generating coefficient. -/
noncomputable def moment (P : FinitePathIntegral ι)
    (field : ι → ℂ) (n : ℕ) : ℂ :=
  P.expectation (fun i => field i ^ n)

/-- A truncated one-parameter source generating functional.

`order` is finite by construction.  A continuum exponential generating
functional is therefore represented only through the explicitly retained
moments and never smuggled in as an infinite sum. -/
noncomputable def sourceGeneratingPolynomial (P : FinitePathIntegral ι)
    (field : ι → ℂ) (source : ℂ) (order : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (order + 1),
    source ^ n / (n.factorial : ℂ) * P.moment field n

@[simp] theorem moment_zero (P : FinitePathIntegral ι) (field : ι → ℂ) :
    P.moment field 0 = 1 := by
  unfold moment
  simpa using P.expectation_const (1 : ℂ)

theorem sourceInsertion_eq_source_mul_moment
    (P : FinitePathIntegral ι) (field : ι → ℂ) (source : ℂ) :
    P.sourceInsertion field (fun _ => source) =
      source * P.moment field 1 := by
  unfold sourceInsertion moment
  simpa [pow_one] using P.expectation_smul source field

theorem sourceGeneratingPolynomial_succ
    (P : FinitePathIntegral ι) (field : ι → ℂ) (source : ℂ) (n : ℕ) :
    P.sourceGeneratingPolynomial field source (n + 1) =
      P.sourceGeneratingPolynomial field source n +
        source ^ (n + 1) / ((n + 1).factorial : ℂ) * P.moment field (n + 1) := by
  unfold sourceGeneratingPolynomial
  rw [Finset.sum_range_succ]

theorem sourceGeneratingPolynomial_zero
    (P : FinitePathIntegral ι) (field : ι → ℂ) (source : ℂ) :
    P.sourceGeneratingPolynomial field source 0 = 1 := by
  unfold sourceGeneratingPolynomial
  simp [moment_zero]

theorem sourceGeneratingPolynomial_one
    (P : FinitePathIntegral ι) (field : ι → ℂ) (source : ℂ) :
    P.sourceGeneratingPolynomial field source 1 =
      1 + source * P.moment field 1 := by
  rw [sourceGeneratingPolynomial_succ]
  simp [sourceGeneratingPolynomial_zero, Nat.factorial, pow_one]

/-! ## A finite change of variables and Schwinger--Dyson balance -/

/-- A finite involutive variation.  `jacobian` is an algebraic multiplier;
the weight balance is explicit because a general finite change of variables
does not preserve an arbitrary complex weight. -/
structure InvolutiveVariation (P : FinitePathIntegral ι) where
  map : Equiv.Perm ι
  involutive : ∀ i, map (map i) = i
  jacobian : ι → ℂ
  balance : ∀ i, P.weight (map i) = jacobian i * P.weight i

theorem weighted_change_of_variables
    (P : FinitePathIntegral ι) (V : InvolutiveVariation P)
    (O : ι → ℂ) :
    ∑ i, P.weight i * O (V.map i) =
      ∑ i, P.weight i * V.jacobian i * O i := by
  have hreindex :
      (∑ i, P.weight i * O (V.map i)) =
        ∑ i, P.weight (V.map i) * O (V.map (V.map i)) := by
    symm
    simpa using
      (Equiv.sum_comp V.map (fun i => P.weight i * O (V.map i)))
  calc
    (∑ i, P.weight i * O (V.map i)) =
        ∑ i, P.weight (V.map i) * O (V.map (V.map i)) := hreindex
    _ = ∑ i, P.weight (V.map i) * O i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [V.involutive i]
    _ = ∑ i, (V.jacobian i * P.weight i) * O i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [V.balance i]
    _ = ∑ i, P.weight i * V.jacobian i * O i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem schwinger_dyson_insertion
    (P : FinitePathIntegral ι) (V : InvolutiveVariation P)
    (O : ι → ℂ) :
    ∑ i, P.weight i * (O (V.map i) - O i) =
      ∑ i, P.weight i * (V.jacobian i - 1) * O i := by
  have hchange := P.weighted_change_of_variables V O
  calc
    (∑ i, P.weight i * (O (V.map i) - O i)) =
        (∑ i, P.weight i * O (V.map i)) -
          ∑ i, P.weight i * O i := by
      rw [show (fun i => P.weight i * (O (V.map i) - O i)) =
          (fun i => P.weight i * O (V.map i) - P.weight i * O i) by
            funext i; ring]
      rw [Finset.sum_sub_distrib]
    _ = (∑ i, P.weight i * V.jacobian i * O i) -
          ∑ i, P.weight i * O i := by rw [hchange]
    _ = ∑ i, P.weight i * (V.jacobian i - 1) * O i := by
      rw [show (fun i => P.weight i * (V.jacobian i - 1) * O i) =
          (fun i => P.weight i * V.jacobian i * O i -
            P.weight i * O i) by funext i; ring]
      rw [Finset.sum_sub_distrib]

theorem schwinger_dyson_expectation
    (P : FinitePathIntegral ι) (V : InvolutiveVariation P)
    (O : ι → ℂ) :
    P.expectation (fun i => O (V.map i) - O i) =
      P.expectation (fun i => (V.jacobian i - 1) * O i) := by
  unfold expectation insertion
  rw [P.schwinger_dyson_insertion V O]
  apply congrArg (fun z : ℂ => z / P.partition)
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The invariant-weight specialization: the finite variation insertion
vanishes when the supplied Jacobian is one everywhere. -/
theorem schwinger_dyson_of_invariant_weight
    (P : FinitePathIntegral ι) (V : InvolutiveVariation P)
    (hjac : ∀ i, V.jacobian i = 1) (O : ι → ℂ) :
    P.expectation (fun i => O (V.map i) - O i) = 0 := by
  rw [P.schwinger_dyson_expectation V O]
  simp [hjac]

end FinitePathIntegral

end LeanPhy.Mathematics
