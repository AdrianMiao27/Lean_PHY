import LeanPhy.Mathematics.FinitePathIntegral
import LeanPhy.Mathematics.Approximation
import Mathlib.Tactic

/-!
# Certified errors for finite normalized path integrals

Finite sums are exact, but numerical weights, truncations and sampled
insertions are not.  This module records the extra facts needed to turn errors
in an insertion and in a partition function into an error for a normalized
expectation.  In particular, both the exact and approximate denominators need
explicit positive lower bounds.  No concentration estimate, continuum limit,
or Monte-Carlo convergence theorem is inferred.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

universe u v

namespace FinitePathIntegral

variable {ι : Type u} [Fintype ι]

/-! An observable may itself be truncated or evaluated numerically.  Keeping
the pointwise error separate from the weight error lets a normalized
expectation report both sources instead of silently treating the observable
as exact. -/

structure ObservableApproximationCertificate
    (O O' : ι → ℂ) where
  radius : ι → ℝ
  radius_nonneg : ∀ i, 0 ≤ radius i
  error : ∀ i, ErrorCertificate (O i) (O' i) (radius i)

namespace ObservableApproximationCertificate

theorem insertion_error (P : FinitePathIntegral ι)
    (O O' : ι → ℂ) (C : ObservableApproximationCertificate O O') :
    ErrorCertificate (P.insertion O) (P.insertion O')
      (∑ i, ‖P.weight i‖ * C.radius i) := by
  refine ⟨Finset.sum_nonneg (fun i hi =>
    mul_nonneg (norm_nonneg _) (C.radius_nonneg i)), ?_⟩
  rw [dist_eq_norm]
  calc
    ‖P.insertion O - P.insertion O'‖ =
        ‖∑ i, P.weight i * (O i - O' i)‖ := by
      congr 1
      unfold insertion
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i, ‖P.weight i * (O i - O' i)‖ := by
      simpa using (norm_sum_le Finset.univ
        (fun i => P.weight i * (O i - O' i)))
    _ = ∑ i, ‖P.weight i‖ * ‖O i - O' i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul]
    _ ≤ ∑ i, ‖P.weight i‖ * C.radius i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (by simpa [dist_eq_norm] using (C.error i).bound) (norm_nonneg _)

theorem expectation_error
    (P : FinitePathIntegral ι) (O O' : ι → ℂ)
    (C : ObservableApproximationCertificate O O')
    (lower : ℝ) (hlower_pos : 0 < lower)
    (hlower : lower ≤ ‖P.partition‖) :
    ErrorCertificate (P.expectation O) (P.expectation O')
      ((∑ i, ‖P.weight i‖ * C.radius i) / lower) := by
  have hI : ‖P.insertion O - P.insertion O'‖ ≤
      ∑ i, ‖P.weight i‖ * C.radius i := by
    simpa [dist_eq_norm] using (C.insertion_error P O O').bound
  have hfirst :
      ‖P.insertion O - P.insertion O'‖ / ‖P.partition‖ ≤
        (∑ i, ‖P.weight i‖ * C.radius i) / lower := by
    exact div_le_div₀
      (Finset.sum_nonneg (fun i hi =>
        mul_nonneg (norm_nonneg _) (C.radius_nonneg i)))
      hI hlower_pos hlower
  refine ⟨div_nonneg
      (Finset.sum_nonneg (fun i hi =>
        mul_nonneg (norm_nonneg _) (C.radius_nonneg i)))
      (le_of_lt hlower_pos), ?_⟩
  rw [dist_eq_norm]
  change ‖P.insertion O / P.partition - P.insertion O' / P.partition‖ ≤ _
  rw [← sub_div, norm_div]
  exact hfirst

end ObservableApproximationCertificate

/-! The numerical facts are kept as a certificate rather than hidden in a
constructor.  `P` is the reference finite path integral and `Q` is a finite
surrogate, which may come from quadrature, truncation or sampled weights. -/
structure ApproximationCertificate
    (P Q : FinitePathIntegral ι) (O : ι → ℂ) where
  insertionRadius : ℝ
  partitionRadius : ℝ
  insertion_nonneg : 0 ≤ insertionRadius
  partition_nonneg : 0 ≤ partitionRadius
  insertion_error :
    ErrorCertificate (P.insertion O) (Q.insertion O) insertionRadius
  partition_error :
    ErrorCertificate P.partition Q.partition partitionRadius
  exactLower : ℝ
  approximateLower : ℝ
  exactLower_pos : 0 < exactLower
  approximateLower_pos : 0 < approximateLower
  exact_lower_bound : exactLower ≤ ‖P.partition‖
  approximate_lower_bound : approximateLower ≤ ‖Q.partition‖
  insertionUpper : ℝ
  insertionUpper_nonneg : 0 ≤ insertionUpper
  approximate_insertion_upper : ‖Q.insertion O‖ ≤ insertionUpper

namespace ApproximationCertificate

/-- The zero-radius certificate for comparing a path integral with itself.
The positive denominator lower bound is derived from its stored nonzero
partition certificate, rather than being silently assumed. -/
noncomputable def exact (P : FinitePathIntegral ι) (O : ι → ℂ) :
    ApproximationCertificate P P O :=
  { insertionRadius := 0
    partitionRadius := 0
    insertion_nonneg := le_rfl
    partition_nonneg := le_rfl
    insertion_error := ErrorCertificate.of_eq rfl
    partition_error := ErrorCertificate.of_eq rfl
    exactLower := ‖P.partition‖
    approximateLower := ‖P.partition‖
    exactLower_pos := (norm_pos_iff.mpr P.partition_ne_zero)
    approximateLower_pos := (norm_pos_iff.mpr P.partition_ne_zero)
    exact_lower_bound := le_rfl
    approximate_lower_bound := le_rfl
    insertionUpper := ‖P.insertion O‖
    insertionUpper_nonneg := norm_nonneg _
    approximate_insertion_upper := le_rfl }

/-- Widening either numerical budget preserves a path-integral certificate. -/
def weaken {P Q : FinitePathIntegral ι} {O : ι → ℂ}
    (C : ApproximationCertificate P Q O)
    {insertionRadius partitionRadius : ℝ}
    (hi : C.insertionRadius ≤ insertionRadius)
    (hp : C.partitionRadius ≤ partitionRadius) :
    ApproximationCertificate P Q O :=
  { insertionRadius := insertionRadius
    partitionRadius := partitionRadius
    insertion_nonneg := C.insertion_nonneg.trans hi
    partition_nonneg := C.partition_nonneg.trans hp
    insertion_error := ErrorCertificate.weaken C.insertion_error hi
    partition_error := ErrorCertificate.weaken C.partition_error hp
    exactLower := C.exactLower
    approximateLower := C.approximateLower
    exactLower_pos := C.exactLower_pos
    approximateLower_pos := C.approximateLower_pos
    exact_lower_bound := C.exact_lower_bound
    approximate_lower_bound := C.approximate_lower_bound
    insertionUpper := C.insertionUpper
    insertionUpper_nonneg := C.insertionUpper_nonneg
    approximate_insertion_upper := C.approximate_insertion_upper }

/-! Local-to-global error aggregation.  A numerical adapter may certify each
configuration separately; the following two theorems sum those certificates
before any normalization is attempted. -/

theorem partition_error_of_pointwise
    (P Q : FinitePathIntegral ι) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i)
    (h : ∀ i, ErrorCertificate (P.weight i) (Q.weight i) (radius i)) :
    ErrorCertificate P.partition Q.partition (∑ i, radius i) := by
  refine ⟨Finset.sum_nonneg (fun i hi => hr i), ?_⟩
  rw [dist_eq_norm]
  calc
    ‖P.partition - Q.partition‖ =
        ‖∑ i, (P.weight i - Q.weight i)‖ := by
      congr 1
      simp only [partition]
      rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖P.weight i - Q.weight i‖ := by
      simpa using (norm_sum_le Finset.univ
        (fun i => P.weight i - Q.weight i))
    _ ≤ ∑ i, radius i := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [dist_eq_norm] using (h i).bound

theorem insertion_error_of_pointwise
    (P Q : FinitePathIntegral ι) (O : ι → ℂ) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i)
    (h : ∀ i, ErrorCertificate (P.weight i) (Q.weight i) (radius i)) :
    ErrorCertificate (P.insertion O) (Q.insertion O)
      (∑ i, radius i * ‖O i‖) := by
  refine ⟨Finset.sum_nonneg (fun i hi =>
    mul_nonneg (hr i) (norm_nonneg _)), ?_⟩
  rw [dist_eq_norm]
  calc
    ‖P.insertion O - Q.insertion O‖ =
        ‖∑ i, (P.weight i - Q.weight i) * O i‖ := by
      congr 1
      unfold insertion
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i, ‖(P.weight i - Q.weight i) * O i‖ := by
      simpa using (norm_sum_le Finset.univ
        (fun i => (P.weight i - Q.weight i) * O i))
    _ = ∑ i, ‖P.weight i - Q.weight i‖ * ‖O i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul]
    _ ≤ ∑ i, radius i * ‖O i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right
        (by simpa [dist_eq_norm] using (h i).bound) (norm_nonneg _)

theorem expectation_error {P Q : FinitePathIntegral ι} {O : ι → ℂ}
    (C : ApproximationCertificate P Q O) :
    ErrorCertificate
      (P.expectation O)
      (Q.expectation O)
      (C.insertionRadius / C.exactLower +
        C.insertionUpper * C.partitionRadius /
          (C.exactLower * C.approximateLower)) := by
  have hI : ‖P.insertion O - Q.insertion O‖ ≤ C.insertionRadius := by
    simpa [dist_eq_norm] using C.insertion_error.bound
  have hZ : ‖P.partition - Q.partition‖ ≤ C.partitionRadius := by
    simpa [dist_eq_norm] using C.partition_error.bound
  have hdecomp :
      P.insertion O / P.partition - Q.insertion O / Q.partition =
        (P.insertion O - Q.insertion O) / P.partition +
          Q.insertion O * (Q.partition - P.partition) /
            (P.partition * Q.partition) := by
    field_simp [P.partition_ne_zero, Q.partition_ne_zero]
    ring
  have hfirst :
      ‖P.insertion O - Q.insertion O‖ / ‖P.partition‖ ≤
        C.insertionRadius / C.exactLower := by
    exact div_le_div₀ C.insertion_nonneg hI C.exactLower_pos
      C.exact_lower_bound
  have hprod :
      C.exactLower * C.approximateLower ≤
        ‖P.partition‖ * ‖Q.partition‖ := by
    exact mul_le_mul C.exact_lower_bound C.approximate_lower_bound
      (le_of_lt C.approximateLower_pos) (norm_nonneg _)
  have hZrev : ‖Q.partition - P.partition‖ ≤ C.partitionRadius := by
    simpa only [norm_sub_rev] using hZ
  have hfrac :
      ‖Q.partition - P.partition‖ /
          (‖P.partition‖ * ‖Q.partition‖) ≤
        C.partitionRadius / (C.exactLower * C.approximateLower) := by
    exact div_le_div₀ C.partition_nonneg hZrev
      (mul_pos C.exactLower_pos C.approximateLower_pos) hprod
  have hsecond :
      C.insertionUpper *
          (‖Q.partition - P.partition‖ /
            (‖P.partition‖ * ‖Q.partition‖)) ≤
        C.insertionUpper *
          (C.partitionRadius / (C.exactLower * C.approximateLower)) :=
    mul_le_mul_of_nonneg_left hfrac C.insertionUpper_nonneg
  refine ⟨?_, ?_⟩
  · exact add_nonneg
      (div_nonneg C.insertion_nonneg (le_of_lt C.exactLower_pos))
      (div_nonneg (mul_nonneg C.insertionUpper_nonneg C.partition_nonneg)
        (le_of_lt (mul_pos C.exactLower_pos C.approximateLower_pos)))
  rw [dist_eq_norm]
  change ‖P.insertion O / P.partition - Q.insertion O / Q.partition‖ ≤ _
  rw [hdecomp]
  calc
    ‖(P.insertion O - Q.insertion O) / P.partition +
        Q.insertion O * (Q.partition - P.partition) /
          (P.partition * Q.partition)‖ ≤
      ‖(P.insertion O - Q.insertion O) / P.partition‖ +
        ‖Q.insertion O * (Q.partition - P.partition) /
          (P.partition * Q.partition)‖ := norm_add_le _ _
    _ = ‖P.insertion O - Q.insertion O‖ / ‖P.partition‖ +
        ‖Q.insertion O‖ *
          (‖Q.partition - P.partition‖ /
            (‖P.partition‖ * ‖Q.partition‖)) := by
      simp only [norm_div, norm_mul]
      ring
    _ ≤ C.insertionRadius / C.exactLower +
        C.insertionUpper *
          (C.partitionRadius / (C.exactLower * C.approximateLower)) := by
      have hfrac_nonneg : 0 ≤
          ‖Q.partition - P.partition‖ /
            (‖P.partition‖ * ‖Q.partition‖) :=
        div_nonneg (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      have hsecond' := mul_le_mul_of_nonneg_right
        C.approximate_insertion_upper hfrac_nonneg
      exact add_le_add hfirst (hsecond'.trans hsecond)
    _ = C.insertionRadius / C.exactLower +
          C.insertionUpper * C.partitionRadius /
            (C.exactLower * C.approximateLower) := by ring

/-! Combine weight/partition error with an independently approximated
observable.  The second term uses the approximate measure's denominator, so
the caller must still provide the same explicit lower-bound certificate. -/

theorem expectation_error_with_observable
    {P Q : FinitePathIntegral ι} {O O' : ι → ℂ}
    (C : ApproximationCertificate P Q O)
    (D : ObservableApproximationCertificate O O') :
    ErrorCertificate
      (P.expectation O) (Q.expectation O')
      (C.insertionRadius / C.exactLower +
        C.insertionUpper * C.partitionRadius /
          (C.exactLower * C.approximateLower) +
        (∑ i, ‖Q.weight i‖ * D.radius i) / C.approximateLower) := by
  exact ErrorCertificate.trans C.expectation_error
    (D.expectation_error Q O O' C.approximateLower
      C.approximateLower_pos C.approximate_lower_bound)

end ApproximationCertificate

/-! A normalized expectation is often passed through several numerical or RG
adapters.  This small wrapper makes the reported scalar error composable: each
step still carries its own kernel-checked `ErrorCertificate`, and the chain
only adds the advertised nonnegative radii. -/

structure NormalizedExpectationCertificate
    (P Q : FinitePathIntegral ι) (O : ι → ℂ) where
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  error : ErrorCertificate (P.expectation O) (Q.expectation O) radius

namespace NormalizedExpectationCertificate

variable {ι : Type u} [Fintype ι]

noncomputable def ofApproximation {P Q : FinitePathIntegral ι} {O : ι → ℂ}
    (C : ApproximationCertificate P Q O) :
    NormalizedExpectationCertificate P Q O :=
  { radius := C.insertionRadius / C.exactLower +
      C.insertionUpper * C.partitionRadius /
        (C.exactLower * C.approximateLower)
    radius_nonneg := C.expectation_error.nonneg
    error := C.expectation_error }

def weaken {P Q : FinitePathIntegral ι} {O : ι → ℂ}
    (C : NormalizedExpectationCertificate P Q O) {δ : ℝ}
    (hδ : C.radius ≤ δ) : NormalizedExpectationCertificate P Q O :=
  { radius := δ
    radius_nonneg := C.radius_nonneg.trans hδ
    error := C.error.weaken hδ }

def compose {P Q R : FinitePathIntegral ι} {O : ι → ℂ}
    (C₁ : NormalizedExpectationCertificate P Q O)
    (C₂ : NormalizedExpectationCertificate Q R O) :
    NormalizedExpectationCertificate P R O :=
  { radius := C₁.radius + C₂.radius
    radius_nonneg := add_nonneg C₁.radius_nonneg C₂.radius_nonneg
    error := C₁.error.trans C₂.error }

end NormalizedExpectationCertificate

/-! The RG observable generally changes type after a blocking step.  This
comparison certificate keeps the source and target configuration spaces and
observables separate, so a chain may be composed even when each step changes
the finite label type. -/

structure ExpectationComparisonCertificate
    {ι : Type u} [Fintype ι] {κ : Type v} [Fintype κ]
    (P : FinitePathIntegral ι) (Q : FinitePathIntegral κ)
    (O : ι → ℂ) (O' : κ → ℂ) where
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  error : ErrorCertificate (P.expectation O) (Q.expectation O') radius

namespace ExpectationComparisonCertificate

variable {ι : Type u} [Fintype ι]
variable {κ : Type v} [Fintype κ]

def ofError {P : FinitePathIntegral ι} {Q : FinitePathIntegral κ}
    {O : ι → ℂ} {O' : κ → ℂ} {ε : ℝ}
    (h : ErrorCertificate (P.expectation O) (Q.expectation O') ε) :
    ExpectationComparisonCertificate P Q O O' :=
  { radius := ε, radius_nonneg := h.nonneg, error := h }

def weaken {P : FinitePathIntegral ι} {Q : FinitePathIntegral κ}
    {O : ι → ℂ} {O' : κ → ℂ}
    (C : ExpectationComparisonCertificate P Q O O') {δ : ℝ}
    (hδ : C.radius ≤ δ) : ExpectationComparisonCertificate P Q O O' :=
  { radius := δ
    radius_nonneg := C.radius_nonneg.trans hδ
    error := C.error.weaken hδ }

noncomputable def ofApproximation {P Q : FinitePathIntegral ι} {O : ι → ℂ}
    (C : ApproximationCertificate P Q O) :
    ExpectationComparisonCertificate P Q O O :=
  ofError C.expectation_error

def compose {τ : Type*} [Fintype τ]
    {P : FinitePathIntegral ι} {Q : FinitePathIntegral κ}
    {R : FinitePathIntegral τ}
    {O : ι → ℂ} {O' : κ → ℂ} {O'' : τ → ℂ}
    (C₁ : ExpectationComparisonCertificate P Q O O')
    (C₂ : ExpectationComparisonCertificate Q R O' O'') :
    ExpectationComparisonCertificate P R O O'' :=
  { radius := C₁.radius + C₂.radius
    radius_nonneg := add_nonneg C₁.radius_nonneg C₂.radius_nonneg
    error := C₁.error.trans C₂.error }

end ExpectationComparisonCertificate

/-! RG-facing constructor: a numerical or truncated coarse weight table can be
checked pointwise against the exact finite push-forward.  The constructor
then assembles the partition/insertion budgets needed by the normalized
expectation theorem; denominator bounds and the insertion upper bound remain
explicit inputs. -/

namespace FiniteRGStep

variable {κ : Type u} [Fintype κ]

noncomputable def coarse_approximation_certificate
    {ι : Type u} [Fintype ι]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (Q : FinitePathIntegral κ) (O : κ → ℂ)
    (radius : κ → ℝ) (hr : ∀ y, 0 ≤ radius y)
    (hw : ∀ y, ErrorCertificate (R.coarseWeight y) (Q.weight y) (radius y))
    (exactLower approximateLower : ℝ)
    (hexact_pos : 0 < exactLower)
    (happrox_pos : 0 < approximateLower)
    (hexact_lower : exactLower ≤
      ‖(R.coarsePathIntegral h).partition‖)
    (happrox_lower : approximateLower ≤ ‖Q.partition‖)
    (insertionUpper : ℝ) (hinsertionUpper_nonneg : 0 ≤ insertionUpper)
    (hinsertion_upper : ‖Q.insertion O‖ ≤ insertionUpper) :
    ApproximationCertificate (R.coarsePathIntegral h) Q O :=
  { insertionRadius := ∑ y, radius y * ‖O y‖
    partitionRadius := ∑ y, radius y
    insertion_nonneg := Finset.sum_nonneg (fun y hy =>
      mul_nonneg (hr y) (norm_nonneg _))
    partition_nonneg := Finset.sum_nonneg (fun y hy => hr y)
    insertion_error :=
      ApproximationCertificate.insertion_error_of_pointwise
        (R.coarsePathIntegral h) Q O radius hr hw
    partition_error :=
      ApproximationCertificate.partition_error_of_pointwise
        (R.coarsePathIntegral h) Q radius hr hw
    exactLower := exactLower
    approximateLower := approximateLower
    exactLower_pos := hexact_pos
    approximateLower_pos := happrox_pos
    exact_lower_bound := hexact_lower
    approximate_lower_bound := happrox_lower
    insertionUpper := insertionUpper
    insertionUpper_nonneg := hinsertionUpper_nonneg
    approximate_insertion_upper := hinsertion_upper }

noncomputable def coarse_expectation_certificate
    {ι : Type u} [Fintype ι]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (Q : FinitePathIntegral κ) (O : κ → ℂ)
    (radius : κ → ℝ) (hr : ∀ y, 0 ≤ radius y)
    (hw : ∀ y, ErrorCertificate (R.coarseWeight y) (Q.weight y) (radius y))
    (exactLower approximateLower : ℝ)
    (hexact_pos : 0 < exactLower)
    (happrox_pos : 0 < approximateLower)
    (hexact_lower : exactLower ≤
      ‖(R.coarsePathIntegral h).partition‖)
    (happrox_lower : approximateLower ≤ ‖Q.partition‖)
    (insertionUpper : ℝ) (hinsertionUpper_nonneg : 0 ≤ insertionUpper)
    (hinsertion_upper : ‖Q.insertion O‖ ≤ insertionUpper) :
    NormalizedExpectationCertificate
      (R.coarsePathIntegral h) Q O :=
  NormalizedExpectationCertificate.ofApproximation
    (coarse_approximation_certificate R h Q O radius hr hw
      exactLower approximateLower hexact_pos happrox_pos hexact_lower
      happrox_lower insertionUpper hinsertionUpper_nonneg hinsertion_upper)

end FiniteRGStep

end FinitePathIntegral

end LeanPhy.Mathematics

/-! Domain-facing names for normalized path-integral error certificates. -/

namespace LeanPhy

namespace FieldTheory
abbrev FinitePathApproximationCertificate {ι : Type*} [Fintype ι]
    (P Q : Mathematics.FinitePathIntegral ι) (O : ι → ℂ) :=
  Mathematics.FinitePathIntegral.ApproximationCertificate P Q O
abbrev ObservableApproximationCertificate {ι : Type*} [Fintype ι]
    (O O' : ι → ℂ) :=
  Mathematics.FinitePathIntegral.ObservableApproximationCertificate O O'
abbrev NormalizedExpectationCertificate {ι : Type*} [Fintype ι]
    (P Q : Mathematics.FinitePathIntegral ι) (O : ι → ℂ) :=
  Mathematics.FinitePathIntegral.NormalizedExpectationCertificate P Q O
abbrev ExpectationComparisonCertificate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Mathematics.FinitePathIntegral ι)
    (Q : Mathematics.FinitePathIntegral κ) (O : ι → ℂ) (O' : κ → ℂ) :=
  Mathematics.FinitePathIntegral.ExpectationComparisonCertificate P Q O O'
end FieldTheory

namespace Quantum
abbrev FiniteEuclideanExpectationCertificate {ι : Type*} [Fintype ι]
    (P Q : Mathematics.FinitePathIntegral ι) (O : ι → ℂ) :=
  Mathematics.FinitePathIntegral.ApproximationCertificate P Q O
abbrev ObservableApproximationCertificate {ι : Type*} [Fintype ι]
    (O O' : ι → ℂ) :=
  Mathematics.FinitePathIntegral.ObservableApproximationCertificate O O'
abbrev NormalizedExpectationCertificate {ι : Type*} [Fintype ι]
    (P Q : Mathematics.FinitePathIntegral ι) (O : ι → ℂ) :=
  Mathematics.FinitePathIntegral.NormalizedExpectationCertificate P Q O
abbrev ExpectationComparisonCertificate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Mathematics.FinitePathIntegral ι)
    (Q : Mathematics.FinitePathIntegral κ) (O : ι → ℂ) (O' : κ → ℂ) :=
  Mathematics.FinitePathIntegral.ExpectationComparisonCertificate P Q O O'
end Quantum

namespace Condensed
abbrev FiniteLatticeExpectationCertificate {ι : Type*} [Fintype ι]
    (P Q : Mathematics.FinitePathIntegral ι) (O : ι → ℂ) :=
  Mathematics.FinitePathIntegral.ApproximationCertificate P Q O
abbrev ObservableApproximationCertificate {ι : Type*} [Fintype ι]
    (O O' : ι → ℂ) :=
  Mathematics.FinitePathIntegral.ObservableApproximationCertificate O O'
abbrev NormalizedExpectationCertificate {ι : Type*} [Fintype ι]
    (P Q : Mathematics.FinitePathIntegral ι) (O : ι → ℂ) :=
  Mathematics.FinitePathIntegral.NormalizedExpectationCertificate P Q O
abbrev ExpectationComparisonCertificate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Mathematics.FinitePathIntegral ι)
    (Q : Mathematics.FinitePathIntegral κ) (O : ι → ℂ) (O' : κ → ℂ) :=
  Mathematics.FinitePathIntegral.ExpectationComparisonCertificate P Q O O'
end Condensed

namespace StatMech
abbrev FiniteRGExpectationCertificate {ι : Type*} [Fintype ι]
    (P Q : Mathematics.FinitePathIntegral ι) (O : ι → ℂ) :=
  Mathematics.FinitePathIntegral.ApproximationCertificate P Q O
abbrev ObservableApproximationCertificate {ι : Type*} [Fintype ι]
    (O O' : ι → ℂ) :=
  Mathematics.FinitePathIntegral.ObservableApproximationCertificate O O'
abbrev NormalizedExpectationCertificate {ι : Type*} [Fintype ι]
    (P Q : Mathematics.FinitePathIntegral ι) (O : ι → ℂ) :=
  Mathematics.FinitePathIntegral.NormalizedExpectationCertificate P Q O
abbrev ExpectationComparisonCertificate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Mathematics.FinitePathIntegral ι)
    (Q : Mathematics.FinitePathIntegral κ) (O : ι → ℂ) (O' : κ → ℂ) :=
  Mathematics.FinitePathIntegral.ExpectationComparisonCertificate P Q O O'
end StatMech

end LeanPhy
