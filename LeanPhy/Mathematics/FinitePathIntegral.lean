import Mathlib.Tactic

/-!
# Finite path integrals and exact finite coarse graining

A path integral in a lattice, truncated field or finite-state toy model is a
finite weighted sum.  This module makes the measure, its nonzero partition
function and the observable insertion explicit.  It proves only finite-sum
identities: normalization, linearity, permutation invariance and exact
push-forward under a coarse map.  No continuum measure, oscillatory integral,
limit, reflection positivity or renormalization-group universality claim is
hidden here.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

universe u v

/-- A finite (possibly complex/oscillatory) path integral measure.  The
nonzero partition certificate is required before normalized expectations can
be formed. -/
structure FinitePathIntegral (ι : Type u) [Fintype ι] where
  weight : ι → ℂ
  partition_ne_zero : (∑ i, weight i) ≠ 0

namespace FinitePathIntegral

variable {ι : Type u} [Fintype ι]

/-- The finite partition function. -/
noncomputable def partition (P : FinitePathIntegral ι) : ℂ := ∑ i, P.weight i

@[simp] theorem partition_apply (P : FinitePathIntegral ι) :
    P.partition = ∑ i, P.weight i := rfl

theorem partition_ne_zero_cert (P : FinitePathIntegral ι) : P.partition ≠ 0 :=
  P.partition_ne_zero

/-- Unnormalized insertion of an observable. -/
noncomputable def insertion (P : FinitePathIntegral ι) (O : ι → ℂ) : ℂ :=
  ∑ i, P.weight i * O i

/-- Normalized expectation of a finite observable. -/
noncomputable def expectation (P : FinitePathIntegral ι) (O : ι → ℂ) : ℂ :=
  P.insertion O / P.partition

@[simp] theorem insertion_apply (P : FinitePathIntegral ι) (O : ι → ℂ) :
    P.insertion O = ∑ i, P.weight i * O i := rfl

@[simp] theorem expectation_apply (P : FinitePathIntegral ι) (O : ι → ℂ) :
    P.expectation O = (∑ i, P.weight i * O i) / (∑ i, P.weight i) := rfl

/-! Action-facing constructor.  The action is allowed to be complex so the
same interface covers Euclidean weights and finite oscillatory toy models. -/

/-- Build a finite path integral from an action and an explicit nonzero
partition certificate for its exponential weight. -/
noncomputable def fromAction (S : ι → ℂ)
    (h : (∑ i, Complex.exp (-S i)) ≠ 0) : FinitePathIntegral ι where
  weight := fun i => Complex.exp (-S i)
  partition_ne_zero := h

@[simp] theorem fromAction_weight (S : ι → ℂ)
    (h : (∑ i, Complex.exp (-S i)) ≠ 0) :
    (fromAction S h).weight = fun i => Complex.exp (-S i) := rfl

theorem action_shift_weight_sum (S : ι → ℂ) (c : ℂ) :
    (∑ i, Complex.exp (-(S i + c))) =
      Complex.exp (-c) * (∑ i, Complex.exp (-S i)) := by
  calc
    (∑ i, Complex.exp (-(S i + c))) =
        ∑ i, (Complex.exp (-c) * Complex.exp (-S i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show -(S i + c) = -c + -S i by ring, Complex.exp_add]
    _ = Complex.exp (-c) * (∑ i, Complex.exp (-S i)) := by
      rw [Finset.mul_sum]

theorem action_shift_insertion (S : ι → ℂ) (c : ℂ) (O : ι → ℂ) :
    (∑ i, Complex.exp (-(S i + c)) * O i) =
      Complex.exp (-c) * (∑ i, Complex.exp (-S i) * O i) := by
  calc
    (∑ i, Complex.exp (-(S i + c)) * O i) =
        ∑ i, (Complex.exp (-c) * (Complex.exp (-S i) * O i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show -(S i + c) = -c + -S i by ring, Complex.exp_add]
      ring
    _ = Complex.exp (-c) * (∑ i, Complex.exp (-S i) * O i) := by
      rw [Finset.mul_sum]

theorem action_shift_expectation (S : ι → ℂ) (c : ℂ) (O : ι → ℂ)
    (h : (∑ i, Complex.exp (-S i)) ≠ 0) :
    (fromAction (fun i => S i + c)
      (by
        rw [action_shift_weight_sum]
        exact mul_ne_zero (Complex.exp_ne_zero (-c)) h)).expectation O =
      (fromAction S h).expectation O := by
  unfold expectation insertion partition fromAction
  rw [action_shift_insertion, action_shift_weight_sum]
  field_simp [h, Complex.exp_ne_zero]

/-- A real finite Euclidean action has strictly positive exponential weights.
For a nonempty finite configuration space this discharges the partition
nonzero obligation constructively, while the complex-action constructor above
continues to cover oscillatory models where cancellation is possible. -/
noncomputable def fromRealAction [Nonempty ι] (S : ι → ℝ) :
    FinitePathIntegral ι where
  weight := fun i => (Real.exp (-S i) : ℂ)
  partition_ne_zero := by
    intro h
    have hre : (∑ i, Real.exp (-S i)) = 0 := by
      apply Complex.ofReal_inj.mp
      rw [Complex.ofReal_sum]
      exact h
    have hpos : 0 < ∑ i, Real.exp (-S i) := by
      apply Finset.sum_pos
      · intro i hi
        exact Real.exp_pos _
      · exact Finset.univ_nonempty
    linarith

@[simp] theorem fromRealAction_weight (S : ι → ℝ) [Nonempty ι] :
    (fromRealAction S).weight = fun i => (Real.exp (-S i) : ℂ) := rfl

theorem fromRealAction_partition_re (S : ι → ℝ) [Nonempty ι] :
    (fromRealAction S).partition.re = ∑ i, Real.exp (-S i) := by
  unfold fromRealAction partition
  change Complex.reCLM (∑ i, (Real.exp (-S i) : ℂ)) = _
  rw [map_sum Complex.reCLM]
  apply Finset.sum_congr rfl
  intro i hi
  change (Real.exp (-S i) : ℂ).re = Real.exp (-S i)
  rfl

theorem fromRealAction_partition_pos (S : ι → ℝ) [Nonempty ι] :
    0 < (fromRealAction S).partition.re := by
  rw [fromRealAction_partition_re]
  apply Finset.sum_pos
  · intro i hi
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

theorem fromRealAction_partition_lower_bound (S : ι → ℝ) [Nonempty ι]
    (i₀ : ι) :
    Real.exp (-S i₀) ≤ ‖(fromRealAction S).partition‖ := by
  have hpos : 0 ≤ ∑ i, Real.exp (-S i) := by
    apply le_of_lt
    apply Finset.sum_pos
    · intro i hi
      exact Real.exp_pos _
    · exact Finset.univ_nonempty
  have hsum : Real.exp (-S i₀) ≤ ∑ i, Real.exp (-S i) :=
    Finset.single_le_sum (fun i hi => le_of_lt (Real.exp_pos (-S i)))
      (Finset.mem_univ i₀)
  simp only [partition, fromRealAction]
  change Real.exp (-S i₀) ≤ ‖∑ i, (Real.exp (-S i) : ℂ)‖
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hpos]
  exact hsum

/-- A constant observable has the expected constant value. -/
theorem expectation_const (P : FinitePathIntegral ι) (c : ℂ) :
    P.expectation (fun _ => c) = c := by
  unfold expectation insertion partition
  rw [← Finset.sum_mul]
  field_simp [P.partition_ne_zero]

/-- Expectation is additive in the observable insertion. -/
theorem expectation_add (P : FinitePathIntegral ι) (O Q : ι → ℂ) :
    P.expectation (fun i => O i + Q i) = P.expectation O + P.expectation Q := by
  unfold expectation insertion
  simp only [mul_add, Finset.sum_add_distrib, add_div]

/-- Expectation is homogeneous in the observable insertion. -/
theorem expectation_smul (P : FinitePathIntegral ι) (c : ℂ) (O : ι → ℂ) :
    P.expectation (fun i => c * O i) = c * P.expectation O := by
  unfold expectation insertion
  have hsum : (∑ i, P.weight i * (c * O i)) =
      c * (∑ i, P.weight i * O i) := by
    calc
      (∑ i, P.weight i * (c * O i)) =
          ∑ i, c * (P.weight i * O i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = c * (∑ i, P.weight i * O i) := by rw [Finset.mul_sum]
  rw [hsum]
  field_simp [P.partition_ne_zero]

/-- Reindexing a finite path space by an equivalence preserves the partition
function and the normalized expectation. -/
theorem partition_reindex {κ : Type v} [Fintype κ]
    (P : FinitePathIntegral κ) (e : ι ≃ κ) :
    (∑ i, P.weight (e i)) = P.partition := by
  unfold partition
  exact Equiv.sum_comp e P.weight

theorem insertion_reindex {κ : Type v} [Fintype κ]
    (P : FinitePathIntegral κ) (e : ι ≃ κ) (O : κ → ℂ) :
    (∑ i, P.weight (e i) * O (e i)) = P.insertion O := by
  unfold insertion
  exact Equiv.sum_comp e (fun x => P.weight x * O x)

/-! A finite symmetry certificate for path-integral weights.  It is the
algebraic part of a Ward/change-of-variables argument: invariance of the
finite weight under a permutation is an input, and the kernel proves the
corresponding insertion and expectation identities. -/

def WeightSymmetry (P : FinitePathIntegral ι) (e : ι ≃ ι) : Prop :=
  ∀ i, P.weight (e i) = P.weight i

theorem insertion_reindex_of_weightSymmetry
    (P : FinitePathIntegral ι) (e : ι ≃ ι)
    (hsym : WeightSymmetry P e) (O : ι → ℂ) :
    ∑ i, P.weight i * O (e i) = ∑ i, P.weight i * O i := by
  calc
    (∑ i, P.weight i * O (e i)) =
        ∑ i, P.weight (e i) * O (e i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hsym i]
    _ = ∑ i, P.weight i * O i := P.insertion_reindex e O

theorem expectation_reindex_of_weightSymmetry
    (P : FinitePathIntegral ι) (e : ι ≃ ι)
    (hsym : WeightSymmetry P e) (O : ι → ℂ) :
    P.expectation (fun i => O (e i)) = P.expectation O := by
  unfold expectation insertion
  rw [P.insertion_reindex_of_weightSymmetry e hsym O]

theorem insertion_symmetry_difference_zero
    (P : FinitePathIntegral ι) (e : ι ≃ ι)
    (hsym : WeightSymmetry P e) (O : ι → ℂ) :
    ∑ i, P.weight i * (O (e i) - O i) = 0 := by
  rw [show (fun i => P.weight i * (O (e i) - O i)) =
      (fun i => P.weight i * O (e i) - P.weight i * O i) by
        funext i
        ring]
  rw [Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr (P.insertion_reindex_of_weightSymmetry e hsym O)

/-- A coarse map pushes a finite weight to a finite target space. -/
noncomputable def pushforwardWeight {κ : Type v} [Fintype κ]
    (R : ι → κ) (w : ι → ℂ) (y : κ) : ℂ := by
  classical
  exact ∑ x, if R x = y then w x else 0

/-- Exact preservation of the finite partition function under a coarse map. -/
theorem pushforward_partition {κ : Type v} [Fintype κ]
    (R : ι → κ) (w : ι → ℂ) :
    ∑ y, pushforwardWeight R w y = ∑ x, w x := by
  classical
  unfold pushforwardWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp

/-- Exact insertion push-forward: a coarse observable pulled back along `R`
has the same weighted sum before and after coarse graining. -/
theorem pushforward_insertion {κ : Type v} [Fintype κ]
    (R : ι → κ) (w : ι → ℂ) (O : κ → ℂ) :
    ∑ y, pushforwardWeight R w y * O y =
      ∑ x, w x * O (R x) := by
  classical
  unfold pushforwardWeight
  calc
    (∑ y, (∑ x, if R x = y then w x else 0) * O y) =
        ∑ y, ∑ x, (if R x = y then w x else 0) * O y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.sum_mul]
    _ = ∑ x, ∑ y, (if R x = y then w x else 0) * O y := by
          rw [Finset.sum_comm]
    _ = ∑ x, w x * O (R x) := by
          apply Finset.sum_congr rfl
          intro x hx
          calc
            (∑ y, (if R x = y then w x else 0) * O y) =
                ∑ y, if R x = y then w x * O y else 0 := by
                  apply Finset.sum_congr rfl
                  intro y hy
                  split <;> simp_all
            _ = w x * O (R x) := by simp

/-- A finite renormalization/blocking step.  Its coarse weights are defined by
an exact finite push-forward; the partition certificate is therefore a
computable theorem rather than an assumed continuum RG law. -/
structure FiniteRGStep (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] where
  coarse : ι → κ
  fineWeight : ι → ℂ

namespace FiniteRGStep

variable {κ : Type v} [Fintype κ]

noncomputable def coarseWeight (R : FiniteRGStep ι κ) : κ → ℂ :=
  pushforwardWeight R.coarse R.fineWeight

theorem partition_preserved (R : FiniteRGStep ι κ) :
    ∑ y, R.coarseWeight y = ∑ x, R.fineWeight x :=
  pushforward_partition R.coarse R.fineWeight

theorem insertion_preserved (R : FiniteRGStep ι κ) (O : κ → ℂ) :
    ∑ y, R.coarseWeight y * O y =
      ∑ x, R.fineWeight x * O (R.coarse x) :=
  pushforward_insertion R.coarse R.fineWeight O

/-- The nonzero partition certificate is transported through exact finite
coarse graining.  This is the finite analogue of the normalization obligation
that a continuum RG construction must discharge separately. -/
theorem coarse_partition_ne_zero (R : FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0) :
    (∑ y, R.coarseWeight y) ≠ 0 := by
  rw [R.partition_preserved]
  exact h

/-- Turn a finite RG record into a normalized fine path integral. -/
noncomputable def finePathIntegral (R : FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0) : FinitePathIntegral ι where
  weight := R.fineWeight
  partition_ne_zero := h

/-- Turn the exact push-forward into a normalized coarse path integral. -/
noncomputable def coarsePathIntegral (R : FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0) : FinitePathIntegral κ where
  weight := R.coarseWeight
  partition_ne_zero := R.coarse_partition_ne_zero h

@[simp] theorem finePathIntegral_weight (R : FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0) :
    (R.finePathIntegral h).weight = R.fineWeight := rfl

@[simp] theorem coarsePathIntegral_weight (R : FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0) :
    (R.coarsePathIntegral h).weight = R.coarseWeight := rfl

/-- Exact finite RG invariance of normalized expectations for observables that
depend only on the coarse configuration. -/
theorem expectation_preserved (R : FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0) (O : κ → ℂ) :
    (R.coarsePathIntegral h).expectation O =
      (R.finePathIntegral h).expectation (fun x => O (R.coarse x)) := by
  unfold FinitePathIntegral.expectation FinitePathIntegral.insertion
    FinitePathIntegral.partition coarsePathIntegral finePathIntegral
  rw [R.insertion_preserved, R.partition_preserved]

/-- Compose two finite blocking maps while retaining the original fine
weights.  The second map is a map on the already-coarse configuration space.
This is intentionally a finite push-forward composition theorem, not a claim
about a continuum RG semigroup or fixed point. -/
def coarsen {W : Type v} [Fintype W]
    (R : FiniteRGStep ι κ) (next : κ → W) : FiniteRGStep ι W where
  coarse := next ∘ R.coarse
  fineWeight := R.fineWeight

theorem coarsen_partition_preserved {W : Type v} [Fintype W]
    (R : FiniteRGStep ι κ) (next : κ → W) :
    ∑ z, (R.coarsen next).coarseWeight z = ∑ x, R.fineWeight x := by
  exact pushforward_partition (next ∘ R.coarse) R.fineWeight

theorem coarsen_insertion_preserved {W : Type v} [Fintype W]
    (R : FiniteRGStep ι κ) (next : κ → W) (O : W → ℂ) :
    ∑ z, (R.coarsen next).coarseWeight z * O z =
      ∑ x, R.fineWeight x * O (next (R.coarse x)) := by
  simpa [coarsen, coarseWeight, Function.comp_def] using
    (pushforward_insertion (next ∘ R.coarse) R.fineWeight O)

/-! The two-step push-forward is definitionally a composition of finite
blocking maps.  Keeping this equality explicit is useful when a numerical RG
pipeline stores the intermediate coarse weights separately. -/

theorem coarsen_weight_eq_pushforward_coarseWeight {W : Type v}
    [Fintype W] (R : FiniteRGStep ι κ) (next : κ → W) (z : W) :
    (R.coarsen next).coarseWeight z =
      pushforwardWeight next R.coarseWeight z := by
  classical
  unfold coarsen coarseWeight pushforwardWeight
  change (∑ x, if next (R.coarse x) = z then R.fineWeight x else 0) =
    ∑ y, if next y = z then
      ∑ x, if R.coarse x = y then R.fineWeight x else 0 else 0
  calc
    (∑ x, if next (R.coarse x) = z then R.fineWeight x else 0) =
        ∑ x, ∑ y,
          if next y = z then
            (if R.coarse x = y then R.fineWeight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hsum :
          (∑ y, if next y = z then
            (if R.coarse x = y then R.fineWeight x else 0) else 0) =
            if next (R.coarse x) = z then R.fineWeight x else 0 := by
        rw [Finset.sum_eq_single (R.coarse x)]
        · simp
        · intro y hy hxy
          by_cases hnext : next y = z
          · simp [hnext, Ne.symm hxy]
          · simp [hnext]
        · intro hmem
          exact absurd (Finset.mem_univ (R.coarse x)) hmem
      exact hsum.symm
    _ = ∑ y, ∑ x,
          if next y = z then
            (if R.coarse x = y then R.fineWeight x else 0) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ y, if next y = z then
          ∑ x, if R.coarse x = y then R.fineWeight x else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases h : next y = z <;> simp [h]

theorem coarsen_weight_assoc {W Z : Type v} [Fintype W] [Fintype Z]
    (R : FiniteRGStep ι κ) (next : κ → W) (last : W → Z) :
    ((R.coarsen next).coarsen last).coarseWeight =
      (R.coarsen (last ∘ next)).coarseWeight := by
  funext z
  simp [coarsen, coarseWeight, Function.comp_def]

theorem coarsen_expectation_preserved {W : Type v} [Fintype W]
    (R : FiniteRGStep ι κ) (next : κ → W)
    (h : (∑ x, R.fineWeight x) ≠ 0) (O : W → ℂ) :
    ((R.coarsen next).coarsePathIntegral
      (by simpa [coarsen] using h)).expectation O =
      (R.finePathIntegral h).expectation
        (fun x => O (next (R.coarse x))) := by
  unfold FinitePathIntegral.expectation FinitePathIntegral.insertion
    FinitePathIntegral.partition coarsePathIntegral finePathIntegral
  rw [R.coarsen_insertion_preserved next O,
    R.coarsen_partition_preserved next]

/-! A finite RG chain is an explicit list of blocking maps on the same finite
coarse label space.  The definition keeps every map visible and the theorems
below reduce the whole chain to one exact push-forward.  This is useful for
finite-size or truncated RG experiments, while making no claim that the list
approximates a continuum semigroup. -/

def coarsenMany (R : FiniteRGStep ι κ) : List (κ → κ) → FiniteRGStep ι κ
  | [] => R
  | next :: rest => coarsenMany (R.coarsen next) rest

@[simp] theorem coarsenMany_fineWeight
    (R : FiniteRGStep ι κ) (maps : List (κ → κ)) :
    (R.coarsenMany maps).fineWeight = R.fineWeight := by
  induction maps generalizing R with
  | nil => rfl
  | cons next rest ih =>
      simpa [coarsenMany, coarsen] using ih (R := R.coarsen next)

theorem coarsenMany_partition_preserved
    (R : FiniteRGStep ι κ) (maps : List (κ → κ)) :
    ∑ y, (R.coarsenMany maps).coarseWeight y = ∑ x, R.fineWeight x := by
  simpa [coarseWeight] using
    (pushforward_partition (R.coarsenMany maps).coarse R.fineWeight)

theorem coarsenMany_insertion_preserved
    (R : FiniteRGStep ι κ) (maps : List (κ → κ)) (O : κ → ℂ) :
    ∑ y, (R.coarsenMany maps).coarseWeight y * O y =
      ∑ x, R.fineWeight x * O ((R.coarsenMany maps).coarse x) := by
  simpa [coarseWeight] using
    (pushforward_insertion (R.coarsenMany maps).coarse R.fineWeight O)

theorem coarsenMany_expectation_preserved
    (R : FiniteRGStep ι κ) (maps : List (κ → κ))
    (h : (∑ x, R.fineWeight x) ≠ 0) (O : κ → ℂ) :
    ((R.coarsenMany maps).coarsePathIntegral
      (by simpa only [coarsenMany_fineWeight] using h)).expectation O =
      (R.finePathIntegral h).expectation
        (fun x => O ((R.coarsenMany maps).coarse x)) := by
  unfold FinitePathIntegral.expectation FinitePathIntegral.insertion
    FinitePathIntegral.partition coarsePathIntegral finePathIntegral
  rw [coarsenMany_insertion_preserved, coarsenMany_partition_preserved]

/-- Exact finite fixed-point certificate: after blocking, every coarse weight
equals the weight on the same finite label set.  This is a deliberately strong
finite predicate; it does not encode a continuum fixed point or a critical
exponent. -/
def IsFixedPoint {ι : Type u} [Fintype ι]
    (R : FiniteRGStep ι ι) : Prop :=
  ∀ y, R.coarseWeight y = R.fineWeight y

theorem fixedPoint_partition {ι : Type u} [Fintype ι]
    (R : FiniteRGStep ι ι) (hR : IsFixedPoint R) :
    ∑ y, R.coarseWeight y = ∑ y, R.fineWeight y := by
  apply Finset.sum_congr rfl
  intro y hy
  exact hR y

theorem fixedPoint_expectation {ι : Type u} [Fintype ι]
    (R : FiniteRGStep ι ι) (h : (∑ y, R.fineWeight y) ≠ 0)
    (hR : IsFixedPoint R) (O : ι → ℂ) :
    (R.coarsePathIntegral h).expectation O =
      (R.finePathIntegral h).expectation O := by
  unfold coarsePathIntegral finePathIntegral FinitePathIntegral.expectation
    FinitePathIntegral.insertion FinitePathIntegral.partition
  simp only [coarseWeight]
  have hw : ∀ y, pushforwardWeight R.coarse R.fineWeight y = R.fineWeight y := hR
  simp_rw [hw]

/-- A finite operator-scaling certificate.  `lambda` is supplied by the model;
the theorem below only transports that exact relation through a finite
push-forward.  It is the auditable finite counterpart of an RG scaling law,
without interpreting `lambda` as a continuum critical exponent. -/
def ScalingCertificate {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ]
    (R : FiniteRGStep ι κ) (fineObs : ι → ℂ) (coarseObs : κ → ℂ)
    (lambda : ℂ) : Prop :=
  ∀ x, fineObs x = lambda * coarseObs (R.coarse x)

theorem ScalingCertificate.compose {W : Type v} [Fintype W]
    (R : FiniteRGStep ι κ) (next : κ → W)
    (fineObs : ι → ℂ) (middleObs : κ → ℂ) (coarseObs : W → ℂ)
    (lambda mu : ℂ)
    (h₁ : ScalingCertificate R fineObs middleObs lambda)
    (h₂ : ∀ y, middleObs y = mu * coarseObs (next y)) :
    ScalingCertificate (R.coarsen next) fineObs coarseObs (lambda * mu) := by
  intro x
  change fineObs x = (lambda * mu) * coarseObs (next (R.coarse x))
  rw [h₁ x, h₂ (R.coarse x)]
  ring

theorem insertion_scales {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ]
    (R : FiniteRGStep ι κ) (fineObs : ι → ℂ) (coarseObs : κ → ℂ)
    (lambda : ℂ) (hscale : ScalingCertificate R fineObs coarseObs lambda) :
    ∑ x, R.fineWeight x * fineObs x =
      lambda * (∑ y, R.coarseWeight y * coarseObs y) := by
  calc
    (∑ x, R.fineWeight x * fineObs x) =
        ∑ x, R.fineWeight x * (lambda * coarseObs (R.coarse x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hscale x]
    _ = ∑ x, lambda * (R.fineWeight x * coarseObs (R.coarse x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = lambda * (∑ x, R.fineWeight x * coarseObs (R.coarse x)) := by
          rw [Finset.mul_sum]
    _ = lambda * (∑ y, R.coarseWeight y * coarseObs y) := by
          rw [R.insertion_preserved]

theorem coarsenMany_insertion_scales
    (R : FiniteRGStep ι κ) (maps : List (κ → κ))
    (fineObs : ι → ℂ) (coarseObs : κ → ℂ) (lambda : ℂ)
    (hscale : ScalingCertificate (R.coarsenMany maps)
      fineObs coarseObs lambda) :
    ∑ x, R.fineWeight x * fineObs x =
      lambda * (∑ y, (R.coarsenMany maps).coarseWeight y * coarseObs y) := by
  have h := (R.coarsenMany maps).insertion_scales
    fineObs coarseObs lambda hscale
  rw [coarsenMany_fineWeight] at h
  exact h

theorem expectation_scales {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ]
    (R : FiniteRGStep ι κ) (h : (∑ x, R.fineWeight x) ≠ 0)
    (fineObs : ι → ℂ) (coarseObs : κ → ℂ) (lambda : ℂ)
    (hscale : ScalingCertificate R fineObs coarseObs lambda) :
    (R.finePathIntegral h).expectation fineObs =
      lambda * (R.coarsePathIntegral h).expectation coarseObs := by
  unfold finePathIntegral coarsePathIntegral FinitePathIntegral.expectation
    FinitePathIntegral.insertion FinitePathIntegral.partition
  rw [R.insertion_scales fineObs coarseObs lambda hscale,
    R.partition_preserved]
  field_simp [h]

theorem coarsenMany_expectation_scales
    (R : FiniteRGStep ι κ) (maps : List (κ → κ))
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (fineObs : ι → ℂ) (coarseObs : κ → ℂ) (lambda : ℂ)
    (hscale : ScalingCertificate (R.coarsenMany maps)
      fineObs coarseObs lambda) :
    (R.finePathIntegral h).expectation fineObs =
      lambda * ((R.coarsenMany maps).coarsePathIntegral
        (by simpa only [coarsenMany_fineWeight] using h)).expectation coarseObs := by
  unfold FinitePathIntegral.expectation FinitePathIntegral.insertion
    FinitePathIntegral.partition coarsePathIntegral finePathIntegral
  rw [coarsenMany_insertion_scales R maps fineObs coarseObs lambda hscale,
    coarsenMany_partition_preserved]
  field_simp [h]

end FiniteRGStep

end FinitePathIntegral

end LeanPhy.Mathematics

/-! Domain-facing names for finite path and coarse-graining calculations. -/

namespace LeanPhy

namespace FieldTheory
abbrev FinitePathMeasure {ι : Type*} [Fintype ι] :=
  Mathematics.FinitePathIntegral (ι := ι)
end FieldTheory

namespace Quantum
abbrev FiniteEuclideanPathMeasure {ι : Type*} [Fintype ι] :=
  Mathematics.FinitePathIntegral (ι := ι)
end Quantum

namespace Condensed
abbrev FiniteLatticePathMeasure {ι : Type*} [Fintype ι] :=
  Mathematics.FinitePathIntegral (ι := ι)
end Condensed

namespace StatMech
abbrev FiniteBlockRG {ι κ : Type*} [Fintype ι] [Fintype κ] :=
  Mathematics.FinitePathIntegral.FiniteRGStep (ι := ι) (κ := κ)
end StatMech

namespace GaugeTheory
abbrev FiniteGaugeBlocking {ι κ : Type*} [Fintype ι] [Fintype κ] :=
  Mathematics.FinitePathIntegral.FiniteRGStep (ι := ι) (κ := κ)
end GaugeTheory

end LeanPhy
