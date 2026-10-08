import LeanPhy.StatMech.SourceEnsemble

set_option autoImplicit false

/-!
# Thermal and Hamiltonian-parameter derivatives of finite Gibbs states

The energy convention is `exp(-β E)` with dimensionless `β E`. A source of
energy dimension changes the energy to `E - h A`; its response is `β Cov(O,A)`,
not the dimensionless-source formula without β. Parameter-dependent energies
and observables retain both the covariance and contact terms.

These statements apply to commuting, real finite configuration energies.
They do not differentiate `exp(-β H)` for a noncommuting quantum Hamiltonian;
that requires an operator/Duhamel response theorem.
-/

namespace LeanPhy.StatMech

open LeanPhy.Mathematics
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The existing Gibbs probability is the normalized exponential ensemble. -/
theorem finiteGibbs_expectation_eq_weighted (β : ℝ) (E O : ι → ℝ) :
    (finiteGibbsProbability β E).expectation O =
      FiniteWeighted.expectation (fun i => Real.exp (-β * E i)) O := by
  simp only [FiniteProbability.expectation, finiteGibbsProbability, finiteGibbsWeight,
    FiniteWeighted.expectation, FiniteWeighted.insertion, FiniteWeighted.partition,
    finitePartitionFunction]
  simp_rw [div_mul_eq_mul_div]
  rw [Finset.sum_div]

theorem finiteGibbs_covariance_eq_connected (β : ℝ) (E O A : ι → ℝ) :
    (finiteGibbsProbability β E).covariance O A =
      FiniteWeighted.connected (fun i => Real.exp (-β * E i)) O A := by
  simp only [FiniteProbability.covariance, FiniteWeighted.connected,
    ← finiteGibbs_expectation_eq_weighted]

/-- General parameter response, including the observable's explicit derivative. -/
theorem hasDerivAt_finiteGibbs_parameter (β : ℝ) (E O : ℝ → ι → ℝ)
    (E' O' : ι → ℝ) (t : ℝ)
    (hE : ∀ i, HasDerivAt (fun s => E s i) (E' i) t)
    (hO : ∀ i, HasDerivAt (fun s => O s i) (O' i) t) :
    HasDerivAt (fun s => (finiteGibbsProbability β (E s)).expectation (O s))
      ((finiteGibbsProbability β (E t)).expectation O' -
        β * (finiteGibbsProbability β (E t)).covariance (O t) E') t := by
  have hw (i : ι) := ((hE i).const_mul (-β)).exp
  have h := FiniteWeighted.hasDerivAt_expectation_score
    (fun s i => Real.exp (-β * E s i)) O (fun i => -β * E' i) O' t hw hO
    (ne_of_gt (finitePartitionFunction_pos β (E t)))
  simp_rw [← finiteGibbs_expectation_eq_weighted, ← finiteGibbs_covariance_eq_connected] at h
  have hc : (finiteGibbsProbability β (E t)).covariance (O t) (fun i => -β * E' i) =
      -β * (finiteGibbsProbability β (E t)).covariance (O t) E' := by
    rw [FiniteProbability.covariance_symm]
    change (finiteGibbsProbability β (E t)).covariance ((-β) • E') (O t) = _
    rw [FiniteProbability.covariance_smul_left, FiniteProbability.covariance_symm]
  rw [hc] at h
  simpa [sub_eq_add_neg] using h

/-- Static susceptibility to the energy perturbation `E - h A`. -/
theorem hasDerivAt_finiteGibbs_energySource (β : ℝ) (E A O : ι → ℝ) (h : ℝ) :
    HasDerivAt (fun s => (finiteGibbsProbability β (fun i => E i - s * A i)).expectation O)
      (β * (finiteGibbsProbability β (fun i => E i - h * A i)).covariance O A) h := by
  have hw (i : ι) : HasDerivAt (fun s => Real.exp (-β * (E i - s * A i)))
      (Real.exp (-β * (E i - h * A i)) * (β * A i)) h := by
    convert! ((((hasDerivAt_id h).mul_const (A i)).const_sub (E i)).const_mul (-β)).exp using 1 <;> dsimp <;> ring
  have hr := FiniteWeighted.hasDerivAt_expectation_fixed
    (fun s i => Real.exp (-β * (E i - s * A i))) O (fun i => β * A i) h hw
    (ne_of_gt (finitePartitionFunction_pos β (fun i => E i - h * A i)))
  simp_rw [← finiteGibbs_expectation_eq_weighted, ← finiteGibbs_covariance_eq_connected] at hr
  convert! hr using 1
  exact ((finiteGibbsProbability β (fun i => E i - h * A i)).covariance_smul_right β O A).symm

/-- Inverse-temperature differentiation inserts minus the energy. -/
theorem hasDerivAt_finiteGibbs_beta (E O : ι → ℝ) (β : ℝ) :
    HasDerivAt (fun b => (finiteGibbsProbability b E).expectation O)
      (-(finiteGibbsProbability β E).covariance O E) β := by
  have hw (i : ι) : HasDerivAt (fun b => Real.exp (-b * E i))
      (Real.exp (-β * E i) * (-E i)) β := by
    convert! (((hasDerivAt_id β).neg).mul_const (E i)).exp using 1 <;> dsimp <;> ring
  have hr := FiniteWeighted.hasDerivAt_expectation_fixed
    (fun b i => Real.exp (-b * E i)) O (fun i => -E i) β hw
    (ne_of_gt (finitePartitionFunction_pos β E))
  simp_rw [← finiteGibbs_expectation_eq_weighted, ← finiteGibbs_covariance_eq_connected] at hr
  convert! hr using 1
  have hc := (finiteGibbsProbability β E).covariance_smul_right (-1) O E
  convert! hc.symm using 1 <;> simp <;> rfl

theorem finiteGibbs_energy_deriv (E : ι → ℝ) (β : ℝ) :
    deriv (fun b => (finiteGibbsProbability b E).expectation E) β =
      -(finiteGibbsProbability β E).variance E :=
  (hasDerivAt_finiteGibbs_beta E E β).deriv

theorem finiteGibbs_energy_deriv_nonpos (E : ι → ℝ) (β : ℝ) :
    deriv (fun b => (finiteGibbsProbability b E).expectation E) β ≤ 0 := by
  rw [finiteGibbs_energy_deriv]
  exact neg_nonpos.mpr ((finiteGibbsProbability β E).variance_nonneg E)

/-- Heat-capacity identity in units `k_B = 1`, with β = 1/T. The nonzero
T condition belongs to the analytic inverse-temperature conversion. -/
theorem hasDerivAt_finiteGibbs_temperature (E : ι → ℝ) (T : ℝ) (hT : T ≠ 0) :
    HasDerivAt (fun t => (finiteGibbsProbability t⁻¹ E).expectation E)
      ((finiteGibbsProbability T⁻¹ E).variance E / T ^ 2) T := by
  have h := (hasDerivAt_finiteGibbs_beta E E T⁻¹).comp T (hasDerivAt_inv hT)
  convert! h using 1 <;> simp [FiniteProbability.variance, div_eq_mul_inv]

theorem finiteGibbs_heat_capacity_nonneg (E : ι → ℝ) (T : ℝ) (hT : T ≠ 0) :
    0 ≤ deriv (fun t => (finiteGibbsProbability t⁻¹ E).expectation E) T := by
  rw [(hasDerivAt_finiteGibbs_temperature E T hT).deriv]
  exact div_nonneg ((finiteGibbsProbability T⁻¹ E).variance_nonneg E) (sq_nonneg T)

end LeanPhy.StatMech
