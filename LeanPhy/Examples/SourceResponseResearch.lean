import LeanPhy.StatMech.GibbsResponse
import LeanPhy.StatMech.ResponseBound
import LeanPhy.FieldTheory.FiniteSourceResponse
import LeanPhy.FieldTheory.FiniteActionResponse
import LeanPhy.Quantum.FiniteThermalState
import LeanPhy.Workflow.Core

set_option autoImplicit false

/-!
# Research-chain regressions for source derivatives and response

A finite Ising configuration space has variable site count, couplings and edge
set. Its susceptibility follows from the shared Gibbs derivative, not a
closed-form two-state example. Additional checks cover contact terms, finite
source error bounds, the real/complex ensemble bridge and an actual complex
partition zero. Analytic finite-state results leave dynamical response and
thermodynamic/continuum limits as explicit project obligations.
-/

namespace LeanPhy.Examples.SourceResponseResearch

open LeanPhy.StatMech LeanPhy.Mathematics LeanPhy.Workflow LeanPhy.Quantum
open scoped BigOperators

abbrev SpinConfiguration (n : ℕ) := Fin n → Bool

def spinValue (b : Bool) : ℝ := if b then 1 else -1

noncomputable def magnetization {n : ℕ} (q : SpinConfiguration n) : ℝ :=
  ∑ i, spinValue (q i)

/-- Every listed edge contributes once; listing both orientations counts both.
There is no implicit graph/symmetry or missing factor of one half. -/
noncomputable def isingEnergy {n : ℕ} (edges : Finset (Fin n × Fin n))
    (K : Fin n × Fin n → ℝ) (q : SpinConfiguration n) : ℝ :=
  -∑ e ∈ edges, K e * spinValue (q e.1) * spinValue (q e.2)

/-- Arbitrary finite graph, coupling table, field and inverse temperature. -/
theorem ising_magnetic_response {n : ℕ} (edges : Finset (Fin n × Fin n))
    (K : Fin n × Fin n → ℝ) (β h : ℝ) :
    HasDerivAt (fun s => (finiteGibbsProbability β
      (fun q => isingEnergy edges K q - s * magnetization q)).expectation magnetization)
      (β * (finiteGibbsProbability β
        (fun q => isingEnergy edges K q - h * magnetization q)).variance magnetization) h :=
  hasDerivAt_finiteGibbs_energySource β (isingEnergy edges K) magnetization magnetization h

/-- Positivity of magnetic susceptibility needs the physical β sign. -/
theorem ising_response_nonneg {n : ℕ} (edges : Finset (Fin n × Fin n))
    (K : Fin n × Fin n → ℝ) (β h : ℝ) (hβ : 0 ≤ β) :
    0 ≤ deriv (fun s => (finiteGibbsProbability β
      (fun q => isingEnergy edges K q - s * magnetization q)).expectation magnetization) h := by
  rw [(ising_magnetic_response edges K β h).deriv]
  exact mul_nonneg hβ (FiniteProbability.variance_nonneg _ _)

/-- The same model gives decreasing energy as inverse temperature increases. -/
theorem ising_energy_beta_nonpos {n : ℕ} (edges : Finset (Fin n × Fin n))
    (K : Fin n × Fin n → ℝ) (β : ℝ) :
    deriv (fun b => (finiteGibbsProbability b (isingEnergy edges K)).expectation
      (isingEnergy edges K)) β ≤ 0 :=
  finiteGibbs_energy_deriv_nonpos (isingEnergy edges K) β

/-- A source-dependent observable equal to the source itself has derivative
one even when its covariance with every source insertion is zero. -/
theorem moving_constant_contact {ι σ : Type*} [Fintype ι] [Nonempty ι] [Fintype σ]
    (S : ι → ℝ) (A : σ → ι → ℝ) (J v : σ → ℝ) (t : ℝ) :
    HasDerivAt (fun s => (SourceEnsemble.probability S A
      (SourceEnsemble.sourceLine J v s)).expectation (fun _ => s)) 1 t := by
  have h := SourceEnsemble.hasDerivAt_moving_expectation S A J v
    (fun s _ => s) (fun _ => 1) t (fun _ => hasDerivAt_id t)
  simpa only [FiniteProbability.expectation_const, FiniteProbability.covariance_const_left,
    add_zero] using h

/-- Generic finite changes produce a certificate with an explicit radius,
not an unjustified equality to the tangent line. -/
theorem bounded_source_change {ι σ : Type*} [Fintype ι] [Nonempty ι] [Fintype σ]
    (S : ι → ℝ) (A : σ → ι → ℝ) (J v : σ → ℝ) (O : ι → ℝ)
    (hO : ∀ i, |O i| ≤ 1) (hA : ∀ i, |SourceEnsemble.directionObservable A v i| ≤ 1)
    (s t : ℝ) :
    ErrorCertificate ((SourceEnsemble.probability S A (SourceEnsemble.sourceLine J v s)).expectation O)
      ((SourceEnsemble.probability S A (SourceEnsemble.sourceLine J v t)).expectation O)
      (2 * |s - t|) := by
  simpa using SourceEnsemble.expectation_source_error S A J v O 1 1 (by norm_num)
    (by norm_num) hO hA s t

/-- A real Gibbs/source covariance is exactly the existing Euclidean
connected correlator after the stated representation conversion. -/
theorem euclidean_response_bridge {ι σ : Type*} [Fintype ι] [Nonempty ι] [Fintype σ]
    (S : ι → ℝ) (A : σ → ι → ℝ) (J : σ → ℝ) (O Q : ι → ℝ) :
    (FinitePathIntegral.fromRealAction (SourceEnsemble.action S A J)).connectedCorrelator
      (fun i => (O i : ℂ)) (fun i => (Q i : ℂ)) =
      ((SourceEnsemble.probability S A J).covariance O Q : ℂ) :=
  SourceEnsemble.fromRealAction_connected S A J O Q

/-- A valid base ensemble with signed/complex weights need not remain
normalizable at every source value. -/
noncomputable def cancellingBase : FinitePathIntegral (Fin 2) where
  weight := fun i => if i = 0 then 2 else -1
  partition_ne_zero := by norm_num [Fin.sum_univ_two]

def cancellationInsertion (i : Fin 2) : ℂ := if i = 0 then 0 else 1

theorem source_partition_can_vanish :
    cancellingBase.sourcePartition cancellationInsertion (Complex.log 2) = 0 := by
  simp [FinitePathIntegral.sourcePartition, FinitePathIntegral.sourceWeight,
    FiniteWeighted.partition, cancellingBase, cancellationInsertion, Fin.sum_univ_two,
    Complex.exp_log (by norm_num : (2 : ℂ) ≠ 0)]

/-- A nonzero real partition does not make signed weights into a probability.
The connected self-correlation here is strictly negative. -/
theorem signed_connected_negative :
    (cancellingBase.connectedCorrelator cancellationInsertion cancellationInsertion).re = -2 := by
  norm_num [FinitePathIntegral.connectedCorrelator, FinitePathIntegral.correlator,
    FinitePathIntegral.expectation, FinitePathIntegral.insertion, FinitePathIntegral.partition,
    cancellingBase, cancellationInsertion, Fin.sum_univ_two]

theorem signed_zero_source_response (O : Fin 2 → ℂ) :
    HasDerivAt (cancellingBase.sourceExpectation cancellationInsertion O)
      (cancellingBase.connectedCorrelator O cancellationInsertion) 0 :=
  cancellingBase.hasDerivAt_sourceExpectation_zero _ _

/-- The finite spin example already has nonzero susceptibility at zero
field; omitting β is detected when β is two. -/
theorem beta_factor_regression :
    deriv (fun h => (finiteGibbsProbability 2 (fun b : Bool => -h * spinValue b)).expectation
      spinValue) 0 = 2 := by
  have h := (hasDerivAt_finiteGibbs_energySource 2 (fun _ : Bool => 0)
    spinValue spinValue 0).deriv
  norm_num [FiniteProbability.covariance, FiniteProbability.expectation,
    finiteGibbsProbability, finiteGibbsWeight, finitePartitionFunction,
    Fintype.sum_bool, spinValue] at h ⊢
  exact h

/-- Reuse the action layer from the previous construction stage: arbitrary
polynomial densities evaluated on an explicit finite field/gradient table. -/
theorem density_coupling_response
    (L V : LeanPhy.FieldTheory.FirstOrderLagrangian ℝ Unit Unit)
    (values : Fin 2 → Unit → Unit × Option Unit → ℝ)
    (O : Fin 2 → ℝ) (h : ℝ) :
    HasDerivAt (fun t => (LeanPhy.FieldTheory.FirstOrderLagrangian.finiteProbability
      (L + t • V) (fun _ => 1) values).expectation O)
      (-(LeanPhy.FieldTheory.FirstOrderLagrangian.finiteProbability
        (L + h • V) (fun _ => 1) values).covariance O
        (LeanPhy.FieldTheory.FirstOrderLagrangian.finiteAction V (fun _ => 1) values)) h :=
  LeanPhy.FieldTheory.FirstOrderLagrangian.hasDerivAt_finiteAction_expectation L V
    (fun _ => 1) values O h

/-- The statistical susceptibility is read from an actual density and matrix
probe after any fixed unitary change of the energy basis. -/
theorem thermal_beta_factor_regression (U : FiniteUnitary Bool) :
    deriv (fun h => (Matrix.trace
      ((thermalStateInBasis U 2 (fun b => -h * spinValue b)).rho *
        U.conjugate (realDiagonal spinValue))).re) 0 = 2 := by
  simpa only [thermalStateInBasis_expectation, Complex.ofReal_re] using beta_factor_regression

def flipBasis : FiniteUnitary (Fin 2) where
  op := !![0, 1; 1, 0]
  unitary := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply]

def leftProbability : FiniteProbability (Fin 2) where
  weight := fun i => if i = 0 then 1 else 0
  nonneg := by intro i; split <;> norm_num
  normalised := by norm_num [Fin.sum_univ_two]

/-- Rotating only the state changes a physical readout. The common-basis
invariance theorem must also transport the probe. -/
theorem changing_only_state_changes_readout :
    Matrix.trace (flipBasis.conjugate (diagonalDensity leftProbability).rho *
      realDiagonal leftProbability.weight) = 0 ∧
    Matrix.trace ((diagonalDensity leftProbability).rho *
      realDiagonal leftProbability.weight) = 1 := by
  norm_num [flipBasis, leftProbability, FiniteUnitary.conjugate, diagonalDensity,
    realDiagonal, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.vecMul, dotProduct, Fin.sum_univ_two]

def package : TheoryPackage :=
  TheoryPackage.empty "finite source response" "statistical mechanics and Euclidean field theory"
    |>.addTheorem "finite graph susceptibility" "arbitrary finite Ising couplings give beta times a variance"
      "ising_magnetic_response" (@ising_magnetic_response)
    |>.addTheorem "observable contact term" "source-dependent observables retain their explicit derivative"
      "moving_constant_contact" (@moving_constant_contact (Fin 2) Unit inferInstance inferInstance inferInstance)
    |>.addTheorem "Euclidean covariance bridge" "real normalized states match complex finite connected correlators"
      "euclidean_response_bridge" (@euclidean_response_bridge (Fin 2) Unit inferInstance inferInstance inferInstance)
    |>.addTheorem "complex partition zero" "a valid base ensemble can have a zero at nonzero source"
      "source_partition_can_vanish" source_partition_can_vanish
    |>.addTheorem "finite source budget" "bounded observables yield a finite-source error certificate"
      "bounded_source_change" (@bounded_source_change (Fin 2) Unit inferInstance inferInstance inferInstance)
    |>.addTheorem "action coupling insertion" "a positive Euclidean action perturbation gives minus covariance"
      "density_coupling_response" density_coupling_response
    |>.addTheorem "quantum Gibbs operator" "every finite Hermitian Hamiltonian has the normalized exponential density"
      "LeanPhy.Quantum.finiteThermalState_eq_exp" (@finiteThermalState_eq_exp.{0})
    |>.addTheorem "thermal stationarity" "the thermal state is stationary under its Hamiltonian flow"
      "LeanPhy.Quantum.finiteThermalState_stationary" (@finiteThermalState_stationary.{0})
    |>.addTheorem "quantum trace susceptibility" "fixed-basis matrix expectation retains the beta factor"
      "thermal_beta_factor_regression" thermal_beta_factor_regression
    |>.addTheorem "probe basis transport" "changing the state basis alone can change the readout"
      "changing_only_state_changes_readout" changing_only_state_changes_readout
    |>.addObligationText "thermodynamic limit" "prove volume-uniform bounds and a limiting state"
      "many-body analysis"
    |>.addObligationText "dynamical response" "construct causal quantum evolution and its time-dependent response"
      "operator dynamics"

example : package.claimCount = 10 := rfl
example : package.obligationCount = 2 := rfl
example : package.hasErrors = false := by decide

end LeanPhy.Examples.SourceResponseResearch
