import LeanPhy.Workflow.Core
import LeanPhy.Quantum.Pauli
import LeanPhy.FieldTheory.CCR
import LeanPhy.FieldTheory.MultiWick
import LeanPhy.HighEnergy.Gamma
import LeanPhy.HighEnergy.EffectiveTheory
import LeanPhy.Mathematics.FiniteParabolic
import LeanPhy.Mathematics.FiniteEnergy
import LeanPhy.Mathematics.FinitePathReflection
import LeanPhy.Mathematics.Hilbert
import LeanPhy.Mathematics.SpectralCalculus
import LeanPhy.Mathematics.SpectralGap
import LeanPhy.Classical.Symplectic
import LeanPhy.Condensed.BCS
import LeanPhy.GaugeTheory.FieldStrength
import LeanPhy.Relativity.Minkowski
import LeanPhy.StatMech.FiniteGibbs
import LeanPhy.Mathematics.ExternalCertificate
import LeanPhy.Mathematics.ParametricModel
import LeanPhy.Entry.Optics
import LeanPhy.Entry.Fluid

namespace LeanPhy.Workflow

open scoped Matrix
open Polynomial

/-! ## Shared proof-bearing claims

These universal claims deliberately retain their hypotheses.  A package can
therefore document an algebraic, stochastic or positivity assumption without
silently promoting it to a theorem.
-/

theorem ccr_number_claim :
    ∀ {A : Type} [Ring A] (a adag : A),
      LeanPhy.Quantum.commutator a adag = 1 →
      LeanPhy.Quantum.commutator (LeanPhy.FieldTheory.number adag a) adag = adag := by
  intro A _ a adag h
  exact LeanPhy.FieldTheory.number_commutator a adag h

theorem ccr_number_lowering_claim :
    ∀ {A : Type} [Ring A] (a adag : A),
      LeanPhy.Quantum.commutator a adag = 1 →
      LeanPhy.Quantum.commutator (LeanPhy.FieldTheory.number adag a) a = -a := by
  intro A _ a adag h
  exact LeanPhy.FieldTheory.number_commutator_a a adag h

theorem finite_step_bounds_claim :
    ∀ {ι : Type} [Fintype ι]
      (K : LeanPhy.Mathematics.FinitePositiveStep ι)
      (u : ι → ℝ) (lower upper : ℝ),
      (∀ j, lower ≤ u j) → (∀ j, u j ≤ upper) →
      ∀ i, lower ≤ K.step u i ∧ K.step u i ≤ upper := by
  intro ι _ K u lower upper hlo hhi
  exact K.step_bounds u lower upper hlo hhi

theorem finite_mass_preservation_claim :
    ∀ {ι : Type} [Fintype ι]
      (K : LeanPhy.Mathematics.FinitePositiveStep ι)
      (_C : LeanPhy.Mathematics.FinitePositiveStep.MassConservationCertificate K)
      (u : ι → ℝ),
      ∑ i, K.step u i = ∑ i, u i := by
  intro ι _ K C u
  exact K.sum_preserved C u

theorem finite_energy_bound_claim :
    ∀ {X : Type} (S : LeanPhy.Mathematics.FiniteEnergyStep X)
      (n : ℕ) (x : X),
      S.energy (S.iterate n x) ≤ S.factor ^ n * S.energy x := by
  intro X S n x
  exact S.iterate_energy_bound n x

theorem finite_positive_partition_claim :
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] (S : ι → ℝ),
      0 < (LeanPhy.Mathematics.FinitePositivePathIntegral.fromRealAction S).toComplex.partition.re := by
  intro ι _ _ S
  exact LeanPhy.Mathematics.FinitePositivePathIntegral.toComplex_partition_pos
    (LeanPhy.Mathematics.FinitePositivePathIntegral.fromRealAction S)

theorem finite_gram_positivity_claim :
    ∀ {ι α : Type} [Fintype ι] [Fintype α]
      (G : LeanPhy.Mathematics.FiniteWeightedGramKernel ι α)
      (f : ι → ℝ),
      0 ≤ G.kernelQuadratic f := by
  intro ι α _ _ G f
  exact G.kernelQuadratic_nonneg f

theorem finite_reflection_positivity_claim :
    ∀ {ι α : Type} [Fintype ι] [Fintype α]
      (C : LeanPhy.Mathematics.FiniteWeightedReflectionCertificate ι α)
      (f : ι → ℝ),
      0 ≤ C.reflectedKernelQuadratic f := by
  intro ι α _ _ C f
  exact C.reflectedKernelQuadratic_nonneg f

/-! Explicit proposition annotations keep polymorphic theorem schemas from
being prematurely instantiated while they are inserted into the heterogeneous
claim list. -/

def ccrRaisingChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "number raising" "[N, a†] = a† under CCR"
    "LeanPhy.FieldTheory.CCR" ["CCR", "finite operators", "scalar field"]
    (P := ∀ {A : Type} [Ring A] (a adag : A),
      LeanPhy.Quantum.commutator a adag = 1 →
      LeanPhy.Quantum.commutator (LeanPhy.FieldTheory.number adag a) adag = adag)
    ccr_number_claim

def ccrLoweringChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "number lowering" "[N, a] = -a under CCR"
    "LeanPhy.FieldTheory.CCR" ["CCR", "finite operators", "scalar field"]
    (P := ∀ {A : Type} [Ring A] (a adag : A),
      LeanPhy.Quantum.commutator a adag = 1 →
      LeanPhy.Quantum.commutator (LeanPhy.FieldTheory.number adag a) a = -a)
    ccr_number_lowering_claim

def finiteStepBoundsChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "maximum principle"
    "positive row-stochastic steps preserve pointwise bounds"
    "LeanPhy.Mathematics.FiniteParabolic"
    ["finite mesh", "positive step"]
    (P := ∀ {ι : Type} [Fintype ι]
      (K : LeanPhy.Mathematics.FinitePositiveStep ι)
      (u : ι → ℝ) (lower upper : ℝ),
      (∀ j, lower ≤ u j) → (∀ j, u j ≤ upper) →
      ∀ i, lower ≤ K.step u i ∧ K.step u i ≤ upper)
    finite_step_bounds_claim

def finiteMassChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "mass conservation"
    "a column-sum certificate preserves the finite total"
    "LeanPhy.Mathematics.FiniteParabolic"
    ["finite mesh", "conservation"]
    (P := ∀ {ι : Type} [Fintype ι]
      (K : LeanPhy.Mathematics.FinitePositiveStep ι)
      (_C : LeanPhy.Mathematics.FinitePositiveStep.MassConservationCertificate K)
      (u : ι → ℝ), ∑ i, K.step u i = ∑ i, u i)
    finite_mass_preservation_claim

def finiteEnergyChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "finite energy propagation"
    "one-step energy bounds propagate to every finite iterate"
    "LeanPhy.Mathematics.FiniteEnergy"
    ["finite mesh", "energy estimate"]
    (P := ∀ {X : Type} (S : LeanPhy.Mathematics.FiniteEnergyStep X)
      (n : ℕ) (x : X),
      S.energy (S.iterate n x) ≤ S.factor ^ n * S.energy x)
    finite_energy_bound_claim

def finitePartitionChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "positive partition"
    "a nonempty finite real-action model has positive partition"
    "LeanPhy.Mathematics.FinitePathReflection"
    ["finite configuration space", "positive weights"]
    (P := ∀ {ι : Type} [Fintype ι] [Nonempty ι] (S : ι → ℝ),
      0 < (LeanPhy.Mathematics.FinitePositivePathIntegral.fromRealAction S).toComplex.partition.re)
    finite_positive_partition_claim

def finiteGramChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "Gram positivity"
    "a finite weighted Gram kernel is positive"
    "LeanPhy.Mathematics.FinitePathReflection"
    ["finite configuration space", "Gram factorisation"]
    (P := ∀ {ι α : Type} [Fintype ι] [Fintype α]
      (G : LeanPhy.Mathematics.FiniteWeightedGramKernel ι α)
      (f : ι → ℝ), 0 ≤ G.kernelQuadratic f)
    finite_gram_positivity_claim

def finiteReflectionChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "reflection positivity"
    "an involutive reflected Gram kernel is nonnegative"
    "LeanPhy.Mathematics.FinitePathReflection"
    ["finite configuration space", "reflection", "Gram factorisation"]
    (P := ∀ {ι α : Type} [Fintype ι] [Fintype α]
      (C : LeanPhy.Mathematics.FiniteWeightedReflectionCertificate ι α)
      (f : ι → ℝ), 0 ≤ C.reflectedKernelQuadratic f)
    finite_reflection_positivity_claim

def classicalSymplecticChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "symplectic composition"
    "the product of two finite canonical transformations preserves the symplectic form"
    "LeanPhy.Classical.Symplectic"
    ["finite phase space", "canonical form"]
    (P := ∀ (A B : LeanPhy.Classical.M2R),
      Aᵀ * LeanPhy.Classical.symplecticJ * A = LeanPhy.Classical.symplecticJ →
      Bᵀ * LeanPhy.Classical.symplecticJ * B = LeanPhy.Classical.symplecticJ →
      (A * B)ᵀ * LeanPhy.Classical.symplecticJ * (A * B) =
        LeanPhy.Classical.symplecticJ)
    LeanPhy.Classical.symplectic_mul

def gaugeFieldStrengthChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "gauge curvature antisymmetry"
    "the finite algebraic field strength is antisymmetric in its directions"
    "LeanPhy.GaugeTheory.FieldStrength"
    ["covariant derivatives", "finite directions"]
    (P := ∀ {A : Type} [Ring A] (D : Fin 4 → A) (mu nu : Fin 4),
      LeanPhy.GaugeTheory.fieldStrength D mu nu =
        -LeanPhy.GaugeTheory.fieldStrength D nu mu)
    LeanPhy.GaugeTheory.fieldStrength_antisym

def condensedBdGChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "BdG quadratic identity"
    "the legacy complex-symmetric block squares to (ε² + Δ²) times the identity; Hermiticity is not inferred"
    "LeanPhy.Condensed.BCS"
    ["finite block", "parameters"]
    (P := ∀ (eps Delta : ℂ),
      LeanPhy.Condensed.bdg eps Delta * LeanPhy.Condensed.bdg eps Delta =
        (eps ^ 2 + Delta ^ 2) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ))
    LeanPhy.Condensed.bdg_sq

def relativityMetricChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "Minkowski signature"
    "the finite (+---) metric has the declared diagonal signature"
    "LeanPhy.Relativity.Minkowski"
    ["signature", "integer witness"]
    LeanPhy.Relativity.metric_diagonal

def gibbsPartitionChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "finite Gibbs partition"
    "a nonempty finite Gibbs partition function is strictly positive"
    "LeanPhy.StatMech.FiniteGibbs"
    ["finite state space", "Boltzmann weight"]
    (P := ∀ {ι : Type} [Fintype ι] [Nonempty ι] (β : ℝ) (E : ι → ℝ),
      0 < LeanPhy.StatMech.finitePartitionFunction β E)
    LeanPhy.StatMech.finitePartitionFunction_pos

def multiWickFourChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "four-point Wick contraction"
    "the finite four-point Gaussian moment is the sum of its three pairings"
    "LeanPhy.FieldTheory.MultiWick"
    ["finite field labels", "commutative coefficient algebra"]
    (P := ∀ (C : Fin 4 → Fin 4 → ℂ),
      LeanPhy.FieldTheory.MultiWick.gaussianMoment C [0, 1, 2, 3] =
        C 0 1 * C 2 3 + C 0 2 * C 1 3 + C 0 3 * C 1 2)
    LeanPhy.FieldTheory.MultiWick.gaussianMoment_four

def gammaCliffordChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "Dirac Clifford anticommutation"
    "γ⁰γ¹ + γ¹γ⁰ = 0 in the explicit 4 × 4 representation"
    "LeanPhy.HighEnergy.Gamma"
    ["finite spinor representation", "metric convention"]
    LeanPhy.HighEnergy.gamma0_anticommutes_gamma1

theorem finite_eft_truncation_claim
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : LeanPhy.HighEnergy.ExpansionParameter)
    (T : LeanPhy.HighEnergy.FiniteEFT ι) (S : Finset ι) (cutoff : ℕ)
    (horder : ∀ i ∈ Finset.univ \ S, cutoff ≤ T.order i) :
    LeanPhy.Mathematics.ErrorCertificate (T.amplitude E)
      (T.retainedAmplitude E S)
      (((Finset.univ \ S).card : ℝ) * T.coefficientBound * E.value ^ cutoff) :=
  T.truncation_error_certificate E S cutoff horder

def finiteEftTruncationChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "finite EFT truncation error"
    "the omitted finite operator tail is bounded by its cardinality, coefficient bound, and cutoff power"
    "LeanPhy.HighEnergy.EffectiveTheory"
    ["finite operator basis", "expansion parameter hierarchy", "coefficient bound"]
    (P := ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (E : LeanPhy.HighEnergy.ExpansionParameter)
      (T : LeanPhy.HighEnergy.FiniteEFT ι) (S : Finset ι) (cutoff : ℕ)
      (horder : ∀ i ∈ Finset.univ \ S, cutoff ≤ T.order i),
      LeanPhy.Mathematics.ErrorCertificate (T.amplitude E)
        (T.retainedAmplitude E S)
        (((Finset.univ \ S).card : ℝ) * T.coefficientBound * E.value ^ cutoff))
    finite_eft_truncation_claim

theorem finite_eft_matching_claim
    {ι : Type} [Fintype ι]
    (M : LeanPhy.HighEnergy.FiniteEFT.MatchingCertificate ι)
    (weights : ι → ℝ) (S : Finset ι) (weightBound : ℝ)
    (weightBound_nonneg : 0 ≤ weightBound)
    (weight_abs_le : ∀ i ∈ S, |weights i| ≤ weightBound) :
    LeanPhy.Mathematics.ErrorCertificate
      (LeanPhy.HighEnergy.FiniteEFT.MatchingCertificate.observable
        M.uvCoefficient weights S)
      (LeanPhy.HighEnergy.FiniteEFT.MatchingCertificate.observable
        M.irCoefficient weights S)
      ((S.card : ℝ) * weightBound * M.uniformError) :=
  M.error_certificate weights S weightBound weightBound_nonneg weight_abs_le

def finiteEftMatchingChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "finite EFT matching error"
    "a uniform coefficient-matching error yields an observable error budget for every bounded finite weighting"
    "LeanPhy.HighEnergy.EffectiveTheory"
    ["finite operator basis", "matching certificate", "observable weight bound"]
    (P := ∀ {ι : Type} [Fintype ι]
      (M : LeanPhy.HighEnergy.FiniteEFT.MatchingCertificate ι)
      (weights : ι → ℝ) (S : Finset ι) (weightBound : ℝ),
      0 ≤ weightBound →
      (∀ i ∈ S, |weights i| ≤ weightBound) →
      LeanPhy.Mathematics.ErrorCertificate
        (LeanPhy.HighEnergy.FiniteEFT.MatchingCertificate.observable
          M.uvCoefficient weights S)
        (LeanPhy.HighEnergy.FiniteEFT.MatchingCertificate.observable
          M.irCoefficient weights S)
        ((S.card : ℝ) * weightBound * M.uniformError))
    finite_eft_matching_claim

theorem bounded_unitary_norm_claim
    {𝕜 E : Type} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (U : LeanPhy.Mathematics.Hilbert.Unitary (𝕜 := 𝕜) (E := E)) (x : E) :
    ‖U.op x‖ = ‖x‖ := U.norm_preserved x

def boundedUnitaryNormChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "bounded unitary norm"
    "a bounded unitary preserves the Hilbert-space norm"
    "LeanPhy.Mathematics.Hilbert"
    ["complete inner-product space", "bounded unitary"]
    (P := ∀ {𝕜 E : Type} [RCLike 𝕜] [NormedAddCommGroup E]
      [InnerProductSpace 𝕜 E] [CompleteSpace E]
      (U : LeanPhy.Mathematics.Hilbert.Unitary (𝕜 := 𝕜) (E := E)) (x : E),
      ‖U.op x‖ = ‖x‖)
    bounded_unitary_norm_claim

theorem polynomial_spectral_mapping_claim {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Nontrivial E] (A : E →L[ℂ] E) (p : Polynomial ℂ) :
    spectrum ℂ (aeval A p) = (fun z => p.eval z) '' spectrum ℂ A :=
  LeanPhy.Mathematics.polynomial_spectrum_map A p

def polynomialSpectralMappingChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "polynomial spectral mapping"
    "the spectrum of a bounded complex operator polynomial is the polynomial image of the spectrum"
    "LeanPhy.Mathematics.SpectralCalculus"
    ["complete inner-product space", "bounded complex operator"]
    (P := ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
      [CompleteSpace E] [Nontrivial E] (A : E →L[ℂ] E) (p : Polynomial ℂ),
      spectrum ℂ (aeval A p) = (fun z => p.eval z) '' spectrum ℂ A)
    polynomial_spectral_mapping_claim

theorem spectral_gap_iterate_claim {𝕜 E : Type} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (T P : E →L[𝕜] E) (rho : ℝ)
    (h : LeanPhy.Mathematics.SpectralGapCertificate T P rho)
    (n : ℕ) (x : E) :
    ‖(T ^ n) x - P x‖ ≤ rho ^ n * ‖x - P x‖ :=
  h.iterate_decay n x

def spectralGapIterateChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "spectral-gap iterate decay"
    "an explicit invariant projection and one-step residual contraction give a geometric bound for every iterate"
    "LeanPhy.Mathematics.SpectralGap"
    ["complete inner-product space", "bounded spectral gap"]
    (P := ∀ {𝕜 E : Type} [RCLike 𝕜] [NormedAddCommGroup E]
      [NormedSpace 𝕜 E] [CompleteSpace E]
      (T P : E →L[𝕜] E) (rho : ℝ)
      (h : LeanPhy.Mathematics.SpectralGapCertificate T P rho)
      (n : ℕ) (x : E),
      ‖(T ^ n) x - P x‖ ≤ rho ^ n * ‖x - P x‖)
    spectral_gap_iterate_claim

theorem finite_fluid_conservation_claim
    {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V]
    [AddCommGroup A] (tail head : E → V) (current : E → A) :
    ∑ v, LeanPhy.Mathematics.FiniteDivergence.divergence tail head current v = 0 :=
  LeanPhy.Mathematics.FiniteDivergence.total_divergence_zero tail head current

def fluidConservationChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "closed finite-volume conservation"
    "the total source of a closed finite-volume current vanishes"
    "LeanPhy.Mathematics.FiniteDivergence"
    ["finite mesh", "closed internal edges"]
    (P := ∀ {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V]
      [AddCommGroup A] (tail head : E → V) (current : E → A),
      ∑ v, LeanPhy.Mathematics.FiniteDivergence.divergence tail head current v = 0)
    finite_fluid_conservation_claim

def opticsCanonicalChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "ABCD canonical composition"
    "the product of two paraxial canonical transfer matrices is canonical"
    "LeanPhy.Entry.Optics"
    ["finite paraxial phase space", "canonical optical form"]
    (P := ∀ (A B : LeanPhy.Optics.ABCD),
      LeanPhy.Optics.isCanonical A → LeanPhy.Optics.isCanonical B →
      LeanPhy.Optics.isCanonical (A * B))
    LeanPhy.Optics.compose_isCanonical

def opticsJonesChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "Jones intensity preservation"
    "a finite lossless Jones element preserves the complex inner product"
    "LeanPhy.Entry.Optics"
    ["finite polarisation space", "lossless element"]
    (P := ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (U : LeanPhy.Optics.JonesElement ι) (v w : ι → ℂ),
      dotProduct (star (U.evolve v)) (U.evolve w) =
        dotProduct (star v) w)
    LeanPhy.Optics.jones_preserves_inner

/-! ## Domain adapters

Each adapter is a real package value, so downstream theory files can import
one package and add their own claims with the same `CheckedClaim.ofTheorem`
constructor.  The metadata names exactly which assumptions and limits remain
conditional.
-/

def finiteQuantumModel : ModelRegistration :=
  ModelRegistration.text "finite-pauli" "finite quantum / quantum-information model"
    "finite coupling or gate labels" "finite matrices / density operators"
    "Pauli observables and finite expectations" "matrix multiplication or CPTP step"
    ["finite operators", "scalar field"]

def finiteCCRModel : ModelRegistration :=
  ModelRegistration.text "finite-ccr" "abstract bosonic CCR algebra"
    "mode labels" "an operator ring with a supplied CCR relation"
    "operator polynomials" "creation-annihilation algebra step"
    ["CCR", "finite operators", "scalar field"]

def finitePDEModel : ModelRegistration :=
  ModelRegistration.text "finite-positive-step" "finite PDE / lattice evolution"
    "mesh and time-step labels" "finite-index scalar fields"
    "pointwise fields and finite sums" "positive row-stochastic update"
    ["finite mesh", "positive step"]

def finiteEnergyModel : ModelRegistration :=
  ModelRegistration.text "finite-energy-step" "finite stable evolution"
    "time-step and truncation labels" "finite or truncated state"
    "energy and residual observables" "certified one-step evolution"
    ["finite mesh", "energy estimate"]

def finiteEuclideanModel : ModelRegistration :=
  ModelRegistration.text "finite-euclidean" "finite Euclidean / lattice path model"
    "finite configuration labels" "finite configurations"
    "correlators and reflected observables" "finite weighted sum"
    ["finite configuration space", "positive weights", "reflection"]

def finiteClassicalModel : ModelRegistration :=
  ModelRegistration.text "finite-symplectic" "finite classical mechanics"
    "finite matrix parameters" "finite phase-space vectors"
    "quadratic forms and symplectic observables" "matrix composition"
    ["finite phase space", "canonical form"]

def finiteGaugeModel : ModelRegistration :=
  ModelRegistration.text "finite-gauge" "finite gauge curvature algebra"
    "finite direction labels" "abstract covariant-derivative algebra"
    "curvature components" "commutator difference"
    ["covariant derivatives", "finite directions"]

def finiteCondensedModel : ModelRegistration :=
  ModelRegistration.text "finite-bdg" "finite condensed-matter block"
    "momentum or coupling labels" "finite BdG matrices"
    "band, gap and quadratic observables" "finite matrix block update"
    ["finite block", "parameters"]

def finiteRelativityModel : ModelRegistration :=
  ModelRegistration.text "finite-lorentz" "finite relativity convention model"
    "finite component labels" "finite component vectors"
    "metric contractions" "finite Lorentz matrix action"
    ["signature", "integer witness"]

def finiteStatMechModel : ModelRegistration :=
  ModelRegistration.text "finite-gibbs" "finite Gibbs / Markov model"
    "temperature and finite state labels" "finite probability vectors"
    "partition functions and expectations" "finite kernel transition"
    ["finite state space", "Boltzmann weight"]

def finiteCliffordModel : ModelRegistration :=
  ModelRegistration.text "finite-clifford" "finite high-energy Clifford model"
    "finite representation labels" "finite spinor vectors and matrices"
    "Dirac bilinears and traces" "gamma-matrix multiplication"
    ["finite spinor representation", "metric convention"]

def finiteEFTModel : ModelRegistration :=
  ModelRegistration.text "finite-eft" "finite effective-theory expansion model"
    "finite operator labels and a dimensionless expansion parameter"
    "finite real coefficient vectors"
    "truncated amplitudes and matching observables" "power counting and finite weighted sums"
    ["finite operator basis", "expansion parameter hierarchy", "coefficient bound",
      "matching certificate", "observable weight bound"]

def boundedHilbertModel : ModelRegistration :=
  ModelRegistration.text "bounded-hilbert" "bounded Hilbert/numerical bridge"
    "operator and discretisation labels" "complete inner-product space"
    "norms and residual observables" "bounded linear operator action"
    ["complete inner-product space", "bounded unitary"]

def finiteOpticsModel : ModelRegistration :=
  ModelRegistration.text "finite-optics" "finite paraxial and polarisation optics"
    "ray, focal-length and polarisation labels" "2 × 2 transfer matrices / finite Jones vectors"
    "ray coordinates and polarisation inner products" "ABCD composition or Jones action"
    ["finite paraxial phase space", "finite polarisation space"]

def finiteFluidModel : ModelRegistration :=
  ModelRegistration.text "finite-fluid" "finite-volume fluid / plasma transport"
    "finite mesh and edge labels" "finite cell fields and currents"
    "mass, charge and vorticity residuals" "incidence divergence or discrete exterior derivative"
    ["finite mesh", "closed internal edges"]

def QuantumTheoryPackage : TheoryPackage where
  name := "finite quantum algebra"
  domain := "quantum mechanics / quantum information"
  assumptions := [
    { name := "CCR", statement := "[a, a†] = 1 is supplied for the abstract algebra", source := "research model" },
    { name := "finite operators", statement := "operator identities are checked in an abstract ring or finite matrix model", source := "kernel boundary" },
    { name := "scalar field", statement := "ℂ and order properties are used through imported algebraic structures", source := "mathlib" }
  ]
  claims := [
    (CheckedClaim.ofTheoremFromWithAssumptions "Pauli product" "σx σy = i σz"
      "LeanPhy.Quantum.Pauli" ["finite operators", "scalar field"]
      LeanPhy.Quantum.pauliX_pauliY).withModels ["finite-pauli"],
    (CheckedClaim.ofTheoremFromWithAssumptions "Pauli commutator" "[σx, σy] = 2 i σz"
      "LeanPhy.Quantum.Pauli" ["finite operators", "scalar field"]
      LeanPhy.Quantum.pauliXY_commutator).withModels ["finite-pauli"],
    ccrRaisingChecked.withModels ["finite-ccr"],
    ccrLoweringChecked.withModels ["finite-ccr"]
  ]
  models := [finiteQuantumModel, finiteCCRModel]
  outOfScope := [
    { label := "unbounded operators", explanation := "domains, self-adjoint extensions and spectral theorems require a separate analytic layer" },
    { label := "continuum limits", explanation := "infinite-dimensional Hilbert spaces and continuous spectra are not inferred" },
    { label := "measurement statistics", explanation := "physical interpretation still requires explicit state and probability assumptions" }
  ]
  obligations := [
    { name := "operator-domain analysis", statement := "provide domains and self-adjointness before claiming an unbounded-operator result", source := "external analysis / Physlib" }
  ]

def FinitePDETheoryPackage : TheoryPackage where
  name := "finite evolution and PDE certificates"
  domain := "finite-difference / finite-element / lattice PDE"
  assumptions := [
    { name := "finite mesh", statement := "the index type is finite and all sums are finite", source := "model declaration" },
    { name := "positive step", statement := "the update kernel is nonnegative and row stochastic", source := "scheme certificate" },
    { name := "conservation", statement := "mass conservation uses a separately supplied column-sum certificate", source := "model declaration" },
    { name := "energy estimate", statement := "one-step energy amplification is supplied explicitly", source := "stability certificate" }
  ]
  claims := [
    finiteStepBoundsChecked.withModels ["finite-positive-step"],
    finiteMassChecked.withModels ["finite-positive-step"],
    finiteEnergyChecked.withModels ["finite-energy-step"]
  ]
  models := [finitePDEModel, finiteEnergyModel]
  outOfScope := [
    { label := "CFL and mesh convergence", explanation := "stability and convergence of a continuum discretisation must be proved by an external numerical-analysis development" },
    { label := "continuum well-posedness", explanation := "Sobolev estimates, boundary regularity and infinite-dimensional existence are outside this package" },
    { label := "model adequacy", explanation := "the package checks the supplied scheme, not whether it models a physical system" }
  ]
  obligations := [
    { name := "scheme convergence", statement := "supply a CFL/stability and mesh-convergence theorem for the chosen discretisation", source := "external numerical analysis" }
  ]

def FiniteEuclideanTheoryPackage : TheoryPackage where
  name := "finite Euclidean path and reflection certificates"
  domain := "lattice field theory / finite statistical mechanics"
  assumptions := [
    { name := "finite configuration space", statement := "the path/configuration type is finite", source := "model declaration" },
    { name := "positive weights", statement := "real-action weights are nonnegative with a positive finite partition", source := "measure certificate" },
    { name := "reflection", statement := "the reflection is an explicit involutive permutation", source := "model declaration" },
    { name := "Gram factorisation", statement := "the correlator kernel is given by a finite weighted feature factorisation", source := "positivity certificate" }
  ]
  claims := [
    finitePartitionChecked.withModels ["finite-euclidean"],
    finiteGramChecked.withModels ["finite-euclidean"],
    finiteReflectionChecked.withModels ["finite-euclidean"]
  ]
  models := [finiteEuclideanModel]
  outOfScope := [
    { label := "continuum measure", explanation := "measure existence and Osterwalder–Schrader reconstruction are not inferred" },
    { label := "oscillatory path integrals", explanation := "complex cancellation requires an explicit nonzero partition certificate" },
    { label := "renormalisation", explanation := "continuum limits, universality and counterterms need a separate analytic layer" }
  ]
  obligations := [
    { name := "OS reconstruction", statement := "connect the finite reflection certificate to a continuum measure and reconstruction theorem", source := "external constructive QFT" }
  ]

def ClassicalMechanicsTheoryPackage : TheoryPackage where
  name := "finite classical mechanics"
  domain := "Hamiltonian mechanics / symplectic linear algebra"
  assumptions := [
    { name := "finite phase space", statement := "phase-space maps are represented by 2 × 2 real matrices", source := "model declaration" },
    { name := "canonical form", statement := "the symplectic matrix is the declared dq ∧ dp form", source := "convention" }
  ]
  claims := [classicalSymplecticChecked.withModels ["finite-symplectic"]]
  models := [finiteClassicalModel]
  outOfScope := [
    { label := "nonlinear flows", explanation := "generating functions, ODE existence and nonlinear symplectic geometry remain external" },
    { label := "continuum phase space", explanation := "the package checks finite matrices, not smooth manifolds" }
  ]
  obligations := [
    { name := "flow existence", statement := "prove existence and regularity of the intended nonlinear Hamiltonian flow", source := "external ODE / symplectic geometry" }
  ]

def GaugeTheoryPackage : TheoryPackage where
  name := "finite gauge curvature algebra"
  domain := "Yang–Mills / lattice gauge algebra"
  assumptions := [
    { name := "covariant derivatives", statement := "directions are elements of an abstract ring", source := "algebraic model" },
    { name := "finite directions", statement := "the displayed curvature uses four finite direction labels", source := "model declaration" }
  ]
  claims := [gaugeFieldStrengthChecked.withModels ["finite-gauge"]]
  models := [finiteGaugeModel]
  outOfScope := [
    { label := "gauge group geometry", explanation := "principal bundles, global gauge fixing and path-integral measures are external" },
    { label := "field equations", explanation := "Yang–Mills dynamics and boundary conditions require additional certificates" }
  ]
  obligations := [
    { name := "gauge dynamics", statement := "connect the algebraic curvature identity to a well-posed gauge-field model and boundary problem", source := "external gauge geometry / PDE" }
  ]

def CondensedMatterTheoryPackage : TheoryPackage where
  name := "finite condensed-matter blocks"
  domain := "BdG / superconductivity / finite band algebra"
  assumptions := [
    { name := "finite block", statement := "the BdG Hamiltonian is a 2 × 2 complex block", source := "model declaration" },
    { name := "parameters", statement := "ε and Δ are model parameters in the coefficient field", source := "research model" }
  ]
  claims := [condensedBdGChecked.withModels ["finite-bdg"]]
  models := [finiteCondensedModel]
  outOfScope := [
    { label := "thermodynamic limit", explanation := "gap closing, phase transitions and infinite lattice limits are external" },
    { label := "self-consistency", explanation := "gap equations and microscopic derivations need explicit additional inputs" }
  ]
  obligations := [
    { name := "band-limit passage", statement := "provide the finite-volume or momentum-mesh convergence argument for the claimed phase", source := "external condensed-matter analysis" }
  ]

def RelativityTheoryPackage : TheoryPackage where
  name := "finite relativity conventions"
  domain := "special relativity / Lorentz algebra"
  assumptions := [
    { name := "signature", statement := "the metric convention is (+---)", source := "model convention" },
    { name := "integer witness", statement := "the smoke layer uses a finite integer component model", source := "regression model" }
  ]
  claims := [relativityMetricChecked.withModels ["finite-lorentz"]]
  models := [finiteRelativityModel]
  outOfScope := [
    { label := "spacetime analysis", explanation := "smooth manifolds, causal PDE and general relativity are not inferred" },
    { label := "physical units", explanation := "component identities do not establish experimental calibration" }
  ]
  obligations := [
    { name := "geometric lift", statement := "supply the manifold and causal-analytic hypotheses when lifting the component identity", source := "external differential geometry" }
  ]

def StatisticalMechanicsTheoryPackage : TheoryPackage where
  name := "finite statistical mechanics"
  domain := "Gibbs ensembles / finite Markov models"
  assumptions := [
    { name := "finite state space", statement := "the configuration type is finite and nonempty", source := "model declaration" },
    { name := "Boltzmann weight", statement := "weights use the real exponential of a finite energy", source := "ensemble definition" }
  ]
  claims := [gibbsPartitionChecked.withModels ["finite-gibbs"]]
  models := [finiteStatMechModel]
  outOfScope := [
    { label := "thermodynamic limit", explanation := "phase transitions, free-energy limits and ensemble equivalence are external" },
    { label := "mixing", explanation := "irreducibility and Markov mixing rates require separate certificates" }
  ]
  obligations := [
    { name := "equilibrium limit", statement := "prove irreducibility, mixing or thermodynamic-limit estimates for the intended ensemble", source := "external probability / statistical mechanics" }
  ]

def FieldTheoryPackage : TheoryPackage where
  name := "finite field-theory algebra"
  domain := "CCR/CAR algebra / finite Wick contraction kernels"
  assumptions := [
    { name := "finite field labels", statement := "all displayed fields and contractions use a finite index type", source := "model declaration" },
    { name := "commutative coefficient algebra", statement := "the covariance coefficients form a commutative semiring for the finite Wick normaliser", source := "algebraic model" },
    { name := "CCR", statement := "the creation and annihilation symbols satisfy the supplied canonical commutation relation", source := "research model" },
    { name := "finite operators", statement := "the operator ring satisfies the supplied relations; no exact CCR for a finite bosonic truncation is inferred", source := "kernel boundary" },
    { name := "scalar field", statement := "the coefficient ring supplies the required additive and multiplicative laws", source := "mathlib" }
  ]
  claims := [multiWickFourChecked.withModels ["finite-ccr"],
    ccrRaisingChecked.withModels ["finite-ccr"],
    ccrLoweringChecked.withModels ["finite-ccr"]]
  models := [finiteCCRModel]
  outOfScope := [
    { label := "operator domains", explanation := "unbounded creation and annihilation operators require domain and closure theorems" },
    { label := "continuum distributions", explanation := "delta distributions, time ordering and infinite-volume limits are not inferred" },
    { label := "renormalisation", explanation := "counterterms and regulator independence remain external obligations" }
  ]
  obligations := [
    { name := "continuum Wick bridge", statement := "connect the finite contraction normaliser to the chosen continuum distributional theorem", source := "external constructive QFT / analysis" }
  ]

def HighEnergyTheoryPackage : TheoryPackage where
  name := "finite high-energy algebra"
  domain := "Dirac/Clifford matrices / spinor identities / finite EFT power counting"
  assumptions := [
    { name := "finite spinor representation", statement := "spinors are represented by explicit 4-component complex vectors and matrices", source := "model declaration" },
    { name := "metric convention", statement := "the gamma-matrix signs encode the declared (+---) convention", source := "physics convention" },
    { name := "finite operator basis", statement := "the EFT coefficient basis and every omitted sector are finite index sets", source := "model declaration" },
    { name := "expansion parameter hierarchy", statement := "the dimensionless expansion parameter lies in [0,1] and omitted terms have the declared cutoff order", source := "power-counting hypothesis" },
    { name := "coefficient bound", statement := "Wilson coefficients have the supplied uniform absolute bound", source := "matching or model certificate" },
    { name := "matching certificate", statement := "UV and IR coefficients have the supplied uniform difference bound", source := "matching calculation" },
    { name := "observable weight bound", statement := "the finite observable weights have the supplied absolute bound", source := "observable definition" }
  ]
  claims := [gammaCliffordChecked.withModels ["finite-clifford"],
    finiteEftTruncationChecked.withModels ["finite-eft"],
    finiteEftMatchingChecked.withModels ["finite-eft"]]
  models := [finiteCliffordModel, finiteEFTModel]
  outOfScope := [
    { label := "scattering analysis", explanation := "asymptotic states, distributions and cross-section limits are not inferred" },
    { label := "gauge dynamics", explanation := "renormalisation and non-perturbative dynamics require separate inputs" },
    { label := "continuum EFT", explanation := "the finite bounds do not establish existence of a UV completion, continuum limit, or regulator-independent matching" }
  ]
  obligations := [
    { name := "spinor-to-field bridge", statement := "supply the analytic and representation-theoretic hypotheses connecting finite matrices to the target field theory", source := "external QFT analysis" },
    { name := "EFT continuum bridge", statement := "supply the model-specific operator basis, matching derivation, and regulator or continuum estimates before interpreting the finite error budget physically", source := "external EFT analysis" }
  ]

def AnalysisBridgeTheoryPackage : TheoryPackage where
  name := "bounded analysis and numerical bridges"
  domain := "bounded Hilbert operators / residual and approximation certificates"
  assumptions := [
    { name := "complete inner-product space", statement := "the operator acts on a complete normed inner-product space", source := "mathlib typeclasses" },
    { name := "bounded complex operator", statement := "the spectral expression is a bounded continuous complex-linear operator", source := "spectral calculus certificate" },
    { name := "bounded spectral gap", statement := "an invariant projection and a strict one-step residual contraction are supplied", source := "spectral gap certificate" },
    { name := "bounded unitary", statement := "both adjoint-sided inverse equations are supplied", source := "model certificate" },
    { name := "finite mesh", statement := "finite evolution claims use a finite or truncated state index", source := "model declaration" },
    { name := "energy estimate", statement := "the one-step energy amplification inequality is supplied", source := "stability certificate" }
  ]
  claims := [boundedUnitaryNormChecked.withModels ["bounded-hilbert"],
    polynomialSpectralMappingChecked.withModels ["bounded-hilbert"],
    spectralGapIterateChecked.withModels ["bounded-hilbert"],
    finiteEnergyChecked.withModels ["finite-energy-step"]]
  models := [boundedHilbertModel, finiteEnergyModel]
  outOfScope := [
    { label := "unbounded operators", explanation := "domains, self-adjoint extensions and spectral measures are not inferred" },
    { label := "convergence", explanation := "mesh, truncation and continuum convergence require explicit approximation certificates" },
    { label := "well-posedness", explanation := "PDE existence and semigroup generation remain external" }
  ]
  obligations := [
    { name := "analytic completion", statement := "supply the continuity, domain and convergence arguments needed by the target research theorem", source := "external analysis / numerical analysis" }
  ]

def OpticsTheoryPackage : TheoryPackage where
  name := "finite optics and AMO"
  domain := "paraxial optics / polarisation / finite AMO control"
  assumptions := [
    { name := "finite paraxial phase space", statement := "ray transfer matrices use a two-component finite phase space", source := "optical model" },
    { name := "canonical optical form", statement := "lossless paraxial elements preserve the declared symplectic form", source := "ABCD certificate" },
    { name := "finite polarisation space", statement := "Jones vectors use a finite index type", source := "polarisation model" },
    { name := "lossless element", statement := "a Jones element supplies a finite unitary certificate", source := "optical model" }
  ]
  claims := [
    opticsCanonicalChecked.withModels ["finite-optics"],
    opticsJonesChecked.withModels ["finite-optics"]
  ]
  models := [finiteOpticsModel]
  outOfScope := [
    { label := "Maxwell boundary problem", explanation := "continuous electromagnetic boundary conditions and dispersion require an analytic field theory" },
    { label := "diffraction and Fourier limits", explanation := "integral transforms, apertures and propagation limits are not inferred" },
    { label := "atomic calibration", explanation := "the finite unitary certificate does not establish experimental calibration" }
  ]
  obligations := [
    { name := "optical continuum bridge", statement := "connect the finite ABCD/Jones model to the intended Maxwell or atomic Hamiltonian calculation", source := "external optics / AMO analysis" }
  ]

def FluidTheoryPackage : TheoryPackage where
  name := "finite fluid and plasma transport"
  domain := "finite-volume fluids / plasma currents / discrete vorticity"
  assumptions := [
    { name := "finite mesh", statement := "the cell and edge types are finite", source := "discretisation declaration" },
    { name := "closed internal edges", statement := "every edge is internal, so boundary fluxes are included explicitly or absent", source := "finite-volume model" },
    { name := "discrete derivatives", statement := "vorticity uses commuting finite/discrete derivations when invoked", source := "discrete differential model" }
  ]
  claims := [fluidConservationChecked.withModels ["finite-fluid"]]
  models := [finiteFluidModel]
  outOfScope := [
    { label := "continuum Navier--Stokes", explanation := "existence, regularity, turbulence closure and continuum limits require external analysis" },
    { label := "kinetic closure", explanation := "Vlasov, gyrokinetic and collision operators need separately certified approximations" },
    { label := "physical boundary modelling", explanation := "wall, sheath and open-boundary fluxes must be represented by explicit certificates" }
  ]
  obligations := [
    { name := "fluid continuum bridge", statement := "provide stability, consistency and convergence certificates for the selected finite-volume or plasma discretisation", source := "external fluid / numerical analysis" }
  ]

def defaultPackages : List TheoryPackage :=
  [QuantumTheoryPackage, FinitePDETheoryPackage, FiniteEuclideanTheoryPackage,
    ClassicalMechanicsTheoryPackage, GaugeTheoryPackage,
    CondensedMatterTheoryPackage, RelativityTheoryPackage,
    StatisticalMechanicsTheoryPackage]

def defaultProject : ResearchProject :=
  ResearchProject.ofPackages "LeanPhy default domains" defaultPackages

def extendedPackages : List TheoryPackage :=
  defaultPackages ++ [FieldTheoryPackage, HighEnergyTheoryPackage,
    AnalysisBridgeTheoryPackage]

def extendedProject : ResearchProject :=
  ResearchProject.ofPackages "LeanPhy extended domains" extendedPackages

def broadPackages : List TheoryPackage :=
  extendedPackages ++ [OpticsTheoryPackage, FluidTheoryPackage]

def broadProject : ResearchProject :=
  ResearchProject.ofPackages "LeanPhy broad applied domains" broadPackages

def defaultManifest : ResearchManifest :=
  (ResearchManifest.ofProject "LeanPhy default reproducibility manifest"
    defaultProject).withProfiles [
      "LeanPhy.Entry.Research", "LeanPhy.Entry.Quantum",
      "LeanPhy.Entry.FinitePDE", "LeanPhy.Entry.StatMech",
      "LeanPhy.Entry.Gauge", "LeanPhy.Entry.Condensed",
      "LeanPhy.Entry.Classical", "LeanPhy.Entry.Relativity"]
    |>.withSources ["LeanPhy.Workflow", "lakefile.toml", "lean-toolchain"]
    |>.withExternalTools ["Lean kernel", "mathlib", "lake"]

def extendedManifest : ResearchManifest :=
  (ResearchManifest.ofProject "LeanPhy extended reproducibility manifest"
    extendedProject).withProfiles [
      "LeanPhy.Entry.Research", "LeanPhy.Entry.Quantum",
      "LeanPhy.Entry.FieldTheory", "LeanPhy.Entry.HighEnergy",
      "LeanPhy.Entry.Analysis", "LeanPhy.Entry.FinitePDE",
      "LeanPhy.Entry.StatMech", "LeanPhy.Entry.Gauge",
      "LeanPhy.Entry.Condensed", "LeanPhy.Entry.Classical",
      "LeanPhy.Entry.Relativity"]
    |>.withSources ["LeanPhy.Workflow", "lakefile.toml", "lean-toolchain"]
    |>.withExternalTools ["Lean kernel", "mathlib", "lake"]

def broadManifest : ResearchManifest :=
  (ResearchManifest.ofProject "LeanPhy broad reproducibility manifest"
    broadProject).withProfiles [
      "LeanPhy.Entry.Research", "LeanPhy.Entry.Quantum",
      "LeanPhy.Entry.FieldTheory", "LeanPhy.Entry.HighEnergy",
      "LeanPhy.Entry.Analysis", "LeanPhy.Entry.FinitePDE",
      "LeanPhy.Entry.StatMech", "LeanPhy.Entry.Gauge",
      "LeanPhy.Entry.Condensed", "LeanPhy.Entry.Classical",
      "LeanPhy.Entry.Relativity", "LeanPhy.Entry.Optics",
      "LeanPhy.Entry.Fluid"]
    |>.withSources ["LeanPhy.Workflow", "lakefile.toml", "lean-toolchain"]
    |>.withExternalTools ["Lean kernel", "mathlib", "lake"]

end LeanPhy.Workflow
