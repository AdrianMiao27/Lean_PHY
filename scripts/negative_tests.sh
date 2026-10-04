#!/usr/bin/env bash
set -euo pipefail

# These files must fail during elaboration.  The tests protect the main safety
# promise of the physics-facing layer: dimensional and variance mistakes are
# rejected before an invalid proof can be attempted.  They are kept outside
# the source tree so the normal proof-hole scanner never treats an intentional
# failure as library code.
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD_ROOT="${LEANPHY_BUILD_ROOT:-${PROJECT_ROOT}}"
if [[ ! -f "${BUILD_ROOT}/lakefile.toml" ]]; then
  BUILD_ROOT="${PROJECT_ROOT}"
fi
export PATH="/root/.elan/bin:${PATH}"

TMP_ROOT="$(mktemp -d /tmp/leanphy-negative.XXXXXX)"
trap 'rm -rf "${TMP_ROOT}"' EXIT

# Collect independent source files before running them. Lake sets the import
# environment once; each Lean invocation still gets an isolated environment.
expect_failure() {
  local label="$1"
  local source="$2"
  printf '%s\n' "$source" >"${TMP_ROOT}/${label}.lean"
}

expect_failure "dimension_mismatch" 'import LeanPhy
open LeanPhy
example (x : Length) (y : TimeQ) : Length := x + y'

expect_failure "dimension_quotient_mismatch" 'import LeanPhy
open LeanPhy
example (x : Length) (t : TimeQ) : Length := x / t'

expect_failure "integral_certificate_requires_integrability" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
example (μ : MeasureTheory.Measure ℝ) :
    IntegralCertificate μ (fun _ : ℝ => (0 : ℝ)) 0 :=
  { integral_eq := by simp }'

expect_failure "eft_truncation_requires_hierarchy" 'import LeanPhy.Entry.HighEnergy
open LeanPhy.HighEnergy
open LeanPhy.Mathematics
def epsilon : ExpansionParameter :=
  { value := (1 : ℝ) / 10, nonneg := by norm_num, le_one := by norm_num }
def eft : FiniteEFT (Fin 1) :=
  { order := fun _ => 2, coefficient := fun _ => 1,
    coefficientBound := 1, coefficientBound_nonneg := by norm_num,
    coefficient_abs_le := by intro i; simp }
example : ErrorCertificate (eft.amplitude epsilon)
    (eft.retainedAmplitude epsilon (∅ : Finset (Fin 1))) 1 := by
  exact eft.truncation_error_certificate epsilon (∅ : Finset (Fin 1)) 1'

expect_failure "continuous_path_integral_requires_weight_integrability" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
def badPath : ContinuousPathIntegral Unit (MeasureTheory.Measure.dirac ()) :=
  { weight := fun _ => (1 : ℂ), partition := 1,
    partition_eq := by simp, partition_ne_zero := one_ne_zero }'

expect_failure "continuous_path_integral_requires_nonzero_partition" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
def badPath : ContinuousPathIntegral Unit (MeasureTheory.Measure.dirac ()) :=
  { weight := fun _ => (1 : ℂ),
    weight_integrable := by simpa using (MeasureTheory.integrable_const
      (μ := MeasureTheory.Measure.dirac ()) (c := (1 : ℂ))),
    partition := 0, partition_eq := by simp, partition_ne_zero := by simp }'

expect_failure "checked_claim_proof_required" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def missingProof : CheckedClaim :=
  { name := "invalid", statement := "True", proposition := True }'

expect_failure "constrained_dynamics_equivariance_required" 'import LeanPhy.Minimal
open LeanPhy.Mathematics
instance : SMul Unit Nat := ⟨fun _ n => n⟩
instance : MulAction Unit Nat where
  one_smul := by intro n; rfl
  mul_smul := by intro _ _ n; rfl
def system : ConstrainedSymmetry Unit Nat where
  admissible := fun _ => True
  constrained := fun _ => True
  admissible_preserved := by intro _ _ _; trivial
  constrained_preserved := by intro _ _ _; trivial
def missingEquivariance : ConstrainedSymmetry.ConstrainedDynamics system where
  step := id
  preserves_physical := by intro _ _; trivial'

expect_failure "first_class_constraint_closure_required" 'import LeanPhy
open LeanPhy
open LeanPhy.Mathematics
open LeanPhy.Classical
noncomputable def missingFirstClass :
    FirstClassConstraintAlgebra ℝ PhasePolynomial Unit where
  poisson := canonicalPolynomialPoisson
  constraint := fun _ => qPolynomial'

expect_failure "constraint_map_bracket_compatibility_required" 'import LeanPhy
open LeanPhy
open LeanPhy.Mathematics
open LeanPhy.Classical
noncomputable def sourceConstraint :
    FirstClassConstraintAlgebra ℝ PhasePolynomial Unit where
  poisson := canonicalPolynomialPoisson
  constraint := fun _ => qPolynomial
  first_class := by
    intro _ _
    simpa [qPolynomial] using canonical_q_q
noncomputable def missingConstraintMapLaw :
    FirstClassConstraintAlgebra.ConstraintMap sourceConstraint sourceConstraint where
  map := AlgHom.id ℝ PhasePolynomial
  maps_constraint := by
    intro i
    exact sourceConstraint.constraint_mem i'

expect_failure "brst_nilpotency_required" 'import LeanPhy
open LeanPhy
open LeanPhy.Mathematics
noncomputable def missingBRST : BRSTDifferential ℝ PhasePolynomial where
  differential := 0'

expect_failure "equivariant_constraint_zero_fixed_required" 'import LeanPhy.Minimal
open LeanPhy.Mathematics
instance : SMul Unit Nat := ⟨fun _ n => n⟩
instance : MulAction Unit Nat where
  one_smul := by intro n; rfl
  mul_smul := by intro _ _ n; rfl
def missingZeroFixed : EquivariantConstraint Unit Nat Nat where
  value := fun n => n
  equivariant := by intro _ n; rfl'

expect_failure "constrained_observable_invariance_required" 'import LeanPhy.Minimal
open LeanPhy.Mathematics
instance : SMul Unit Nat := ⟨fun _ n => n⟩
instance : MulAction Unit Nat where
  one_smul := by intro n; rfl
  mul_smul := by intro _ _ n; rfl
def system : ConstrainedSymmetry Unit Nat where
  admissible := fun _ => True
  constrained := fun _ => True
  admissible_preserved := by intro _ _ _; trivial
  constrained_preserved := by intro _ _ _; trivial
def missingInvariant : ConstrainedSymmetry.ConstrainedObservable system Nat where
  eval := id'

expect_failure "model_map_dynamics_proof_required" 'import LeanPhy.Minimal
open LeanPhy.Mathematics
def idStep : Process Nat (fun _ => True) where
  toFun := id
  preserves := by intro _ _; trivial
def succStep : Process Nat (fun _ => True) where
  toFun := Nat.succ
  preserves := by intro _ _; trivial
def source : PhysicalModel Nat where
  State := Nat
  valid := fun _ => True
  step := idStep
  Observable := Unit
  evaluate := fun n _ => n
def target : PhysicalModel Nat where
  State := Nat
  valid := fun _ => True
  step := succStep
  Observable := Unit
  evaluate := fun n _ => n
def bad : ModelMap source target where
  state := StateMap.identity Nat (fun _ => True)
  pullback := id
  step_commutes := by intro n _; rfl
  evaluate_commutes := by intro n _ o; rfl'

expect_failure "registered_local_dependency_required" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def detached : CheckedClaim :=
  { name := "detached", statement := "True", source := "test", requiredAssumptions := [],
    dependencies := [], proposition := True, proof := True.intro }
def invalidRegisteredStep : TheoryPackage :=
  TheoryPackage.empty "invalid" "test"
    |>.addDerivedTheoremRegistered detached (by simp)
      "derived" "detached predecessor" "test" [] (fun h : True => h)'

expect_failure "registered_model_reference_required" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def package : TheoryPackage :=
  TheoryPackage.empty "model" "test" |>.addModelText
    "known" "finite" "P" "S" "O" "step" []
def invalidModelReference : TheoryPackage :=
  package.addTheoremForModelRegistered "missing" (by simp [package])
    "claim" "the model must be registered" "test" [] True.intro'

expect_failure "registered_model_assumption_required" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def package : TheoryPackage :=
  TheoryPackage.empty "model" "test"
    |>.addAssumptionText "known" "known premise" "test"
def invalidModel : TheoryPackage :=
  package.addModelTextRegistered "model" "finite" "P" "S" "O" "step"
    ["missing"] (by simp [package])'

expect_failure "assumption_witness_proof_required" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def witness : AssumptionWitness :=
  { metadata := { name := "model", statement := "model premise", source := "test" },
    proposition := True, proof := True.intro }
def invalidWitnessStep : TheoryPackage :=
  TheoryPackage.empty "invalid" "test"
    |>.addAssumptionWitness witness
    |>.addTheoremUnderAssumption witness "claim" "claim" "test"
      (fun h : False => h)'

expect_failure "obligation_resolution_name_checked" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def obligations : TheoryPackage :=
  TheoryPackage.empty "model" "test" |>.addObligationText
    "known obligation" "supply a bridge" "test"
def invalidResolution : TheoryPackage :=
  obligations.resolveObligation "misspelled obligation" (by simp [obligations])
    "closed" "the bridge" "test" [] [] True.intro'

expect_failure "external_certificate_proof_required" 'import LeanPhy.Mathematics.ExternalCertificate
open LeanPhy.Mathematics
def checker : CertificateChecker True String :=
  { check := fun _ => True, sound := fun _ => True.intro }
def envelope : CertificateEnvelope String :=
  { metadata := { producer := "test", format := "raw", digest := "x", source := "test" },
    payload := "untrusted" }
def invalidCertificate : VerifiedCertificate checker :=
  { envelope := envelope }'

expect_failure "typed_obligation_proof_required" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def obligation : ExternalObligationWitness :=
  { metadata := { name := "bridge", statement := "a typed bridge", source := "test" },
    proposition := False }
def package : TheoryPackage :=
  TheoryPackage.empty "model" "test" |>.addObligation obligation.metadata
def invalidTypedResolution : TheoryPackage :=
  package.resolveObligationWitness obligation (by simp [package, obligation])
    "closed" "the bridge" "test" [] [] (fun h => h) True.intro'

expect_failure "cross_package_dependency_missing" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def badClaim : CheckedClaim :=
  { name := "consumer", statement := "bad link", source := "test",
    requiredAssumptions := [], dependencies := [ResearchProject.qualifiedDependency "missing" "claim"],
    proposition := True, proof := True.intro }
def badPackage : TheoryPackage := TheoryPackage.empty "consumer" "test" |>.addClaim badClaim
def badProject : ResearchProject := ResearchProject.ofPackages "bad" [badPackage]
example : badProject.hasErrors = false := by native_decide'

expect_failure "cross_package_proof_missing_source" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def prior : CheckedClaim :=
  { name := "prior", statement := "True", source := "test",
    requiredAssumptions := [], dependencies := [], proposition := True, proof := True.intro }
def target : TheoryPackage := TheoryPackage.empty "target" "test"
def badDerived : ResearchProject :=
  ResearchProject.addDerivedTheorem (ResearchProject.empty "bad" "test")
    "missing" prior target "derived" "bad source" "test" [] (fun h => h)
example : badDerived.hasErrors = false := by native_decide'

expect_failure "qualified_forward_dependency" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def first : CheckedClaim :=
  { name := "first", statement := "True", source := "test",
    requiredAssumptions := [],
    dependencies := [ResearchProject.qualifiedDependency "pkg" "second"],
    proposition := True, proof := True.intro }
def second : CheckedClaim :=
  { name := "second", statement := "True", source := "test",
    requiredAssumptions := [], dependencies := [], proposition := True,
    proof := True.intro }
def pkg : TheoryPackage :=
  TheoryPackage.empty "pkg" "test" |>.addClaim first |>.addClaim second
def badOrder : ResearchProject := ResearchProject.ofPackages "bad" [pkg]
example : badOrder.hasErrors = false := by native_decide'

expect_failure "duplicate_project_package" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def p : TheoryPackage := TheoryPackage.empty "same" "test"
def duplicate : ResearchProject := ResearchProject.ofPackages "bad" [p, p]
example : duplicate.hasErrors = false := by native_decide'

expect_failure "variance_mismatch" 'import LeanPhy
open LeanPhy.Tensor
example {n : Nat} (T : Tensor3N n .up .up .down) : Tensor1N n .down :=
  contract12 T'

expect_failure "fourier_dimension_mismatch" 'import LeanPhy
open LeanPhy.Mathematics
example (x : Fin 2 → ℂ) : Fin 4 → ℂ :=
  FiniteFourierSystem.fourier4.forward x'

expect_failure "unitary_invariant_required" 'import LeanPhy
open LeanPhy.Quantum
example {n : Nat} (A : Operator n) : UnitaryOperator n :=
  { op := A, unitary := rfl }'

expect_failure "second_moment_scalar_mismatch" 'import LeanPhy
open LeanPhy.StatMech
example (p : FiniteDistribution 2) (f : Fin 2 → ℂ) : ℝ :=
  p.secondMoment f'

expect_failure "diagonal_state_observable_dimension_mismatch" 'import LeanPhy
open LeanPhy.Quantum
open LeanPhy.StatMech
example (p : FiniteDistribution 2) (f : Fin 3 → ℝ) : ℂ :=
  expectation (diagonalState p) (diagonalObservable f)'

expect_failure "finite_kernel_label_mismatch" 'import LeanPhy
open LeanPhy.StatMech
example {ι κ : Type} [Fintype ι] [Fintype κ]
    (K : FiniteKernel ι) (p : FiniteProbability κ) : FiniteProbability ι :=
  K.step p'

expect_failure "named_channel_completeness_required" 'import LeanPhy
open LeanPhy.Quantum
example {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
  (K : κ → NamedState ι) : NamedFiniteChannel ι :=
  namedChannelFromKraus K'

expect_failure "conductance_symmetry_required" 'import LeanPhy
open LeanPhy.StatMech
example {ι : Type} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (c : ι → ι → ℝ) (wp : ∀ i, 0 < w i)
    (cn : ∀ i j, 0 ≤ c i j) (rs : ∀ i, ∑ j, c i j = w i) :
    ConductanceModel ι :=
  { weight := w, conductance := c, weight_pos := wp,
    conductance_nonneg := cn, row_sum := rs }'

expect_failure "conductance_positive_weights_required" 'import LeanPhy
open LeanPhy.StatMech
example {ι : Type} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (c : ι → ι → ℝ) (cn : ∀ i j, 0 ≤ c i j)
    (sy : ∀ i j, c i j = c j i) (rs : ∀ i, ∑ j, c i j = w i) :
    ConductanceModel ι :=
  { weight := w, conductance := c, conductance_nonneg := cn,
    symmetric := sy, row_sum := rs }'

expect_failure "conductance_row_normalization_required" 'import LeanPhy
open LeanPhy.StatMech
example {ι : Type} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (c : ι → ι → ℝ) (wp : ∀ i, 0 < w i)
    (cn : ∀ i j, 0 ≤ c i j) (sy : ∀ i j, c i j = c j i) :
    ConductanceModel ι :=
  { weight := w, conductance := c, weight_pos := wp,
    conductance_nonneg := cn, symmetric := sy }'

expect_failure "dirichlet_requires_normalized_kernel" 'import LeanPhy
open LeanPhy.StatMech
example {ι : Type} [Fintype ι] (p : FiniteProbability ι)
    (transition : ι → ι → ℝ) (nonneg : ∀ i j, 0 ≤ transition i j)
    (f : ι → ℝ) :
    0 ≤ FiniteKernel.dirichletForm
      { transition := transition, nonneg := nonneg } p f f := by
  exact FiniteKernel.dirichletForm_nonneg _ p f'

expect_failure "dirichlet_laplacian_requires_detailed_balance" 'import LeanPhy
open LeanPhy.StatMech
example {ι : Type} [Fintype ι] (K : FiniteKernel ι)
    (p : FiniteProbability ι) (f g : ι → ℝ) :
    K.dirichletForm p f g =
      p.expectation (fun i => f i * K.laplacian g i) := by
  exact K.dirichletForm_eq_laplacian_pairing p f g'

expect_failure "response_commutation_certificate_required" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] [DecidableEq ι]
    (rho A B : Matrix ι ι ℂ) :
    commutatorResponse rho A B = 0 :=
  commutatorResponse_eq_zero_of_commute rho A B'

expect_failure "hamiltonian_hermitian_required" 'import LeanPhy
open LeanPhy.Quantum
example {n : Nat} (H : Operator n) : FiniteUnitary (Fin n) :=
  finiteHamiltonianFlow H rfl 1'

expect_failure "flow_invariant_commutation_required" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A O : Matrix ι ι ℂ) :
    (FiniteMatrixFlow.exponential A).IsInvariant O :=
  FiniteMatrixFlow.exponential_isInvariant_of_commute A O'

expect_failure "typed_channel_completeness_required" 'import LeanPhy
open LeanPhy.QuantumInfo
example (K : PUnit → Matrix (Fin 2) (Fin 1) ℂ) :
    TypedKrausChannel (Fin 1) (Fin 2) PUnit :=
  { op := K }'

expect_failure "typed_channel_label_mismatch" 'import LeanPhy
open LeanPhy.QuantumInfo
example (K : PUnit → Matrix (Fin 2) (Fin 1) ℂ) (rho : Matrix (Fin 1) (Fin 1) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  typedApplyKraus K rho'

expect_failure "path_endpoint_mismatch" 'import LeanPhy
open LeanPhy.Mathematics
example {V : Type} {x y z : V} (p : FinitePath V x y) (q : FinitePath V z z) :
    FinitePath V x z :=
  FinitePath.comp p q'

expect_failure "approximation_without_bound" 'import LeanPhy
open LeanPhy.Mathematics
example (x y : ℝ) : ErrorCertificate x y 0 :=
  ErrorCertificate.of_eq rfl'

expect_failure "cross_space_approximation_requires_decoder" 'import LeanPhy
open LeanPhy.Mathematics
example (x : ℝ) (y : Fin 2 → ℝ) : FiniteApproximation x y 0 := by
  exact ⟨ErrorCertificate.of_eq rfl⟩'

expect_failure "winding_without_integer_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {V : Type} [Fintype V] (link : V → ℤ) (step : Equiv.Perm V) :
    DiscreteCochain.WindingCertificate link step 0 :=
  ⟨rfl⟩'

expect_failure "plaquette_orientation_without_antisymmetry" 'import LeanPhy
open LeanPhy.Mathematics
example {V : Type} (α : V → V → ℤ) (x y z w : V) :
    Plaquette.flux α w z y x = -Plaquette.flux α x y z w := by
  exact Plaquette.flux_reverse α (fun _ _ => by rfl) x y z w'

expect_failure "step_residual_without_equation" 'import LeanPhy
open LeanPhy.Mathematics
example (x y : ℝ) : StepResidual x y 0 :=
  stepResidual_of_eq x y rfl'

expect_failure "hilbert_unitary_right_inverse_required" 'import LeanPhy
open LeanPhy.Mathematics
example (U : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :
    Hilbert.Unitary (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin 2)) :=
  { op := U, left_unitary := rfl }'

expect_failure "fermionic_wick_without_antisymmetry" 'import LeanPhy
open LeanPhy.FieldTheory
example {I A : Type} [CommRing A] (C : I → I → A)
    (i j k l : I) :
    FermionicWick.fourPoint C j i k l =
      -FermionicWick.fourPoint C i j k l := by
  exact FermionicWick.fourPoint_swap12 C (fun _ _ => by rfl) i j k l'

expect_failure "finite_divergence_without_local_equation" 'import LeanPhy
open LeanPhy.Mathematics
example {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (current : E → ℤ) (source : V → ℤ) :
    FiniteDivergence.ConservationCertificate tail head current source :=
  ⟨fun _ => rfl⟩'

expect_failure "markov_current_without_divergence_proof" 'import LeanPhy
open LeanPhy.StatMech
example {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : FiniteKernel ι) (p : FiniteProbability ι) :
    MarkovCurrentConservation K p :=
  ⟨fun _ => rfl⟩'

expect_failure "conservation_residual_without_bound" 'import LeanPhy
open LeanPhy.Mathematics
example {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (current : V → ℝ) (source radius : V → ℝ) :
    FiniteDivergence.ConservationError tail head (fun _ => 0) source radius :=
  ⟨fun _ => by positivity, fun _ => by rfl⟩'

expect_failure "representation_homomorphism_without_proof" 'import LeanPhy
open LeanPhy.Mathematics
example {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι]
    (R : FiniteMatrixRepresentation G ι) (g h : G) :
    R.rep (g * h) = R.rep g * R.rep h := by
  rfl'

expect_failure "unitary_representation_without_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    (R : FiniteMatrixRepresentation G ι) :
    UnitaryMatrixRepresentation G ι :=
  { toFiniteMatrixRepresentation := R, unitary := fun _ => rfl }'

expect_failure "chain_complex_boundary_certificate_required" 'import LeanPhy
open LeanPhy.Mathematics
example : FiniteChainComplex PUnit PUnit PUnit ℤ :=
  { boundary10 := fun _ _ => 0, boundary21 := fun _ _ => 0 }'

expect_failure "chain_cycle_hypothesis_required" 'import LeanPhy
open LeanPhy.Mathematics
example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (phi : C0 → A) (c : C1 → A) :
    FiniteChainComplex.pairing (K.coboundary0 phi) c = 0 :=
  K.exact_pairing_zero phi c'

expect_failure "chain_complex_coefficient_ring_required" 'import LeanPhy
open LeanPhy.Mathematics
example : FiniteChainComplex PUnit PUnit PUnit Nat :=
  { boundary10 := fun _ _ => 0, boundary21 := fun _ _ => 0,
    boundary_sq := by simp }'

expect_failure "graph_chain_coefficient_ring_required" 'import LeanPhy
open LeanPhy.Mathematics
example : FiniteChainAdapters.graphChainComplex (A := Nat)
    (fun _ : PUnit => PUnit.unit) (fun _ : PUnit => PUnit.unit) := by
  exact FiniteChainAdapters.graphChainComplex _ _'

expect_failure "cocycle_pairing_without_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (alpha : C1 → A) (b : C2 → A) :
    FiniteChainComplex.pairing alpha (K.boundary2 b) = 0 :=
  K.cocycle_pairing_boundary_zero alpha b'

expect_failure "exact_cycle_pairing_without_cycle" 'import LeanPhy
open LeanPhy.Mathematics
example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (phi : C0 → A) (c : C1 → A) :
    FiniteChainComplex.pairing (K.coboundary0 phi) c = 0 :=
  K.exact_pairing_cycle_zero phi c'

expect_failure "detailed_balance_stationarity_without_certificate" 'import LeanPhy
open LeanPhy.StatMech
example {ι : Type} [Fintype ι]
    (K : FiniteKernel ι) (p : FiniteProbability ι) : K.step p = p :=
  K.step_eq_of_detailedBalance p'

expect_failure "closed_surface_certificate_required" 'import LeanPhy
open LeanPhy.Mathematics
example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (alpha : C1 → A) (surface : C2 → A) :
    FiniteChainComplex.pairing (K.coboundary1 alpha) surface = 0 :=
  K.coboundary1_pairing_cycle2_zero alpha surface'

expect_failure "finite_path_partition_certificate_required" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (w : ι → ℂ) : FinitePathIntegral ι :=
  { weight := w }'

expect_failure "finite_rg_insertion_identity_required" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ) (O : κ → ℂ) :
    ∑ y, R.coarseWeight y * O y =
      ∑ x, R.fineWeight x * O x :=
  R.insertion_preserved O'

expect_failure "finite_pde_solution_certificate_required" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FiniteLinearPDE ι) (u : ι → ℝ) :
    EquationResidual (fun v => P.residual v) u 0 :=
  P.residual_zero u rfl'

expect_failure "finite_gradient_incidence_sum_required" 'import LeanPhy
open LeanPhy.Mathematics
example {V E : Type} [Fintype V] [Fintype E]
    (incidence : E → V → ℝ) : FiniteGradient V E :=
  { incidence := incidence }'

expect_failure "finite_rg_expectation_without_partition_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ) (O : κ → ℂ) :
    (R.coarsePathIntegral (by assumption)).expectation O =
      (R.finePathIntegral (by assumption)).expectation (fun x => O (R.coarse x)) := by
  exact R.expectation_preserved (by assumption) O'

expect_failure "finite_pde_uniqueness_without_coercivity" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FiniteLinearPDE ι)
    {u v : ι → ℝ} (hu : P.IsSolution u) (hv : P.IsSolution v) : u = v :=
  P.solution_unique_of_coercive (by assumption) hu hv'

expect_failure "finite_action_partition_certificate_required" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (S : ι → ℂ) :
    FinitePathIntegral.fromAction S (by assumption) := by
  exact FinitePathIntegral.fromAction S (by assumption)'

expect_failure "finite_expectation_error_without_denominator_bound" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P Q : FinitePathIntegral ι) (O : ι → ℂ)
    (hI : ErrorCertificate (P.insertion O) (Q.insertion O) 0)
    (hP : ErrorCertificate P.partition Q.partition 0) :
    FinitePathIntegral.ApproximationCertificate P Q O :=
  { insertionRadius := 0, partitionRadius := 0,
    insertion_nonneg := by positivity, partition_nonneg := by positivity,
    insertion_error := hI, partition_error := hP,
    exactLower := 0, approximateLower := 0,
    insertionUpper := 0, insertionUpper_nonneg := by positivity,
    approximate_insertion_upper := by positivity }'

expect_failure "finite_pointwise_error_without_nonnegativity" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P Q : FinitePathIntegral ι)
    (radius : ι → ℝ)
    (h : ∀ i, ErrorCertificate (P.weight i) (Q.weight i) (radius i)) :
    ErrorCertificate P.partition Q.partition (∑ i, radius i) :=
  FinitePathIntegral.ApproximationCertificate.partition_error_of_pointwise
    P Q radius (fun _ => by assumption) h'

expect_failure "observable_error_without_partition_lower_bound" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FinitePathIntegral ι)
    (O O2 : ι → ℂ)
    (C : FinitePathIntegral.ObservableApproximationCertificate O O2)
    (lower : ℝ) :
    ErrorCertificate (P.expectation O) (P.expectation O2)
      ((∑ i, ‖P.weight i‖ * C.radius i) / lower) :=
  C.expectation_error P O O2 lower (by assumption) (by assumption)'

expect_failure "rg_coarse_approximation_requires_denominator_bounds" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (Q : FinitePathIntegral κ) (O : κ → ℂ)
    (radius : κ → ℝ) (hr : ∀ y, 0 ≤ radius y)
    (hw : ∀ y, ErrorCertificate (R.coarseWeight y) (Q.weight y) (radius y))
    (insertionUpper : ℝ) (hinsertionUpper_nonneg : 0 ≤ insertionUpper)
    (hinsertion_upper : ‖Q.insertion O‖ ≤ insertionUpper) :
    FinitePathIntegral.ApproximationCertificate
      (R.coarsePathIntegral h) Q O :=
  FinitePathIntegral.FiniteRGStep.coarse_approximation_certificate
    R h Q O radius hr hw 1 1 (by positivity) (by positivity)
      (by assumption) (by assumption) insertionUpper hinsertionUpper_nonneg
      hinsertion_upper'

expect_failure "rg_coarse_approximation_requires_insertion_upper_bound" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (Q : FinitePathIntegral κ) (O : κ → ℂ)
    (radius : κ → ℝ) (hr : ∀ y, 0 ≤ radius y)
    (hw : ∀ y, ErrorCertificate (R.coarseWeight y) (Q.weight y) (radius y))
    (exactLower approximateLower : ℝ)
    (hexact_pos : 0 < exactLower) (happrox_pos : 0 < approximateLower)
    (hexact_lower : exactLower ≤ ‖(R.coarsePathIntegral h).partition‖)
    (happrox_lower : approximateLower ≤ ‖Q.partition‖) :
    FinitePathIntegral.ApproximationCertificate
      (R.coarsePathIntegral h) Q O :=
  FinitePathIntegral.FiniteRGStep.coarse_approximation_certificate
    R h Q O radius hr hw exactLower approximateLower hexact_pos happrox_pos
      hexact_lower happrox_lower 0 (by positivity) (by assumption)'

expect_failure "finite_boundary_uniqueness_without_coercivity" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FiniteLinearPDE ι)
    (B : FiniteBoundaryData ι) {u v : ι → ℝ}
    (hu : P.IsSolution u) (hv : P.IsSolution v)
    (huB : SatisfiesBoundary B u) (hvB : SatisfiesBoundary B v) : u = v :=
  P.solution_unique_of_boundary_coercive B (by assumption) hu hv huB hvB'

expect_failure "structured_pde_certificate_requires_residual" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FiniteEllipticProblem ι) (u : ι → ℝ)
    (hB : SatisfiesBoundary P.boundary u) : FiniteEllipticCertificate P u :=
  { residualRadius := 0, residual_nonneg := by positivity, boundary := hB }'

expect_failure "finite_pde_left_inverse_requires_left_inverse" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FiniteLinearPDE ι)
    (B : FiniteBoundaryData ι) (solve : (ι → ℝ) → (ι → ℝ)) :
    FinitePDELeftInverseCertificate P B :=
  { solve := solve, modulus := 0, modulus_nonneg := by positivity,
    lipschitz := by intro r s; positivity }'

expect_failure "finite_pde_left_inverse_requires_lipschitz" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FiniteLinearPDE ι)
    (B : FiniteBoundaryData ι) (solve : (ι → ℝ) → (ι → ℝ))
    (hleft : ∀ w, SatisfiesHomogeneousBoundary B w →
      solve (P.operator.mulVec w) = w) :
    FinitePDELeftInverseCertificate P B :=
  { solve := solve, modulus := 0, modulus_nonneg := by positivity,
    left_inverse := hleft }'

expect_failure "additive_left_inverse_requires_left_inverse" 'import LeanPhy
open LeanPhy.Mathematics
example {X Y : Type} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] (A : X →+ Y)
    (solve : Y → X) : AdditiveLeftInverseCertificate A :=
  { solve := solve, modulus := 0, modulus_nonneg := by positivity,
    lipschitz := by intro r s; positivity }'

expect_failure "additive_left_inverse_requires_lipschitz" 'import LeanPhy
open LeanPhy.Mathematics
example {X Y : Type} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] (A : X →+ Y)
    (solve : Y → X)
    (hleft : ∀ x, solve (A x) = x) :
    AdditiveLeftInverseCertificate A :=
  { solve := solve, modulus := 0, modulus_nonneg := by positivity,
    left_inverse := hleft }'

expect_failure "finite_boundary_error_requires_bound" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (B : FiniteBoundaryData ι)
    (u : ι → ℝ) : FiniteBoundaryResidualCertificate B u :=
  { radius := fun _ => 0, radius_nonneg := by intro i; positivity }'

expect_failure "joint_pde_certificate_requires_boundary_error" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FiniteEllipticProblem ι)
    (u : ι → ℝ) (h : P.IsSolution u) :
    FiniteEllipticApproximationCertificate P u :=
  { residualRadius := 0, residual_nonneg := by positivity,
    residual := P.equation.residual_zero u h.1 }'

expect_failure "joint_pde_zero_requires_boundary_zero" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    {P : FiniteEllipticProblem ι} {u : ι → ℝ}
    (C : FiniteEllipticApproximationCertificate P u)
    (hres : C.residualRadius = 0) : P.IsSolution u :=
  C.isSolution_of_zero hres (by assumption)'

expect_failure "finite_rg_fixed_point_without_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (h : (∑ y, R.fineWeight y) ≠ 0) (O : ι → ℂ) :
    (R.coarsePathIntegral h).expectation O =
      (R.finePathIntegral h).expectation O := by
  exact R.fixedPoint_expectation h (by assumption) O'

expect_failure "finite_rg_scaling_without_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (fineObs : ι → ℂ) (coarseObs : κ → ℂ) (lambda : ℂ) :
    (R.finePathIntegral h).expectation fineObs =
      lambda * (R.coarsePathIntegral h).expectation coarseObs := by
  exact R.expectation_scales h fineObs coarseObs lambda (by assumption)'

expect_failure "boundary_stability_requires_total_bound" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (P : FiniteEllipticProblem ι) :
    FiniteEllipticResidualStability P :=
  { equationModulus := 1, boundaryModulus := 1,
    equationModulus_nonneg := by positivity,
    boundaryModulus_nonneg := by positivity }'

expect_failure "normalized_expectation_requires_error" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P Q : FinitePathIntegral ι)
    (O : ι → ℂ) :
    FinitePathIntegral.NormalizedExpectationCertificate P Q O :=
  { radius := 0, radius_nonneg := by positivity }'

expect_failure "real_action_lower_bound_requires_nonempty" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (S : ι → ℝ) (i₀ : ι) :
    Real.exp (-S i₀) ≤ ‖(FinitePathIntegral.fromRealAction S).partition‖ :=
  FinitePathIntegral.fromRealAction_partition_lower_bound S i₀'

expect_failure "cross_space_comparison_requires_error" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ : Type} [Fintype ι] [Fintype κ]
    (P : FinitePathIntegral ι) (Q : FinitePathIntegral κ)
    (O : ι → ℂ) (O2 : κ → ℂ) :
    FinitePathIntegral.ExpectationComparisonCertificate P Q O O2 :=
  { radius := 0, radius_nonneg := by positivity }'

expect_failure "cross_space_rg_requires_partition_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ τ : Type} [Fintype ι] [Fintype κ] [Fintype τ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (next : κ → τ) (O : τ → ℂ) :
  ((R.coarsen next).coarsePathIntegral (by assumption)).expectation O =
      (R.finePathIntegral (by assumption)).expectation
        (fun x => O (next (R.coarse x))) :=
  R.coarsen_expectation_preserved next (by assumption) O'

expect_failure "finite_evolution_requires_lipschitz" 'import LeanPhy
open LeanPhy.Mathematics
example {X : Type} [PseudoMetricSpace X] (f : X → X) :
    FiniteEvolutionStep X :=
  { step := f, modulus := 1, modulus_nonneg := by positivity }'

expect_failure "trajectory_requires_step_residual" 'import LeanPhy
open LeanPhy.Mathematics
example {X : Type} [PseudoMetricSpace X]
    (S : FiniteEvolutionStep X) (exact approximate : ℕ → X)
    (hExact : ∀ n, exact (n + 1) = S.step (exact n)) :
    S.TrajectoryCertificate exact approximate 0 (fun _ => 0) :=
  { initial_nonneg := by positivity,
    step_nonneg := by intro n; positivity,
    initial := ErrorCertificate.of_eq rfl,
    exact_step := hExact }'

expect_failure "connected_factorization_requires_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι) (O Q : ι → ℂ) :
    P.connectedCorrelator O Q = 0 :=
  P.connectedCorrelator_eq_zero_of_factorizes O Q (by assumption)'

expect_failure "finite_rg_scaling_composition_requires_intermediate_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ W : Type} [Fintype ι] [Fintype κ] [Fintype W]
    (R : FinitePathIntegral.FiniteRGStep ι κ) (next : κ → W)
    (fineObs : ι → ℂ) (middleObs : κ → ℂ) (coarseObs : W → ℂ)
    (lambda mu : ℂ)
    (h₁ : FinitePathIntegral.FiniteRGStep.ScalingCertificate
      R fineObs middleObs lambda) :
    FinitePathIntegral.FiniteRGStep.ScalingCertificate
      (R.coarsen next) fineObs coarseObs (lambda * mu) :=
  FinitePathIntegral.FiniteRGStep.ScalingCertificate.compose
    R next fineObs middleObs coarseObs lambda mu h₁ (by assumption)'

expect_failure "finite_positive_step_requires_nonnegativity" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (K : Matrix ι ι ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1) : FinitePositiveStep ι :=
  { kernel := K, row_sum := hrow }'

expect_failure "finite_positive_step_requires_row_normalization" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (K : Matrix ι ι ℝ)
    (hnonneg : ∀ i j, 0 ≤ K i j) : FinitePositiveStep ι :=
  { kernel := K, nonneg := hnonneg }'

expect_failure "finite_mass_conservation_requires_column_sum" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (K : FinitePositiveStep ι) :
    FinitePositiveStep.MassConservationCertificate K :=
  {}'

expect_failure "finite_npoint_rg_requires_partition_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (observables : List (κ → ℂ)) :
    (R.coarsePathIntegral (by assumption)).multiCorrelator observables =
      (R.finePathIntegral (by assumption)).multiCorrelator
        (observables.map (fun O => fun x => O (R.coarse x))) :=
  FinitePathIntegral.multiCorrelator_coarsen R (by assumption) observables'

expect_failure "finite_ward_requires_weight_symmetry" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι) (e : Equiv.Perm ι) (O : ι → ℂ) :
    P.expectation (fun i => O (e i)) = P.expectation O :=
  P.expectation_reindex_of_weightSymmetry e (by assumption) O'

expect_failure "finite_parabolic_trajectory_requires_step_residual" 'import LeanPhy
open LeanPhy.Mathematics
open LeanPhy.Mathematics.FinitePositiveStep
example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι)
    (exact approximate : ℕ → (ι → ℝ))
    (initialRadius : ℝ) (stepRadius : ℕ → ℝ)
    (hinit : UniformError (exact 0) (approximate 0) initialRadius)
    (hrec : ∀ n, exact (n + 1) = K.step (exact n)) :
    FinitePositiveStep.TrajectoryCertificate
      K exact approximate initialRadius stepRadius :=
  { initial_nonneg := by positivity,
    step_nonneg := by intro n; positivity,
    initial := hinit,
    exact_step := hrec }'

expect_failure "driven_trajectory_requires_source_recurrence" 'import LeanPhy
open LeanPhy.Mathematics
open LeanPhy.Mathematics.FinitePositiveStep
example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι)
    (source : ℕ → (ι → ℝ))
    (exact approximate : ℕ → (ι → ℝ))
    (initialRadius : ℝ) (stepRadius : ℕ → ℝ)
    (hinit : UniformError (exact 0) (approximate 0) initialRadius)
    (hstep : ∀ n, UniformError (K.drivenStep (approximate n) (source n))
      (approximate (n + 1)) (stepRadius n)) :
    FinitePositiveStep.DrivenTrajectoryCertificate K source exact approximate
      initialRadius stepRadius :=
  { initial_nonneg := by positivity,
    step_nonneg := by intro n; positivity,
    initial := hinit,
    step := hstep }'

expect_failure "schwinger_dyson_requires_weight_balance" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι) (e : Equiv.Perm ι)
    (hinv : ∀ i, e (e i) = i) (jac : ι → ℂ) :
    FinitePathIntegral.InvolutiveVariation P :=
  { map := e, involutive := hinv, jacobian := jac }'

expect_failure "rg_fixed_point_defect_requires_radius" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (herr : ∀ y, ErrorCertificate (R.coarseWeight y) (R.fineWeight y) 0) :
    FinitePathIntegral.FiniteRGStep.FixedPointDefect R :=
  { error := herr }'

expect_failure "source_driven_trajectory_requires_source_error" 'import LeanPhy
open LeanPhy.Mathematics
open LeanPhy.Mathematics.FinitePositiveStep
example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι)
    (exactSource approximateSource : ℕ → (ι → ℝ))
    (exact approximate : ℕ → (ι → ℝ))
    (initialRadius : ℝ) (sourceRadius stepRadius : ℕ → ℝ)
    (hinit : UniformError (exact 0) (approximate 0) initialRadius)
    (hrec : ∀ n, exact (n + 1) = K.drivenStep (exact n) (exactSource n))
    (hstep : ∀ n, UniformError
      (K.drivenStep (approximate n) (approximateSource n))
      (approximate (n + 1)) (stepRadius n)) :
    FinitePositiveStep.SourceDrivenTrajectoryCertificate K exactSource
      approximateSource exact approximate initialRadius sourceRadius stepRadius :=
  { initial_nonneg := by positivity,
    source_nonneg := by intro n; positivity,
    step_nonneg := by intro n; positivity,
    initial := hinit,
    exact_step := hrec,
    step := hstep }'

expect_failure "rg_defect_composition_requires_middle_weights" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (R S : FinitePathIntegral.FiniteRGStep ι ι)
    (first : FinitePathIntegral.FiniteRGStep.FixedPointDefect R)
    (second : FinitePathIntegral.FiniteRGStep.FixedPointDefect S) :
    FinitePathIntegral.FiniteRGStep.FixedPointDefect (R.coarsen S.coarse) :=
  FinitePathIntegral.FiniteRGStep.FixedPointDefect.compose
    R S (by assumption) first second'

expect_failure "reflection_certificate_requires_gram_factorization" 'import LeanPhy
open LeanPhy.Mathematics
example {ι α : Type} [Fintype ι] [Fintype α]
    (e : Equiv.Perm ι) : FiniteReflectionCertificate ι α :=
  { reflection := e }'

expect_failure "reflection_certificate_requires_involution" 'import LeanPhy
open LeanPhy.Mathematics
example {ι α : Type} [Fintype ι] [Fintype α]
    (e : Equiv.Perm ι) (G : FiniteGramKernel ι α) :
    FiniteReflectionCertificate ι α :=
  { reflection := e, gram := G }'

expect_failure "positive_path_requires_weight_nonneg" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (w : ι → ℝ) (hpart : 0 < ∑ i, w i) :
    FinitePositivePathIntegral ι :=
  { weight := w, partition_pos := hpart }'

expect_failure "positive_path_requires_partition_pos" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    FinitePositivePathIntegral ι :=
  { weight := w, weight_nonneg := hw }'

expect_failure "weighted_reflection_requires_involution" 'import LeanPhy
open LeanPhy.Mathematics
example {ι α : Type} [Fintype ι] [Fintype α]
    (e : Equiv.Perm ι) (G : FiniteWeightedGramKernel ι α) :
    FiniteWeightedReflectionCertificate ι α :=
  { reflection := e, gram := G }'

expect_failure "weighted_gram_requires_weight_nonneg" 'import LeanPhy
open LeanPhy.Mathematics
example {ι α : Type} [Fintype ι] [Fintype α]
    (w : α → ℝ) (feature : ι → α → ℝ) :
    FiniteWeightedGramKernel ι α :=
  { weight := w, feature := feature }'

expect_failure "energy_step_requires_one_step_bound" 'import LeanPhy
open LeanPhy.Mathematics
example {X : Type} (step : X → X) (energy : X → ℝ)
    (factor : ℝ) : FiniteEnergyStep X :=
  { step := step,
    energy := energy,
    energy_nonneg := by intro x; positivity,
    factor := factor,
    factor_nonneg := by positivity }'

expect_failure "state_map_intermediate_invariant_required" 'import LeanPhy
open LeanPhy.Mathematics
def firstMap : StateMap Nat Nat (fun _ => True) (fun n => n = 0) :=
  { toFun := fun _ => 0, preserves := by intro n _; rfl }
def secondMap : StateMap Nat Nat (fun n => n = 1) (fun _ => True) :=
  { toFun := fun _ => 0, preserves := by intro n _; trivial }
def invalidComposition : StateMap Nat Nat (fun _ => True) (fun _ => True) :=
  secondMap.compose firstMap'

expect_failure "approximate_model_state_lipschitz_required" 'import LeanPhy.Minimal
open LeanPhy.Mathematics
def idProcess : Process ℝ (fun _ => True) where
  toFun := id
  preserves := by intro _ _; trivial
def idModel : PhysicalModel ℝ where
  State := ℝ
  valid := fun _ => True
  step := idProcess
  Observable := Unit
  evaluate := fun x _ => x
def missingStateLipschitz : ApproximateModelMap idModel idModel where
  state := StateMap.identity ℝ (fun _ => True)
  pullback := id
  modulus := 1
  modulus_nonneg := by norm_num
  target_lipschitz := by intro x y; simpa using (show dist x y ≤ dist x y from le_rfl)
  oneStepRadius := fun _ => 0
  oneStepRadius_nonneg := by intro _; norm_num
  oneStep_error := by intro x _; exact ErrorCertificate.of_eq rfl
  observableRadius := fun _ _ => 0
  observableRadius_nonneg := by intro _ _; norm_num
  observable_error := by intro x _ _; exact ErrorCertificate.of_eq rfl
  observableModulus := fun _ => 1
  observableModulus_nonneg := by intro _; norm_num
  observable_lipschitz := by
    intro _
    exact { nonneg := by norm_num, bound := by intro x y; simpa using (show dist x y ≤ dist x y from le_rfl) }'

expect_failure "approximate_model_one_step_certificate_required" 'import LeanPhy.Minimal
open LeanPhy.Mathematics
def idProcess : Process ℝ (fun _ => True) where
  toFun := id
  preserves := by intro _ _; trivial
def idModel : PhysicalModel ℝ where
  State := ℝ
  valid := fun _ => True
  step := idProcess
  Observable := Unit
  evaluate := fun x _ => x
def missingOneStep : ApproximateModelMap idModel idModel where
  state := StateMap.identity ℝ (fun _ => True)
  stateModulus := 1
  stateModulus_nonneg := by norm_num
  state_lipschitz := by intro x y; simpa [StateMap.identity] using (show dist x y ≤ dist x y from le_rfl)
  pullback := id
  modulus := 1
  modulus_nonneg := by norm_num
  target_lipschitz := by intro x y; simpa using (show dist x y ≤ dist x y from le_rfl)
  oneStepRadius := fun _ => 0
  oneStepRadius_nonneg := by intro _; norm_num
  observableRadius := fun _ _ => 0
  observableRadius_nonneg := by intro _ _; norm_num
  observable_error := by intro x _ _; exact ErrorCertificate.of_eq rfl
  observableModulus := fun _ => 1
  observableModulus_nonneg := by intro _; norm_num
  observable_lipschitz := by
    intro _
    exact { nonneg := by norm_num, bound := by intro x y; simpa using (show dist x y ≤ dist x y from le_rfl) }'

expect_failure "approximate_model_observable_certificate_required" 'import LeanPhy.Minimal
open LeanPhy.Mathematics
def idProcess : Process ℝ (fun _ => True) where
  toFun := id
  preserves := by intro _ _; trivial
def idModel : PhysicalModel ℝ where
  State := ℝ
  valid := fun _ => True
  step := idProcess
  Observable := Unit
  evaluate := fun x _ => x
def missingObservable : ApproximateModelMap idModel idModel where
  state := StateMap.identity ℝ (fun _ => True)
  stateModulus := 1
  stateModulus_nonneg := by norm_num
  state_lipschitz := by intro x y; simpa [StateMap.identity] using (show dist x y ≤ dist x y from le_rfl)
  pullback := id
  modulus := 1
  modulus_nonneg := by norm_num
  target_lipschitz := by intro x y; simpa using (show dist x y ≤ dist x y from le_rfl)
  oneStepRadius := fun _ => 0
  oneStepRadius_nonneg := by intro _; norm_num
  oneStep_error := by intro x _; exact ErrorCertificate.of_eq rfl
  observableRadius := fun _ _ => 0
  observableRadius_nonneg := by intro _ _; norm_num
  observable_error := by intro x _ _; exact ErrorCertificate.of_eq rfl
  observableModulus := fun _ => 1
  observableModulus_nonneg := by intro _; norm_num'

expect_failure "rayleigh_self_adjoint_required" 'import LeanPhy
open LeanPhy.Mathematics
def badRayleigh : RayleighIntervalCertificate (1 : ℂ →L[ℂ] ℂ) 1 1 := by
  refine ⟨True.intro, ?_, ?_⟩
  · intro x
    simp [ContinuousLinearMap.reApplyInnerSelf_apply, one_apply_eq_self,
      inner_self_eq_norm_sq]
  · intro x
    simp [ContinuousLinearMap.reApplyInnerSelf_apply, one_apply_eq_self,
      inner_self_eq_norm_sq]'

expect_failure "positive_operator_quadratic_bound_required" 'import LeanPhy
open LeanPhy.Mathematics
def badPositive : PositiveOperatorCertificate (1 : ℂ →L[ℂ] ℂ) :=
  { selfAdjoint := IsSelfAdjoint.one _ }'

expect_failure "positive_spectrum_bridge_requires_complex_space" 'import LeanPhy
open LeanPhy.Mathematics
example : SpectrumRestricts (1 : ℝ →L[ℝ] ℝ) ContinuousMap.realToNNReal := by
  apply PositiveOperatorCertificate.spectrumRestricts_complex
  exact { selfAdjoint := IsSelfAdjoint.one _, quadratic_nonneg := by
    intro x
    simp [ContinuousLinearMap.reApplyInnerSelf_apply, one_apply_eq_self,
      inner_self_eq_norm_sq] }'

expect_failure "dominated_convergence_requires_integrable_bound" 'import LeanPhy
open LeanPhy.Mathematics MeasureTheory Filter
noncomputable section
abbrev μ : Measure Unit := Measure.dirac ()
def badDct : DominatedConvergenceCertificate μ
    (fun _ _ : Unit => (1 : ℂ)) (fun _ : Unit => (1 : ℂ))
    (fun _ : Unit => (1 : ℝ)) := by
  refine { measurable := ?_, dominated := ?_, pointwise_limit := ?_ }
  · intro n; exact measurable_const.aestronglyMeasurable
  · intro n; filter_upwards [] with a; simp
  · filter_upwards [] with a; exact tendsto_const_nhds'

expect_failure "normalized_limit_requires_nonzero_partition" 'import LeanPhy
open LeanPhy.Mathematics MeasureTheory Filter
noncomputable section
abbrev μ : Measure Unit := Measure.dirac ()
def badNormalized : NormalizedObservableConvergenceCertificate μ
    (fun _ _ : Unit => (1 : ℂ)) (fun _ : Unit => (1 : ℂ))
    (fun _ : Unit => (1 : ℂ)) (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => (1 : ℝ)) := by
  exact { weight_certificate := by
      refine { measurable := ?_, bound_integrable := ?_, dominated := ?_, pointwise_limit := ?_ }
      · intro n; exact measurable_const.aestronglyMeasurable
      · simpa using (integrable_const (μ := μ) (1 : ℝ))
      · intro n; filter_upwards [] with a; simp
      · filter_upwards [] with a; exact tendsto_const_nhds,
    insertion_certificate := by
      refine { measurable := ?_, bound_integrable := ?_, dominated := ?_, pointwise_limit := ?_ }
      · intro n; simpa using (measurable_const : Measurable (fun _ : Unit => (1 : ℂ))).aestronglyMeasurable
      · simpa using (integrable_const (μ := μ) (1 : ℝ))
      · intro n; filter_upwards [] with a; simp
      · filter_upwards [] with a; exact tendsto_const_nhds }'

expect_failure "mean_ergodic_requires_contractive_bound" 'import LeanPhy
open LeanPhy.Mathematics
def badMeanErgodic : MeanErgodicCertificate (0 : ℂ →L[ℂ] ℂ) := by
  exact {}'

expect_failure "lax_milgram_requires_coercivity" 'import LeanPhy
open LeanPhy.Mathematics
noncomputable section
abbrev scalarB : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
def badLaxMilgram : LaxMilgramCertificate scalarB := by
  exact {}'

expect_failure "contraction_requires_factor" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
def badContraction : ContractionCertificate (fun x : ℝ => x) (1 : NNReal) := by
  exact {}'

expect_failure "resolvent_requires_both_inverses" 'import LeanPhy
open LeanPhy.Mathematics
def badResolvent : ResolventCertificate (1 : ℂ →L[ℂ] ℂ) 1 := by
  exact ⟨0, by simp⟩'

expect_failure "resolvent_perturbation_requires_inverse_bound" 'import LeanPhy
open LeanPhy.Mathematics
def hA : ResolventCertificate (0 : ℂ →L[ℂ] ℂ) 2 := by
  apply resolvent_of_norm_bound
  simp
def hB : ResolventCertificate (1 : ℂ →L[ℂ] ℂ) 2 := by
  refine ⟨(1 : ℂ →L[ℂ] ℂ), ?_, ?_⟩ <;>
    ext x <;> simp [Algebra.algebraMap_eq_smul_one] <;> norm_num
example : ‖hA.inverse - hB.inverse‖ ≤ (1 : ℝ) := by
  exact resolvent_perturbation_bound hA hB
'

expect_failure "flow_bound_requires_operator_envelope" 'import LeanPhy
open LeanPhy.Mathematics
open LeanPhy.Mathematics.Hilbert
noncomputable section
def F : Hilbert.Flow (𝕜 := ℂ) (E := ℂ) where
  op := fun _ => 1
  zero := rfl
  add := by intro t s; rfl
def bad : FlowNormCertificate F (fun _ => (1 : ℝ)) := by
  exact { nonneg := by intro t; norm_num }'

expect_failure "duhamel_requires_forcing_integrability" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
open LeanPhy.Mathematics.Hilbert
open MeasureTheory
open scoped Interval
noncomputable section
def F : Hilbert.Flow (𝕜 := ℂ) (E := ℂ) where
  op := fun _ => 1
  zero := rfl
  add := by intro t s; rfl
def bad : VariationOfConstantsCertificate F (fun _ : ℝ => (0 : ℂ))
    (fun _ => (0 : ℂ)) 0 := by
  exact { endpoint_eq := by intro t; simp [F, Hilbert.Flow.evolve] }'

expect_failure "duhamel_requires_majorant_integrability" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
open LeanPhy.Mathematics.Hilbert
open MeasureTheory
open scoped Interval
noncomputable section
def F : Hilbert.Flow (𝕜 := ℂ) (E := ℂ) where
  op := fun _ => 1
  zero := rfl
  add := by intro t s; rfl
variable {bound majorant : ℝ → ℝ}
example (h : VariationOfConstantsCertificate F (fun _ : ℝ => (0 : ℂ))
    (fun _ => (0 : ℂ)) 0)
    (hF : FlowNormCertificate F bound)
    (hs : SourceNormCertificate (fun _ : ℝ => (0 : ℂ)) majorant)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖(0 : ℂ) - F.evolve t 0‖ ≤
      ∫ s in (0 : ℝ)..t, bound (t-s) * majorant s := by
  exact VariationOfConstantsCertificate.norm_error_le h hF hs ht'

expect_failure "neumann_requires_strict_norm_bound" 'import LeanPhy
open LeanPhy.Mathematics
example (A : ℂ →L[ℂ] ℂ) : ResolventCertificate A 1 := by
  apply resolvent_of_neumann
' 

expect_failure "operator_approximation_requires_zero_radius_limit" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics Filter
def badOperatorApprox : UniformOperatorApproximationCertificate
    (fun _ : ℕ => (ContinuousLinearMap.id ℝ ℝ))
    (ContinuousLinearMap.id ℝ ℝ) (fun _ => (0 : ℝ)) := by
  refine { nonneg := ?_, bound := ?_ }
  · intro n; norm_num
  · intro n; simp'

expect_failure "energy_certificate_requires_dissipation_nonneg" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics MeasureTheory
open scoped Interval
def badEnergy : EnergyDissipationCertificate
    (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => (0 : ℝ))
    (fun _ : ℝ => (0 : ℝ)) 0 1 := by
  refine { ordered := by norm_num, energy_nonneg := ?_,
    dissipation_integrable := ?_, forcing_integrable := ?_, balance_le := ?_ }
  · intro t; norm_num
  · simpa using (intervalIntegrable_const (μ := volume) (c := (0 : ℝ)) (a := (0 : ℝ)) (b := 1))
  · simpa using (intervalIntegrable_const (μ := volume) (c := (0 : ℝ)) (a := (0 : ℝ)) (b := 1))
  · simp'

expect_failure "unbounded_resolvent_requires_left_inverse" 'import LeanPhy
open LeanPhy.Mathematics
noncomputable def badDenseZero : DenseDomainOperator (𝕜 := ℂ) (E := ℂ) where
  domain := ⊤
  dense := by simpa using (dense_univ : Dense (Set.univ : Set ℂ))
  operator := (0 : (⊤ : Submodule ℂ ℂ) →ₗ[ℂ] ℂ)
def badInverse : ℂ →ₗ[ℂ] (⊤ : Submodule ℂ ℂ) :=
  LinearMap.codRestrict (⊤ : Submodule ℂ ℂ)
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (by intro y; simp)
def badUnboundedResolvent : DomainResolventCertificate badDenseZero 1 where
  inverse := badInverse
  right_inverse := by
    intro y
    change (1 : ℂ) • y - 0 = y
    simp'

expect_failure "domain_preserving_requires_domain_map" 'import LeanPhy
open LeanPhy.Mathematics
noncomputable def domainMap : DenseDomainOperator (𝕜 := ℂ) (E := ℂ) where
  domain := ⊤
  dense := by simpa using (dense_univ : Dense (Set.univ : Set ℂ))
  operator := (0 : (⊤ : Submodule ℂ ℂ) →ₗ[ℂ] ℂ)
def missingDomainMap : DenseDomainOperator.DomainPreserving domainMap where
  bounded := ContinuousLinearMap.id ℂ ℂ'

expect_failure "graph_bound_requires_bound" 'import LeanPhy
open LeanPhy.Mathematics
noncomputable def graphMap : DenseDomainOperator (𝕜 := ℂ) (E := ℂ) where
  domain := ⊤
  dense := by simpa using (dense_univ : Dense (Set.univ : Set ℂ))
  operator := (0 : (⊤ : Submodule ℂ ℂ) →ₗ[ℂ] ℂ)
def missingGraphBound : DenseDomainOperator.GraphBoundCertificate graphMap
    graphMap.operator 0 0 where
  a_nonneg := by norm_num
  b_nonneg := by norm_num'

expect_failure "self_adjoint_requires_adjoint_equality" 'import LeanPhy
open LeanPhy.Mathematics
noncomputable def selfAdjointMap : DenseDomainOperator (𝕜 := ℂ) (E := ℂ) where
  domain := ⊤
  dense := by simpa using (dense_univ : Dense (Set.univ : Set ℂ))
  operator := (0 : (⊤ : Submodule ℂ ℂ) →ₗ[ℂ] ℂ)
def missingAdjointEquality : DenseDomainOperator.SelfAdjointCertificate selfAdjointMap := {}'

expect_failure "renormalization_requires_limit" 'import LeanPhy
open LeanPhy.Mathematics
def badRenormalization : RenormalizationCertificate
    (fun _ : ℕ => (0 : ℝ)) (fun _ : ℕ => (0 : ℝ))
    (fun _ : ℕ => (0 : ℝ)) 0 where
  relation := by intro n; norm_num'

expect_failure "spectral_gap_requires_strict_contraction" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
def badGap : SpectralGapCertificate
    (0 : ℂ →L[ℂ] ℂ) (0 : ℂ →L[ℂ] ℂ) 1 where
  rho_nonneg := by norm_num
  rho_lt_one := by norm_num
'

expect_failure "polynomial_action_requires_eigenvector" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
open Polynomial
example (A : ℂ →L[ℂ] ℂ) (v : ℂ) (p : Polynomial ℂ) :
    polynomialAction A p v = p.eval 0 • v := by
  apply polynomialAction_apply_eigenvector
'

cd "${BUILD_ROOT}"
lake env python3 "${PROJECT_ROOT}/scripts/run_negative_tests.py" \
  "${TMP_ROOT}" --jobs "${LEANPHY_NEGATIVE_JOBS:-8}" \
  --timeout "${LEANPHY_NEGATIVE_TIMEOUT:-600}"
