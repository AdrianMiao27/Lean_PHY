# Verified versus assumed

LeanPhy is meant to be used as a *reliable verifier* of theoretical-physics
derivations.  That claim is only meaningful if the boundary between what the
kernel actually proved and what was taken as input is written down.  This file
is that record.  It is kept in step with the modules under `LeanPhy/`.

## The one invariant

Every theorem in this repository is checked by the Lean 4 kernel against
mathlib.  There is **no `sorry` and no `axiom`** anywhere in the library or
in the acceptance test `Main.lean`.  You can re-check this yourself:

```bash
lake build                      # every file must compile
lake exe leanphy_smoke          # prints the capability report
lake exe leanphy_prototype      # runs the compact end-to-end workflow
lake exe leanphy_check          # renders the eight proof-bearing theory packages
lake exe leanphy_check --json   # emits the same compiled ledgers as JSON
grep -rn 'sorry\|admit\|axiom' LeanPhy Main.lean Prototype.lean   # only prose in comments
```

The semantics are **conditional correctness**: a theorem always has the shape
"given these hypotheses, this conclusion follows".  LeanPhy never claims
physical truth, convergence of a limit, or the validity of an unbounded-operator
or path-integral manipulation.

The current acceptance report contains **469 kernel-checked smoke
capabilities** and 140 negative elaboration fixtures.  Recent cross-domain additions are:

- `LeanPhy.Mathematics.SymmetryReduction`: constrained state predicates,
  group-orbit equivalence, physical-state quotients, orbit-invariant
  observables, and equivariant finite dynamics.  The preservation and
  invariance proofs are explicit and kernel-checked.  The module does not
  construct gauge fixing, quotient regularity, anomaly cancellation, or a
  physical interpretation of the symmetry.

- `LeanPhy.Mathematics.ConstraintAlgebra`: a commutative Poisson algebra can
  declare constraint generators, their generated ideal, first-class closure,
  weak equality modulo that ideal, and the Dirac-observable normalizer.  The
  kernel checks closure of the constraint ideal and of Dirac observables under
  the algebraic operations exposed by the module.  Constraint classification,
  gauge fixing, quotient regularity, Hamiltonian flow, and physical reduction
  remain separate obligations.

- `LeanPhy.Mathematics.ConstraintMap`: a composable Poisson algebra map can
  preserve the generated constraint ideal and therefore transport weak
  equality.  Dirac-observable transport requires an explicit witness that the
  target constraint ideal is covered by the image of the source ideal.  The
  module does not infer surjectivity, gauge fixing, quotient regularity,
  anomaly cancellation, or physical equivalence.

- `LeanPhy.Mathematics.BRST`: an explicit derivation together with a
  kernel-checked nilpotency proof defines closed, exact, and cohomologous
  elements.  Optional Poisson compatibility closes brackets of closed
  elements, and explicit preservation of a constraint ideal transports weak
  equality.  This is an ungraded algebraic seed.  It does not provide ghost
  number, Koszul signs, a BV antibracket, a gauge-fixing fermion, a path
  integral measure, anomaly cancellation, or a theorem identifying BRST
  cohomology with physical observables.

- `LeanPhy.Mathematics.OperatorConvergence`: uniform operator-norm and strong
  operator convergence certificates.  A radius tending to zero yields
  vector-level and bounded-observable limits, while the strong form records
  pointwise convergence directly.  These interfaces cover Galerkin, lattice,
  finite-volume and regulator approximations; they do not infer compactness,
  spectral convergence or a continuum limit.

- `LeanPhy.Mathematics.EnergyDissipation`: integrated energy and residual
  budgets for dissipative PDE, finite-volume schemes, Langevin dynamics and
  turbulence closures.  Nonnegativity and interval integrability are explicit
  fields, and residuals remain part of the final error bound.  The certificate
  does not construct a PDE solution or prove well-posedness.

- `LeanPhy.Mathematics.UnboundedOperator`: dense-domain operators, symmetry on
  the declared domain and two-sided domain-valued resolvents.  The inverse is
  stored as actual domain data, so uniqueness is kernel-checked.  The
  `LinearPMap` bridge exposes mathlib's graph and formal-adjoint API without
  erasing the declared domain.  Closedness, closability, self-adjointness,
  graph-norm relative bounds, and bounded domain-preserving composition are
  available as explicit certificates.  Essential self-adjointness, general
  self-adjoint extensions, Stone's theorem, spectral measures, and resolvent
  existence remain separate obligations.

- `LeanPhy.Mathematics.Renormalization`: regulator-wise bare/counterterm/
  renormalized relations, supplied renormalized limits, limit uniqueness and
  scheme-independence lemmas.  The module accepts explicit limits and vanishing
  scheme differences; it does not construct a path measure, prove BPHZ or
  establish a non-perturbative QFT limit.

- `LeanPhy.HighEnergy.EffectiveTheory`: finite EFT expansions expose an explicit
  amplitude/retained-amplitude decomposition, a power-counting tail bound,
  and a coefficient-matching `ErrorCertificate` for bounded finite observables.
  The module does not construct a UV completion, a continuum limit, or a
  regulator-independent matching theorem.

- `LeanPhy.Mathematics.Contraction`: `ContractionCertificate` wraps the Banach
  contraction theorem for nonempty complete metric spaces.  The kernel checks
  the unique fixed point, convergence of Picard iterates, a priori and
  a posteriori error bounds, and the `C / (1 - K)` stability bound under a
  uniformly perturbed map.  `InvariantContractionCertificate` handles a
  complete forward-invariant subset.  Contractivity and model adequacy remain
  explicit hypotheses; this is an analytic fixed-point bridge, not a theorem
  that a physical RG or turbulence map is contractive.

- `LeanPhy.Mathematics.InfiniteSpectrum`: in addition to checked two-sided
  resolvents and the resolvent identity, `resolvent_perturbation_bound` turns
  explicit inverse and operator-difference norm envelopes into the quantitative
  estimate `‖R_A - R_B‖ ≤ r_A * δ * r_B`.  `resolvent_of_neumann` additionally
  turns the explicit condition `‖A‖ < 1` into a checked inverse for `1 - A`.
  Both results are conditional on every displayed bound; they do not infer a
  numerical spectrum from sampled data or extend to unbounded operators.

- `LeanPhy.Mathematics.SpectralCalculus`: bounded complex operators now have a
  kernel-checked polynomial spectral-mapping theorem, the Gelfand spectral-radius
  limit, and a polynomial-on-eigenvector action rule.  A finite-dimensional
  symmetric linear operator can additionally be packaged as a certificate exposing
  a real eigenvalue list, orthonormal eigenbasis, characteristic-polynomial and
  determinant identities, with optional explicit interval bounds.  This bridge is
  intentionally limited to bounded operators and polynomial functions: it does not
  implement a general Borel functional calculus, spectral measures, unbounded
  self-adjoint spectral theory, or infer eigenvalue bounds from numerical samples.

- `LeanPhy.Mathematics.SpectralGap`: an explicit invariant projection and
  one-step residual contraction yield a geometric bound for every discrete
  iterate, convergence to the projected state, and convergence after any
  bounded linear observable.  This is a reusable certificate for mixing and
  dissipative finite models; it does not construct the projection from sampled
  eigenvalues, prove semigroup generation, or establish a thermodynamic-limit
  gap.

- `LeanPhy.Mathematics.Hilbert.FlowNormCertificate`: an explicit time-indexed
  operator-norm envelope for a bounded semigroup yields checked state-norm and
  composition bounds.  This is a stability contract; continuity, generators,
  positivity and unbounded domains remain separate hypotheses.

- `LeanPhy.Mathematics.ContinuousEvolution`: `IntervalIntegralCertificate`
  records Bochner interval integrability and an integral equality, with checked
  add/scalar/map constructors. `VariationOfConstantsCertificate` records the
  supplied Duhamel endpoint identity and forcing integrability; together with a
  `FlowNormCertificate` and `SourceNormCertificate`, `norm_error_le` derives
  the explicit convolution bound. The module never constructs an ODE/PDE
  solution or hides generator, domain, or continuity assumptions.

- `LeanPhy.Mathematics.Model`: `PhysicalModel` binds admissible states,
  proof-preserving evolution and typed observables. `ModelMap` requires both
  a dynamics intertwining proof and an observable pullback proof; composition,
  independent products, invariant pullback and finite-time readout transport
  are checked once in the shared layer. `QuantumInfo.Model` and `StatMech.Model`
  connect finite CPTP/Kraus channels and stochastic kernels to this interface.
  A model map is an exact simulation under its hypotheses, not an automatic
  assertion of physical equivalence or convergence of a truncation. Product
  models here are Cartesian independent systems, not general quantum tensor
  products with entangled states.

- `LeanPhy.Mathematics.ApproximateModel`: `ApproximateModelMap` records a
  state-map Lipschitz modulus, target-step stability, one-step residuals and
  observable residual/Lipschitz certificates. `stateRadius`, `iterate_error`
  and `evaluate_error` propagate these budgets over every finite horizon.
  `ApproximateModelMap.compose` composes two adapters while retaining the
  intermediate state error; `toExact` requires zero radii plus an explicit
  separation proof for the pseudometric spaces before producing an exact
  `ModelMap`. This is a finite error contract for truncations and
  discretisations, not a convergence or continuum-equivalence theorem.

- `LeanPhy.Mathematics.ParametricModel`: `ParametricModel` represents families
  indexed by couplings, temperatures, mesh sizes or truncation labels while
  keeping state and observable representations typed. `ParametricModelMap` and
  `ParametricApproximateMap` lift finite-time transport and explicit error
  propagation pointwise in the parameter; `UniformBudget` gives a common
  finite-horizon bound only after one is supplied for every parameter and
  initial state. QuantumInfo and StatMech expose parameter-family constructors.
  This layer does not infer parameter continuity, limits or physical calibration.

- The negative elaboration suite is executed by
  `scripts/run_negative_tests.py`: it runs the 140 independent fixtures in
  parallel, accepts only a source-located Lean elaboration error, rejects
  import/API/compiler failures, and cleans up child compiler groups on
  interruption. This keeps a broken regression fixture from being reported as
  a proof-safety success.

- `LeanPhy.Dimensions`: `Quantity` now supports dimension-changing division,
  explicit inverse and natural powers, together with coefficient scalar action
  and reusable frequency/momentum/energy/action/charge aliases.  The inverse is
  intentionally a function with result type `Quantity (-d) α`, so Lean's
  same-type `Inv` shortcut cannot erase a physical dimension.

- `LeanPhy.Workflow`: `TheoryPackage` keeps assumptions, heterogeneous
  proof-bearing claims and explicit scope boundaries in one reusable research
  ledger. `TheoryPackage.ofModel`, `addTheorem`,
  `addTheoremWithAssumptions`, proof-producing `addDerivedTheorem`/
  `addDerivedTheorem2` and `append` support replacing
  a model or combining independent packages without changing the reporting
  interface. Eight compiled adapters cover quantum, finite PDE/Euclidean,
  classical, gauge, condensed-matter, relativity and statistical-mechanics
  layers; `lake exe leanphy_check` reports their conditional status and
  `--json` emits a machine-readable projection with theorem provenance and
  unresolved-assumption-link, claim-dependency and open-obligation diagnostics. A
  claim cannot be inserted without its Lean proof field; optional assumption
  names are rendered as audit cross-references and do not replace hypotheses.
  The report
  executable only renders compiled metadata. The copyable
  `LeanPhy.Examples.ResearchPackageTemplate` demonstrates the same interface
  for a new domain.
  `addTheoremUnderAssumptionRegistered` combines typed-assumption registration with
  proof consumption; `resolveObligation` closes an external obligation only after a
  membership proof and a new kernel-checked claim are supplied.

- `LeanPhy.Mathematics.FiniteProcess`: `StateMap.compose_assoc` and
  `Process.iterate_add` make proof-preserving finite dynamics compositional.
  Quantum channels, Markov kernels, positive lattice steps and finite unitaries
  share this interface, while `ObservableTransport` composes expectation and
  Heisenberg pullbacks.

- `LeanPhy.Workflow.AssumptionWitness`: when a model assumption is available
  as an explicit proposition, `addAssumptionWitness` records its metadata and
  `addTheoremUnderAssumption`/`addTheoremUnderAssumptions2` pass the witness
  proof into the derived theorem.  This closes the proof-level link between a
  named assumption and a claim; metadata-only assumptions remain available for
  genuinely external physical or analytic premises.

- `Mathematics.ExternalCertificate`: external CAS or numerical output is kept
  as a provenance-bearing `CertificateEnvelope`. A `CertificateChecker` must
  prove its `sound` theorem before `VerifiedCertificate.proof` can be inserted
  into a `CheckedClaim`; a returned runtime Boolean is never evidence. The
  matrix equality adapter is data-only and receives the checker proof
  separately. `ResearchProject` additionally audits `package::claim` links and
  duplicate package names. `LeanPhy.Minimal`, `Entry.Quantum`,
  `Entry.FieldTheory`, `Entry.Condensed`, `Entry.Gauge`, `Entry.HighEnergy`,
  `Entry.Classical`, `Entry.Relativity`, `Entry.StatMech`, `Entry.FinitePDE`,
  `Entry.Analysis` and `Entry.Research` provide selective import profiles.
  `encodeEnvelope` and
  `decodeEnvelope` add a typed JSON data boundary; decoding never creates a
  `VerifiedCertificate` without a separate checker proof.

- `ResearchProject.addDerivedTheorem` and `addDerivedTheorem2`: a target
  package can consume one or two source-package `CheckedClaim.proof` terms.
  Qualified dependencies are generated automatically, and a missing source
  package/claim makes the assembled project invalid rather than silently
  accepting metadata-only provenance.

- `LeanPhy.Examples.ClosedLoop`: `lake exe leanphy_prototype` compiles and
  reports one finite oscillator identity, one shared evolution/energy bound,
  one two-node finite-difference heat step with maximum-principle and mass
  certificates, one positive finite path measure and one reflected weighted
  Gram proof.  The
  executable is a workflow check; the actual obligations are theorem fields
  in `VerifiedPrototype` and are checked by the kernel during compilation.

- `Mathematics.Approximation`: finite truncations, finite-volume or lattice
  replacements, and numerical equation residuals are represented by explicit
  nonnegative distance bounds.  The kernel checks triangle-inequality
  composition, additive error budgets in seminormed groups, and transport
  through a user-supplied Lipschitz certificate; no convergence, continuum
  limit or stability estimate is invented.

- `Mathematics.ApproximationBridge`: `CrossSpaceApproximation` makes the
  reconstruction map between two different Lean types explicit, then reuses
  the ordinary error-certificate lemmas for observables and multistage
  discretisations.  `ReconstructionBridge` supplies a zero-radius certificate
  only after an explicit encode/decode round trip has been proved.  This is a
  reusable boundary for truncated Fock spaces, lattice-to-continuum maps,
  finite-band interpolation and thermodynamic post-processing; it does not
  identify two representations or infer a limit theorem implicitly.

- `Mathematics.ApproximationAdapters`: quantum state/operator, field-theory
  mode, gauge-lattice, condensed band/lattice, statistical finite-volume and
  classical discretisation names are aliases of the same certificate API, so
  downstream proofs can move between subfields without changing the trusted
  semantics.

- `Mathematics.CertifiedResidual`: approximate matrix eigenpairs and one-step
  equation defects are explicit `ErrorCertificate` bounds, with vocabulary
  aliases for QM, BdG, transfer matrices, finite modes and ODE discretisation.
  The interface does not infer spectral error or convergence.

- `Mathematics.FiniteDivergence`: an arbitrary finite oriented graph has a
  kernel-checked incoming-minus-outgoing divergence whose total cancels on
  internal edges.  `ConservationCertificate` records a pointwise continuity
  equation and derives the zero-total source constraint; gauge-lattice,
  condensed-matter, finite-volume, statistical and measurement-flow aliases
  reuse this theorem.  Boundary fluxes and continuum divergence results remain
  explicit inputs.

- `StatMech.FiniteCurrent`: a finite Markov kernel and input distribution
  induce a current on the complete directed state graph.  Its divergence is
  definitionally checked as `K.step p - p`, so the Markov step receives a
  `ConservationCertificate` and a zero-total source theorem from the common
  incidence layer.  Continuous-time processes, stationary limits and mixing
  estimates remain outside this finite bridge.

- `Mathematics.ConservationResidual`: local continuity equations may carry
  explicit nonnegative residual radii.  The kernel derives
  `|∑ source| ≤ ∑ radius` and the cardinality-scaled uniform-radius bound,
  providing a shared error budget for finite-volume, lattice, truncated-field,
  Markov and measurement calculations without inferring convergence or
  stability.

- `Mathematics.FiniteRepresentation`: finite monoid/group actions are stored
  as matrix homomorphisms.  Characters are invariant under conjugation,
  representations pull back along homomorphisms, intertwiners compose, and a
  unitary representation proves inverse equals adjoint.  These are shared
  algebraic contracts for gauge, particle, point-group and quantum-symmetry
  adapters; irreducibility and Haar/Schur analysis are not inferred.

- `Mathematics.FiniteGroupAverage`: finite group sums are invariant under left
  and right reindexing.  For any finite matrix representation, the conjugation
  twirl is invariant under the represented group and commutes with it.  Quantum
  twirling, finite gauge averages and point-group orbit sums therefore share
  one proof, while Haar measure and compact-group analysis remain external.

- `Workflow.ExternalObligationWitness`: an open obligation may carry an
  explicit Lean proposition.  `resolveObligationWitness` removes it only after
  a proof of that proposition is consumed by the derived claim; metadata-only
  obligations remain available for genuinely unformalised analysis.

- `Mathematics.FiniteChainComplex`: finite boundary tables carry an explicit
  boundary-of-boundary cancellation certificate.  The kernel derives the
  boundary and coboundary square-zero laws, a finite discrete Stokes pairing,
  and vanishing of an exact cochain on an explicitly supplied cycle.  Lattice
  gauge, Berry meshes, finite elements and network models use the same
  contract; homology, Chern quantisation, integration and continuum limits
  remain outside the finite theorem.

- `Mathematics.FiniteChainAdapters`: the incidence boundary of a finite
  directed graph is connected by an equality theorem to the existing finite
  divergence contract.  A conservation certificate can therefore be consumed
  as a chain-boundary equation, with domain aliases for gauge, hopping,
  finite-volume and network calculations.

- `StatMech.FiniteDetailedBalance`: a pairwise detailed-balance certificate for
  a finite kernel proves stationarity of the reference finite probability and
  symmetry of the kernel pullback in the weighted expectation pairing.  The
  module does not infer irreducibility, mixing, spectral gaps or any
  continuous-time limit.

- `StatMech.FiniteDirichlet`: defines the finite Dirichlet energy associated
  with a probability and a row-normalized nonnegative kernel.  The kernel
  proves symmetry in the observables, nonnegative quadratic energy, vanishing
  on constant observables and bilinearity in each slot.  This is the shared
  finite algebraic layer for reversible Markov, lattice hopping, graph,
  finite-element and measurement post-processing models.  Reversibility,
  spectral gaps, Poincare inequalities, mixing rates and continuum limits are
  not inferred.

- `StatMech.FiniteDirichletLaplacian`: defines the finite discrete Laplacian
  `I - K` and proves, under detailed balance, that the edge Dirichlet form is
  exactly the probability-weighted pairing with that Laplacian.  This is an
  algebraic bridge between reversible Markov dynamics, graph/finite-element
  stiffness forms and lattice hopping.  Spectral-gap and continuum estimates
  remain outside the theorem.
- `Mathematics.FinitePathIntegral`: finite complex weighted path sums require
  an explicit nonzero partition certificate.  The kernel checks normalized
  expectations, finite reindexing and exact push-forward coarse graining;
  continuum measures, oscillatory limits, reflection positivity and RG
  universality are not claimed.  `fromAction` supplies complex action weights
  and proves normalized expectation invariance under a constant action shift;
  `fromRealAction` obtains a strictly positive finite Euclidean partition real
  part on a nonempty space, and `IsFixedPoint` records exact same-label finite
  blocking invariance without claiming a continuum critical point. A
  `ScalingCertificate` additionally proves finite insertion/expectation
  scaling for an explicit factor, with no hidden critical-exponent claim.
  For a real finite action, `fromRealAction_partition_lower_bound` turns any
  chosen configuration into the explicit positive bound
  `exp (-S i₀) ≤ ‖Z‖`, which can feed a normalized-error certificate; this
  construction does not extend to cancelling complex weights.

- `Mathematics.FiniteReflection`: a finite reflection certificate supplies a
  permutation of labels and an explicit Gram feature factorisation.  The kernel
  expands the reflected quadratic form into a finite sum of squares and proves
  its non-negativity.  This is a finite positivity certificate for lattice or
  truncated models; it does not prove the continuum
  Osterwalder--Schrader axiom, Hilbert-space reconstruction, existence of a
  continuous measure, or Euclidean QFT existence.  The kernel double-sum
  presentation is now proved equal to the supplied Gram square-sum
  factorisation, and the reflection involution is an explicit certificate
  field; this finite bridge still does not reconstruct a continuum theory.

- `Mathematics.FinitePathReflection`: a real nonnegative finite weight table
  constructs a complex finite path integral with a positive real partition
  part, while a weighted feature table proves the usual kernel double sum is a
  nonnegative weighted sum of squares.  `FiniteWeightedReflectionCertificate`
  combines these contracts and retains the reflection involution.  This is a
  reusable lattice/truncated-Euclidean adapter; positivity of a continuum
  measure and the Osterwalder--Schrader axioms remain external obligations.

- `Mathematics.FiniteEnergy`: `FiniteEnergyStep` requires a nonnegative energy,
  a nonnegative one-step amplification factor and an explicit one-step energy
  inequality.  The kernel propagates it to a finite-time factor-power bound and
  derives non-increase when the factor is at most one.  An explicit one-step
  equality constructs the factor-one conservation form.  Physics aliases make
  the same contract available to wave/PDE, Maxwell, lattice, BdG, dissipative
  and finite-mode adapters; no CFL condition, continuum energy identity,
  well-posedness result or mesh limit is inferred.

- `Mathematics.FiniteEnergy` also defines `FiniteEvolutionEnergyStep`, which
  binds one state step to both a discrete-Grönwall trajectory certificate and
  an energy amplification certificate.  The coupled theorems expose state
  error and exact-trajectory energy bounds from one shared step map; they do
  not infer a PDE energy estimate, CFL condition or continuum stability
  theorem.
- `Mathematics.FiniteElliptic`: finite incidence tables provide a `BᵀB`
  weak Laplacian.  Nonnegative energy, summation by parts, constant zero modes
  and exact Poisson/matrix-PDE residual certificates are checked; regularity,
  boundary-value theory, mesh convergence and continuum estimates remain
  external obligations.  An explicit `CoercivityCertificate` is sufficient
  for the finite uniqueness theorem, and `FiniteBoundaryData` records
  Dirichlet values without treating them as hidden assumptions.  A boundary
  coercivity certificate proves uniqueness on the homogeneous Dirichlet
  perturbation space.  `FiniteBoundaryResidualCertificate` records pointwise
  boundary error, while `FiniteEllipticApproximationCertificate` binds it to
  the equation residual, supports explicit budget combination and recovers an
  exact solution only when both radii are zero.  `FiniteEllipticCertificate`
  remains the exact-boundary form, while `FinitePDEResidualStability` turns
  that residual into a solution error only when the user supplies a
  residual-to-solution modulus; no mesh convergence or continuum stability is
  inferred.  A
  `FinitePDELeftInverseCertificate` can produce that stability object from an
  explicit finite left inverse, homogeneous-Dirichlet left-inverse identity
  and Lipschitz bound; the kernel does not infer an inverse or condition
  number.  `FiniteEllipticResidualStability` is the boundary-aware extension:
  it takes separate equation and boundary moduli plus an explicit total bound,
  and converts the joint certificate into one solution-error budget.  The
  boundary budget is a finite sum over marked nodes and is proved nonnegative;
  no continuous trace theorem or mesh estimate is hidden in it.

- `AdditiveLeftInverseCertificate`: a domain-neutral additive operator
  contract records a left inverse and Lipschitz modulus, then turns an
  operator `ErrorCertificate` into a checked `FiniteApproximation`.  Named
  adapters expose the same contract for quantum operators, field modes,
  lattice/gauge discretisations, condensed bands, transfer matrices and
  classical dynamics; no condition number or convergence theorem is inferred.

- `Mathematics.FinitePathApproximation`: numerical or truncated finite path
  integrals carry insertion and partition `ErrorCertificate`s, positive lower
  bounds for both exact and approximate denominators, and an upper bound for
  the approximate insertion.  The kernel derives an explicit normalized
  expectation error bound.  Pointwise weight certificates are aggregated into
  partition and insertion budgets before normalization.  The separate
  `ObservableApproximationCertificate` handles pointwise observable error, and
  `FiniteRGStep.coarse_approximation_certificate` assembles a full coarse
  weight certificate from those pointwise bounds.  No denominator stability
  beyond the supplied lower bounds, sampling concentration or continuum limit
  is inferred.

- `FiniteRGStep.coarsenMany`: a finite list of blocking maps is reduced to one
  auditable push-forward.  Partition sums, pulled-back insertions, normalized
  expectations and explicit finite scaling certificates compose over the list;
  this is not a continuum RG semigroup or a critical-exponent theorem.
- `FiniteRGStep.coarsen_weight_eq_pushforward_coarseWeight` and
  `coarsen_weight_assoc` check the intermediate-weight and coarse-map
  composition laws pointwise.  `ScalingCertificate.compose` combines two
  explicit finite operator-scaling hypotheses with factor `lambda * mu`;
  the intermediate scaling equation remains a required input.

- `Mathematics.FiniteParabolic`: `FinitePositiveStep` packages a nonnegative
  row-stochastic matrix and proves constant preservation, positivity and a
  finite discrete maximum principle for one step and all finite iterates.
  `MassConservationCertificate` separately supplies column sums to prove
  preservation of the unweighted total; row sums alone are not treated as a
  conservation law.

- `FinitePathIntegral.multiCorrelator`: a list of observables gives an
  explicit finite n-point insertion.  The kernel checks the empty insertion,
  permutation symmetry, product concatenation and exact coarse-map pullback;
  continuum time ordering and distributional products remain outside scope.

- `FinitePositiveStep.UniformError` is a componentwise absolute-error ledger
  for finite fields.  A nonnegative row-stochastic step is nonexpansive for
  this ledger, and the ledger composes by an explicit triangle budget.

- `FinitePositiveStep.TrajectoryCertificate` requires an initial error, an
  exact finite recurrence and a residual certificate at every step.  Its
  `bound` theorem produces the componentwise propagated radius at every finite
  time; no residual may be omitted during elaboration.

- `FiniteDrivenParabolic` extends the positive-step ledger to an explicitly
  forced update `u_(n+1) = K u_n + f_n`.  The kernel proves the nonhomogeneous
  maximum-value budget, cancellation of a common source term in the error
  difference, and the finite-time `DrivenTrajectoryCertificate` bound.  The
  certificate must contain the exact source recurrence and every approximate
  step residual; CFL conditions, continuous maximum principles and PDE
  stability are not inferred.

- `FiniteDrivenParabolic` also provides `SourceDrivenTrajectoryCertificate`:
  an independently approximated forcing field has its own pointwise error
  radius, which is added to the state and local-step budgets at every finite
  time.  Omitting the source-error field prevents construction of the
  certificate; this still says nothing about continuous forcing convergence.

- `FiniteSchwingerDyson` defines finite source polynomials, moments and an
  involutive variation with an explicit Jacobian.  A weight-balance field is
  required before the kernel derives the finite Schwinger--Dyson insertion and
  normalized expectation identity.  This does not provide a continuous
  functional derivative, integration-by-parts theorem or nonperturbative path
  integral.

- `FiniteRGDiagnostics` packages a pointwise finite RG fixed-point defect into
  partition-function and normalized-observable error certificates.  Exact
  fixed points have zero radius, while approximate conclusions require user
  supplied denominator lower bounds and insertion upper bounds.  Continuum
  fixed points, critical exponents, universality and RG convergence remain
  outside the verified layer.

- `FiniteRGDiagnostics.FixedPointDefect.compose` combines two consecutive
  finite blocking defects only when the second step's fine weights are
  explicitly identified with the first step's coarse weights.  The resulting
  pointwise and partition radii are the sum of both ledgers, so an intermediate
  numerical mismatch cannot be silently dropped.

- `FinitePathIntegral.WeightSymmetry` records pointwise invariance of finite
  weights under a permutation.  It proves insertion reindexing, expectation
  invariance and a zero weighted insertion difference, giving a finite Ward
  identity while leaving continuum changes of variables and anomalies
  explicit.

- `NormalizedExpectationCertificate`: a single-step normalized expectation
  error becomes a composable object.  `compose` adds nonnegative radii through
  the triangle inequality, and the RG coarse-weight constructor exposes its
  result through `coarse_expectation_certificate`; each denominator bound and
  insertion bound remains an explicit input.

- `ExpectationComparisonCertificate`: source and target finite configuration
  spaces and observables may have different types.  The kernel composes two
  comparisons through their shared intermediate observable, adding the two
  radii.  This is the finite error signal needed for a multi-level blocking
  chain; it does not certify that a continuum observable has been matched.

- `FiniteRGStep.coarsen_expectation_preserved`: a single blocking map may
  change the finite label type.  Partition and insertion preservation still
  yield an exact normalized-expectation equality after pulling the final
  observable back through the full map; no continuum RG law is inferred.

- `StatMech.ConductanceModel`: positive site weights and symmetric nonnegative
  conductances construct a normalized finite kernel and its equilibrium
  probability.  The kernel proves detailed balance and stationarity by
  cancellation, while Metropolis acceptance, irreducibility, mixing and
  thermodynamic/continuum limits remain explicit model obligations.  Hopping,
  gauge-lattice and reversible-network aliases reuse the same contract.
  `ConductanceModel.fromWeights` additionally constructs a rank-one symmetric
  conductance directly from any positive finite Gibbs weight family, providing
  a checked Gibbs-to-Markov bridge without hiding normalization assumptions.

- `Mathematics.FiniteResponse`: the finite weighted commutator response
  `Tr (rho [A,B])` expands into ordered correlators, is antisymmetric under
  probe exchange, is linear in its probes, vanishes under an explicit
  commutation certificate, and has the cyclic Kubo identity
  `Tr (rho [A,B]) = Tr ([rho,A] B)`.  Time ordering, response kernels,
  positivity and thermodynamic limits are not inferred.  Quantum-information,
  condensed-matter, statistical, high-energy and classical aliases share the
  same algebra.

- `Mathematics.FiniteChainComplex` additionally exposes `IsCycle2` and a
  closed-surface pairing theorem: an exact two-cochain has zero pairing on a
  supplied closed finite surface, so adding it leaves a discrete flux/Chern
  pairing unchanged.  Gauge, Berry/Chern, finite-element and discrete-fluid
  aliases reuse this identity; homology quotients and continuum Chern
  quantization remain outside the theorem.

- The cycle/cocycle portion of `Mathematics.FiniteChainComplex` is
  quotient-free by design: it defines finite cycles, boundaries, cocycles and
  exact cochains; proves boundary-is-cycle and exact-is-cocycle; and checks the
  degree-one Stokes identity.  Consequently a supplied cocycle annihilates
  every supplied boundary and a supplied exact cochain annihilates every
  supplied cycle.  Homology quotients, ranks and Chern quantisation are not
  inferred from these predicates.

- `Mathematics.DiscretePlaquette`: the oriented four-edge flux is invariant
  under an exact vertex shift and reverses sign only with a supplied edge
  antisymmetry law, so gauge, Berry, fluid and lattice adapters share one
  checked boundary identity.

- `Mathematics.Hilbert`: complete inner-product spaces carry bounded
  self-adjoint and two-sided unitary operators with kernel-checked expectation,
  inner-product and norm laws.  `matrixOperator` exposes finite matrices as
  bounded operators.  `Quantum.HilbertBridge` additionally checks matrix
  multiplication/composition and conjugate-transpose/adjoint equality, and
  transports finite unitary and Hermitian certificates to `EuclideanSpace`;
  the adapter is polymorphic over `RCLike`, so real classical/relativistic
  matrices and complex quantum matrices use the same checked construction;
  unbounded domains, spectral measures and time evolution remain explicit
  analysis obligations.

- `Mathematics.LinearFlow`: `FiniteMatrixFlow` checks zero-time, semigroup
  composition, vector propagation and inverse matrix-exponential evolution
  over real or complex `RCLike` scalars.  `Quantum.HamiltonianFlow` instantiates
  this interface; the module does not infer ODE differentiability, positivity,
  stability or a continuum limit.

- `Mathematics.FlowInvariant`: a commuting observable is fixed by a finite
  matrix-exponential conjugation.  The theorem is shared by quantum,
  classical, BdG, transfer-matrix and finite-mode field-theory vocabulary
  aliases; it requires an explicit commutation certificate and checked inverse
  law, and does not infer stability, positivity or continuous-time dynamics.

- `FieldTheory.FermionicWick`: the finite four-point fermionic contraction is
  the sign-correct Pfaffian, with adjacent-slot antisymmetry and zero-diagonal
  repeated-slot exclusion.  It is a finite CAR/BdG/QFT algebra kernel; it does
  not assert Grassmann integration, time ordering or continuum Fock theory.

- `Mathematics.DiscreteHigherCochain`: the alternating finite `d₁` and `d₂`
  operators satisfy `d₂ d₁ = 0`, and finite face sums are congruent under
  pointwise equality.  This is a reusable discrete Bianchi layer for gauge,
  Berry, fluid and finite-element models; topology and integration are not
  inferred.

- `Mathematics.PeriodicPlaquette`: two commuting finite translations define a
  periodic plaquette curl.  The kernel checks exact vertex-gauge invariance,
  total-curl telescoping and zero curl for an exact potential; transition
  patches and Chern quantisation remain explicit higher-level inputs.

- `FieldTheory.MultiWick`: a finite covariance-kernel recursion over typed
  bosonic field slots.  The four-slot result expands all three pairings.  It
  does not assert time ordering, distributional products, fermionic signs,
  renormalisation or a continuum limit.

- `FieldTheory.MultiCAR`: finite fermionic mode families carry explicit CAR
  relations and the kernel proves the individual and total number-operator
  ladder identities.  Fock completion, domains and continuum distributions
  are not inferred.

- `Mathematics.Winding`: an integer lift on a finite permuted cycle can carry a
  checked winding/flux/circulation value.  Integer gauge coboundaries preserve
  that value.  This is a finite certificate for Berry, lattice-gauge and fluid
  adapters; Chern integrals and continuum homotopy classes remain outside it.

- `Mathematics.Holonomy`: endpoint-indexed finite paths compose associatively;
  group-valued transport composes, open paths transform by endpoint
  conjugation, closed holonomies transform by base-point conjugation, and
  Abelian or class-function observables are gauge invariant.  The legacy
  four-link Wilson plaquette is connected to this generic path API.  This is a
  finite algebraic bridge for lattice Wilson loops, discrete Berry phases and
  graph connections; path-ordered exponentials, continuum limits and Chern or
  winding integrals remain explicit future layers.

- `Condensed.Berry.discreteBerryHolonomy`: finite-mesh Berry link products
  reuse the same Abelian closed-path theorem; smooth eigenvector patches and
  Chern-number integration remain explicit analytic/topological obligations.

- `Mathematics.AdditivePath`: additive link transport, endpoint gauge
  telescoping and the additive plaquette-flux bridge are checked for every
  closed finite path.  This is the common finite layer for lattice flux,
  discrete one-forms and angle-valued phases.

- `Mathematics.DiscreteCochain`: arbitrary vertex/edge/triangle labels carry
  `d0` and oriented `d1`; the kernel proves `d1(d0 φ)=0`, exact fields are
  closed, and curvature is unchanged by an exact gauge shift.  Maxwell's
  finite-difference adapter and the discrete Berry-curvature adapter reuse
  these theorems.

- `DiscreteCochain.cycleSum`: a finite permutation-indexed cycle sum cancels
  every additive gauge coboundary.  This is only a finite algebraic flux
  certificate; winding numbers, Chern integers and continuum integration still
  require separate topological hypotheses.

- `Classical.discreteVorticity`: lattice/network velocity one-forms reuse the
  exact-shift invariance of the cochain curvature.  This connects the fluid
  adapter to the same kernel theorem used by discrete Maxwell and Berry layers;
  Navier--Stokes dynamics and continuum limits remain outside the module.

- `Quantum.SpectralGap` and `Quantum.ParametricSpectralGap`: explicit
  two-sided finite resolvents are equivalent to nonzero determinants and
  exclusion from the finite spectrum; quadratic operator relations yield
  certified inverse formulas and real interval gaps.  Finite unitary
  similarity preserves the gap, and one radius can be checked uniformly over
  a finite momentum, flavor, boundary or volume family.  The real BdG and
  real Bloch modules instantiate this family interface.  Continuity,
  compactness and thermodynamic-limit gaps remain explicit analysis inputs.

- `Quantum.FiniteDensity`: the common `IsFiniteDensity` predicate and
  `FiniteDensity` bundle identify `IsDensity` and `IsNamedDensity` as the same
  finite matrix invariant; finite-unitary conjugation and named Kraus channels
  preserve it for any finite label type.

- `Quantum.HamiltonianFlow`: a finite Hermitian Hamiltonian produces the
  matrix exponential `exp(i t H)` as a unitary; time addition, trace and
  positive-semidefinite preservation are checked.  If `[H,O]=0`, the finite
  Heisenberg conjugation fixes `O`.  This is a finite matrix theorem; it does
  not assert Stone's theorem, unbounded-operator dynamics or a continuum
  limit.

- `QuantumInfo.Measurement`: one-Kraus-per-outcome and finite general
  multi-Kraus instruments, branch positivity, Born traces, total normalization
  and normalized conditional states;
- `Mathematics.LieRepresentation`: a reusable linear Lie-algebra/
  representation interface whose explicit compatibility field transports the
  Jacobi identity to matrices or operators;
- `Mathematics.LieAdapters`: the coefficient-space `su(2)` bracket and the
  explicit spin-one matrix family are packaged as a concrete representation;
  a table-level Jacobi theorem is shared by the Lorentz and colour families;
  the explicit Lorentz `so(3,1)` family is also packaged with its structure
  constants;
- `QuantumInfo.Channel`: every finite Kraus family has a kernel-checked
  ancillary extension `I ⊗ K` that preserves positive semidefiniteness, giving
  the finite complete-positivity property used by CPTP calculations;
- `QuantumInfo.KrausBundle`: `KrausChannel` stores the completeness relation,
  derives trace preservation and finite complete positivity, and composes with
  a product Kraus family whose completeness is checked by the kernel.
- `QuantumInfo.Heisenberg`: the finite dual action
  `A ↦ sum_i K_i† A K_i` satisfies the trace-pairing identity, is unital under
  Kraus completeness, and reverses product-channel composition.
- `QuantumInfo.POVMDistribution`: a finite POVM applied to a density matrix is
  packaged as a normalized finite classical distribution, allowing measurement
  outcomes to reuse the statistical and Markov APIs.
- `StatMech.Entropy`: finite second moments and collision probability are
  exposed as a shared algebraic API.  Nonnegativity, the `[0,1]` bound and the
  uniform-distribution value are kernel-checked; logarithmic Renyi entropy and
  continuum entropy remain explicit analysis boundaries.  The POVM adapter
  exposes the same collision probability for measurement outcomes.
- `StatMech.FiniteProbability`: the same finite probability semantics now work
  over any `Fintype` outcome type, with expectation, second moments and
  collision bounds.  This avoids encoding named lattice, spin, band, or colour
  labels as `Fin n` merely to use the probability API.
- `StatMech.FiniteKernel`: arbitrary finite labels support normalized state
  push-forward, observable pullback, composition, and preservation of the
  uniform state for doubly-stochastic kernels.
- `StatMech.TransferKernel`: arbitrary finite nonnegative transfer weights with
  positive row sums normalize to a finite Markov kernel; probability
  preservation and the expectation pullback identity are checked through the
  shared kernel API.  Perron--Frobenius asymptotics and thermodynamic limits
  remain outside the finite layer.
- `StatMech.FiniteGibbs`: arbitrary finite labels support positive partition
  functions, normalized Gibbs probabilities and invariance under an additive
  energy shift; thermodynamic limits remain outside the layer.
- `Quantum.NamedChannel`: arbitrary finite label types support Kraus CPTP
  maps, an explicit finite ancillary complete-positivity property, density
  preservation and channel composition.  A Gibbs state represented in a named
  basis can therefore pass through the same channel invariant.
- `QuantumInfo.TypedChannel`: rectangular Kraus operators `Matrix κ ι ℂ`
  support channels whose input and output labels differ.  Input completeness
  proves output positivity, trace preservation, finite-density transport and
  composition across an intermediate finite space.  The same module checks
  the cross-dimensional Schrödinger/Heisenberg trace pairing and dual
  unitality; this remains a finite matrix adapter rather than an
  infinite-dimensional trace-class theorem.
- `Quantum.NamedClassical`: finite Markov state propagation on named labels is
  embedded into diagonal density matrices, with expectation pullback and
  purity/collision identities checked by the kernel.
- `Quantum.DiagonalState`: a finite classical distribution is embedded as a
  diagonal density matrix; its trace, positivity, matrix purity and diagonal
  observable expectations are identified with the corresponding classical
  normalization, collision probability and finite expectation.  This is a
  finite interoperability adapter, not a claim about general spectral theory.
- `QuantumInfo.POVMDistribution`: the preceding adapter is composed with a
  finite POVM, so its classical output distribution can be viewed as a diagonal
  state whose matrix purity is the measurement collision probability.
- `Quantum.Unitary`: finite unitary operators preserve ket inner products and
  density-matrix validity; conjugation and unitary composition are checked by
  the kernel; the corresponding finite Schrödinger/Heisenberg trace pairing
  is also checked.
- `QuantumInfo.UnitaryChannel`: a finite unitary is exposed as a singleton
  Kraus/CPTP channel, reusing trace, positivity and channel-composition laws;
  its state-level composition agrees with direct unitary conjugation.
- `Particles.ckm_unitaryOperator`: converts CKM right-unitarity into the shared
  `UnitaryOperator` object used by finite quantum dynamics.
- `Quantum.FiniteUnitary`: a generic finite-index unitary structure with a
  kernel-checked tensor-product constructor and inner-product-preserving
  finite-index evolution.
- `Mathematics.BilinearIsometry`: a generic finite `Aᵀ G A = G` structure with
  kernel-checked composition closure.
- `Mathematics.FiniteFourier`: a finite complex kernel with explicit left and
  right orthogonality has a kernel-checked forward/inverse transform; concrete
  roots of unity and continuum limits remain explicit inputs; the two-point
  Hadamard and four-point periodic kernels are concrete checked instances; the
  same interface proves the unnormalised finite Parseval identity.
- `FiniteFourierSystem.normalizedUnitary`: an explicit normalization
  hypothesis produces a generic finite unitary; the four-site periodic
  instance is checked.
- `Quantum.SpectralModels`: computational qubit projectors form a complete
  finite spectral family, reconstruct Pauli Z, and certify both eigenvalue
  branches; the adapter is reusable for two-band and BdG models.
- `Quantum.SpectralDecomposition`: complete pairwise-orthogonal finite
  projector families reconstruct operators and act with the prescribed
  eigenvalue on each projector range; spectral existence is kept explicit.
- `QuantumInfo.Lindblad`: the finite-dimensional Hamiltonian plus dissipator
  generator has zero trace for every matrix, proved from cyclicity; positivity
  of a generated semigroup and master-equation existence remain explicit
  analytic obligations;
- `GaugeTheory.Maxwell`: the Abelian potential construction proves
  antisymmetry, gauge invariance under commuting derivations and the cyclic
  Bianchi identity.  Its component field strength is definitionally the
  `Mathematics.Exterior` finite `d` of a one-form, and a second theorem
  reuses the generic `d² = 0` result to reprove the cyclic identity;
  smoothness and PDE existence remain outside the algebraic layer;
- `Mathematics.Exterior`: finite one-, two- and three-form coefficient APIs,
  commutative-coefficient wedge antisymmetry, and a finite `d² = 0` theorem
  under an explicit commuting-derivation hypothesis.  This shared algebraic
  layer is intended for Maxwell, discrete differential forms and future
  geometric/fluid adapters; manifolds, integration and regularity are not
  inferred;
- `Classical.Vorticity`: a finite/discrete velocity one-form is mapped to
  vorticity `d u`; its closedness and exact-potential-shift invariance reuse
  the exterior layer. Navier--Stokes dynamics, Hodge theory and continuum
  limits remain outside the algebraic module;
- `GaugeTheory.YangMills`: a noncommutative matrix-valued connection carries
  explicit Leibniz derivations; `dA + [A,A]`, the adjoint covariant derivative,
  curvature antisymmetry and the covariant Bianchi identity are checked by the
  kernel.  Gauge-group global analysis remains outside the layer;
- `Mathematics.AlgebraicDerivation` and `Mathematics.NoncommExterior`: the
  additive Leibniz interface and finite-index noncommutative connection are
  separated from the four-dimensional adapter. Curvature antisymmetry and the
  covariant Bianchi identity are proved for arbitrary finite index sets, and
  `YangMillsConnection.bianchi_via_noncommExterior` reuses that theorem;
  `innerDerivation` supplies a concrete commutator action, and
  `innerConnection` constructs a finite connection when its generators
  commute pairwise;
- `Quantum.Spectral`: finite characteristic-polynomial monicity, degree and
  Cayley–Hamilton are exposed alongside exact eigenvector and ladder results;
- `Quantum.HermitianSpectrum`: the mathlib Hermitian spectral theorem is
  exposed for finite operators and density matrices; density eigenvalues are
  nonnegative, sum to one, and have an explicit unitary diagonalization.
- `Quantum.NamedFinite`: arbitrary finite basis labels index diagonal density
  matrices and observables; named finite-state purity and expectation reduce to
  collision probability and classical expectation.
- `Quantum.NamedFinite` also exposes a finite Gibbs-to-density-state adapter:
  thermal expectations and purity reuse the generic finite Gibbs/probability
  interfaces.
- `StatMech.Probability`: finite normalized distributions, expectation
  linearity, positivity and variance nonnegativity;
- `Surface.HigherTensor`: rank-three/rank-four variance-aware contractions and
  compile-time rejection of same-variance contractions.
- `Mathematics.Derivation`: explicit Leibniz derivations, covariant curvature,
  antisymmetry and pointwise Bianchi identity;
- `Mathematics.Poisson`: a reusable Poisson-algebra interface with explicit
  bilinearity, Jacobi and Leibniz laws, plus conservation closure under
  products, powers, linear combinations and brackets.  The Hamiltonian action
  is packaged as a mathlib Leibniz derivation for reuse by continuum layers;
- `Classical.PolynomialPhaseSpace`: a concrete polynomial phase space whose
  commuting formal partial derivatives construct the canonical Poisson bracket
  and prove `{q,p}=1`.
- `Mathematics.PoissonAlgebra.hamiltonianDerivation_commutator`: Hamiltonian
  derivations reproduce the Poisson bracket under commutator, giving a checked
  classical Lie action.
- `Classical.PolynomialPhaseSpace`: the formal derivative construction is
  parameterized by any selected pair of variables in a larger polynomial
  algebra, not only the two-variable oscillator example.
- `Classical.PolynomialPhaseSpace`: the normalized polynomial oscillator has
  kernel-checked Hamiltonian equations `{H,q}=-p`, `{H,p}=q`, and conserved H.
- `Quantum.Spectral`: exact finite eigenvector, commuting-operator and ladder
  eigenvalue-shift theorems.
- `Classical.Lagrangian`: finite jet-polynomial total derivatives and the
  Euler–Lagrange residual; the oscillator gives `q+a=0`, while componentwise
  field/lattice jets reuse the same derivation constructor.
- `Quantum.Projector`: rank-one ket-bra projectors satisfy the Dirac action
  rule, positivity, Hermiticity, normalized idempotence and trace identities;
  spectral completeness remains an explicit analysis layer.
- `StatMech.Markov`: finite nonnegative row-normalized kernels preserve finite
  distributions, compose by finite sums, and doubly-stochastic kernels preserve
  the uniform state; ergodicity and mixing remain analysis assumptions.
- `StatMech.Gibbs`: a nonempty finite state space has a strictly positive
  partition function; Gibbs weights form a normalized finite distribution and
  are invariant under an additive shift of all energies.  Thermodynamic limits,
  entropy derivatives and phase transitions remain analysis assumptions.
- `StatMech.Entropy`: finite second moments and collision probability provide a
  common second-order interface for statistical and measurement distributions;
  nonnegativity, the `[0,1]` bound, the expectation identity and the uniform
  value are checked by the kernel.  Logarithmic Renyi entropy and continuum
  entropy remain outside the finite algebraic layer.

These modules widen the common layer used by quantum, gauge, high-energy,
condensed-matter, classical and statistical models.  Measurement instruments
remain finite-dimensional and use a finite internal Kraus index; complete
positivity on arbitrary ancillary systems, infinite-dimensional probability,
and entropy/capacity results remain explicit future layers.  The Lie
representation fields remain explicit model hypotheses.

As a stronger check than a text search, `#print axioms` on the load-bearing
theorems reports only Lean's three standard axioms — `propext`,
`Classical.choice`, `Quot.sound` — which are the same ones mathlib itself
rests on.  No theorem depends on `sorryAx`.  For example:

```
'LeanPhy.FieldTheory.Pairing.wick_pairing_count' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.HighEnergy.tr4_slash_mul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.HighEnergy.ward_identity' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.HighEnergy.mass_shell' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Condensed.CliffordPair.bogoliubov_rotation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Condensed.bdg_sq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.HighEnergy.SusyQM.H_commutator_Q' depends on axioms:
  [propext]
'LeanPhy.Einstein.einsum_mul_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.QuantumInfo.kraus_trace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.QuantumInfo.kraus_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.GaugeTheory.loop_conj' depends on axioms:
  [propext]
'LeanPhy.GaugeTheory.wilson_loop_invariant' depends on axioms:
  [propext]
'LeanPhy.Condensed.bloch_sq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.HighEnergy.mandelstam' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.StatMech.isingTransferMatrix_charpoly' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.GaugeTheory.bianchi' depends on axioms:
  [propext]
'LeanPhy.HighEnergy.sigma_antisym' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Particles.smGen_anomalyFree' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Particles.gm_fierz' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.HighEnergy.cov_fierz_expansion' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Quantum.pauli_twirl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Quantum.pauli_twirl_depolarise' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Particles.ckm_unitary' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.QuantumInfo.mermin_ghz_eigen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Relativity.boost_lorentz' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Condensed.berry_density' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Condensed.jwHop_eq_xy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Condensed.car_zero_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Quantum.spinOne_casimir' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Quantum.S3_commutator_Jplus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.QuantumInfo.no_cloning' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Relativity.B1_commutator_B2' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Relativity.metric_B3' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.QuantumInfo.stab1_code' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.QuantumInfo.xx2_syndrome1' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.QuantumInfo.teleportation_identity' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Tensor.raise_lower' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Tensor.contractUD_lower' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Classical.symplectic_iff_det' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

## What is proved (kernel-checked)

Finite-dimensional quantum mechanics

- the Pauli matrices: `X^2 = Y^2 = Z^2 = I`, the cyclic products, and the
  commutators `[X,Y] = 2iZ` and partners;
- the spin-vector identity `(σ·a)(σ·b) = (a·b) I + i σ·(a×b)`;
- spin-1/2 su(2): `J_i = σ_i/2`, `[J_x, J_y] = i J_z`, and the Casimir
  `J^2 = (3/4) I`;
- the **Pauli group** `{1, sigma_x, sigma_y, sigma_z}`: each element squares to
  the identity, the four elements are **trace-orthogonal**
  (`tr (sigma_a sigma_b) = 2 delta_ab`), and the **Pauli twirl**
  `sum_a sigma_a M sigma_a = 2 tr (M) 1` holds for every `2 x 2` matrix `M`;
  the normalised twirl `(1/4) sum_a sigma_a M sigma_a` preserves the trace and
  equals `(tr M / 2) 1`, the completely depolarising channel in Pauli form.
  This is the algebraic core of Pauli channels and of Bell-diagonalising a
  two-qubit state; the twirl constant `2` is a kernel-evaluated trace, not a
  convention.
- coupled spins: total su(2) on the two-spin space, the singlet
  `|01> - |10>` annihilated by every total generator, and the total Casimir
  identity `J^4 = 2 J^2` (spectrum `{0, 2}`).

Angular momentum one (spin-1 representation)

- the Cartesian generators `S_1, S_2, S_3` as explicit `3 x 3` matrices satisfying
  the `su(2)` relations `[S_1, S_2] = i S_3`, `[S_2, S_3] = i S_1`, `[S_3, S_1] = i S_2`,
  checked entrywise (`S1_commutator_S2` and partners);
- the **Casimir** `S . S = 2 * 1 = l(l+1) 1` at `l = 1` (`spinOne_casimir`),
  exactly `2` rather than the spin-1/2 value `3/4`;
- the **cubic identity** `S_i^3 = S_i` (`S1_cubed`, `S2_cubed`, `S3_cubed`), whose
  eigenvalues are `{-1, 0, 1}`;
- the **ladder operators** `J_+ = S_1 + i S_2`, `J_- = S_1 - i S_2` raise and lower the
  `S_3` eigenvalue (`S3_commutator_Jplus`, `S3_commutator_Jminus`), and
  `J_+ J_- = S_1^2 + S_2^2 + S_3` (`Jplus_mul_Jminus`).  All entrywise; the general
  spin-`l` representation and the Clebsch-Gordan decomposition are out of scope.

Quantum information

- the Bell state, its EPR correlations, and the reduced density matrix;
- the CHSH operator, the Tsirelson square identity
  `S^2 = 4 I + 4 (σ_y ⊗ σ_y)`, and the Tsirelson value on the Bell state;
- entanglement measures: the purity `tr (ρ^2)` of the maximally mixed qubit (1/2),
  of a pure projector (1), and of the Bell marginal (2, the maximum at its trace),
  the algebraic core of the Renyi-2 entropy.
- tensor products: bilinearity, the mixed-product law, partial trace and its
  trace preservation.

- finite POVMs: a family of positive semidefinite effects whose sum is the
  identity; the finite-dimensional matrix order bridge proves that Born
  weights are real and nonnegative, and that their sum is one on every valid
  density matrix.  The order bridge is proved from the matrix square-root
  theorem and is not an application-specific axiom.

- three-qubit **GHZ / Mermin** nonlocality: the Mermin operator
  `M = X Y Y + Y X Y + Y Y X - X X X` on the explicit `8 x 8` Pauli matrices is
  symmetric (`mermin_symm`); it maps the GHZ vector `|000> + |111>` to `-4` times
  itself (`mermin_ghz_eigen`); and its GHZ expectation is `-8` (`ghzExpect_mermin`),
  i.e. `-4` on the normalised state.  This is the multipartite Bell combination
  (quantum value `4` versus the local-hidden-variable bound `2`).


No-cloning theorem

- a linear `U` copying both basis states, `U (|0> (x) b) = |0> (x) |0>` and
  `U (|1> (x) b) = |1> (x) |1>`, is forced by linearity to send `|0> + |1>` to the
  entangled `|00> + |11>` (`clone_zero_one_form`);
- that output is not a product `(|0> + |1>) (x) P` for any `P` (`sum_clone_ne`),
  so no linear operation clones every state (`no_cloning`).  Everything is over `ℂ` on
  the explicit qubit vectors `e0, e1`; the unitary completion and the
  density-matrix (mixed-state) formulation are out of scope.

Three-qubit bit-flip code

- the encoded vector `a |000> + b |111>` for arbitrary complex amplitudes is fixed by both stabilizers
  `Z Z I` and `I Z Z` (`stab1_code`, `stab2_code`);
- the first physical bit flip `X_1` has syndrome `(-1, +1)` (`xx1_syndrome`, `xx1_syndrome2`),
  the second `X_2` has `(-1, -1)` (`xx2_syndrome1`, `xx2_syndrome2`), and the third
  `X_3` has `(+1, -1)` (`xx3_syndrome1`, `xx3_syndrome2`);
- these are exact `8 x 8` matrix-vector identities over `ℂ`, the stabilizer error-detection table.
  The recovery circuit, phase noise and general quantum channels are out of scope; the proved
  statement is conditional on the bit-flip noise model.

Quantum teleportation

- the Bell-basis expansion for an arbitrary input `|psi> = a|0> + b|1>` and the unnormalised
  resource `|Phi+>`:
  `|psi> (x) |Phi+> = 1/2 [ |Phi+> (x) |psi> + |Phi-> (x) Z|psi> + |Psi+> (x) X|psi>`,
  `|Psi-> (x) XZ|psi> ]` (`teleportation_identity`), checked entrywise over `ℂ`;
- the `Z`, `X` and `ZX` corrections recover the original state exactly on the three
  nontrivial branches (`teleport_correction_Z`, `teleport_correction_X`, `teleport_correction_ZX`).  Normalisation,
  measurement probabilities and the classical communication channel are out of scope.

Quantum channels (Kraus operator sum)

- the channel `applyKraus K rho = sum_k K_k rho K_k†` is additive and
  homogeneous in the state;
- **trace preservation**: `sum_k K_k† K_k = 1` implies
  `tr (applyKraus K rho) = tr rho`, proved by cyclicity of the trace;
- **unitality**: `sum_k K_k K_k† = 1` implies `applyKraus K 1 = 1`;
- **composition**: applying `K` then `L` equals the Kraus family
  `(j, k) |-> L_j K_k`, so channels compose;
- **state validity**: each term `K ρ K†` preserves positive semidefiniteness,
  finite sums preserve it, and a trace-preserving Kraus family maps an
  `IsDensity` state (Hermitian, positive semidefinite, trace one) to another
  `IsDensity` state;
- **bundled channels**: `FiniteChannel` stores positivity and trace preservation
  as fields, together with additivity and scalar homogeneity; the identity,
  Kraus constructor and composition preserve all fields, and composition maps
  an `IsDensity` state to an `IsDensity` state;
- the single-qubit **amplitude-damping** channel `K0 = diag (1, c)`,
  `K1 = [[0, s], [0, 0]]` satisfies the Kraus completeness relation
  `sum_k K_k† K_k = 1` exactly when `c^2 + s^2 = 1`, hence is trace
  preserving on every state;
- the qubit **depolarising** channel `rho |-> (1 - 4p/3) rho + (4p/3) (I/2)`:
  it is the identity at `p = 0`, total decoherence to `I/2` at `p = 3/4`, and
  has the stated trace.  Every Kraus family also has a finite ancillary-system
  complete-positivity theorem, by applying the same operator-sum to `I ⊗ K`;
  infinite-dimensional operator-algebraic versions remain out of scope.

Lindblad generators

- `lindbladGenerator H L rho` is the finite matrix expression
  `-i[H,rho] + sum_k (L_k rho L_k† - 1/2 {L_k†L_k,rho})`;
- `trace_commutator_zero` and `trace_lindblad_dissipator` prove the two
  cancellation identities by cyclicity of the finite trace;
- `lindblad_trace_zero` proves the complete finite sum has zero trace.  This is
  the invariant needed by master-equation derivations, while positivity of the
  semigroup and long-time limits are deliberately not claimed.

Finite Gibbs ensembles

- `partitionFunction β E` is a finite exponential sum and is strictly positive
  whenever `Fin n` is nonempty;
- `gibbsWeight` is nonnegative and its finite sum is exactly one, so
  `gibbsDistribution` reuses the common `FiniteDistribution` API;
- `gibbsWeight_shift` proves that `E -> E + c` leaves the Gibbs distribution
  unchanged.  Thermodynamic limits and differentiating `log Z` are out of scope.

Bosonic field algebra

- the CCR `[a, a†] = 1` implies `[a†a, a†] = a†` and `[a†a, a] = -a`;
- finite multi-mode CCR: the total number operator is a ladder for every mode;
- Wick's theorem for one free mode: the contraction recursion
  `<φ^{n+2}> = (n+1) <φ^n>`, the even-point closed form `<φ^{2k}> = (2k-1)!!`,
  the vanishing of all odd moments `<φ^{2k+1}> = 0`, and the explicit
  pairing statement: the perfect matchings of 2k objects are enumerated as a
  concrete list whose length is proved to be (2k-1)!!, and the (2k)-point
  function equals that count.

Fermionic / condensed-matter algebra

- one fermionic mode: `{c, c†} = 1`, `c^2 = 0`, `N = c†c` is a projector
  and a ladder;
- the Hubbard site: commuting spin projectors, the double-occupancy projector,
  the nilpotent Cooper-pair operator `P = c↑† c↓†` with `[D, P] = P`, and
  the total number operator as a ladder;
- Majorana fermions: the two real Majorana combinations of one Dirac mode
  satisfy `g1^2 = 1`, `g2^2 = -1`, `{g1, g2} = 0` (Cl(1,1)), and the Dirac
  number operator is recovered as `c†c = (1 - i gamma1 gamma2)/2`;
- BCS mean field: the Bogoliubov rotation of a Majorana pair preserves the
  Clifford relations (`(c g1 + s g2)^2 = 1` and the rotated anticommutator
  vanishes); the BdG matrix `[[eps, Delta], [Delta, -eps]]` squares to
  `(eps^2 + Delta^2) 1`, is traceless with determinant `-(eps^2 + Delta^2)`
  (symmetric spectrum `± sqrt (eps^2 + Delta^2)`), equals `eps sigma_z + Delta sigma_x`,
  and reflects correctly under `sigma_x`/`sigma_z` conjugation.  A real finite
  family of BdG blocks instantiates the common uniform spectral-gap certificate
  from `Quantum.ParametricSpectralGap`; the mean-field gap equation
  `gap = -g * pairingAmp` is carried as an explicit hypothesis;
- finite lattice hopping and occupation sums.

Topological band structure (two-band Bloch Hamiltonians)

- the Bloch Hamiltonian `H = d1 sigma_x + d2 sigma_y + d3 sigma_z` shown equal to
  its explicit `2 x 2` matrix form (`bloch_eq_pauli`);
- `H^2 = (d . d) 1` (`bloch_sq`), so the spectrum is the symmetric pair
  `± sqrt (d . d)`; `tr H = 0` and `det H = -(d . d)`;
- over complex coefficients, **the determinant criterion** is
  `det H = 0 ↔ d . d = 0` (`bloch_gap_closed_iff`); for real coefficients,
  `bloch_real_det_zero_iff` additionally proves the Hermitian criterion
  `det H = 0 ↔ d1 = d2 = d3 = 0`.  The complex null counterexample is checked
  explicitly, so a bilinear square is not silently treated as a positive norm;
- the spectral polynomial: any `lam` with `lam^2 = d . d` satisfies
  `(H - lam)(H + lam) = 0` (`bloch_spectral_poly`);
- **chiral (sublattice) symmetry**: when the `d3` term is absent,
  `sigma_z H sigma_z = -H`, the symmetry that protects a zero mode in
  SSH-type models, forcing the spectrum symmetric about zero;
- concrete gapped (`d = (0,0,1)`) and gap-closing (`d = 0`) witnesses
  evaluated by the kernel.  A gap closing alone does not prove a topological
  transition; winding, Chern and bulk-boundary claims remain outside scope.

Berry curvature of a two-level system

- the Bloch vector in spherical coordinates
  `dhat = (sin theta cos phi, sin theta sin phi, cos theta)` has unit norm (`dhat_unit`);
- its `theta` and `phi` tangents `dTheta`, `dPhi` are orthogonal to `dhat` and to each
  other (`dhat_dTheta`, `dhat_dPhi`, `dTheta_dPhi`), `dTheta` is a unit vector
  (`dTheta_unit`) and `dPhi` has squared norm `sin theta ^ 2` (`dPhi_norm`), so the
  spherical frame is orthonormal;
- **Berry curvature density** (`berry_density`): the scalar triple product
  `dhat . (d_theta dhat x d_phi dhat)` is exactly `sin theta`, the field of a charge-one
  Dirac monopole and the integrand of the first Chern number.  Everything is
  trigonometric ring algebra over `ℝ` closed by the Pythagorean identity alone, so it is
  kernel-verified with no analysis.  What is *not* proved: the surface integral
  (`4 pi`) and the integer Chern number, which need the integral on top and are out
  of scope.

Jordan-Wigner transformation (two-site fermion chain)

- the annihilation operators `c_0 = sigma^- (x) 1`, `c_1 = sigma^z (x) sigma^-` as explicit
  `4 x 4` matrices, with `c_j^dag` proved to be the conjugate transpose of `c_j`;
- the full two-site **CAR**, checked entrywise: `{c_0, c_0^dag} = 1` (`car_zero`),
  `{c_1, c_1^dag} = 1` (`car_one`), `{c_0, c_1^dag} = 0` (`car_zero_one`),
  `{c_1, c_0^dag} = 0` (`car_one_zero`), the nilpotency `c_0^2 = c_1^2 = 0` and
  `{c_0, c_1} = 0`;
- **the string is load-bearing** (`naive_anticommutator`, `naive_anticommutator_ne_zero`): without
  the `sigma^z` factors the cross-site anticommutator is `2 (sigma^- (x) sigma^+) != 0`, so
  the transform is not a relabelling;
- each number operator `n_j = c_j^dag c_j` is a projector (`jwN0_projector`, `jwN1_projector`),
  and the two commute (`jwN0_comm_jwN1`);
- **number conservation**: the hopping term `c_0^dag c_1 + c_1^dag c_0` commutes with the total
  number `n_0 + n_1` (`jwHop_num_comm`);
- **spin-chain map**: the hopping term equals
  `(1/2)(sigma^x (x) sigma^x + sigma^y (x) sigma^y)` (`jwHop_eq_xy`), the XY coupling.
  The general `N`-site string, momentum space and the interacting chain are out of scope.

Lattice gauge theory (Wilson loops)

- **gauge covariance**: under a link transformation
  `U_i -> g_i U_i g_{i+1}^{-1}` the ordered loop product conjugates,
  `W -> g W g^{-1}` (`loop_conj`), i.e. a Wilson loop transforms in the
  adjoint representation;
- for an **abelian** gauge group the conjugation is trivial and the Wilson loop
  is gauge invariant (`wilson_loop_invariant`);
- additively, the **plaquette flux** `U_0 + U_1 + U_2 + U_3` is invariant under
  the finite-difference gauge transformation `U_i -> g_i + U_i - g_{i+1}`
  (`plaquette_flux_gauge_invariant`), with a kernel-evaluated `ZMod 7` witness;
- a group homomorphism respects the loop product (`loop_map`), so any **class
  function** of the loop is automatically gauge invariant
  (`classFunction_invariant`), the shape of every gauge-invariant observable;
  finite matrix representations additionally prove trace invariance under an
  explicitly `IsUnit` conjugating matrix (`matrix_trace_conjugate`);
- a concrete nonabelian witness shows the covariance is not vacuous.

The lattice action, the strong-coupling expansion and the continuum limit are
not attempted; the group-level covariance above is the input they consume.
- **Continuum field strength** (`LeanPhy.GaugeTheory.fieldStrength`): with the
  field strength defined as the commutator `F_{mu nu} = [D_mu, D_nu]` of
  covariant derivatives, it is antisymmetric (`fieldStrength_antisym`),
  vanishes on the diagonal, satisfies the **algebraic Bianchi identity** (the
  cyclic sum of `[F, D]` vanishes, `bianchi`), and is forced to zero for
  commuting (abelian) derivatives (`fieldStrength_abelian`).  A `2 x 2` matrix
  witness shows `F_01 != 0` for a nonabelian choice, so the module is not
  vacuous; all in an abstract ring with no representation assumed.

High energy / gamma algebra

- the explicit chiral gamma matrices, their squares, and the Clifford relation
  `{γ^μ, γ^ν} = 2 η^{μν}` as a single indexed statement;
- `γ^5`: it squares to 1, anticommutes with every `γ^μ`, is Hermitian, and
  the chiral projectors are idempotent, orthogonal, and sum to 1;
- gamma-matrix traces: every gamma is traceless, `tr (γ^μ γ^ν) = 4 η^{μν}`,
  the four-point trace `tr (γ^μ γ^ν γ^ρ γ^σ) = 4 (η^{μν} η^{ρσ} - η^{μρ} η^{νσ} + η^{μσ} η^{νρ})`,
  and the chiral traces `tr γ^5 = 0`, `tr (γ^5 γ^μ γ^ν) = 0`;
- supersymmetry: for a nilpotent supercharge `Q`, the Hamiltonian `H = {Q, Q†}`
  commutes with both supercharges and annihilates any state killed by both
  (the BPS condition), with a concrete 2x2 realization `H = 1`;
- Dirac bilinears: the Feynman slash and its two-point trace
  `tr (a̸ b̸) = 4 (a·b)`, the vanishing of traces with an odd number of
  slashes, and `tr (γ^5 a̸) = 0`;
- the Ward identity: with the Feynman slash shown to be linear, the photon
  vertex `vertexAmplitude eps ub u = sum_mu eps_mu (ubar γ^μ u)` is proved to
  equal the slash sandwich `ubar slash(eps) u` and to be linear in `eps`.  With
  both legs on shell (`slash p u = 0` and `ubar slash p' = 0`, explicit
  hypotheses) the longitudinal polarisation `p' - p` decouples
  (`ward_identity`), so `eps -> eps + lam (p' - p)` leaves the amplitude fixed
  (`gauge_invariance`).  A concrete lightlike configuration
  (`wardP = (1,0,0,1)`) solves both on-shell equations, so the hypotheses are
  satisfiable and the identity is not vacuous;
- spinor kinematics: the Feynman slash squares to the invariant
  `a̸ p * a̸ p = (p·p) 1`, with trace shadow `tr (a̸ p a̸ p) = 4 (p·p)`;
  from the Dirac equation `a̸ p u = m u` the momentum is forced on shell,
  `(p·p - m m) • u = 0`, and a massless on-shell spinor has lightlike momentum;
- the Lorentz algebra `so(1,3)`: the boost/rotation generators `J_i`, `K_i`
  with all nine commutators, tied to `(i/4)[γ^μ, γ^ν]`.
- spinor covariants: the antisymmetric tensor generator
  `sigma^{mu nu} = (i/2)[gamma^mu, gamma^nu]` is antisymmetric
  (`sigma_antisym`), vanishes on the diagonal (`sigma_self`), and
  commutes with `gamma^5` (`gamma5_commute_sigma`), which is exactly the
  property that makes the tensor a genuine Lorentz covariant rather than
  mixing with the pseudotensor.  Completeness of the five-covariant basis (the
  Fierz expansion, which needs a `+/- 4` weighting) is not proved here.


Standard Model anomaly cancellation (particle physics)

- the fermion content of one generation is a five-element list with the quantum
  numbers `(3,2,1/6)` (Q), `(3,1,-2/3)` (U), `(3,1,1/3)` (D),
  `(1,2,-1/2)` (L), `(1,1,1)` (E), each entry a `(colour, isospin, hypercharge)` triple
  over `ℚ`;
- **all four gauge-anomaly coefficients vanish**, evaluated by the kernel over `ℚ`
  (`smGen_anomalyFree`): the mixed gravitational-`U(1)` coefficient
  `∑ (colour)(isospin) Y`, the `SU(3)^2 U(1)` and `SU(2)^2 U(1)` coefficients (the two
  second-Casimir-weighted sums), and the `U(1)^3` coefficient `∑ (colour)(isospin) Y^3`;
- **any number `n` of identical generations** is anomaly free (`smContent_anomalyFree`):
  the sum of `n` copies of a zero coefficient is zero;
- **hypercharge rigidity**: under a uniform shift `Y -> Y + eps` the `U(1)^3` coefficient
  becomes the cubic `15 eps^3 + 10 eps` (`smGen_accU1cubed_shift`) and the gravitational
  coefficient becomes `15 eps` (`smGen_accGrav_shift`); the general affine and cubic
  transformation laws of these coefficients under the shift are stated and proved as
  `accGrav_hyperShift` and `accU1cubed_hyperShift`.  Hence the only rational shift that
  keeps the content anomaly free is `eps = 0` (`smGen_shift_rigid`, `smGen_grav_shift_rigid`),
  the algebraic statement that the hypercharge normalisation is fixed by the content.

  **Hypothesis boundary**: the fermion content (the quantum-number table) is the
  input.  The statement is conditional correctness — *given* these quantum numbers,
  the anomaly coefficients vanish — not a derivation of the content from a deeper
  principle.  The colour and isospin representation dimensions enter only through
  their Casimir weights `(colour-1)/2` and `(isospin-1)`, so the module checks the
  arithmetic of the anomaly conditions, not the group theory that produces the
  weights.

Particle physics: colour algebra and Dirac covariants

- **SU(3) colour algebra** (Gell-Mann matrices, integer normalisation with
  `1/sqrt 3` in `lam_8`): every `lam_a` is traceless (`gm_traceless`);
  **trace orthonormality** `tr (lam_a lam_b) = 2 delta_ab` (`gm_trace_orthonormal`);
  the **fundamental quadratic Casimir** `sum_a lam_a lam_a = (16/3) 1`
  (`gm_casimir`), whose coefficient is `4 C_F` with the quark colour factor
  `C_F = 4/3`; the **Fierz completeness** relation
  `sum_a (lam_a)_{ij} (lam_a)_{kl} = 2 delta_il delta_jk - (2/3) delta_ij delta_kl`
  (`gm_fierz`), the identity that rearranges a four-quark operator into
  colour-singlet and colour-octet channels with the weights `2` and `-2/3`; and
  the **colour-singlet trace** `sum_a tr (lam_a lam_a) = 16` (`gm_casimir_trace`).
  The `sqrt 3` is an explicit algebraic symbol (`sqrt3 * sqrt3 = 3`), never
  approximated.
- **Dirac covariant completeness** (the sixteen `Gamma_A`): the covariants are
  **trace-orthogonal** with the definite Fierz weight `w_A = tr (Gamma_A Gamma_A)/4`,
  `+1` on the scalar, pseudoscalar, vector and tensor families and `-1` on the
  axial-vector family, so `tr (Gamma_A Gamma_B) = 4 w_A delta_AB`
  (`cov_trace_orthonormal`); **Fierz completeness** holds entrywise,
  `sum_A w_A (Gamma_A)_{ij} (Gamma_A)_{kl} = 4 delta_il delta_jk` (`cov_fierz`);
  and the **closure form** `sum_A w_A tr (Gamma_A M) Gamma_A = 4 M` holds for any
  `4 x 4` matrix `M` (`cov_fierz_expansion`), the identity a Fierz
  rearrangement of an operator product is read off from.  The axial-vector signs
  (the `w_A = -1` cases) are precisely where a Fierz computation is most often done
  wrong, so each is kernel-checked rather than assumed.  What is *not* proved:
  the covariant expansion of a specific bilinear product (a rewriting, not a new
  identity) and the group-theoretic Casimir ratio `C_A = 3` from the structure constants,
  which is left to the anomaly module's arithmetic.
Particle physics: CKM quark mixing

- the Cabibbo-Kobayashi-Maskawa matrix in the product parametrisation
  `V = R_23 (gamma) P (delta) R_12 (theta)` (`ckm`): each of the two real
  rotations (`rot12`, `rot23`) is **unitary** (`rot12_unitary`,
  `rot23_unitary`) and the phase-carrying rotation is unitary from the unit modulus
  of the phase (`phaseRot13_unitary`); a product of three unitary matrices is unitary
  (`unitary_mul3`), so `V Vᴴ = 1` (`ckm_unitary`);
- the **unitarity-triangle** relation: the rows are orthonormal,
  `sum_k V_ik (V_jk)^* = delta_ij` (`ckm_row_orthonormal`), whose
  `(i, j) = (0, 2)` case is the closure of the standard CP-violation triangle.
  The phase is carried as an abstract unit-modulus complex number (`u^* u = 1`) rather
  than `exp (i delta)`, so no analysis enters; the mixing angles are hypotheses, so
  this is conditional correctness.  The Jarlskog invariant and the explicit Wolfenstein
  expansion are out of scope.

Scattering kinematics (Mandelstam invariants)

- the Minkowski product `minkowskiDot` is symmetric and bilinear, with the
  sign law under negation;
- **Mandelstam identity, off shell**: the defect
  `s + t + u - (m1^2 + m2^2 + m3^2 + m4^2)` equals
  `2 p1 . (p1 + p2 - p3 - p4)`, which vanishes on four-momentum
  conservation (`mandelstam_defect`);
- **on shell** (`p1 + p2 = p3 + p4`) the invariants obey
  `s + t + u = m1^2 + m2^2 + m3^2 + m4^2` (`mandelstam`), with a
  concrete massless configuration evaluated by the kernel.  Crossing,
  dispersion relations and the optical theorem are out of scope.

Symplectic canonical transformations (classical mechanics and optics)

- the canonical form `J = [[0,1],[-1,0]]` and the two-dimensional condition `A^T J A = J`;
- **symplectic iff determinant one** (`symplectic_iff_det`): for every real `2 x 2` matrix,
  `A^T J A = J ↔ det A = 1`;
- symplectic maps compose (`symplectic_mul`), and the phase-space rotation and free-particle
  shear families preserve `J` (`rotation_symplectic`, `shear_symplectic`);
- this is finite linear algebra shared by Hamiltonian mechanics, paraxial optics, accelerator
  lattices and bosonic Gaussian systems.

Generic finite typed tensors

- `Tensor2N n up/down` carries the variance of both rank-two slots for any
  finite `Fin n` index;
- mixed composition is associative, has a typed identity, and its trace is
  cyclic (`mixedTraceN_comp_comm`);
- the same-variance trace is rejected by the elaborator, before proof search;
  no metric is assumed in this generic layer, so it can be reused for Lorentz,
  colour, lattice and finite Hilbert-space indices.

Associative-algebra Lie core and conserved observables

- `commutator_jacobi` proves the Jacobi identity for commutators in every ring;
  the adjoint action is additive and obeys the Leibniz rule;
- `Conserved H O := [H,O] = 0` is closed under sums, products, powers,
  commutators and natural scalar multiples; linear combinations with arbitrary
  coefficients require explicit centrality hypotheses. This is the shared algebraic
  conservation layer for spin, Lorentz, gauge, QFT and lattice models. The
  commutator and conservation interfaces are universe-polymorphic, so named
  finite-index matrices are not forced into `Fin n`.

Hamiltonian interface (finite algebraic layer)

- `Quantum.HamiltonianFlow` turns a finite Hermitian matrix into the checked
  propagator `exp(i t H)`, proves composition at times `t+s`, and proves that
  any `O` with `[H,O]=0` is invariant under `U_t O U_t†`. Continuous-time
  differentiability, Stone's theorem, unbounded operators and continuum
  limits remain explicit analysis obligations.
- affine phase-space observables `a q + b p + c` with the canonical Poisson bracket;
  in particular `{q,p} = 1`, antisymmetry and bilinearity are kernel-checked;
- the normalized harmonic-oscillator rotation flow is symplectic and preserves the exact
  quadratic energy `q² + p²`;
- derivatives, nonlinear flows, generating functions, and ODE existence/uniqueness remain
  outside this layer and must be supplied by a future analysis module or explicit hypotheses.

Statistical mechanics (Ising transfer matrix)

- the symmetric transfer matrix `T = c I + s sigma_x` (`isingTransferMatrix_eq_pauli`);
- **composition law**: `T(c,s) T(c2,s2) = T(c c2 + s s2, c s2 + s c2)`, so the
  parameters combine by the addition (rapidity) formulas;
- all symmetric transfer matrices **commute** (`isingTransferMatrix_comm`), so a
  chain diagonalises in one fixed basis;
- the **characteristic polynomial** `T^2 - 2 c T + (c^2 - s^2) 1 = 0`, giving the
  spectrum `{c + s, c - s}` (`isingTransferMatrix_charpoly`);
- trace identities: `tr T = 2c` (`isingTransferMatrix_trace`) and the two-site
  partition function `tr (T^2) = 2 (c^2 + s^2) = (c+s)^2 + (c-s)^2`
  (`isingTransferMatrix_trace_sq`), with `det T = c^2 - s^2`
  (`isingTransferMatrix_det`), plus a kernel-evaluated diagonal witness.  The
  thermodynamic limit (free energy per site, the `N -> infinity` analysis) is
  out of scope.

Lorentz boosts (1+1 dimensions)

- the one-axis boost `B(c, s) = [[c, -s], [-s, c]]` (`boost`), with the Minkowski
  metric `eta = diag (1, -1)` (`etaM`) carried as an explicit matrix;
- **rapidity addition** (`boost_mul`): `B(c1,s1) B(c2,s2) = B(c1 c2 + s1 s2, c1 s2 + s1 c2)`,
  the relativistic velocity-addition law, so the boosts form a one-parameter group
  (`boost_one_mul`);
- **the Lorentz condition** (`boost_lorentz`): `B^T eta B = eta` holds exactly when
  `c^2 - s^2 = 1`, the invariance of the interval `t^2 - x^2`; a real rapidity
  (`c = cosh phi`, `s = sinh phi`) supplies that hypothesis, so this is
  conditional correctness;
- `det B = c^2 - s^2` (`boost_det`) and `B(c,s) B(c,-s) = 1` on the mass shell
  (`boost_inv`).  No hyperbolic functions enter; the parameters are abstract
  complex numbers under the single hypothesis `c^2 - s^2 = 1`.  The full Lorentz
  group, boosts along arbitrary axes, and the spinor representation are out of scope.

The Lorentz algebra so(3,1)

- the six generators as explicit `4 x 4` matrices: rotations `R_1, R_2, R_3` and boosts
  `B_1, B_2, B_3`;
- the rotations close on `so(3)`: `[R_1, R_2] = R_3` (`R1_commutator_R2`) and partners;
- rotations act on boosts as vectors: `[R_1, B_2] = B_3` (`R1_commutator_B2`) and partners;
- **two boosts close into a rotation**: `[B_1, B_2] = - R_3` (`B1_commutator_B2`) and
  partners, the Thomas-Wigner precession statement;
- every generator is **metric-antisymmetric**, `X^T eta + eta X = 0` with
  `eta = diag (1, -1, -1, -1)` (`metric_R1` ... `metric_B3`), the defining condition of
  `so(3,1)`.  Exponentiation to finite transformations, the spinor representation and
  the Poincare group are out of scope.

Relativity and dimensions

- the `(+---)` Minkowski metric and the lightlike relation;
- SI dimensions as a type index, so adding mismatched dimensions is a type error.

Variance-aware Lorentz tensors

- `UpVec` and `DownVec` are distinct four-component complex-vector types, so a term` contractUD x y`,
  where both arguments are upper vectors, is rejected by the type checker before proof search;
- `lower : UpVec -> DownVec` and `raise : DownVec -> UpVec` use the explicit `(+---)` metric and
  are inverse (`raise_lower`, `lower_raise`);
- only upper-lower contractions are exposed (`contractUD`, `contractDU`), with bilinearity and
  the symmetric Minkowski scalar `x^mu y_mu` expanded to `x0*y0 - x1*y1 - x2*y2 - x3*y3`;
- this is the first typed step toward automatic index variance checking.  Rank-2 tensors,
  finite covariant derivatives and finite differential forms now have separate
  kernel-checked interfaces; manifold-valued forms, continuous Stokes theory
  and a fully automatic Einstein elaborator remain future work.

Surface layer

- Dirac notation as a real elaborator: `|k⟩`, `⟨u|`, `⟨u|v⟩`, `⟨u|A|v⟩`,
  `⟨u|A` and `|u⟩⟨v|` infer the Hilbert-space dimension `n` from context and
  check every slot against it, so a dimension clash is a Chinese diagnostic
  rather than a silent mis-elaboration.  Orthonormal basis kets, completeness
  `∑_k |k⟩⟨k| = 1`, and the composition rule `|u⟩⟨v| |w⟩ = ⟨v|w⟩ |u⟩` are
  proved through it, and each positive form is shown by `rfl` to be the thin
  underlying definition.  The three dimension-clash diagnostics are pinned by
  `#guard_msgs` tests;
- index calculus: the Kronecker delta, finite Einstein sums and contractions,
  the Levi-Civita symbol with its antisymmetry, and the epsilon-delta identity.
- Einstein summation elaborator: `einsum k, M i k * N k j` is real syntax whose
  index type is inferred from context and whose result is the kernel-checked
  finite sum; the delta contraction (`∑_j δ_ij v_j = v_i`), the delta chain, the
  dot and cross products in index notation, and the matrix product and trace
  identities.  Its three diagnostics (index type not inferable, index type not
  finite, index absent from the summand) are pinned by `#guard_msgs` tests.

End-to-end example

- the harmonic-oscillator ladder identity `[a†a, a†] = a†` as an abstract ring
  theorem (CCR as hypothesis), and its concrete finite shadow on a two-level
  truncation, given both as a matrix identity and in Dirac notation.

## What is assumed, and where

Nothing is assumed silently.  Every hypothesis is a named field of a structure
or an explicit function argument, so a reader can see exactly what a proof
consumes.  The recurring hypotheses are:

```
FermionicMode / HubbardSite   the canonical anticommutation relations
                              {c, c†} = 1, c^2 = 0 and the cross relations
MultiModeCCR                  [a_i, a_j†] = δ_ij and mutual commutativity
FreeMode                      [a, a†] = 1 and a vacuum functional ω that is
                              additive, normalised (ω 1 = 1), and annihilates
                              a on the right and a† on the left
cliffordRelation              the Clifford bilinear form
CliffordPair / MeanField      the Majorana Clifford relations g1² = g2² = 1,
                              {g1,g2} = 0 with central ℂ coefficients, and the
                              mean-field gap equation gap = -g * pairingAmp
on-shell legs (Ward)           slash p u = 0 and ubar slash p' = 0, i.e. the
                              two electron legs solve the Dirac equation
Kraus completeness             sum_k K_k† K_k = 1 (trace preservation) and
                              sum_k K_k K_k† = 1 (unitality) are hypotheses,
                              not derived from a dilation of the channel
```

These are the physics input.  In particular the vacuum functional is an
*assumption* about a linear functional, not a construction of a Hilbert space;
the CCR is an algebraic relation in a ring, not an operator-domain statement.

## What is deliberately out of scope

The following are not attempted, and are not hidden behind a `sorry` or an
`axiom`.  They are listed so that a user knows the edge of the verified region.

- Real and complex **analysis**: limits, integrals, power-series and asymptotic
  expansions.  `ℝ` and `ℂ` are used as the ambient number fields, but no
  construction of the reals or of measure theory is carried out here.
- **Infinite-dimensional Hilbert spaces** and the functional-analytic theory of
  **unbounded operators** (domains, closures, self-adjointness).
- **Path integrals** and the measure-theoretic content of quantisation.
- **Renormalisation** and any statement whose meaning depends on a regulator
  and a limiting procedure.
- The **topological invariant itself**: the winding number of the Bloch vector,
  the Brillouin-zone integral, and the bulk-boundary correspondence.  The
  linear algebra of gap closing and chiral symmetry is proved in
  `LeanPhy.Condensed.Topological`, but assigning an integer invariant
  needs the topological input on top.
- **Crossing, dispersion relations and the optical theorem** for scattering
  amplitudes.  The kinematic Mandelstam identity is proved in
  `LeanPhy.HighEnergy.Scattering`, but the analytic continuation is not.
- The **thermodynamic limit**: the free energy per site of a statistical
  model.  The transfer-matrix algebra is proved in
  `LeanPhy.StatMech.TransferMatrix`, but the `N -> infinity` limit and the
  phase-transition analysis need the analytic layer.
- The **multi-field and fermionic** form of Wick's theorem beyond the single
  free mode: the pairing enumeration and the bosonic single-field statement are
  proved in `LeanPhy/FieldTheory/Pairing.lean`, but the sign and
  ordering bookkeeping for several fields (Grassmann signs) is not carried out.

In every one of those cases the honest move is to carry the missing input as an
explicit hypothesis or axiom *in the user's development*, where it is visible,
rather than to import it into this library.

## How to read a LeanPhy theorem

When you see a theorem such as

```lean
theorem wick_even_moment (k : ℕ) : ω (φ ^ (2*k)) = (doubleFact k : ℂ)
```

read it as: *for any structure `M` of type `FreeMode` — that is, for any ring
with a pair of operators satisfying the CCR and any additive, normalised
functional annihilating the ladder directions — the equality holds.*  If your
physical situation satisfies those hypotheses, the conclusion is not merely
plausible; it is checked by the kernel.  If it does not, the theorem says
nothing about your situation, and that gap is the physics you still owe.
