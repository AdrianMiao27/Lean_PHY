# LeanPhy v1.1 architecture

The [capability inventory](capabilities.md) distinguishes implemented operations, local results,
and interfaces requiring supplied premises. The [global roadmap](roadmap.md) sets priorities
across physical models, formal operations, observables, approximation, and research workflows;
the specialist developments below are building blocks within that plan.

LeanPhy is deliberately a library on top of Lean 4 and mathlib.  It does not
fork the Lean kernel and it does not introduce a second proof logic.  A physics
project therefore uses the normal Lean editor, elaborator, `lake build`, and CI
workflow.

## Shared research operations

The common ledger now lives in `Workflow.Core`; its original proposition is
stored when an obligation is registered. A package-indexed reference and a
proof of that target are required to resolve it, and the target proof remains
in history. Default physics packages are in `Workflow.DefaultPackages`.
`CLI.Core` and `Library.Core` can be used without the built-in catalogue;
compatibility imports preserve existing domain clients. The compiled
`Library.Index` supports declaration discovery, while `Verification` retains
the wider full-declaration audit boundary. See [migration](research-core.md).

`Workflow.Exploration` binds questions to actual model/parameter predicates and
stores hypothesis branches with dependent evidence. Restriction, predicate
pullback, explicit implication transport and proved domain coverage preserve
those conditions. Counterexamples prove the negation of a branch goal; failed
attempts carry no such theorem. Revision archives old evidence under its original
target and starts a pending root. The same `TheoryPackage`/`CLI.Core` report exports
these records, while root completion still uses indexed obligation resolution.
The physical client exercises complex pairing and singular auxiliary elimination.
Automatic condition search and cross-project change impact analysis remain open.
See [exploratory workflow](exploratory-workflow.md).

The coupled-action layer uses `FieldTheory.Jet`, `Variational`,
`PolynomialAction`, `EnergyMomentum`, and `VariationalResidual`. They derive
Euler equations, the complete local boundary current, off/on-shell Noether
relations and local error budgets from first-order polynomial densities.
`Classical.VariationalBridge` connects these results to the corrected
all-component mechanical total derivative. Condensed-matter and high-energy
entry points share these operations; solution existence, general spacetime-integrated
charges and graded/covariant fields remain separate work. See [variational operations](variational.md).

The actual-action layer uses `Mathematics.PolynomialEvaluation` and
`PolynomialIntegral` to derive analytic chain rules and differentiation of
polynomial interval integrals, including the compact domination proof.
`FieldTheory.FieldEvaluation` consumes actual C² fields in explicit directions.
`CurveJet` interprets all formal jets of a one-dimensional smooth profile;
`IntervalAction` retains endpoint flux, derives stationarity and Noether balance,
and transports local equation/breaking budgets to actual integrated current drift.
It shares the existing `ErrorCertificate` and exploration ledger. Multidimensional
spacetime boundary integration, solution existence, and graded/covariant semantics
remain open. See [actual fields and actions](action-evaluation.md).

The field-change layer uses `PointTransformation`, `TransformationEvaluation`
and `RedefinitionVariation` for full polynomial substitutions, actual evaluation
and infinitesimal action changes. `EulerTransport` derives the actual Jacobian
transpose law for Euler equations, including the cancellation of Hessian terms,
and transports boundary currents and interval-action derivatives. Forward
transport permits singular or rectangular maps; reverse transport consumes a
right inverse, constructed from a nonzero determinant in the square case.
Pointwise regular domains do not establish global inverse charts. Derivative
dependent changes, higher-order EFT operator relations and quantum equivalence
remain open. See [field changes](field-redefinitions.md).

The normalized-response layer uses `Mathematics.FiniteWeightedResponse` for
real or complex finite weights, `StatMech.FiniteCovariance` for positivity,
and `SourceEnsemble`/`GibbsResponse` for actual exponential source and temperature
derivatives. `FieldTheory.FiniteActionResponse` consumes polynomial densities;
`FiniteSourceResponse` retains complex partition nonzero conditions.
`ResponseBound` produces finite-source error certificates from uniform bounds.

`Quantum.FiniteThermalState` embeds probabilities as valid density matrices,
proves the normalized matrix-exponential formula in any supplied energy basis,
and uses the spectral theorem to construct a thermal state for every finite
Hermitian Hamiltonian. Unitary basis transport, stationary evolution, and
energy-temperature derivatives use the existing state/flow APIs. The original changing-Hamiltonian/probe theorems in this module use a fixed common
basis; the new response layer below removes that restriction for general Hermitian
perturbations. See the
[source and thermal guide](source-response.md).

The response layer uses `Mathematics.Duhamel` to derive an exact finite-time
exponential difference, its noncommuting perturbation derivative, and conjugation
insertions. `Quantum.DynamicalResponse` transports these results to actual
Hamiltonians, density states and trace readouts; its Kubo formula is a derivative
of the perturbed readout. A constant source switched on at zero has a causal
response, while the unwindowed two-time kernel keeps its explicit time arguments.
`Quantum.ThermalPerturbation` differentiates normalized Gibbs expectations without
using a moving eigenbasis, retaining the probe and normalization terms. The
commuting limit is a separate theorem with an explicit premise. The independent
client consumes arbitrary-mode CAR Hamiltonians and keeps general-drive, remainder
and continuum obligations open. See [quantum response](quantum-response.md).

The effective-operation layer separates three contracts. `FormalExpansion`,
`FormalMatrix` and `FormalBlockElimination` preserve retained coefficients over
noncommutative rings. `BlockElimination` preserves actual block solutions,
sources and linear readouts given a certified inverse. `EliminationError`
turns an actual inverse residual into a norm error certificate; a formal
coefficient equality alone cannot satisfy this contract.

`Quantum.EffectiveHamiltonian` consumes the block equations at a specified
energy and transports both quadratic observables and the normalization metric.
`FieldTheory.HeavyFieldElimination` substitutes a solved algebraic auxiliary
field in arbitrary light polynomials and passes the induced action to the
existing variational layer. `PropagatingHeavy` builds finite ordered inverses
from a certified mass matrix and actual divergence-form kinetic operators.
`HeavyFieldMatching` derives the quadratic heavy equation from the density,
retaining finite-order residuals, local divergences and source contact terms.
`HeavyFieldInterval` evaluates these jets on smooth profiles and proves actual
interval-action matching, first variations and residual/endpoint budgets.
The independent effective client retains spectral-domain, Green-function,
quantum-matching and unitary-dynamics obligations. See the
[effective-operation guide](effective-theory.md). These additions occupy T2/T4/T5
of the global roadmap; general interacting-model construction, dynamical response, physical
certificate checkers and automated exploration support remain separate deliverables.

The finite-data certification layer uses `RationalMatrix` for exact rational
real/imaginary data and conservative operator-norm row bounds. `ResidualInverse`
constructs an exact unit and inverse error from a residual below one;
`MatrixCertificate` checks the actual data and combines model uncertainty with
the computed residual before accepting. `CertifiedElimination` handles rectangular
blocks, sources, reconstruction and linear probes. `Quantum.CertifiedResolvent`
turns a model ball into a finite energy disk and supplies the existing effective
Hamiltonian model. The Python producer remains untrusted and emits a kernel
acceptance goal. See [matrix certificates](matrix-certificates.md). General interval
arithmetic, automatically derived rounding enclosures and continuum domains remain open.

The finite-fermion layer now constructs CAR matrices recursively on an
occupation space of dimension `2^n`, with explicit mode ordering, parity strings
and adjoints. `FermionBilinear`/`FermionLinear` keep coefficient operations
independent of matrix expansion. `FermionHamiltonian` proves the full Nambu
commutator equation and energy relation, retaining the normal-ordering constant;
the actual many-body operator supplies the thermal density. `FermionBasis`
transports both generators and coefficients, and `PhysicalMajorana` fixes the
phase and adjoint convention. The condensed-matter complex-pairing block is a
separate reduced object. See [fermion model construction](fermion-models.md).
`FermionWord` and `FermionPolynomial` extend this to arbitrary finite interacting
expressions, with terminating CAR normalization, strict ordering and semantic
proofs. `FermionEmbedding` transports local identities through injective mode
assignments. `InteractingFermion` consumes checked expressions in actual occupation
operators, thermal densities and initial unitary-observable derivatives. See
[fermion expressions](fermion-words.md). The existing dynamics and exploration
layers consume finite physical objects. `FermionicQuasiFree` adds a certificate
for ordered four-point contractions tied to an actual finite density, with
single-mode and two-mode matrix anchors. `FermionVacuum` now derives two- and
four-point contractions from CAR and density annihilation, constructing the
actual empty-occupation state for every finite mode count.
`FermionicMoment` supplies a terminating signed deletion recursion on ordered
positions; `FermionVacuumWick` proves that it evaluates any actual vacuum probe
product, derives odd-moment vanishing and adjacent CAR contact identities, and
connects executable integer word moments to symbolic interaction readouts.
The density annihilation condition, not a supplied Wick equality, drives the proof.
General Gaussian/thermal and time-ordered Wick factorization, bosonic cutoff corrections,
efficient expression backends and large-system limits remain open.

## Layers

### Kernel and mathlib

Lean's kernel checks every proposition and proof term.  mathlib supplies the
trusted mathematical foundation used by the library, including algebra,
topology, measure theory, functional analysis, and finite-dimensional linear
algebra.  Tactics are proof-producing elaborators; their output is still
checked by the kernel.

`LeanPhy.Verification` inspects transitive declaration dependencies in the
checked environment. Selection by defining module includes imports, private
declarations and declarations placed in external namespaces. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted as foundational axioms;
theorem parameters remain explicit assumptions. The release driver enumerates
and imports every library source module rather than relying on the umbrella's
exports, verifies source/mirror hashes, and rejects empty audit selections.
See [declaration auditing](declaration-auditing.md), including the correction to
the former local-only environment traversal and the toolchain trust boundary.

Generated downstream projects use `scripts/audit_project.py` before producing
their research reports. It enumerates every local source module under the
recorded Lake source directories, builds by source-file target, queries actual
module setup/artifact paths and binds those imports for the audit. This avoids
auditing a dependency's same-named executable module. Source and artifact hashes
must remain unchanged through validation. The verifier is copied from the
declared LeanPhy dependency when a project is created and can be versioned
with that project; mathematical assumptions and physical obligations remain
visible in the separate research ledger.

### Mathematical certificates

`LeanPhy.Mathematics` packages recurring assumptions without hiding them:

- `ContinuousAnalysis`, `DominatedConvergence`, and `ContinuousPathIntegral`
  represent limits, Bochner integrals, normalized expectations, and regulator
  sequences;
- `Hilbert`, `InfiniteSpectrum`, `HilbertSpectrum`, `SpectralCalculus`, and
  `SpectralGap` represent bounded operators, resolvents, spectral bounds, and
  discrete mixing estimates;
- `UnboundedOperator` carries a dense domain and domain-valued resolvent.  Its
  `asPMap` adapter exposes the same object as mathlib's `LinearPMap`, while
  preserving the domain in the type.  The module also provides explicit
  certificates for formal adjoints, closedness, closability, self-adjointness,
  graph-norm relative bounds, and bounded maps that preserve the domain;
- `WeakPDE`, `Contraction`, `ContinuousEvolution`, and `EnergyDissipation`
  expose weak solutions, fixed points, Duhamel estimates, and energy budgets;
- `Approximation`, `OperatorConvergence`, `CertifiedResidual`, and
  `Renormalization` keep truncation, discretisation, numerical residual, and
  regulator errors explicit.
- `SymmetryReduction` is the shared constraint boundary for gauge systems,
  constrained Hamiltonian models, quantum symmetries, and lattice reductions.
  `ConstrainedSymmetry` stores admissibility and constraint predicates together
  with their preservation proofs; `ConstrainedDynamics` adds an equivariant
  proof-preserving step; `ConstrainedObservable` records invariance on physical
  orbits and can be lifted to an explicit quotient. The quotient is built from
  the proved group-orbit equivalence relation, so no gauge slice or manifold
  structure is assumed.
- `ConstraintAlgebra` complements the state-level interface with a commutative
  Poisson algebra, a generated constraint ideal, first-class closure, weak
  equality, and the Dirac-observable normalizer. Its closure theorems are
  algebraic; constraint classification, gauge fixing, quotient regularity,
  Hamiltonian flow, and physical reduction remain model-specific obligations.
- `ConstraintMap` represents a composable Poisson algebra map that sends source
  constraints into the target constraint ideal. It transports weak equality by
  ideal membership. Transporting a Dirac observable additionally requires an
  explicit `CoversConstraintIdeal` witness for the target ideal; no surjectivity,
  gauge fixing, quotient regularity, anomaly cancellation, or physical
  equivalence is inferred.
- `BRST` is the next algebraic layer for constrained and gauge-theory work.
  `BRSTDifferential` stores a concrete derivation and its nilpotency proof;
  closed, exact, and cohomologous elements are ordinary propositions.  The
  optional `PoissonBRSTDifferential` and `ConstraintBRSTDifferential` add
  bracket compatibility and preservation of the declared constraint ideal.
  This layer is intentionally ungraded.  Ghost number, Koszul signs, the BV
  antibracket, gauge-fixing data, path-integral measures, anomaly cancellation,
  and any physical-equivalence theorem are separate future structures or open
  obligations.
- `GradedBRST` refines this boundary for ghost-bearing calculations.  A
  `GradedRing` declares homogeneous pieces, parity, and an explicitly odd
  differential degree; `GradedDerivation` then requires the corresponding
  signed Leibniz law on homogeneous inputs.  `GradedBRSTDifferential` adds
  nilpotency and the same closed/exact/cohomology vocabulary.  The declaration
  of a grading is a model input: it does not construct a ghost polynomial
  algebra or a BV theory.
- `GaugeTheory.FiniteGhost` supplies the first concrete finite adapter for that
  interface: a `2 × 2` matrix CAR ghost pair, an explicit diagonal/off-diagonal
  grading, and a square-zero odd differential.  The adapter is useful for
  checking signs and algebraic BRST steps, while continuum, BV, gauge-fixing,
  anomaly, and physical-equivalence claims remain
  explicit obligations.
- `GaugeTheory.FiniteGhostPolynomial` constructs the exterior algebra on
  finitely many generators and its parity involution. `GhostKoszul` supplies
  left derivatives, the signed product rule, CAR identities and Koszul
  differentials over arbitrary commutative coefficient rings, including
  polynomial constraint sequences. `QuadraticGhost` proves nilpotency and
  nontriviality of `cᵢ cⱼ ∂ⱼ` for distinct indices. `GhostDegree` then uses
  actual exterior powers for an integer grading, finite homogeneous projections,
  ascending Lie BRST and descending Koszul differentials, including in
  characteristic two. A general Lie-cochain identification, negative-degree
  antighosts and BV structure remain separate; certified Lie modules now supply
  a matter tensor differential. The original
  pure-exterior inner charge is explicitly proved to vanish.
- `Mathematics.LieCohomology` records the Lie action and representation law
  and defines `differential0`/`differential1`. `LieCohomology2` explicitly
  adapts these structures to mathlib without global Lie instances, supplies
  the next differential and proves `d₂ d₁ = 0`. Cocycles and boundaries are
  submodules, and `H2` is their quotient with checked class-equality criteria.
- `Mathematics.CentralExtension` constructs the bracket on `V × M` from a
  two-cocycle for trivial coefficients. An extension equivalence carries
  source/target cocycle proofs and preserves the bracket, base projection
  and central inclusion. Every such equivalence yields a coboundary;
  conversely an explicit coboundary yields a shear equivalence. This proves
  the `H²` criterion for these product-carrier models. The worked affine
  example links its degree-one CE map to the quadratic ghost differential.
  All-degree ghost/CE correspondence, integration and physical interpretation
  remain separate obligations.

- `Mathematics.CohomologyReduction` is the computation boundary. A solver
  supplies projection `P`, representatives `I`, primitive `K` and correction
  `T`; Lean checks `d₂d₁ = 0`, `d₂I = 0`, `Pd₁ = 0`, `PI = 1`, and
  `d₁K + IP + Td₂ = 1`. The last identity certifies completeness, including
  the treatment of nonclosed cochains. The quotient is linearly equivalent
  to the parameter space. `LieCohomologyReduction` transfers these
  certificates to declared CE maps. The Heisenberg example includes this
  transfer and derives a two-dimensional `H²`, rather than trusting a matrix
  rank reported by an external solver. v1.1 keeps these Lean modules and
  checked examples while removing the old symbolic Python frontends.

- `Mathematics.FiniteLieCohomology` proves that the next CE differential is
  alternating, so increasing basis triples detect its vanishing. Explicit
  finite brackets, module actions, coordinate equivalences and CE matrix
  bridges are checked in Lean. The reported computation remains conditional
  on the supplied model laws and is kept separate from any physical anomaly
  or BRST interpretation.

- `Mathematics.DiagonalCohomology` retains exceptional parameter values in
  the coordinate type: a coordinate survives iff both adjacent weights vanish.
  The primitive and correction use total inverses, while the representative
  term restores the identity precisely on zero weights. This certifies the
  quotient at each point and gives equivalences within a fixed zero pattern.
  `SolvableLieFamily` transports the reduction through proved CE coordinate
  maps for a three-parameter Lie/module family. Its conditional dimension
  formula counts intersecting resonance conditions separately; generic
  primitive theorems retain all nonresonance and closedness premises.

A certificate is an ordinary `Prop` structure.  Its fields are inputs, and its
theorems derive consequences from those fields.  The structure is not a way to
turn an unchecked number or a claimed physical interpretation into a theorem.

### Physics domains

Domain modules provide typed objects and reusable algebra: quantum states and
channels, CCR/CAR/Fock structures, Clifford and gauge identities, condensed
matter and statistical models, classical/relativistic transformations, and
surface notation.  Domain modules depend on the certificate layer where
appropriate, but the mathematics modules do not depend on a particular physical
model.

### Research workflow

`LeanPhy.Workflow` is the reproducibility boundary.  A `TheoryPackage` stores
assumptions, models, checked claims, dependencies, scope boundaries, and open
obligations.  `ResearchProject` composes packages and checks qualified links.
`CheckedClaim.proof` is a Lean proof term, so metadata cannot create a claim.
External CAS and numerical tools cross the boundary only through a
`CertificateChecker` whose `sound` theorem is consumed by the claim.

## Soundness boundary

The logical statement is always conditional:

```text
declared assumptions + proof term  ──kernel──>  checked conclusion
```

The library intentionally does not infer:

- existence of a path measure, PDE solution, self-adjoint extension, or
  thermodynamic limit;
- convergence from a finite numerical sample;
- continuum equivalence of a truncation;
- physical adequacy of a supplied model;
- that a symmetry action admits a valid gauge fixing or that its quotient is a
  manifold;
- that a nilpotent algebraic differential is a complete BRST/BV construction,
  or that its cohomology equals the physical observable space;
- that a declared graded differential has a physical ghost interpretation, or
  that its parity laws imply anomaly cancellation;
- that a low-degree Lie cochain calculation is a completed anomaly or BRST
  classification, or that a cocycle quotient has been constructed when only a
  cochain-level witness is present;
- a sign, convention, or boundary condition that is absent from the type.

For unbounded operators, a name such as `Hamiltonian` carries no analytic
meaning by itself.  A user must supply the relevant domain, density, inverse,
adjoint equality, graph bound, or domain-preservation proof.  The current
bridge does not implement Stone's theorem, general self-adjoint extensions,
spectral measures, or the passage from a resolvent certificate to a time
evolution.  Those are separate research obligations.

These are represented as explicit hypotheses or open obligations.  This makes
partial formalisation useful in a real paper without confusing a verified
algebraic step with a verified physical theory.

## Parameterised algebraic models

The finite Lie, ghost and deformation modules retain parameter conditions,
exceptional loci and obstruction equations as explicit Lean hypotheses. Their
checked examples cover representative resonance and extension cases. The
former SymPy based parameter-stratification and model-discovery frontends are
not part of the v1.1 script set; new external calculations must enter through
the retained matrix or Gibbs certificate interfaces and must compile against a
Lean soundness theorem.

## Lie deformation jets

`LieDeformation` consumes the existing adjoint module and actual H2 quotient.
Its first-order carrier is V × V with a square-zero parameter map; Jacobi is
proved equivalent to the CE cocycle condition. Reduction- and tangent-preserving
linear bracket equivalences are proved to be exactly the shears arising from
one-cochains, so equality in H2 gives the precise equivalence criterion.
Second-order V × V × V brackets are expanded on arbitrary jets, deriving the
necessary-and-sufficient equations d2(omega)=0 and d2(nu)+Q(omega)=0. Both orders
construct actual LieAlgebra structures. The parameter-ring Module instance and analytic integration are
not part of this interface; the H3 quotient and third-order extensions live
in the dedicated modules described below. A worked example consumes the discovered raw
bracket and demonstrates that the first-order tangent space can strictly
exceed the directions which extend through order two.

`LieDeformationReduction` connects a complete adjoint CE reduction to the
first-order equivalence API. Its primitive constructs the shear, and its
representatives give a complete, uniquely parameterized family of jet models.
Both Lie frontends derive adjoint matrices from constants[row,col] with the
coefficient mode explicitly declared. Emitted coefficients use the canonical
adjoint module; computed CE matrices still pass the independent differential
bridges. A wrong representation with the same carrier and H2 dimension cannot
pass those bridges. Default explicit-coefficient generation is unchanged.

`LieDeformationSecondOrder` bundles the quadratic term as a trilinear map,
proves alternation and checks the entire second-order residual from increasing
basis triples. A `SecondOrderSolver` connects actual adjoint cochains to a
linear image test. Its two certificate identities imply a computed correction,
nonexistence off the obstruction locus and a description of all corrections.
The checked examples retain exact rational inputs and independently prove the
emitted quadratic identities. No assertion that the resulting cokernel is H3
enters the construction. The separate H3 layer supports characteristic-zero
parameter families, including real and complex fields.

`LieDeformationGauge` bridges first-order normalization and second-order
solvers. It checks the inverse and composition of `1 + εφ + ε²ψ`, derives
correction transport from full jet bracket preservation and proves that the
second-order residual is preserved for closed directions. Applying a certified
cokernel projection proves equality of obstruction coordinates, not merely
agreement of their zero loci. The checked examples substitute complete H2 representative matrices into the
quadratic equations and prove that bridge separately. Solving in that smaller
space returns a correction in the original
generators and an actual second-order equivalence; two solvers may choose
different corrections differing by a cocycle.

`LieCohomology3` and `FiniteLieCohomology3` supply alternating three-cochains,
`d3 d2 = 0`, the actual quotient and the transport of checked matrix reductions.
`LieDeformationObstruction` places the closed quadratic Jacobi obstruction in
that quotient. The rational and polynomial-parameter H3 frontends prove both
CE coordinate bridges and every certificate identity.

`LieDeformationThirdOrder` takes a first direction and a specified second
correction. Its carrier `(V × V × V) × V` retains the old second jet as the
first component. Full Jacobi is equivalent to all three coefficient equations.
A polarized Bianchi identity together with the self Bianchi identity proves
closedness of the next obstruction under the two lower equations, without
characteristic restrictions. `LieDeformationThirdObstruction` then turns any
existing adjoint `ThirdReduction` into a third-order solver, actual model
constructor and complete description of third corrections. Choice dependence is explicit: no canonical third obstruction on H2 is
asserted. Higher-order recursion and third-order generator equivalence remain
separate developments.

`LieDeformationThirdSearch` assembles the two remaining correction equations
into an affine block system for a fixed first direction. An explicit
`JointReduction` is a complete image certificate for this map, with a zero
outgoing differential; its cokernel is not identified with CE H3. Full paired
cochain coordinates connect exact rational matrices to unrestricted second and
third corrections. All solutions are characterized by the joint kernel. A
four-dimensional checked example separates second-order from third-order
existence even when all second choices are allowed.

`GhostDerivation` extends even finite generator images by Grassmann left
derivatives and proves a necessary-and-sufficient finite nilpotency criterion.
`LieGhost` constructs canonical increasing-pair quadratic images and a
degree-one CE bridge. `LieGhostComplex` adds increasing triples, the degree-two
bridge and canonical nilpotency from d2 d1 = 0 over every commutative ring.
`LieGhostFamily` proves an exact parameter closedness locus, including rings
with zero divisors. `GhostDegree` supplies actual integer pieces, homogeneous
projection and boundary criteria; the public API exports
these shifts alongside its original parity API. `LieGhostCohomology` then recovers
ordered cochain coordinates, proves complete degree-two coordinates and reflects
closedness and arbitrary-polynomial exactness. An actual quotient equivalence
transfers scalar CE H2 reductions to ghost class coordinates and normal forms.
The Heisenberg and weight-family examples compute H2, retaining all parameter
and characteristic-dependent resonances. Certified matter actions now define
a tensor differential with low-degree CE bridges; negative-degree antighosts,
higher matter quotient computations and all-degree chain equivalences remain
future work. The current scope and physical boundary are recorded in the
[capability inventory](capabilities.md).

## Import policy

Use a selective `LeanPhy.Entry.*` profile in research files.  Import
`LeanPhy.Entry.Physics` only for projects that genuinely span several domains;
the umbrella import is convenient but slower.  New public definitions should
live in a focused module, be exported by an appropriate entry profile, and have
at least one positive and one negative regression.

`LieGhostMatter` forms `GhostPolynomial R n ⊗[R] M` from a certified Lie module.
It derives nilpotency from the representation law, proves the signed module
product rule and raises integer ghost degree. `LieGhostMatterCohomology` recovers
one/two-cochain coefficients, proves CE d0/d1 bridges and characterizes every
actual degree-zero cycle by its unique invariant vector. No product on `M`, finite
matter basis, or physical interpretation is assumed. Generated ghost models expose
this API while retaining the pure-bracket JSON schema; representation input and
higher matter quotient computations are separate extensions.

## Actual finite-source self-consistency

`SourceFeedback` composes actual `SourceEnsemble` probabilities and covariance
bounds with `ContractionCertificate`. `FeedbackCertificate.Envelope` carries
finite observable/coupling bounds; `automatic` constructs them by finite maxima.
The library derives the contraction instead of requiring it as a model field.
Residuals, approximate-update errors and readout-evaluation errors remain distinct.
`MeanFieldFunctional` connects actual covariance derivatives, stationary functionals
and beta-scaled energy conventions. See [scope and usage](self-consistency.md).
The defined closure does not assert an approximation theorem for the original
interacting model, and its mathematical fixed point is not a numerical solver.

`Mathematics.RationalExp` derives exact rational exponential enclosures from
Taylor remainders and repeated squaring. `StatMech.GibbsCertificate` combines
these with a positive partition lower bound and a centered readout residual;
a common exponent shift cancels from the actual normalized expectation.
The source and feedback adapters check numerical candidates against the actual
finite model and feed the existing solution/readout bounds. `gibbs_certificate.py`
emits data and kernel-reduced acceptance goals; model tables and target outputs
remain checker indices. General input uncertainty, other functions and scalable
local solvers remain open. See [numerical Gibbs certificates](numerical-gibbs.md).
