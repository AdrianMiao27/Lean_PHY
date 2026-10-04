# LeanPhy v1 architecture

LeanPhy is deliberately a library on top of Lean 4 and mathlib.  It does not
fork the Lean kernel and it does not introduce a second proof logic.  A physics
project therefore uses the normal Lean editor, elaborator, `lake build`, and CI
workflow.

## Layers

### Kernel and mathlib

Lean's kernel checks every proposition and proof term.  mathlib supplies the
trusted mathematical foundation used by the library, including algebra,
topology, measure theory, functional analysis, and finite-dimensional linear
algebra.  Tactics are proof-producing elaborators; their output is still
checked by the kernel.

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

## Import policy

Use a selective `LeanPhy.Entry.*` profile in research files.  Import
`LeanPhy.Entry.Physics` only for projects that genuinely span several domains;
the umbrella import is convenient but slower.  New public definitions should
live in a focused module, be exported by an appropriate entry profile, and have
at least one positive and one negative regression.
