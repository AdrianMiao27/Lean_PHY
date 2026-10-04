# LeanPhy v1.0

LeanPhy is a Lean 4 / mathlib library for formalising and checking derivations in theoretical physics. It keeps Lean's language, type system, editor support, theorem library, tactics, Lake build, and CI workflow, while adding physics notation, domain objects, reusable theorems, and a research ledger. LeanPhy uses the same logic and kernel as an ordinary Lean project; it does not introduce a second proof system.

The goal is to make theoretical-physics derivations **compilable, reproducible, and auditable**. LeanPhy is designed for symbolic derivations, finite models, and mathematical steps whose assumptions have been stated explicitly. It does not hide unfinished physical or analytical premises.

[![Lean](https://img.shields.io/badge/Lean-4.34.0-5f5f5f.svg)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.34.0-7b68ee.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://img.shields.io/github/actions/workflow/status/AdrianMiao27/Lean_PHY/leanphy.yml?label=CI)](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

中文说明：[README.zh-CN.md](README.zh-CN.md)

## Verification boundary

LeanPhy checks **conditional correctness**: whether a conclusion follows from assumptions that have been stated. A checked theorem should therefore be read as: if the listed mathematical premises, physical conventions, and certificates hold, then the conclusion follows.

LeanPhy does not decide:

- whether a model describes the real world;
- whether a continuum, thermodynamic, or path-integral limit exists;
- whether an unbounded-operator manipulation satisfies domain and self-adjointness conditions;
- whether a mathematical object has the intended physical interpretation.

These matters must appear as explicit propositions, structure fields, external certificates, or open obligations in the research ledger. Every checked result has a proof term checked by the Lean kernel. An external CAS or program can enter the verified layer only through a Lean-side `CertificateChecker.sound` theorem. Unchecked runtime booleans, JSON, numerical output, limits, and approximations do not acquire theorem status.

```text
explicit assumptions and certificates  ->  Lean proof term  ->  Lean kernel  ->  conditional checked conclusion
```

## Current status and scope

Version 1.0.0 focuses on finite-dimensional, truncated, and bounded objects. It also offers interfaces for unbounded operators, continuous analysis, numerical computation, and external programs that require user-supplied proofs or certificates. The current regression baseline contains **209 Lean source files, 473 smoke checks, and 141 expected-failure elaboration tests**. The research ledger contains 13 domain packages, 28 kernel-checked claims, and 14 open obligations. These figures describe library and regression coverage; they are not a count of complete physics papers.

| Area | Available foundations | Separate proof or ledger obligation |
| --- | --- | --- |
| Quantum mechanics and information | Pauli and Dirac notation, finite states and density matrices, POVMs, CPTP/Kraus channels, Bell/CHSH, finite Lindblad models, oscillator and CCR algebra | Unbounded-operator domains, self-adjointness, continuous-measurement semantics, and the correspondence between a finite model and a physical system |
| Field and high-energy algebra | Finite Fock spaces, CAR/CCR and Wick identities, Clifford/gamma matrices, spinors, traces, Ward-style algebraic steps, finite EFT expansions and truncation certificates, plus ungraded and graded BRST interfaces | Field existence, infinite-dimensional limits, UV completion, renormalisation limits, a concrete ghost algebra, BV structure, anomaly cancellation, and non-perturbative conclusions |
| Classical, gauge, relativity, optics, and fluids | Poisson algebras, first-class constraint ideals, constraint-preserving maps, weak equality, Dirac observables, discrete Maxwell/Yang–Mills, exterior and plaquette identities, symplectic and Lorentz algebra, ABCD/Jones optics, finite-volume conservation, and discrete vorticity | Gauge fixing, regularity of the reduced space, continuum regularity, global existence, boundary physics, and turbulence closure |
| Condensed matter and statistical mechanics | Lattice, Hubbard, BdG, Berry, Jordan–Wigner, finite Gibbs/Markov kernels, and transfer matrices | Thermodynamic limits, phase transitions, experimental calibration, and equivalence with a continuum theory |
| Mathematical analysis and numerical bridges | Bochner integration, dominated convergence, Lax–Milgram, Banach fixed points, bounded Hilbert operators, spectral calculus, spectral gaps, operator convergence, residual/energy budgets, finite path integrals, and regulator-wise certificates | External programs provide traceable data only; a Lean-side `CertificateChecker.sound` theorem is required before a result can enter the verified layer |

The unbounded-operator layer uses mathlib's `LinearPMap` and keeps the declared domain in the type. `DenseDomainOperator` provides interfaces for formal adjoints, closedness and closability, self-adjointness, graph-norm relative bounds, and domain-preserving bounded composition; each interface consumes a user-supplied proof. Naming an object `Hamiltonian` does not prove self-adjointness or generate time evolution. Stone's theorem, self-adjoint extensions, spectral measures, and the resolvent-to-evolution bridge remain open obligations.

`LeanPhy.Mathematics.SymmetryReduction` covers admissible states, group actions, orbit transport, and invariant observables for constrained systems. `ConstraintAlgebra` and `ConstraintMap` cover constraint-generated ideals, first-class closure, weak equality, Dirac observables, and Poisson maps that preserve constraint ideals. They do not construct a gauge slice, prove that a quotient is a manifold, or interpret gauge equivalence as physical equivalence.

`LeanPhy.Mathematics.BRST` provides an ungraded algebraic pre-layer: users supply a derivation and a nilpotency proof, after which the library defines closed, exact, and cohomologous elements and their basic transport theorems. `LeanPhy.Mathematics.GradedBRST` adds homogeneous pieces, an explicitly odd degree shift, the signed Koszul Leibniz rule, and a graded cohomology interface. Neither module constructs a concrete ghost algebra, BV antibracket, gauge fixing, path-integral measure, anomaly-cancellation theorem, or physical-equivalence theorem; those must be supplied by later models or recorded as open obligations.

See [VERIFIED.md](VERIFIED.md) and [docs/verified-scope.md](docs/verified-scope.md) for the module-by-module inventory and limitations.

## Quick start

Lean 4.34.0 is pinned in [`lean-toolchain`](lean-toolchain). After installing that version, run from the repository root:

```bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
```

The release verification script also checks public entry points, downstream clients, research ledgers, declaration audits, project scaffolding, and negative tests:

```bash
./scripts/verify.sh
```

A local ext4 or overlay filesystem is recommended. Mathlib imports and cache access can be much slower on FUSE or network-mounted filesystems.

## Minimal example: a commutator derived from a CCR premise

This is ordinary Lean code. `hCCR` is an explicit CCR premise, and the conclusion comes from a theorem that has compiled and passed kernel checking:

```lean
import LeanPhy.Entry.Quantum
import LeanPhy.Entry.FieldTheory
open scoped LeanPhy.Quantum

example {R : Type} [Ring R] (a adag : R)
    (hCCR : ⟦a, adag⟧ = 1) :
    ⟦LeanPhy.FieldTheory.number adag a, adag⟧ = adag := by
  exact LeanPhy.FieldTheory.number_commutator a adag hCCR
```

The finite-EFT interface puts truncation order, coefficient bounds, and error budgets in theorem arguments. The finite path-integral interface requires an explicit normalisation certificate. If a required premise is missing, elaboration fails instead of producing an unconditional conclusion.

## Recommended research workflow

1. Import the smallest suitable `LeanPhy.Entry.*` profile to keep dependencies and compile times under control.
2. State mathematical premises, physical conventions, boundary conditions, truncation ranges, and approximation parameters as types, structure fields, or theorem arguments.
3. Prove algebraic steps with reusable theorems and tactics. If a CAS or numerical program is used, import its result through an interface with a `CertificateChecker.sound` theorem.
4. Register the result as a `checked claim` in a `TheoryPackage` or `ResearchProject`; record unfinished analysis, interpretation, and continuum work as `open obligations`.
5. Run `leanphy_check` and `scripts/verify.sh`, then inspect both the human-readable and JSON reports.

`VERIFIED-CONDITIONAL` means that the proof terms compiled and passed kernel checking while explicitly listed open obligations may remain.

## Repository layout

```text
LeanPhy/                 library source grouped by physics domain
  Mathematics/            analysis, operators, spectra, limits, certificates, models
  Quantum/ QuantumInfo/   quantum mechanics and quantum information
  FieldTheory/            CCR/CAR/Fock/Wick algebra
  HighEnergy/             Clifford, gamma, spinor, and finite EFT interfaces
  GaugeTheory/            gauge fields and discrete geometric algebra
  Condensed/ StatMech/    condensed-matter and statistical models
  Classical/ Relativity/  classical mechanics and relativity structures
  Surface/                Dirac, Einstein, index, and dimension notation
  Entry/                  selective public import profiles
  Examples/               workflow and research-project examples
Main.lean                kernel regression entry point
Prototype.lean           end-to-end closed-loop prototype
Check.lean               research-ledger CLI
scripts/                 release verification and negative tests
docs/                    architecture, roadmap, and scope
```

Common entry points are `LeanPhy.Minimal`, the domain-specific `LeanPhy.Entry.*` profiles, and `LeanPhy.Entry.Physics` for projects that combine several domains.

## Reports, development, and citation

```bash
lake exe leanphy_check --project-json
lake exe leanphy_check --broad --claims-json
lake exe leanphy_check --extended --manifest-json
```

New modules should provide reusable theorems, explicit hypotheses, a positive smoke regression, any necessary negative regression, and documentation. See [CONTRIBUTING.md](CONTRIBUTING.md), [docs/architecture.md](docs/architecture.md), and [docs/roadmap.md](docs/roadmap.md).

The package version is 1.0.0; Lean and mathlib are pinned in [`lean-toolchain`](lean-toolchain) and [`lakefile.toml`](lakefile.toml). When citing LeanPhy, record the commit, toolchain, mathlib revision, import profile, and generated ledger JSON. Citation metadata is in [CITATION.cff](CITATION.cff). LeanPhy is released under the Apache License 2.0.
