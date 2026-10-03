# LeanPhy v1

LeanPhy is a Lean 4 and mathlib library for formal verification of derivations
in theoretical physics. A derivation is expressed as a Lean proposition with
explicit assumptions, and the Lean kernel checks the resulting proof term.

The question LeanPhy answers is precise: **does the conclusion follow from the
declared assumptions?** This is conditional verification of derivation validity.
Whether a model describes nature, whether a continuum or thermodynamic limit
exists, whether a path integral has a rigorous definition, and whether a
physical interpretation is adequate are separate research questions. They must
be represented by explicit hypotheses, certificates, or open obligations; a
description in prose does not become a theorem by itself.

[![Lean](https://img.shields.io/badge/Lean-4.34.0-5f5f5f.svg)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.34.0-7b68ee.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml/badge.svg)](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

中文说明：[README.zh-CN.md](README.zh-CN.md)

## Project position

LeanPhy v1 uses Lean's native syntax, type system, elaborator, tactics, Lake
builds, and CI workflow. It adds physics-oriented types, theorems, tactics,
surface notation, and research ledgers so that existing derivations can be
introduced incrementally. It does not create a second proof logic alongside
Lean.

The first release focuses on finite-dimensional, truncated, and bounded
objects. Analysis and continuum interfaces are available when the user supplies
the required continuity, integrability, domain, stability, or convergence
proofs. The acceptance baseline contains 203 Lean source files, 446 kernel
regression capabilities, 130 negative elaboration fixtures, and a research
ledger spanning 13 domain packages with 26 checked claims and 13 open
obligations. These figures describe library coverage and regression tests; they
do not mean that an equivalent number of complete physics papers has been
formalized.

## Scope

| Area | Included in v1 | Boundary |
| --- | --- | --- |
| Quantum mechanics and information | Pauli and Dirac notation, density matrices, POVMs, CPTP/Kraus channels, Bell/CHSH, finite Lindblad models, oscillator and CCR algebra | Primarily finite-dimensional matrices and explicit algebraic assumptions |
| Field and high-energy algebra | Finite Fock/CAR/CCR/Wick identities, Clifford and gamma matrices, spinors, traces, and Ward-style algebraic steps | Field existence, infinite-dimensional limits, and non-perturbative results require separate work |
| Condensed matter and statistical mechanics | Lattice, Hubbard, BdG, Berry, Jordan–Wigner, finite Gibbs and Markov kernels, and transfer matrices | Thermodynamic and phase-transition limits remain explicit obligations |
| Gauge, classical, relativistic, optical, and fluid models | Discrete Maxwell/Yang–Mills, exterior and plaquette identities, symplectic and Lorentz algebra, ABCD/Jones optics, finite-volume conservation, and discrete vorticity | Continuum regularity and global existence do not follow from a finite model automatically |
| Mathematical and numerical bridges | Bochner integration, dominated convergence, Lax–Milgram, Banach fixed points, bounded Hilbert operators, spectral calculus, spectral gaps, operator convergence, residual/energy budgets, finite path integrals, and regulator-wise certificates | Every analytic conclusion requires its hypotheses or a proof term; numerical output alone is not a proof |

The following remain open or conditional interfaces in v1: self-adjointness of
general unbounded Hamiltonians, Stone's theorem, general spectral measures,
infinite-dimensional path measures, Osterwalder–Schrader reconstruction, full
renormalization limits, Navier–Stokes regularity, and non-perturbative QFT
existence. See [VERIFIED.md](VERIFIED.md) and
[docs/verified-scope.md](docs/verified-scope.md) for the detailed boundary.

## Quick start

Install Lean 4.34.0, then run the following commands from the repository root:

```bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
```

The complete release gate also runs declaration audits, research-package
ledgers, downstream clients, scaffold generation, and negative elaboration
tests:

```bash
./scripts/verify.sh
```

A local ext4 or overlay filesystem is recommended. Mathlib imports and cache
access can be substantially slower on FUSE or network-mounted filesystems.

## A minimal checked derivation

LeanPhy uses ordinary Lean declarations and tactics. In the following example,
`adag` denotes the creation operator `a†`, and the CCR assumption is passed to
a checked commutator theorem:

```lean
import LeanPhy.Entry.Quantum
import LeanPhy.Entry.FieldTheory
open scoped LeanPhy.Quantum

example {R : Type} [Ring R] (a adag : R)
    (hCCR : ⟦a, adag⟧ = 1) :
    ⟦LeanPhy.FieldTheory.number adag a, adag⟧ = adag := by
  exact LeanPhy.FieldTheory.number_commutator a adag hCCR
```

Public entry points include `LeanPhy.Minimal`, selective `LeanPhy.Entry.*`
profiles, and `LeanPhy.Entry.Physics` for projects spanning several domains.
`LeanPhy/Workflow.lean` records named assumptions, models, proof-bearing
claims, dependencies, certificates, and open obligations. The `physics` and
`physics_search` tactics, Dirac notation, Einstein sums, index variance, and
dimension-aware quantities are exposed through the corresponding modules while
remaining part of the native Lean workflow.

## Research workflow

For a new derivation:

1. Import the smallest suitable `LeanPhy.Entry.*` profile.
2. State mathematical premises, physical conventions, boundary conditions, and
   approximation ranges as types, structure fields, or theorem arguments.
3. Prove algebraic steps with reusable theorems and tactics. If a CAS or
   numerical program is used, bring its output across the boundary through a
   `CertificateChecker.sound` theorem.
4. Register the result as a checked claim in a `TheoryPackage` or
   `ResearchProject`, with dependencies and unresolved obligations listed.
5. Run `leanphy_check` and `scripts/verify.sh`, and inspect both the human and
   JSON reports.

The trust boundary is:

```text
explicit assumptions + Lean proof term  ── Lean kernel ──>  checked conclusion
```

Runtime booleans, unchecked JSON, uncertified numerical output, and implicit
continuum limits do not acquire theorem status.

## Repository layout

```text
LeanPhy/                 library source grouped by physics domain
  Mathematics/            analysis, operators, spectra, limits, certificates
  Quantum/ QuantumInfo/   quantum mechanics and quantum information
  FieldTheory/            CCR/CAR/Fock/Wick algebra
  HighEnergy/ GaugeTheory/ high-energy and gauge algebra
  Condensed/ StatMech/     condensed-matter and statistical models
  Classical/ Relativity/  classical and relativistic structures
  Surface/                Dirac, Einstein, index, and dimension notation
  Entry/                  selective public import profiles
  Examples/               workflow and research-project examples
Main.lean                kernel regression entry point
Prototype.lean           compact end-to-end workflow executable
Check.lean               research-ledger CLI executable
scripts/                 release verification and negative tests
docs/                    architecture, roadmap, and scope documents
.github/                 CI, issue templates, and pull-request template
```

## Reports, development, and citation

The CLI provides human-readable and machine-readable ledgers:

```bash
lake exe leanphy_check --project-json
lake exe leanphy_check --broad --claims-json
lake exe leanphy_check --extended --manifest-json
```

The default report keeps unresolved obligations visible and uses the status
`VERIFIED-CONDITIONAL`. Use `--strict` when a CI job should fail while any open
obligation remains. New modules should provide reusable theorems, explicit
hypotheses, a positive smoke regression, any necessary negative regression, and
documentation. See [CONTRIBUTING.md](CONTRIBUTING.md),
[docs/architecture.md](docs/architecture.md), and
[docs/roadmap.md](docs/roadmap.md).

This repository is version `1.0.0`, with Lean and mathlib pinned in
[lean-toolchain](lean-toolchain) and [lakefile.toml](lakefile.toml). When citing
LeanPhy, record the commit, toolchain, mathlib revision, import profile, and
generated ledger JSON; citation metadata is provided in [CITATION.cff](CITATION.cff).
LeanPhy is released under the [Apache License 2.0](LICENSE).
