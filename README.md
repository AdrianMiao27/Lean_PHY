# LeanPhy

LeanPhy is a theoretical-physics formalisation library built on **Lean 4 and
mathlib**. It keeps Lean's syntax, type checker, editor support, theorem
library, tactics, Lake build, and CI workflow, and adds physics objects,
notation, reusable theorems, and a ledger for research boundaries. It is not a
Lean fork and it does not introduce a second proof logic.

> **Positioning:** have Lean check the mathematical steps of a theoretical-
> physics derivation that can be formalised, while recording unfinished
> analysis, modelling assumptions, and physical interpretation as explicit open
> obligations.

[![Lean](https://img.shields.io/badge/Lean-4.34.0-5f5f5f.svg)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.34.0-7b68ee.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://img.shields.io/github/actions/workflow/status/AdrianMiao27/Lean_PHY/leanphy.yml?label=CI)](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

中文说明：[README.zh-CN.md](README.zh-CN.md)

## Read the verification boundary first

LeanPhy checks **conditional correctness**: whether a conclusion follows from
the mathematical assumptions, physical conventions, and certificates that are
explicitly stated. A `checked claim` should therefore be read as:

> Under the listed premises, the conclusion follows from Lean's proof rules.

LeanPhy does not decide whether a model describes the real world or a particular
experiment. It also does not silently turn any of the following into a theorem:

- the existence of a continuum, thermodynamic, or renormalisation limit;
- the existence or convergence of a path integral, or its intended physical
  interpretation;
- the domain, self-adjointness, or time-evolution conditions of an unbounded
  operator;
- the physical meaning assigned to a formal object.

These matters must be stated as explicit propositions, structure fields, or
user-supplied certificates. Unfinished analytical properties, physical premises,
and interpretation work are recorded as **open obligations** in the research
ledger. Every checked conclusion contains a Lean proof term, and the Lean
kernel checks that term. A CAS, numerical program, or external script crosses
into the verified layer only through a Lean-side soundness theorem such as
`CertificateChecker.sound`; an unchecked Boolean, JSON file, numerical output,
limit, or approximation does not become a theorem by itself.

```text
explicit assumptions/certificates -> Lean proof term -> Lean kernel -> checked conditional conclusion
                                             └ unfinished analysis and modelling premises -> open-obligation ledger
```

## Version 1.0 scope

LeanPhy v1.0.0 targets finite-dimensional, truncated, and bounded objects.
It also provides interfaces for unbounded operators, continuous analysis,
numerical computation, and external programs. Those interfaces require proofs
or certificates supplied by the user; they do not fill in missing mathematics
or physics.

The current regression baseline contains **209 Lean source files, 473 smoke
checks, and 141 expected-failure elaboration tests**. The default
`leanphy_check --project-json` report contains **8 domain packages, 15 checked
claims, and 8 open obligations**. With `--broad`, it contains **13 domain
packages, 28 checked claims, and 14 open obligations**. These numbers describe
library and regression coverage, not the number of complete physics papers.

| Area | Reusable foundations | Boundary that remains explicit |
| --- | --- | --- |
| Quantum mechanics and information | Pauli and Dirac notation, finite states and density matrices, POVMs, CPTP/Kraus channels, Bell/CHSH, finite Lindblad models, oscillator and CCR algebra | Unbounded-operator domains, self-adjointness, continuous-measurement semantics, and the correspondence between a finite model and a physical system |
| Field and high-energy algebra | Finite truncated Fock spaces, CAR/CCR and Wick identities, Clifford/gamma matrices, spinors, traces, Ward-style algebraic steps, finite EFT expansions and truncation certificates, and ungraded/graded BRST interfaces | Field existence, infinite-dimensional limits, UV completion, renormalisation limits, a concrete ghost algebra, BV structure, anomaly cancellation, and non-perturbative conclusions |
| Classical, gauge, relativity, optics, and fluids | Poisson algebras, first-class constraint ideals, constraint-preserving maps, weak equality, Dirac observables, discrete Maxwell/Yang–Mills, exterior and plaquette identities, symplectic and Lorentz algebra, ABCD/Jones optics, finite-volume conservation, and discrete vorticity | Gauge fixing, regularity of the reduced space, continuum regularity, global existence, boundary physics, and turbulence closure |
| Condensed matter and statistical mechanics | Lattice, Hubbard, BdG, Berry, Jordan–Wigner, finite Gibbs/Markov kernels, and transfer matrices | Thermodynamic limits, phase transitions, experimental calibration, and equivalence with a continuum theory |
| Analysis and numerical bridges | Bochner integration, dominated convergence, Lax–Milgram, Banach fixed points, bounded Hilbert operators, spectral calculus, spectral gaps, operator convergence, residual/energy budgets, finite path integrals, and regulator-wise certificates | External programs provide traceable data only; a Lean-side `CertificateChecker.sound` theorem is still required before a result enters the verified layer |

The unbounded-operator interface uses mathlib's `LinearPMap` while retaining the
declared domain in the type. `DenseDomainOperator` exposes interfaces for
formal adjoints, closedness/closability, self-adjointness, graph-norm relative
bounds, and bounded domain-preserving composition; each consumes a user-supplied
proof. Calling an object a `Hamiltonian` does not prove self-adjointness or
generate time evolution. Stone's theorem, self-adjoint extensions, spectral
measures, and the bridge from resolvents to evolution groups remain open
obligations.

For constrained and gauge systems, `ConstraintAlgebra` and `ConstraintMap`
cover generated constraint ideals, first-class closure, weak equality, Dirac
observables, and Poisson maps preserving constraint ideals. `BRST` requires the
user to supply a derivation and a nilpotency proof. `GradedBRST` adds homogeneous
pieces, an odd degree shift, the signed Koszul Leibniz rule, and graded
cohomology vocabulary. Neither module claims to construct a complete ghost
algebra, BV antibracket, gauge fixing, path-integral measure, anomaly
cancellation, or an equivalence between BRST cohomology and physical
observables. Those belong in a concrete model or in the open-obligation ledger.

See [VERIFIED.md](VERIFIED.md) and [docs/verified-scope.md](docs/verified-scope.md)
for the module-by-module inventory and limitations.

## Quick start

Lean 4.34.0 is pinned in [`lean-toolchain`](lean-toolchain). After installing
that version, run from the repository root:

```bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
```

The release verification script also checks public entry points, downstream
clients, research ledgers, declaration audits, project scaffolding, and
negative tests:

```bash
./scripts/verify.sh
```

A local ext4 or overlay filesystem is recommended. Mathlib imports and cache
access can be substantially slower on FUSE or network-mounted filesystems.

## Minimal example: derive a commutator identity from a CCR premise

This is ordinary Lean code. `hCCR` is an explicit CCR premise, and the
conclusion comes from a theorem that has compiled and passed kernel checking:

```lean
import LeanPhy.Entry.Quantum
import LeanPhy.Entry.FieldTheory
open scoped LeanPhy.Quantum

example {R : Type} [Ring R] (a adag : R)
    (hCCR : ⟦a, adag⟧ = 1) :
    ⟦LeanPhy.FieldTheory.number adag a, adag⟧ = adag := by
  exact LeanPhy.FieldTheory.number_commutator a adag hCCR
```

This verifies the algebraic implication from the CCR premise. It does not prove
the existence of an unbounded Hilbert-space representation satisfying the CCR,
or that such a representation describes an experiment. The finite-EFT
interface likewise puts truncation order, coefficient bounds, and error budgets
in theorem arguments; the finite path-integral interface requires an explicit
normalisation certificate. If a required premise is missing, elaboration fails
instead of producing an unconditional conclusion.

## Recommended research workflow

1. Import the smallest suitable `LeanPhy.Entry.*` profile to keep dependencies
   and compile times under control.
2. State mathematical premises, physical conventions, boundary conditions,
   truncation ranges, and approximation parameters as types, structure fields,
   or theorem arguments.
3. Use reusable theorems and tactics for algebraic steps. If a CAS or numerical
   program is used, import its result through an interface with a
   `CertificateChecker.sound` theorem.
4. Register the result as a `checked claim` in a `TheoryPackage` or
   `ResearchProject`; record unfinished analysis, interpretation, continuum
   work, and other modelling premises as `open obligations`.
5. Run `leanphy_check` and `scripts/verify.sh`, then inspect both the human-
   readable and JSON reports.

`VERIFIED-CONDITIONAL` means that the proof terms compiled and passed kernel
checking. It does not mean that the model has been experimentally validated or
that the listed open obligations have been discharged.

Run the soundness audit separately when reviewing a release:

```bash
lake env lean scripts/axioms.lean
```

The project source and acceptance entry points do not use `sorry`, `admit`, or
application-specific unchecked axioms. `#print axioms` may list standard
foundational axioms used by Lean/mathlib, such as `propext`,
`Classical.choice`, and `Quot.sound`; that is different from declaring a
physics result as an axiom.

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
  Surface/                Dirac, Einstein, index, and dimensional notation
  Entry/                  selective public import profiles
  Examples/               workflow and research-project examples
Main.lean                kernel regression entry point
Prototype.lean           end-to-end closed-loop prototype
Check.lean               research-ledger CLI
scripts/                 release verification and negative tests
docs/                    architecture, roadmap, and scope
```

Common entry points are `LeanPhy.Minimal`, the domain-specific
`LeanPhy.Entry.*` profiles, and `LeanPhy.Entry.Physics` for projects spanning
several domains.

## Reports, development, and citation

```bash
lake exe leanphy_check --project-json
lake exe leanphy_check --broad --claims-json
lake exe leanphy_check --extended --manifest-json
```

New modules should provide reusable theorems, explicit hypotheses, a positive
smoke regression, any necessary negative regression, and documentation. See
[CONTRIBUTING.md](CONTRIBUTING.md), [docs/architecture.md](docs/architecture.md),
and [docs/roadmap.md](docs/roadmap.md).

The package version is 1.0.0; Lean and mathlib are pinned in
[`lean-toolchain`](lean-toolchain) and [`lakefile.toml`](lakefile.toml). When
citing LeanPhy, record the commit, toolchain, mathlib revision, import profile,
and generated ledger JSON. Citation metadata is in [CITATION.cff](CITATION.cff).
LeanPhy is released under the Apache License 2.0.
