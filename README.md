# LeanPhy v1

LeanPhy is a Lean 4 / mathlib library for formalising and checking derivations in theoretical physics. It keeps Lean's language, type system, editor, theorem library, tactics, Lake build, and CI workflow, and adds physics objects, notation, reusable theorems, domain-specific entry modules, and a research ledger.

The project aims to make a theoretical-physics derivation **compilable, reproducible, and auditable**. LeanPhy is a physics extension for Lean: it uses the same language and kernel as ordinary Lean projects and does not introduce a second proof logic.

[![Lean](https://img.shields.io/badge/Lean-4.34.0-5f5f5f.svg)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.34.0-7b68ee.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://img.shields.io/github/actions/workflow/status/AdrianMiao27/Lean_PHY/leanphy.yml?label=CI)](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

中文说明：[README.zh-CN.md](README.zh-CN.md)

## Verification boundary

LeanPhy checks **conditional correctness**: whether a conclusion follows from the assumptions that have been stated. It does not decide whether a model describes the real world, whether a continuum limit or path integral exists, or whether a physical interpretation is correct; none of those premises is promoted to a theorem automatically. It checks the logical validity of a derivation; it does not decide whether the model is physically adequate.

A result enters the verified layer only as a Lean proposition with a proof term checked by the Lean kernel, or through an external-certificate interface with a Lean-side `sound` theorem. Unfinished analysis, numerical-reliability arguments, and physical premises remain in the open-obligation ledger.

```text
explicit assumptions + Lean proof term  ── Lean kernel ──>  conditional checked conclusion
```

Runtime booleans, unchecked JSON, uncertified CAS or numerical output, and limits or approximations that have not been stated explicitly as propositions do not acquire theorem status.

## Current scope

Version 1.0.0 concentrates on finite-dimensional, truncated, and bounded objects. It also provides interfaces for unbounded operators, continuous analysis, numerical computation, and external programs that require user-supplied proofs or certificates. The current regression baseline contains **207 Lean source files, 465 smoke regression checks, and 139 negative elaboration fixtures**. The research ledger contains 13 domain packages, 28 kernel-checked claims, and 14 open obligations. These figures describe library and regression coverage; they are not a count of complete physics papers.

| Area | Available foundations | Separate proof or ledger obligation |
| --- | --- | --- |
| Quantum mechanics and information | Pauli/Dirac notation, finite states and density matrices, POVMs, CPTP/Kraus channels, Bell/CHSH, finite Lindblad models, oscillator and CCR algebra | Unbounded-operator domains, self-adjointness, continuous measurement semantics, and the correspondence between a finite model and a physical system |
| Field and high-energy algebra | Finite Fock, CAR/CCR, and Wick identities, Clifford/gamma matrices, spinors, traces, Ward-style algebraic steps, finite EFT expansions, and truncation certificates | Field existence, infinite-dimensional limits, UV completion, renormalisation limits, and non-perturbative conclusions |
| Classical, gauge, relativity, optics, and fluids | Poisson algebras, first-class constraint ideals, constraint-preserving maps, weak equality, Dirac observables, discrete Maxwell/Yang–Mills, exterior and plaquette identities, symplectic and Lorentz algebra, ABCD/Jones optics, finite-volume conservation, and discrete vorticity | Gauge fixing, regularity of the reduced space, continuum regularity, global existence, boundary physics, and turbulence closure |
| Condensed matter and statistical mechanics | Lattice, Hubbard, BdG, Berry, Jordan–Wigner, finite Gibbs/Markov kernels, and transfer matrices | Thermodynamic limits, phase transitions, experimental calibration, and equivalence with a continuum theory |
| Mathematical and numerical bridges | Bochner integration, dominated convergence, Lax–Milgram, Banach fixed points, bounded Hilbert operators, spectral calculus, spectral gaps, operator convergence, residual/energy budgets, finite path integrals, and regulator-wise certificates | External programs provide traceable data only; a Lean-side `CertificateChecker.sound` theorem is required before a result can enter the verified layer |

The unbounded-operator layer uses mathlib's `LinearPMap` while preserving the declared domain in the type. `DenseDomainOperator` provides formal-adjoint, closedness/closability, self-adjointness, graph-norm relative-bound, and domain-preserving composition interfaces; each consumes a user-supplied proof. Naming an object `Hamiltonian` does not prove self-adjointness or generate a time evolution. Stone's theorem, general self-adjoint extensions, spectral measures, and the resolvent-to-evolution bridge remain open obligations.

`LeanPhy.Mathematics.SymmetryReduction` covers admissible states, group actions, orbit transport, and invariant observables for constrained systems. `LeanPhy.Mathematics.ConstraintAlgebra` adds constraint-generated ideals, first-class closure, weak equality, and algebraic closure of Dirac observables in commutative Poisson algebras. `ConstraintMap` adds composable Poisson maps that preserve constraint ideals; transport of Dirac observables requires an explicit target-ideal cover. These modules do not construct a gauge slice, prove that a quotient is a manifold, or interpret gauge equivalence as physical equivalence.

See [VERIFIED.md](VERIFIED.md) and [docs/verified-scope.md](docs/verified-scope.md) for the per-module inventory and limitations.

## Quick start

Lean 4.34.0 is pinned in [`lean-toolchain`](lean-toolchain). After installing that version, run from the repository root:

```bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
```

The release verification script also checks public entry points, downstream clients, research ledgers, declaration audits, project scaffolding, and negative fixtures:

```bash
./scripts/verify.sh
```

A local ext4 or overlay filesystem is recommended. Mathlib imports and cache access can be much slower on FUSE or network-mounted filesystems.

## Minimal example: a commutator derived from a CCR premise

This is ordinary Lean code. `hCCR` is an explicit CCR premise, and the conclusion is obtained from a theorem that has compiled and passed kernel checking:

```lean
import LeanPhy.Entry.Quantum
import LeanPhy.Entry.FieldTheory
open scoped LeanPhy.Quantum

example {R : Type} [Ring R] (a adag : R)
    (hCCR : ⟦a, adag⟧ = 1) :
    ⟦LeanPhy.FieldTheory.number adag a, adag⟧ = adag := by
  exact LeanPhy.FieldTheory.number_commutator a adag hCCR
```

The finite-EFT interface puts truncation order, coefficient bounds, and error budgets in theorem arguments; the finite path-integral interface requires an explicit normalisation certificate. If a premise is missing, elaboration fails instead of producing an unconditional conclusion.

## Recommended research workflow

1. Import the smallest suitable `LeanPhy.Entry.*` profile to keep dependencies and compile times under control.
2. State mathematical premises, physical conventions, boundary conditions, truncation ranges, and approximation parameters as types, structure fields, or theorem arguments.
3. Prove algebraic steps with reusable theorems and tactics. If a CAS or numerical program is used, import its result through an interface with a `CertificateChecker.sound` theorem.
4. Register the result as a `checked claim` in a `TheoryPackage` or `ResearchProject`; record unfinished analysis, interpretation, and continuum work as `open obligations`.
5. Run `leanphy_check` and `scripts/verify.sh`, then inspect both the human-readable and JSON reports.

`VERIFIED-CONDITIONAL` means that the ledger's proof terms compiled and passed kernel checking while explicitly listed obligations may remain open.

## Repository layout

```text
LeanPhy/                 library source grouped by physics domain
  Mathematics/            analysis, operators, spectra, limits, certificates, models
  Quantum/ QuantumInfo/   quantum mechanics and quantum information
  FieldTheory/            CCR/CAR/Fock/Wick algebra
  HighEnergy/             Clifford, gamma, spinor, and finite EFT interfaces
  GaugeTheory/            gauge fields and discrete geometric algebra
  Condensed/ StatMech/    condensed-matter and statistical models
  Classical/ Relativity/  classical mechanics and relativity
  Surface/                Dirac, Einstein, index, and dimension notation
  Entry/                  selective public import profiles
  Examples/               workflow and research-project examples
Main.lean                kernel regression entry point
Prototype.lean           end-to-end closed-loop prototype
Check.lean               research-ledger CLI
scripts/                 release verification and negative tests
docs/                    architecture, roadmap, and scope
```

Common entry points are `LeanPhy.Minimal`, the domain-specific `LeanPhy.Entry.*` profiles, and `LeanPhy.Entry.Physics` for projects that span several domains.

## Reports, development, and citation

```bash
lake exe leanphy_check --project-json
lake exe leanphy_check --broad --claims-json
lake exe leanphy_check --extended --manifest-json
```

New modules should provide reusable theorems, explicit hypotheses, a positive smoke regression, any necessary negative regression, and documentation. See [CONTRIBUTING.md](CONTRIBUTING.md), [docs/architecture.md](docs/architecture.md), and [docs/roadmap.md](docs/roadmap.md).

The package version is 1.0.0; Lean and mathlib are pinned in [`lean-toolchain`](lean-toolchain) and [`lakefile.toml`](lakefile.toml). When citing LeanPhy, record the commit, toolchain, mathlib revision, import profile, and generated ledger JSON. Citation metadata is in [CITATION.cff](CITATION.cff). LeanPhy is released under the Apache License 2.0.
