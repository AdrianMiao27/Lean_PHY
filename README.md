# LeanPhy v1

LeanPhy is a Lean 4 / mathlib library for formalising and checking derivations in theoretical physics. It reuses Lean's language, type system, editor, theorem library, tactics, Lake build, and CI. On top of that foundation it provides physics objects, notation, reusable theorems, domain entry points, and a research ledger.

The goal is to make a theoretical-physics derivation **compilable, reproducible, and auditable**. LeanPhy is a physics extension for Lean; it is not a second proof logic or a runtime model.

## Verification boundary

LeanPhy checks **conditional correctness**: whether a conclusion follows from the assumptions that have been stated. It does not turn a model's claim to describe the real world into a theorem. It does not automatically prove the existence of a continuum or thermodynamic limit or of a path integral, and it does not decide whether a physical interpretation is correct.

A result enters the verified layer only as a Lean proposition with a proof term checked by the Lean kernel, or through an external-certificate interface with a proved `sound` theorem. Unfinished analysis, numerical reliability arguments, and physical premises remain in the open-obligation ledger:

```text
explicit assumptions + Lean proof term  ── Lean kernel ──>  conditional checked conclusion
```

Runtime booleans, unchecked JSON, uncertified CAS/numerical output, and implicit limits do not acquire theorem status.

[![Lean](https://img.shields.io/badge/Lean-4.34.0-5f5f5f.svg)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.34.0-7b68ee.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://img.shields.io/github/actions/workflow/status/AdrianMiao27/Lean_PHY/leanphy.yml?label=CI)](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

中文说明：[README.zh-CN.md](README.zh-CN.md)

## Current scope

Version 1 concentrates on finite-dimensional, truncated, and bounded objects. It also exposes assumption-driven interfaces for unbounded operators, continuous analysis, and numerical bridges. The current regression baseline contains **205 Lean source files, 457 smoke checks, and 137 negative elaboration fixtures**. The research ledger contains 13 domain packages, 28 kernel-checked claims, and 14 open obligations. These numbers describe library and regression coverage; they are not a count of complete physics papers.

| Area | Available foundations | Explicit boundary |
| --- | --- | --- |
| Quantum mechanics and information | Pauli/Dirac notation, finite states and density matrices, POVMs, CPTP/Kraus channels, Bell/CHSH, finite Lindblad models, oscillator and CCR algebra | Results target finite matrices, bounded objects, and stated algebraic assumptions; unbounded domains, self-adjointness, and measurement interpretation require separate proofs or obligations |
| Field and high-energy algebra | Finite Fock/CAR/CCR/Wick identities, Clifford/gamma matrices, spinors, traces, Ward-style algebraic steps, finite EFT expansions, and truncation certificates | Field existence, infinite-dimensional limits, UV completion, renormalisation limits, and non-perturbative results are outside the automatic contract |
| Condensed matter and statistical mechanics | Lattice, Hubbard, BdG, Berry, Jordan–Wigner, finite Gibbs/Markov kernels, and transfer matrices | Thermodynamic limits, phase transitions, and experimental calibration remain separate obligations |
| Gauge, classical, relativity, optics, and fluids | Discrete Maxwell/Yang–Mills, exterior and plaquette identities, symplectic and Lorentz algebra, ABCD/Jones optics, finite-volume conservation, and discrete vorticity | Continuum regularity, global existence, boundary physics, and turbulence closure do not follow from a finite model |
| Mathematical and numerical bridges | Bochner integration, dominated convergence, Lax–Milgram, Banach fixed points, bounded Hilbert operators, spectral calculus, spectral gaps, operator convergence, residual/energy budgets, finite path integrals, and regulator-wise certificates | External programs provide traceable data only; a Lean-side `CertificateChecker` soundness proof is required to promote the result to a theorem |

The unbounded-operator layer is connected to mathlib's `LinearPMap` without erasing the declared domain. `DenseDomainOperator` exposes formal adjoints, closedness/closability, self-adjointness certificates, graph-norm relative bounds, and domain-preserving bounded composition; each interface consumes a user-supplied proof. Naming an object `Hamiltonian` does not prove self-adjointness or generate a time evolution. Stone's theorem, general self-adjoint extensions, spectral measures, and the resolvent-to-evolution bridge remain open obligations.

`LeanPhy.Mathematics.SymmetryReduction` provides a shared contract for constrained systems. A model supplies admissible states, constraints, a group action, and preservation proofs; the library then checks finite-step constraint preservation, orbit transport, and descent of invariant observables to a quotient of physical states. It does not construct a gauge slice, prove that a quotient is a manifold, or interpret gauge equivalence as physical equivalence.

See [VERIFIED.md](VERIFIED.md) and [docs/verified-scope.md](docs/verified-scope.md) for the per-module inventory and limitations.

## Quick start

Install Lean 4.34.0 (pinned in `lean-toolchain`) and run from the repository root:

```bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
```

The release verification script also checks public entry points, downstream clients, research ledgers, declaration audits, scaffold generation, and negative fixtures:

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

The finite-EFT interface puts truncation order and error budgets in theorem arguments; the finite path-integral interface likewise requires an explicit normalisation certificate. If a premise is missing, elaboration fails instead of producing an unconditional conclusion.

## Recommended research workflow

1. Import the smallest suitable `LeanPhy.Entry.*` profile.
2. State mathematical premises, physical conventions, boundary conditions, truncation ranges, and approximation parameters as types, structure fields, or theorem arguments.
3. Prove algebraic steps with reusable theorems and tactics. If a CAS or numerical program is used, import its result through a `CertificateChecker.sound` theorem.
4. Register the result as a checked claim in a `TheoryPackage` or `ResearchProject`; record unfinished analysis, interpretation, and continuum work as open obligations.
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

Common entry points are `LeanPhy.Minimal`, the domain-specific `LeanPhy.Entry.*` profiles, and `LeanPhy.Entry.Physics` for multi-domain projects.

## Reports, development, and citation

```bash
lake exe leanphy_check --project-json
lake exe leanphy_check --broad --claims-json
lake exe leanphy_check --extended --manifest-json
```

New modules should provide reusable theorems, explicit hypotheses, a positive smoke regression, any necessary negative regression, and documentation. See [CONTRIBUTING.md](CONTRIBUTING.md), [docs/architecture.md](docs/architecture.md), and [docs/roadmap.md](docs/roadmap.md).

The package version is 1.0.0; Lean and mathlib are pinned in `lean-toolchain` and `lakefile.toml`. When citing LeanPhy, record the commit, toolchain, mathlib revision, import profile, and generated ledger JSON. Citation metadata is in [CITATION.cff](CITATION.cff). LeanPhy is released under the Apache License 2.0.
