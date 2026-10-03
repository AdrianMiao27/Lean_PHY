# LeanPhy v1

**LeanPhy** is a Lean 4/mathlib library for checking derivations in theoretical
physics.  It keeps the trusted boundary small: a result is reported as checked
only when the Lean kernel verifies a proof term from explicit assumptions.
Physical truth, model adequacy, convergence of an unproved limit, and the
existence of a continuum or non-perturbative object are recorded separately.

> 面向理论物理的条件性证明工具：验证“给定假设，结论确实由推导推出”，而不把
> 尚未形式化的物理解释伪装成定理。

[![Lean](https://img.shields.io/badge/Lean-4.34.0-5f5f5f.svg)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.34.0-7b68ee.svg)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

中文说明：[README.zh-CN.md](README.zh-CN.md)

## What v1 provides

The v1 release is a research-grade **conditional verification library** for
finite, truncated, and bounded portions of common physics workflows.  It is
already suitable for a researcher who is willing to write ordinary Lean.  It
is not yet a standalone replacement for Lean syntax or a complete formalisation
of continuum quantum field theory.

The repository currently contains about 203 Lean source files and 29k lines.
The acceptance baseline is 446 kernel-checked smoke capabilities and 130
negative elaboration fixtures.  The broad research ledger reports 13 domain
packages, 26 checked claims, and 13 explicitly open obligations.  These counts
measure reusable interfaces and regressions; they do not claim that 446 papers
have been formalised.

## Scope

The reusable layer covers:

- quantum mechanics and quantum information: Pauli/Dirac notation, density
  matrices, POVMs, CPTP/Kraus channels, Bell/CHSH, Lindblad finite models,
  oscillator and CCR algebra;
- field and high-energy algebra: finite Fock/CAR/CCR/Wick identities,
  Clifford and gamma matrices, spinors, traces, Ward-style algebraic steps;
- condensed matter and statistical mechanics: lattice/BdG/Hubbard models,
  Berry and Jordan–Wigner algebra, finite Gibbs and Markov kernels;
- gauge, classical, relativity, optics and fluids: discrete Maxwell/Yang–Mills,
  exterior and plaquette identities, symplectic and Lorentz algebra, ABCD/Jones
  optics, finite-volume conservation and discrete vorticity;
- analysis and numerical bridges: Bochner integrals, dominated convergence,
  Lax–Milgram, Banach contraction, bounded Hilbert operators, resolvents,
  polynomial spectral calculus, spectral-gap certificates, operator convergence,
  residual/energy budgets, finite path integrals and regulator-wise
  renormalisation certificates.

The analysis modules consume explicit continuity, integrability, domain,
stability, convergence, or limit proofs.  They do not construct these facts
from numerical output or from a physics narrative.

The following remain open or conditional interfaces: self-adjointness and
essential self-adjointness of general unbounded Hamiltonians, Stone's theorem,
general spectral measures, infinite-dimensional path measures, Osterwalder–
Schrader reconstruction, full renormalisation limits, Navier–Stokes regularity,
and non-perturbative QFT existence.  See [VERIFIED.md](VERIFIED.md) for the
authoritative verified/assumed boundary and [docs/verified-scope.md](docs/verified-scope.md)
for the detailed research status.

## Quick start

Install Lean 4.34.0 with Lake, then run from the repository root:

```bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
```

For the complete release gate, including declaration audits, package ledgers,
downstream clients, scaffold generation, and negative elaboration tests:

```bash
./scripts/verify.sh
```

Builds should run on a local ext4/overlay filesystem.  The source tree is also
usable on a mounted workspace, but mathlib's cache and import traversal can be
very slow on FUSE or network filesystems.

## A minimal checked derivation

LeanPhy uses ordinary Lean declarations and tactics.  For example, a CCR
assumption can be consumed by a checked commutator theorem:

```lean
import LeanPhy.Entry.Quantum
import LeanPhy.Entry.FieldTheory

example {R : Type} [Ring R] (a a† : R)
    (hCCR : ⟦a, a†⟧ = 1) :
    ⟦LeanPhy.FieldTheory.number a† a, a†⟧ = a† := by
  exact LeanPhy.FieldTheory.number_commutator a a† hCCR
```

The public entry points include `LeanPhy.Minimal`, selective `LeanPhy.Entry.*`
profiles, and the umbrella `LeanPhy.Entry.Physics`.  The shared workflow in
[`LeanPhy/Workflow.lean`](LeanPhy/Workflow.lean) records named assumptions,
models, proof-bearing claims, dependencies, certificates, and open obligations.
`physics`, `physics_search`, Dirac notation, Einstein sums, index variance, and
dimension-aware quantities are available through the corresponding surface and
tactic modules.

## Repository layout

```text
LeanPhy/                 library source, grouped by physics domain
  Mathematics/            analysis, operators, spectra, limits, certificates
  Quantum/ QuantumInfo/   quantum mechanics and quantum information
  FieldTheory/            CCR/CAR/Fock/Wick algebra
  HighEnergy/ GaugeTheory/ particle and gauge algebra
  Condensed/ StatMech/     lattice, condensed matter, statistical models
  Classical/ Relativity/  classical and relativistic structures
  Surface/                Dirac, Einstein, index and dimension syntax
  Entry/                  selective public import profiles
  Examples/               reusable workflow examples
Main.lean                kernel-checked smoke acceptance target
Prototype.lean           compact end-to-end workflow executable
Check.lean               research-ledger CLI executable
scripts/                 release verification and negative tests
docs/                    architecture and detailed scope documents
.github/workflows/       GitHub Actions release checks
```

## Trust model

LeanPhy distinguishes three things in every research package:

1. **Assumptions** are named physical or mathematical inputs.
2. **Checked claims** contain a Lean proposition and a proof term; the kernel
   checks the proof during compilation.
3. **Open obligations** are visible research tasks without a proof field.

External CAS or numerical programs may supply data, but data becomes usable in
a checked claim only through a `CertificateChecker.sound` theorem.  A runtime
Boolean, an unchecked JSON field, `sorry`, or an implicit continuum limit is
never treated as evidence.  This is conditional correctness: if the declared
assumptions hold, the checked conclusion follows.

## Profiles and reports

Use selective imports for fast iteration:

```text
LeanPhy.Minimal
LeanPhy.Entry.Quantum       LeanPhy.Entry.FieldTheory
LeanPhy.Entry.Analysis      LeanPhy.Entry.FinitePDE
LeanPhy.Entry.Condensed     LeanPhy.Entry.StatMech
LeanPhy.Entry.Gauge         LeanPhy.Entry.HighEnergy
LeanPhy.Entry.Classical     LeanPhy.Entry.Relativity
LeanPhy.Entry.Optics        LeanPhy.Entry.Fluid
LeanPhy.Entry.Research      LeanPhy.Entry.Physics
```

The CLI supports human-readable and machine-readable ledgers:

```bash
lake exe leanphy_check --project-json
lake exe leanphy_check --broad --claims-json
lake exe leanphy_check --extended --manifest-json
```

`--strict` intentionally fails while a package still has open obligations;
the default conditional report keeps those obligations visible for research
development.

## Development

1. Keep the mathematical statement honest: put every analytic or physical
   premise in a type, structure field, or explicit theorem argument.
2. Add a reusable theorem or certificate before adding a domain-specific smoke
   example.
3. Add a negative elaboration fixture whenever a new safety boundary is
   introduced.
4. Run `./scripts/verify.sh` before opening a pull request.

See [CONTRIBUTING.md](CONTRIBUTING.md), [docs/architecture.md](docs/architecture.md),
and [docs/roadmap.md](docs/roadmap.md).  Contributions that expand an analytic
boundary must state exactly which existence, domain, convergence, or model
adequacy assumptions remain external.

## Versioning and citation

This repository is the v1 migration of the experimental
`Inspirations/Lean_phy` tree.  The Lean package version is `1.0.0`; the pinned
Lean and mathlib versions are recorded in `lean-toolchain` and `lakefile.toml`.
The API may evolve within v1 when required to preserve kernel soundness or to
repair a documented interface, with changes recorded in [CHANGELOG.md](CHANGELOG.md).

If you use LeanPhy in research, cite the repository and record the exact
commit, Lean toolchain, mathlib revision, profile, and generated ledger JSON.

## License

LeanPhy is released under the [Apache License 2.0](LICENSE).  It incorporates
the Lean community's mathlib as a pinned dependency; mathlib remains under its
own license.
