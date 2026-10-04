# LeanPhy v1

LeanPhy is a Lean 4 and mathlib library for formal verification of derivations
in theoretical physics. A derivation is represented as a Lean proposition with
explicit assumptions, and its proof term is checked by the Lean kernel.

LeanPhy verifies **conditional correctness**: whether a conclusion follows from
the assumptions that have been stated. It checks the logical validity of a
derivation; it does not decide physical truth. A model description does not, by
itself, prove that a model describes the physical world, that a continuum or
thermodynamic limit exists, that a path integral is well-defined, or that a
physical interpretation is correct. Such statements enter the verified layer
only as Lean propositions with proof terms or through a trusted certificate
interface. Unfinished analysis and physical premises remain visible in the open
obligation ledger.

[![Lean](https://img.shields.io/badge/Lean-4.34.0-5f5f5f.svg)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.34.0-7b68ee.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://img.shields.io/github/actions/workflow/status/AdrianMiao27/Lean_PHY/leanphy.yml?label=CI)](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

中文说明：[README.zh-CN.md](README.zh-CN.md)

## Positioning and scope

LeanPhy uses Lean's native syntax, type system, elaborator, tactics, Lake
builds, and CI workflow. Physics modules add reusable objects, theorems,
notation, tactics, and research ledgers; they do not introduce a second proof
logic. Existing Lean projects can adopt one domain entry point at a time.

Version 1 is designed first for finite-dimensional, truncated, and bounded
objects. Analysis interfaces are available when the user supplies the required
continuity, integrability, domain, stability, or convergence proof. The current
regression baseline contains 204 Lean source files, 448 smoke capabilities, 131
negative elaboration fixtures, and a 13-package ledger with 28 kernel-checked
claims and 14 open obligations. These figures describe library and regression
coverage; they are not a count of complete physics papers.

| Area | Available in v1 | Boundary |
| --- | --- | --- |
| Quantum mechanics and information | Pauli and Dirac notation, density matrices, POVMs, CPTP/Kraus channels, Bell/CHSH, finite Lindblad models, oscillator and CCR algebra | Primarily finite matrices and explicit algebraic assumptions; unbounded domains and measurement interpretation remain hypotheses |
| Field and high-energy algebra | Finite Fock/CAR/CCR/Wick identities, Clifford and gamma matrices, spinors, traces, Ward-style algebraic steps, finite EFT expansions, truncation bounds, and matching budgets | Field existence, infinite-dimensional limits, UV completion, renormalisation, and non-perturbative results require separate work |
| Condensed matter and statistical mechanics | Lattice, Hubbard, BdG, Berry, Jordan–Wigner, finite Gibbs and Markov kernels, and transfer matrices | Thermodynamic limits, phase transitions, and experimental calibration remain external obligations |
| Gauge, classical, relativity, optics, and fluids | Discrete Maxwell/Yang–Mills, exterior and plaquette identities, symplectic and Lorentz algebra, ABCD/Jones optics, finite-volume conservation, and discrete vorticity | Continuum regularity, global existence, boundary physics, and turbulence closure do not follow from a finite model |
| Mathematical and numerical bridges | Bochner integration, dominated convergence, Lax–Milgram, Banach fixed points, bounded Hilbert operators, spectral calculus, spectral gaps, operator convergence, residual/energy budgets, finite path integrals, and regulator-wise certificates | CAS or numerical output must cross a Lean-side CertificateChecker; data and JSON are not proofs |

Open or conditional interfaces include general self-adjointness of unbounded
Hamiltonians, Stone's theorem, general spectral measures, infinite-dimensional
path measures, Osterwalder–Schrader reconstruction, full renormalisation
limits, Navier–Stokes regularity, and non-perturbative QFT existence. See
[VERIFIED.md](VERIFIED.md) and [docs/verified-scope.md](docs/verified-scope.md).

## Quick start

Install Lean 4.34.0 and run from the repository root:

```bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
```

The release gate also checks public entry points, downstream clients, research
ledgers, declaration audits, scaffold generation, and negative elaboration
fixtures:

```bash
./scripts/verify.sh
```

A local ext4 or overlay filesystem is recommended. Mathlib imports and cache
access can be much slower on FUSE or network-mounted filesystems.

## Minimal checked derivation

This is ordinary Lean code. The CCR premise is passed to a checked commutator
theorem; the variable adag stands for the creation operator a†.

```lean
import LeanPhy.Entry.Quantum
import LeanPhy.Entry.FieldTheory
open scoped LeanPhy.Quantum

example {R : Type} [Ring R] (a adag : R)
    (hCCR : ⟦a, adag⟧ = 1) :
    ⟦LeanPhy.FieldTheory.number adag a, adag⟧ = adag := by
  exact LeanPhy.FieldTheory.number_commutator a adag hCCR
```

The finite-EFT interface makes the hierarchy and error budget explicit:

```lean
import LeanPhy.Entry.HighEnergy
open LeanPhy.HighEnergy
open LeanPhy.Mathematics

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : ExpansionParameter) (T : FiniteEFT ι) (S : Finset ι) (cutoff : ℕ)
    (horder : ∀ i ∈ Finset.univ \ S, cutoff ≤ T.order i) :
    ErrorCertificate (T.amplitude E) (T.retainedAmplitude E S)
      (((Finset.univ \ S).card : ℝ) * T.coefficientBound * E.value ^ cutoff) := by
  exact T.truncation_error_certificate E S cutoff horder
```

This is a statement about the supplied finite coefficient table, expansion
parameter, omitted set, and order hypothesis. It does not assert a continuum
EFT, a UV completion, or regulator-independent matching.

Public entry points include LeanPhy.Minimal, selective LeanPhy.Entry.* profiles,
and LeanPhy.Entry.Physics for multi-domain projects. LeanPhy/Workflow.lean
records named assumptions, models, proof-bearing claims, dependencies,
certificates, and open obligations.

## Research workflow

1. Import the smallest suitable LeanPhy.Entry.* profile.
2. State mathematical premises, physical conventions, boundary conditions,
   truncation ranges, and approximation parameters as types, structure fields,
   or theorem arguments.
3. Prove algebraic steps with reusable theorems and tactics. If a CAS or
   numerical program is used, bring its output through a Lean
   CertificateChecker.sound theorem.
4. Register the result as a checked claim in a TheoryPackage or ResearchProject,
   and list unfinished analysis, interpretation, and continuum work as open
   obligations.
5. Run leanphy_check and scripts/verify.sh; inspect both the human-readable and
   JSON reports.

The trust boundary is:

```text
explicit assumptions + Lean proof term  ── Lean kernel ──>  conditional checked conclusion
```

Runtime booleans, unchecked JSON, uncertified numerical output, and implicit
continuum limits do not acquire theorem status. VERIFIED-CONDITIONAL means that
the ledger's proof terms compiled and passed kernel checking while listed
obligations remain open.

## Repository layout

```text
LeanPhy/                 library source grouped by physics domain
  Mathematics/            analysis, operators, spectra, limits, certificates
  Quantum/ QuantumInfo/   quantum mechanics and quantum information
  FieldTheory/            CCR/CAR/Fock/Wick algebra
  HighEnergy/             Clifford, gamma, spinor, and finite EFT interfaces
  GaugeTheory/            gauge fields and discrete geometric algebra
  Condensed/ StatMech/     condensed-matter and statistical models
  Classical/ Relativity/  classical mechanics and relativity
  Surface/                Dirac, Einstein, index, and dimension notation
  Entry/                  selective public import profiles
  Examples/               workflow and research-project examples
Main.lean                kernel regression entry point
Prototype.lean           end-to-end closed-loop prototype
Check.lean               research-ledger CLI
scripts/                 release verification and negative tests
docs/                    architecture, roadmap, and scope
.github/                 CI, issue templates, and pull-request template
```

## Reports, development, and citation

The CLI emits human-readable and machine-readable ledgers:

```bash
lake exe leanphy_check --project-json
lake exe leanphy_check --broad --claims-json
lake exe leanphy_check --extended --manifest-json
```

The default status is VERIFIED-CONDITIONAL and keeps open obligations visible.
Use --strict when a CI job must fail while obligations remain unresolved. New
modules should provide reusable theorems, explicit hypotheses, a positive smoke
regression, any needed negative regression, and documentation. See
CONTRIBUTING.md, docs/architecture.md, and docs/roadmap.md.

The package version is 1.0.0; Lean and mathlib are pinned in lean-toolchain and
lakefile.toml. When citing LeanPhy, record the commit, toolchain, mathlib
revision, import profile, and generated ledger JSON. Citation metadata is in
CITATION.cff. LeanPhy is released under the Apache License 2.0.
