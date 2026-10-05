# LeanPhy

LeanPhy is a physics-oriented library for [Lean 4](https://lean-lang.org/)
and [mathlib](https://github.com/leanprover-community/mathlib4). It helps a
researcher express the mathematical steps of a theoretical-physics derivation
and ask Lean's kernel to check them. The project reuses Lean's language,
elaborator, editor support, theorem library, tactics, Lake build, and CI. It
adds physics objects, notation, reusable certificates, and a research ledger
for assumptions and unfinished work.

LeanPhy is a library on top of Lean. It is not a fork of Lean and it does not
introduce a second proof logic.

> **One-line description:** check that a stated conclusion follows from the
> stated mathematical and physical premises, while keeping unproved analysis
> and modelling decisions visible.

[![Lean](https://img.shields.io/badge/Lean-4.34.0-5f5f5f.svg)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.34.0-7b68ee.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://img.shields.io/github/actions/workflow/status/AdrianMiao27/Lean_PHY/leanphy.yml?label=CI)](https://github.com/AdrianMiao27/Lean_PHY/actions/workflows/leanphy.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

中文说明：[README.zh-CN.md](README.zh-CN.md)

## What LeanPhy verifies

LeanPhy verifies **conditional mathematical correctness**. A checked claim has
a Lean proof term, and that proof term has passed the Lean kernel. In plain
language:

> Given the premises written in the development, the conclusion follows by
> the accepted proof rules.

This is deliberately different from deciding whether a model is physically
true. LeanPhy does not silently turn any of the following into a theorem:

- that a model describes the real world or a particular experiment;
- that a continuum, thermodynamic, or renormalisation limit exists or
  converges;
- that a path integral exists, converges, or has the intended interpretation;
- that an unbounded operator has the required domain, self-adjointness, or
  time-evolution properties;
- that a formal object has the physical meaning assigned to it by a paper.

Such statements must enter as propositions, structure fields, theorem
arguments, or soundness certificates. Analysis that has not been completed,
external numerical evidence, and physical modelling assumptions are recorded
in the **open-obligation ledger**. The ledger is an audit record; it is not a
substitute for a proof.

An external CAS, numerical program, or script can supply data, but the data
enters the verified layer only through a Lean-side soundness theorem such as
`CertificateChecker.sound`. A Boolean, JSON file, sampled limit, or numerical
approximation is not a theorem merely because another program produced it.

The repository uses three labels:

| Label | Meaning |
| --- | --- |
| kernel-checked claim | A proof term passed Lean's kernel; the result is conditional on its explicit premises. |
| declared premise | An assumption, convention, or external certificate used by a claim. Its adequacy for a physical system needs a separate argument. |
| open obligation | Analysis, numerical certification, continuum passage, or physical interpretation that is still outstanding. |

~~~text
premises and certificates -> Lean proof term -> Lean kernel -> checked conditional claim
                                      \
                                       -> unfinished work -> open-obligation ledger
~~~

## Scope of v1.0

LeanPhy v1.0.0 concentrates on finite-dimensional, finite-truncation, and
bounded constructions. It also provides interfaces for unbounded operators,
continuous analysis, approximation, numerical certificates, and external data.
Those interfaces make missing hypotheses explicit; they do not prove results
that have not been supplied.

The current acceptance baseline contains **211 Lean source files, 478
kernel-checked smoke capabilities, and 143 expected-failure elaboration
fixtures**. The default `leanphy_check --project-json` report contains **8
proof-bearing domain packages, 15 checked claims, and 8 `open obligations`**;
`--broad` reports **13 packages, 28 claims, and 14 `open obligations`**. These
are library and regression metrics, not a count of complete physics papers.

| Area | Reusable foundations | Boundary that remains explicit |
| --- | --- | --- |
| Quantum mechanics and information | Pauli and Dirac notation, finite states and density matrices, POVMs, CPTP/Kraus channels, Bell/CHSH, finite Lindblad models, oscillator and CCR algebra | Domains and self-adjointness of unbounded operators, continuous-measurement semantics, and the relation between a finite model and a physical system |
| Field and high-energy algebra | Finite truncated Fock spaces, CAR/CCR and Wick identities, Clifford and gamma matrices, spinors, traces, Ward-style algebraic steps, finite EFT expansions, `BRST` interfaces, low-degree Lie-module cochains, and a finite CAR ghost-pair adapter | Field existence, infinite-dimensional limits, UV completion, renormalisation limits, a full ghost-polynomial algebra, BV structure, anomaly cancellation, Lie-group integration, and non-perturbative conclusions |
| Classical, gauge, relativity, optics, and fluids | Poisson algebras, first-class constraint ideals, weak equality, Dirac observables, discrete Maxwell/Yang--Mills, exterior and plaquette identities, symplectic and Lorentz algebra, Lie representations, ABCD/Jones optics, finite-volume conservation, and discrete vorticity | Gauge fixing, quotient regularity, continuum regularity, global existence, boundary physics, anomaly cancellation, and turbulence closure |
| Condensed matter and statistical mechanics | Lattice, Hubbard, BdG, Berry, Jordan--Wigner, finite Gibbs/Markov kernels, and transfer matrices | Thermodynamic limits, phase transitions, experimental calibration, and equivalence with a continuum theory |
| Analysis and numerical bridges | Bochner integration, dominated convergence, Lax--Milgram, Banach fixed points, bounded Hilbert operators, spectral calculus, spectral gaps, operator convergence, residual/energy budgets, finite path-integral interfaces, and regulator-wise certificates | External programs provide traceable data only; a Lean-side soundness theorem is still required before that data becomes a checked claim |

The unbounded-operator interface uses mathlib's `LinearPMap` and keeps the
operator domain in the type. `DenseDomainOperator` exposes interfaces for
formal adjoints, closedness, closability, self-adjointness, graph-norm bounds,
and domain-preserving bounded composition; each interface requires the
corresponding proof. Naming an object `Hamiltonian` does not prove
self-adjointness or generate time evolution. Stone's theorem, self-adjoint
extensions, spectral measures, and the passage from resolvents to evolution
groups remain `open obligations`.

For gauge systems, `ConstraintAlgebra` and `ConstraintMap` cover generated
constraint ideals, first-class closure, weak equality, Dirac observables, and
Poisson maps that preserve the relevant ideals. `BRST` requires an explicit
differential and a nilpotency proof. `GradedBRST` adds homogeneous pieces, an
odd degree shift, and the signed Koszul Leibniz rule. The finite CAR
ghost--antighost adapter is a concrete kernel-checked algebraic model for
these interfaces; it is not a full ghost-polynomial algebra, BV antibracket,
gauge-fixing construction, path-integral measure, anomaly theorem, or
physical `BRST`-cohomology equivalence.

`Mathematics.LieCohomology` provides a low-degree algebraic interface for gauge,
representation, and anomaly-candidate calculations. The action and
representation law are explicit, and the kernel checks the first
Chevalley--Eilenberg identities. The module keeps witnesses visible: it does
not silently construct quotient cohomology, integrate a Lie algebra, prove
anomaly cancellation, or identify a cocycle with a physical observable.

See VERIFIED.md and docs/verified-scope.md for the module-by-module inventory
and its limitations.

## Quick start

Lean 4.34.0 and mathlib v4.34.0 are pinned in lean-toolchain and lakefile.toml.
From the repository root:

~~~bash
lake build
lake exe leanphy_smoke
lake exe leanphy_prototype
lake exe leanphy_check --broad --project-json
~~~

The release verification script checks public entry points, downstream
clients, research ledgers, declaration audits, project scaffolding, and
negative tests:

~~~bash
./scripts/verify.sh
~~~

A local ext4 or overlay filesystem is recommended. Mathlib imports and cache
access can be substantially slower on FUSE or network-mounted filesystems.

## Minimal example

The following is ordinary Lean code. `hCCR` is an explicit canonical
commutation relation; the conclusion is a theorem whose proof has passed the
kernel:

~~~lean
import LeanPhy.Entry.Quantum
import LeanPhy.Entry.FieldTheory
open scoped LeanPhy.Quantum

example {R : Type} [Ring R] (a adag : R)
    (hCCR : ⟦a, adag⟧ = 1) :
    ⟦LeanPhy.FieldTheory.number adag a, adag⟧ = adag := by
  exact LeanPhy.FieldTheory.number_commutator a adag hCCR
~~~

This proves the algebraic implication from the stated CCR premise. It does
not prove the existence of an unbounded Hilbert-space representation or that
the representation describes an experiment. Likewise, the finite EFT and
finite path-integral interfaces require explicit truncation, error, and
normalisation certificates. If a required premise is missing, elaboration
fails instead of producing an unconditional conclusion.

## A research workflow

1. Import the smallest suitable `LeanPhy.Entry.*` profile.
2. State mathematical premises, physical conventions, boundary conditions,
   truncation ranges, and approximation parameters as types, structure fields,
   or theorem arguments.
3. Use reusable theorems and tactics for algebraic steps. If a CAS or numerical
   program is used, pass its result through an interface with a
   `CertificateChecker.sound` theorem.
4. Register the result as a checked claim in a `TheoryPackage` or
   `ResearchProject`; put unfinished analysis, interpretation, continuum work,
   and modelling premises in `open obligations`.
5. Run `leanphy_check` and `scripts/verify.sh`, then inspect both the human-readable
   and JSON reports.

`VERIFIED-CONDITIONAL` means that the proof term compiled and passed the kernel.
It does not mean that a model has been experimentally validated or that its
`open obligations` have been discharged.

For a separate soundness audit, run:

~~~bash
lake env lean scripts/axioms.lean
~~~

The library and release checks do not use `sorry`, `admit`, or
application-specific unchecked axioms. `#print axioms` may list standard
foundational axioms used by Lean/mathlib, such as `propext`, `Classical.choice`,
and `Quot.sound`; that is different from declaring a physics result as an axiom.

## Repository layout

~~~text
LeanPhy/                 library source grouped by physics domain
  Mathematics/            analysis, operators, spectra, limits, certificates
  Quantum/ QuantumInfo/   quantum mechanics and quantum information
  FieldTheory/            CCR/CAR/Fock/Wick algebra
  HighEnergy/             Clifford, gamma, spinor, and finite EFT interfaces
  GaugeTheory/            gauge fields, discrete geometry, finite ghost adapter
  Condensed/ StatMech/    condensed-matter and statistical models
  Classical/ Relativity/  classical mechanics and relativity structures
  Surface/                Dirac, Einstein, index, and dimensional notation
  Entry/                  selective public import profiles
  Examples/               workflow and research-project examples
Main.lean                kernel regression entry point
Prototype.lean           compact end-to-end workflow
Check.lean               research-ledger CLI
scripts/                 release verification and negative tests
docs/                    architecture, roadmap, and detailed scope
~~~

Common entry points are `LeanPhy.Minimal`, the domain-specific `LeanPhy.Entry.*`
profiles, and `LeanPhy.Entry.Physics` for projects spanning several domains.

## Development and citation

~~~bash
lake exe leanphy_check --project-json
lake exe leanphy_check --broad --claims-json
lake exe leanphy_check --extended --manifest-json
~~~

New modules should provide reusable theorems, explicit hypotheses, a positive
smoke regression, a negative regression where a safety boundary can fail, an
entry-point export, and documentation showing how the module composes with
existing certificates. See CONTRIBUTING.md, docs/architecture.md, and
docs/roadmap.md.

When citing LeanPhy, record the commit, Lean toolchain, mathlib revision,
import profile, and generated ledger JSON. Citation metadata is in
CITATION.cff. LeanPhy is released under the Apache License 2.0.
