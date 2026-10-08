# LeanPhy

LeanPhy is a Lean 4 library for conditional verification of theoretical-physics
derivations. It lets a researcher state a model, its conventions, an
intermediate calculation, and the hypotheses needed for a physical conclusion;
Lean's kernel then checks the resulting proof. Unproved analysis, modelling
choices, external numerical data, and failed exploratory branches remain
visible as assumptions or open obligations.

LeanPhy is built on Lean and mathlib. It does not replace Lean's logic and it
does not decide whether a model describes a real material or experiment.

中文说明：[README.zh-CN.md](README.zh-CN.md) · Documentation map: [docs/README.md](docs/README.md)

## Current snapshot

Version `1.1.0`, reviewed on **2026-10-08**. The project is aimed at
exploratory work in condensed matter, quantum/statistical physics, and high
energy or field theory. The main design goal is a reusable chain:

```text
model and conventions -> formal operation -> physical readout -> applicability/error evidence
```

The chain is conditional: finite-dimensional or finite-truncation theorems do
not silently become continuum, thermodynamic-limit, or experimentally valid
claims.

## What this revision changed

- Added `LeanPhy.FieldTheory.FermionUnitaryWick`. A finite many-body unitary
  can transport a vacuum density, CAR generators, and all ordered linear-probe
  moments together. The result covers finite orbital or quench-style changes
  of basis and keeps CAR contact terms explicit.
- Connected the new transport API to the field-theory and condensed-matter
  entries and to `Examples/FermionResearch.lean`. The client now reports 19
  kernel-checked claims and 3 open obligations.
- Extended the response regression with Pauli-matrix pulses, the zero-background
  case, and a time envelope whose exact pulse area and integrated response are
  checked in Lean.
- Consolidated documentation responsibilities. The detailed capability table
  and roadmap live in `docs/capabilities.md` and `docs/roadmap.md`; redundant
  phase and compatibility copies were removed; `VERIFIED.md` is the only
  verification record.

## Current capabilities

The reusable library currently provides the following research-facing chains.

| Area | Available now | Main boundary |
| --- | --- | --- |
| Finite fermions | Occupation-space CAR, Nambu and complex pairing, orbital transport, arbitrary fermion words, vacuum moments, CAR contact terms, and finite unitary transport | General Gaussian or thermal Wick theorems, interacting ground-state selection, and large-system sparse performance |
| Quantum dynamics and response | Finite non-autonomous evolution, Heisenberg/state derivatives, two-time response, contact terms, causal pulses, non-commuting Gibbs response, and exact finite-grid Fourier reconstruction | General laboratory-frame drives, continuous-frequency/transport limits, and finite-amplitude remainder bounds |
| Actions and field theory | Polynomial actions, actual field evaluation, Euler and variational currents, interval actions, boundary terms, field redefinitions, and quadratic heavy-field matching | Global inverse charts, derivative-dependent or higher-order EFT transformations, multidimensional boundaries, Green functions, and loop matching |
| Effective theories and certificates | Noncommutative retained-order operations, block elimination, source/readout transport, rational matrix inverse and spectral certificates, and residual/error budgets | Automatic interval arithmetic, robust uncertain real inputs, exact-solution error bounds, and energy-independent unitary reduction |
| Statistical and lattice tools | Finite Gibbs/source response, feedback self-consistency on certified contraction domains, finite Ward insertions, and blocking-defect budgets | Critical and multi-branch self-consistency, quantum closure, physical coupling flows, and thermodynamic limits |
| Gauge/deformation and research workflow | Finite Lie/ghost/cohomology calculations, deformation obstructions, target-bound obligations, hypothesis branches, counterexamples, audits, and reproducible clients | Connecting every algebraic certificate to a physical action/observable and automatic semantic impact analysis |

The complete C01–C28 inventory, source links, maturity labels, and research
gaps are maintained in [the capability inventory](docs/capabilities.md). Use
the individual guides in [the documentation index](docs/README.md) for API
details and examples.

## Scope and trust boundary

A checked claim means that a Lean proof term passed the kernel under its stated
premises. LeanPhy does not by itself prove:

- that a chosen Hamiltonian, action, or state models a real system;
- existence or convergence of a continuum, thermodynamic, renormalisation, or
  path-integral limit;
- domains, self-adjointness, or evolution of arbitrary unbounded operators;
- correctness of an external numerical approximation without a Lean-side
  soundness certificate; or
- that a supplied finite vacuum is the ground state of an interacting model.

These boundaries are part of the project interface. Open analysis and physical
interpretation are recorded in research packages and `VERIFIED.md` rather than
being hidden behind a successful compilation.

## Verification

The focused checks for this snapshot pass:

```bash
lake env lean LeanPhy/FieldTheory/FermionUnitaryWick.lean
lake build leanphy_fermion_client
python3 scripts/test_driven_response.py --build-root .
python3 scripts/test_fermion_vacuum.py --build-root .
git diff --check
```

The complete `scripts/verify.sh` release run does not yet have a successful
terminal record for the current worktree. Focused checks and library builds
must therefore be read together with the limits in [VERIFIED.md](VERIFIED.md).

## Layout and contribution path

Reusable proofs belong under `LeanPhy/`; domain import surfaces under
`LeanPhy/Entry/`; compilable research packages under `LeanPhy/Examples/`;
executable wrappers under `Clients/`; and the six compatibility/smoke roots
(`Main.lean`, `Prototype.lean`, `Check.lean`, `ClientMain.lean`,
`StrictClientMain.lean`, `Scaffold.lean`) remain at the root for Lake and
downstream-project conventions. JSON inputs and external reports live under
`examples/`. See [the project layout](docs/project-layout.md) before adding a
module or document.

## Future directions

Development is paused after this cleanup while the next scope is reviewed. The
roadmap prioritises functions that close real theoretical-physics research
steps rather than more fixed examples:

1. Construct general Gaussian and thermal states, including pairing, source
   insertions, and time-ordered multi-point correlations.
2. Extend finite response to general laboratory-frame drives, stationarity and
   continuous-frequency or transport readouts with controlled remainders.
3. Connect spectral certificates to stable low-energy subspaces, Bogoliubov
   reductions, band geometry, topology, and finite RG coupling flows.
4. Add Green-function and boundary-value error statements for effective
   theories, together with higher-order field redefinitions, IBP/EOM bases,
   and selected loop or non-quadratic matching tasks.
5. Improve reliable numerical enclosures, uncertain-input propagation, sparse
   many-body representations, and performance evidence.
6. Build carefully chosen continuum, thermodynamic, and non-equilibrium bridges
   only when a concrete model supplies the required analytic hypotheses.

The current priorities, dependencies, and acceptance criteria are kept in
[docs/roadmap.md](docs/roadmap.md).
