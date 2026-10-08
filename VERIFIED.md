# Verified versus assumed

LeanPhy is meant to be used as a *reliable verifier* of theoretical-physics
derivations.  That claim is only meaningful if the boundary between what the
kernel actually proved and what was taken as input is written down.  This file
is that record.  It is kept in step with the modules under `LeanPhy/`.

## Current snapshot: finite unitary vacuum transport and repository cleanup (2026-10-08)

`FieldTheory.FermionUnitaryWick` adds the finite common-unitary transport bridge
for a vacuum density, CAR generators, and ordered linear-probe moments. It
preserves the transported CAR, adjoint relations, and annihilation condition.
The result is intended for finite orbital changes and finite many-body quench
steps. It does not establish a general Gaussian or thermal Wick theorem, a
time-ordered identity, or an interacting ground-state statement.

`FermionResearch` now exposes **19 kernel-checked claims and three open
obligations**. The focused finite-vacuum regression passes **6 tests**, including
the new transport API and documentation snippets. The driven-response
regression passes **4 tests**, including Pauli matrices, zero background, a
time-dependent pulse, and its exact area/response integral. The following
commands were run successfully in the current worktree:

```text
lake env lean LeanPhy/FieldTheory/FermionUnitaryWick.lean
lake build leanphy_fermion_client
python3 scripts/test_driven_response.py --build-root .
python3 scripts/test_fermion_vacuum.py --build-root .
git diff --check
```

Capability and roadmap decisions are maintained in `docs/capabilities.md` and
`docs/roadmap.md`; redundant phase and compatibility copies have been removed.
The v1.1 release script set keeps only the audit, certificate, focused physics
regression and negative-test tools. The older symbolic Lie/cohomology
generators described in the historical entries below were removed from the
repository; those entries document earlier validation runs only.
This entry does not claim a successful full `scripts/verify.sh` release run for
the current worktree.

## Current worktree: quadratic propagating-heavy matching (2026-10-08)

`FieldTheory.PropagatingHeavy` builds finite ordered inverse expansions from an
actual unit mass operator. Its matrix adapter accepts arbitrary finite heavy
labels and a proved invertible real mass matrix. The kinetic operator is
`div Z grad` in a differential algebra: variable background coefficients are
actually differentiated. The exact reconstructed equation residual retains
`ε^N M (M⁻¹ L)^N M⁻¹ J`; reversing the factors or increasing the power of ε
is not justified. N counts kinetic insertions with an exclusive cutoff.

`HeavyFieldMatching` supplies symmetric quadratic heavy sectors and polynomial
jet constructors. It derives the equation from the density variation and
retains the residual pairing, total divergence, mixed source terms, quadratic
source contact and linear readouts. `HeavyFieldInterval` evaluates the same
jets on actual smooth profiles, proves the kinetic/equation interpretation,
actual first variation and interval-action matching, and combines uniform
residual and endpoint evidence into a quantitative action discrepancy.

The discrepancy compares the action at the finite reconstructed field with
the matched action. It is **not** an error to an unsupplied exact boundary-value
solution. General formal directions are supported; actual region integration
here is one-dimensional. Green functions, exact-solution/large-order bounds,
nonquadratic heavy sectors, general EFT basis/EOM quotients, multidimensional
boundary integration and quantum measures/determinants remain open. Symmetry
does not supply positivity, stability, a chosen signature or a global solution.

The library, HighEnergy/FieldTheory/Condensed entries, effective client and
compiled declaration index build in the local validation copy
(`/tmp/leanphy-heavy-integration.log`). The canonical effective client and
declaration index also rebuild successfully
(`/tmp/leanphy-heavy-canonical-clients.log`). All **19 infrastructure tests** pass
(`/tmp/leanphy-heavy-infrastructure.log`), including public-operation discovery
and strict rejection of the unfinished effective project. The client now has
**14 claims and three open obligations**: low-energy validity, Green functions
and quantum matching, and energy-independent unitary dynamics. All **378
library source/config files** and **36 root client sources** match the canonical
workspace by SHA-256 (`/tmp/leanphy-heavy-source-match.json`).

All **three heavy-field regression methods** pass across two focused runs.
`/tmp/leanphy-heavy-differential.log` covers seven models with heavy/light/direction/
cutoff counts `(1,1,1,0)`, `(1,1,1,1)`, `(1,1,1,3)`, `(2,1,1,2)`, `(2,2,1,2)`,
`(2,2,2,2)` and `(3,2,1,2)`. SymPy independently differentiates concrete
coordinate-space polynomials; Lean checks the public jet results against the
corresponding exact derivative data. There are **28 generated readout equalities**,
including mixed masses, variable derivative coefficients, fields, residuals
and action densities. The run took 90.948 seconds locally; this is a regression
observation, not a scalability benchmark.

`/tmp/leanphy-heavy-guide.log` covers all **five guide snippets** and actual
interval integrals. With `M=Z=ε=1`, `J(t)=t`, `N=1` and interval `[0,1]`, the
reconstructed field `χ=-t` has zero equation residual, but the original action
is `1/3` and the matched action is `-1/6`; the proved difference `1/2` is its
nonzero endpoint contribution. The values are also independently integrated
in Python. Oracle outputs are comparison data, never proof premises.

All **ten new rejection fixtures** pass (`/tmp/leanphy-heavy-negatives.log`):
mass symmetry, differentiation of coefficients, operator order, exclusive
cutoff, nonzero residuals, source/probe shifts, endpoints, smoothness and uniform
interval evidence. The script now defines **427 fixtures**; this batch did
**not** rerun all 427. Declaration scanning, shell syntax and `git diff --check`
also pass. The new regression suite is wired into `scripts/verify.sh`.

A fresh full library build and transitive dependency audit pass in the
**canonical workspace**: **375 modules, 17,434 declarations, 490 private
declarations and 10,593 theorems**. Only `propext`, `Classical.choice` and
`Quot.sound` occur transitively. Report: `/tmp/leanphy-heavy-audit.json`;
compiler log: `/tmp/leanphy-heavy-audit.log`. There are **374 library sources /
68,267 lines / 73 example modules** under `LeanPhy/`, plus the root import.

The single complete `scripts/verify.sh` release run remains without a successful
terminal record. The focused checks and full dependency audit above are not
reported as a complete release pass. Global capability IDs and priorities
remain organized as 28 capabilities, seven tracks and fourteen deliveries.
R08 remains partial; the next selected gap is R06 general time-dependent
driving derived from actual evolution.

## Historical arbitrary ordered vacuum batch (2026-10-08)

`FieldTheory.FermionicMoment` implements signed deletion by position, proves
length descent and defines a terminating coefficient recursion. It preserves
repeated physical probes and commutes with relabeling and ring-homomorphism
specialization. `FieldTheory.FermionVacuumWick` derives this recursion from CAR
and the supplied actual density's annihilation condition. The final Wick
identity is not an input. Odd moments vanish; adjacent exchanges in arbitrary
surrounding products retain the symmetric CAR contact term.

Executable integer `FermionWord.vacuumMoment` and symbolic
`FermionPolynomial.vacuumValue` are proved to equal the corresponding actual
vacuum trace after coefficient specialization. Existing CAR compilation
preserves the readout. This supports interaction insertions in a specified
reference vacuum. It does not prove that vacuum is the interaction's ground
state, or establish general Gaussian/thermal factorization, time ordering,
perturbative remainder bounds or continuum limits. Direct pairing enumeration
still grows as `(2m-1)!!` for dense even lists; no scalable pairing backend is
claimed.

The library, Quantum/Condensed/FieldTheory/HighEnergy entries, fermion client
and declaration index build in the local validation copy
(`/tmp/leanphy-multipoint-integration.log`). The canonical client and declaration index also rebuild successfully
(`/tmp/leanphy-multipoint-canonical-clients.log`). The client has **18 claims
and three open obligations**. All **19 infrastructure tests** pass there, including
public-operation discovery and strict rejection of the unfinished client
(`/tmp/leanphy-multipoint-infrastructure.log`). All **375 library source/config
files** and **36 root client sources** match the canonical workspace by SHA-256
(`/tmp/leanphy-multipoint-source-match.json`). The reused local copy is not a
historical frozen snapshot.

All **five fermion-vacuum regression methods** pass
(`/tmp/leanphy-multipoint-regression.log`), including all **six guide snippets**.
An independent exact Gaussian-integer oracle applies operators to occupation
states, without using Wick recursion. New comparisons cover **23 probe lists**
with lengths 0, 1, 3, 6 and 8 and mode counts 0–4, repeated Majorana probes,
complex coefficients and a nonzero crossing-sign case. Integer readouts cover
**359 words** (all 341 two-mode words of lengths 0–4, sixteen sampled longer
words and two nonzero eight-letter words) and **eight expression tables**.
The earlier four-point regressions also pass. Generated integer equalities use
`decide +kernel`; Python values are comparison data, not proof premises.

All **eight new negative fixtures** pass
(`/tmp/leanphy-multipoint-negatives.log`), rejecting absent vacuum evidence,
erased contact terms, wrong crossing parity, absent oddness, changed probes,
unordered vacuum kernels, changed coefficients and false repeated-probe zeros.
The full script now defines **417 fixtures**; this batch did **not** rerun all
417. Declaration scanning, shell syntax, documentation links and `git diff
--check` also pass.

A fresh full library build and transitive dependency audit pass in the
**canonical workspace**: **372 modules, 17,318 declarations, 490 private
declarations and 10,517 theorems**. Only `propext`, `Classical.choice` and
`Quot.sound` occur transitively. Report: `/tmp/leanphy-multipoint-audit.json`;
compiler log: `/tmp/leanphy-multipoint-audit.log`. There are **371 library
sources / 67,650 lines / 73 example modules** under `LeanPhy/`; the module
audit additionally includes the root import.

The latest single `scripts/verify.sh` run still has no completed success marker.
This batch's successful builds, focused regressions and full dependency audit
are not reported as a complete release run. The global plan remains 28
capabilities, seven tracks and fourteen deliveries; R05 remains partial, and
the next priority is R08 propagating-heavy-field matching with the R07
operations needed by that physical chain.

## Historical numerical Gibbs batch (2026-10-08)

`Mathematics.RationalExp` derives executable rational exponential enclosures
from Taylor remainders and repeated squaring. `StatMech.GibbsCertificate`
checks a positive partition lower bound and a centered residual for arbitrary
signed observables. A common exponent shift is proved to cancel from the actual
normalized readout. Acceptance includes the proposed output's rounding error;
all arithmetic in the checker is exact rational arithmetic reduced by the Lean
kernel. The generator's Python precheck and metadata do not produce proofs.

The source/feedback bridge derives exponent tables from the actual rational
model, checks component outputs against the candidate point, and supplies the
previously external actual-residual premise. Existing contraction and readout
theorems then bound the true finite-closure solution and its observables. The
updated self-consistency client has **11 claims and four open obligations**.
For bias `1/3`, coupling `1/8` and the rounded candidate `0.361413`, it proves a
residual budget of `1/100000`, a solution budget of `1/75000` and a separate signed
readout budget of `3/200000`. Uncertain real inputs, scalable local solvers,
critical/multiple branches, closure error, quantum self-consistency and
thermodynamic limits remain outside this delivery.

The new scalar module, Gibbs module, generated data and physical client compile.
The library, Analysis/StatMech/Condensed/FieldTheory/HighEnergy entries, numerical
client and declaration index also build (`/tmp/leanphy-gibbs-integration.log`).
The canonical numerical client and index also rebuilt successfully
(`/tmp/leanphy-gibbs-canonical-clients.log`). All **19 infrastructure tests**
pass in the canonical workspace (`/tmp/leanphy-gibbs-canonical-infrastructure.log`),
including discovery of the new public operations and strict rejection of the
unfinished eleven-claim/four-obligation self-consistency project. An earlier
mirror-wide attempt lacked unrelated executable targets; its setup errors are
superseded by this canonical result. The missing mirror targets were subsequently
built successfully (`/tmp/leanphy-gibbs-all-clients.log`).

The adjacent Euler client was rebuilt in the local test copy
(`/tmp/leanphy-gibbs-adjacent-client.log`). All **373 library source/configuration
files** match the canonical workspace by SHA-256 at this boundary
(`/tmp/leanphy-gibbs-source-match.json`); executable root sources were also
compared. The reused local copy is not a historical frozen snapshot.

All **eight numerical regression methods** pass across focused invocations:
three in `/tmp/leanphy-gibbs-regression-initial.log`, four completed methods in
`/tmp/leanphy-gibbs-regression-remaining.log`, and the repaired guide method in
`/tmp/leanphy-gibbs-guide.log`. The earlier guide attempt exposed a rational-cast
error in its snippet; all **three current guide snippets** now compile.
Independent 80-digit Decimal exponential evaluations select candidate outputs
for six scalar inputs and seven finite readouts. Five feedback models vary
order-parameter/configuration counts as (1,2), (2,3), (3,4), (2,1) and (0,2).
Their generated proofs check the actual feedback residual and consume the
fixed-point theorem; Decimal values are test oracles, never proof premises.
Twelve deliberately invalid generated data sets are rejected by Lean, including
mutated models/outputs/budgets, invalid range reduction, an empty ensemble and a
nonpositive certified denominator. Parser, provenance and overwrite checks pass.

All **eight new negative fixtures** pass (`/tmp/leanphy-gibbs-negatives.log`).
The script now defines 409 fixtures; this batch did **not** rerun all 409.
The prior 393-fixture vacuum and eight-fixture Euler checks remain historical
evidence with their original scopes.

The current full dependency audit, run in the canonical workspace, passes for
**370 source modules, 17,231 declarations and 480 private declarations**; only
`propext`, `Classical.choice` and `Quot.sound` occur transitively.
Report: `/tmp/leanphy-gibbs-audit.json`; log: `/tmp/leanphy-gibbs-audit.log`.
There are 369 files and 67,249 lines under `LeanPhy/`, including 73 example
modules. The audit also includes the root import.

The initial thirteen positive compiler invocations took 2.01–2.17 seconds each,
including process startup and imports, with an observed maximum process RSS of
3,429,712 KiB. They cover at most six configurations and three order parameters;
these are local observations under concurrent build activity, not a large-system
benchmark. The checked-in feedback data produce 2,173 bytes of generated source
and exponential enclosure rationals up to 295 bits. Metrics are in
`/tmp/leanphy-gibbs-regression-initial.json`,
`/tmp/leanphy-gibbs-regression-remaining.json`, `/tmp/leanphy-gibbs-guide.json`
and `/tmp/leanphy-gibbs-generation.json`.

The latest single `scripts/verify.sh` invocation still has no completed success
marker. The numerical suite is now wired into that script; focused regressions,
builds and the fresh dependency audit do not replace a complete release run.
Temporary logs are local evidence, not a versioned release. See the
[numerical guide](docs/numerical-gibbs.md) and [global roadmap](docs/roadmap.md).

## Historical Euler batch: transport and regular domains (2026-10-08)

This section records the preceding batch before the numerical Gibbs additions.


`FieldTheory.EulerTransport` derives momentum, force and directional-momentum
transport from a polynomial point transformation of a first-order real
commuting-field density. For actual C² fields, the Hessian contributions cancel
in the Euler expression: the transformed equations are the original equations
multiplied by the Jacobian transpose. The operation also transports variations,
boundary currents and the actual interval-action derivative, including endpoints.

Forward equation transport allows rectangular or singular Jacobians. Recovering
the original equations requires a **right inverse** `J K = I_old`; square
Jacobians with nonzero determinant construct that inverse. Domain theorems retain
the supplied regularity region. They do not prove a global inverse chart. The
parameterized nonlinear-shear client proves its determinant is one, while a
square-map counterexample proves that a singular change can erase an equation.
The client now records **13 claims and four open obligations**: global inverse
field charts, higher-order/derivative-dependent changes, multidimensional/graded
boundaries, and quantum measure/scattering.

The library, Classical/Condensed/FieldTheory/HighEnergy entries, client and index
build successfully (`/tmp/leanphy-euler-integration.log`). All **six field-change
regressions**, including **four compiled guide snippets**, pass
(`/tmp/leanphy-euler-field-suite.log`). Independent exact rational calculations
expand transformed densities before directly computing Euler expressions for
five old/new field dimensions: (1,1), (1,2), (2,1), (2,2) and (2,3). Nine actual
Euler components on quadratic time profiles are checked in Lean using both
actual-jet evaluation and the transport theorem, with declaration-axiom checks.
Mixed kinetic terms, cubic potentials, sources and field-gradient couplings
are included. All **19 infrastructure tests** pass
(`/tmp/leanphy-euler-infrastructure.log`).

All **eight new rejection fixtures** pass (`/tmp/leanphy-euler-negatives.log`),
protecting C² regularity, Jacobian/Hessian factors, pushed variations, inverse
orientation, determinant conditions and domain/singular-map boundaries. There
are now 401 fixture definitions; this batch did **not** rerun all 401. The
393-fixture results below belong to the preceding vacuum batch.

The current full dependency audit passes for **367 source modules, 17,079
declarations and 477 private declarations**, with only `propext`,
`Classical.choice` and `Quot.sound` allowed transitively.
Report: `/tmp/leanphy-euler-audit.json`; log: `/tmp/leanphy-euler-audit.log`.
The source tree under `LeanPhy/` contains 366 files and 66,801 lines, including
72 example modules; the audit additionally includes the root import.

The latest single `scripts/verify.sh` invocation still has no completed success
marker. These focused checks and the new full dependency audit do not turn the
interrupted release run into a success. The local build copy
`/tmp/leanphy-vacuum-validation.l5nw3q1f` has been reused for Euler development;
its earlier whole-copy hash match is historical evidence, not a claim that it
remains a frozen vacuum snapshot. Temporary logs are local evidence, not a
versioned release. See the [field-change guide](docs/field-redefinitions.md).

## Historical vacuum batch: component checks passed, single release run incomplete (2026-10-08)

This section records the batch **before `EulerTransport`**; its counts, source
matches and test totals describe that earlier worktree.


The latest `bash scripts/verify.sh` run was interrupted before its final success
marker. `/tmp/leanphy-current-verify.log` records passing builds, 777 smoke checks,
the dependency audit (365 modules, 16,954 declarations, 477 private), downstream
project audit and the first twelve Python suites. It stops inside the symbolic
Lie regression. This is not a completed release check. The remaining suites are
checked separately; the resumed-check evidence is described below.

The updated library and public entries, fermion/dynamics/finite-lattice clients
and declaration index build successfully. The new full dependency audit passes
for **366 source modules, 17,043 declarations and 477 private declarations**,
using only `propext`, `Classical.choice` and `Quot.sound` transitively.
Report: `/tmp/leanphy-vacuum-audit.json`; log: `/tmp/leanphy-vacuum-audit.log`.
This audit covers the new vacuum module; it does not replace release regressions.

All **19 infrastructure tests** pass. They check fourteen fermion claims and
three open obligations, eleven dynamics claims and three open obligations, and
six finite-lattice claims and three open obligations. Strict mode rejects the
unfinished clients. `verify.sh` now explicitly builds the finite-lattice client;
its report correctly identifies a **unit-Jacobian** Ward insertion.

### Derived vacuum correlations

`FermionVacuum` derives two- and four-point expectations of arbitrary complex
linear creation/annihilation probes from CAR, adjoints and annihilation of an
actual normalized density. `FiniteFermion.vacuumState n` constructs that density
and proves the annihilation condition for every finite mode count, including
zero; `vacuumOfOrder` supports named modes. The resulting `certificate` supplies
the existing ordered four-point interface without asking for Wick as an input.

Independent exact Gaussian-integer occupation actions check forty probe quartets
across zero through four modes. Ten generated quartets are also checked by Lean
using the public formula, with declaration-axiom checks. Both regression tests
pass (`/tmp/leanphy-vacuum-regressions.log`). Four focused negative fixtures pass:
missing annihilation, the crossed-contraction sign, repeated-probe contact terms
and unintended coefficient conjugation (`/tmp/leanphy-vacuum-negative.log`).
All four Lean snippets in the fermion-model guide also compile
(`/tmp/leanphy-vacuum-guide.log`). The three vacuum regression tests have thus
passed across two focused invocations.

### Resumed regression evidence

All **393 independent negative fixtures** pass: nineteen completed in
`/tmp/leanphy-vacuum-all-negative.log`; the remaining 374 completed in
`/tmp/leanphy-vacuum-remaining-negative.log`. The local continuation uses exactly
the same fixture texts and rejection classifier. The disjoint label sets and
remaining fixture hashes are recorded in `/tmp/leanphy-vacuum-negative-resume.json`.

Mounted-filesystem import latency motivated a local copy at
`/tmp/leanphy-vacuum-validation.l5nw3q1f`. At that batch boundary, all **369 audited source/configuration
files and 2,011 library artifacts** matched the canonical workspace by SHA-256
(`/tmp/leanphy-vacuum-artifact-match.json`). No compiler result is accepted merely
because a cached file exists in that copy.

The symbolic Lie, condition-discovery, adjoint-deformation and second-order
suites pass (8, 7, 7 and 9 tests) in
`/tmp/leanphy-remaining-verification.log`. The third-cohomology and joint
third-order-search suites also pass across resumed invocations (8 and 10 tests).
For the last three suites, completed method names and the uncompleted selections
are recorded in `/tmp/leanphy-vacuum-suite-resume.json`; local continuations log
to `/tmp/leanphy-local-third_cohomology.log`,
`/tmp/leanphy-local-symbolic_third_cohomology.log` and
`/tmp/leanphy-local-third_order_search.log`. All three now pass: respectively
4 + 4, 1 + 7 and 5 + 5 completed methods. Each suite's disjoint method sets cover
its entire current test class, and its script hash is unchanged.

Across the original, focused and resumed invocations, all **177 tests in twenty
Python suites** have passing results. The earlier eighteen-test infrastructure
result is superseded by nineteen passing tests; the three vacuum tests are new.
Summary: `/tmp/leanphy-vacuum-verification-summary.json`. Documentation links,
the 28/7/14 inventory identifiers, declaration scanning and `git diff --check`
also pass. The original interrupted run and deliberately stopped continuation
drivers do not acquire a successful release marker from these separate checks.

The worktree also adds finite Fourier reconstruction and finite weight-symmetry
Ward/blocking-error readouts. These finite operations do not prove thermal or
general Gaussian factorization, arbitrary-point or time-ordered Wick, continuous
frequency/transport limits, continuous RG or a thermodynamic limit. A constructed
empty vacuum is not automatically a ground state of the user's Hamiltonian.

The previously written current-worktree full-pass claim is superseded by this
record; historical batch records below retain their original scopes. Temporary
logs are local evidence, not a durable source snapshot or a reproducible release.

## Historical point field transformations: focused checks passed

This is the initial three-module batch; the current Euler extension is recorded above.

Three public modules implement nonlinear polynomial point transformations of
first-order real commuting-field densities. Full gradient Jacobians, potentials
and source terms transform together. Polynomial composition and explicit inverse
restoration are proved. Actual field evaluation, interval actions and fixed
finite-configuration probabilities consume the operation.

Infinitesimal changes give the actual Euler bulk integral plus endpoint flux;
on-shell stationarity requires matched boundaries. A physical client checks
nonlinear kinetic/source changes, inverse shears, actual finite readouts and an
on-shell profile with nonzero boundary variation. Finite changes retain higher
orders. General local Euler transport, derivative-dependent and higher-order EFT
changes, multidimensional/graded fields and quantum measure/scattering remain open.

Three independent data regressions, ten new rejection fixtures and two guide
snippets passed. Public entries/index and the eight-claim/four-open-task client
passed build and integration checks. The latest current-worktree full release run
remains incomplete, as recorded above. This confirms the stated finite point-transformation
scope; general local Euler transport, derivative-dependent and higher-order EFT
changes, multidimensional/graded fields and quantum measure/scattering remain
open.

See the [field-redefinition guide](docs/field-redefinitions.md).

## Actual finite-source self-consistency and physical error budgets

The complete `scripts/verify.sh` run passed: 777 smoke capabilities,
378 independent negative elaboration fixtures and 169 Python tests
(including seventeen public-infrastructure tests and four self-consistency regressions).
The full dependency audit covered 358 modules, 16,770 declarations
and 464 private declarations. The library contains 357 sources,
65,037 lines and 70 example modules; its compiled index has
9,120 public entries and 4,268 theorems. Counts measure
verification coverage and discovery, not completeness of physics capabilities.

Validation used the pinned Lean/mathlib toolchain:

```bash
LEANPHY_BUILD_ROOT=/tmp/leanphy-ghost-validation.3zioi127 bash scripts/verify.sh
```

Log: `/tmp/leanphy-self-consistency-full-verify.log`. All 435 frozen source,
configuration, script and data hashes match the canonical worktree and build mirror.
Both guide snippets compile. Existing generator and downstream checks remained
enabled; the optional clean scaffold build with fresh fetching was not enabled.

Three public modules construct an actual finite Gibbs feedback map, derive its
contraction from finite input envelopes, and transfer residuals to the unique
solution and physical readouts. Finite maxima construct input envelopes;
approximate updates and evaluated readouts retain separate numerical-error inputs.
Symmetric couplings give an actual stationary-functional derivative. The exact
energy-source bridge retains beta in both applied field and feedback coupling.

The variable finite-cluster client retains eight claims and four open tasks;
strict mode rejects the unfinished project. It checks nonzero solution/readout
budgets and exhibits a stationary but non-self-consistent point for singular
coupling. Independent rational enumeration checks eight finite envelopes and
47 actual Gibbs feedback derivative directions. Empty order labels and a single
configuration remain supported; a raw moment cannot replace covariance.
Ten negative fixtures protect beta, strict smallness, error budgets, model binding,
symmetry, nonempty configurations and the stationary converse.

The sufficient contraction domain is conservative. No critical surface, variational
minimum, original-model approximation, certified floating-point solver,
noncommuting quantum closure or thermodynamic limit is asserted. These remain
separate research obligations. R10 is partially delivered within this finite scope;
R05/R07/R08 and the numerical-envelope part of R11 remain independent priorities.

After the full run, matching build artifacts were synchronized to the canonical
`/mnt/data/tingchia/Lean_PHY` workspace. The physical-client integration test and
both guide snippets passed again there. All 435 frozen files still match the
canonical worktree and build mirror. Global planning retains 28 capabilities,
seven tracks and fourteen deliveries. The isolated field-redefinition draft is
not part of this accepted public baseline.

See the [self-consistency guide](docs/self-consistency.md).

## Fermion words, interacting expressions and actual derivatives

The complete `scripts/verify.sh` run passed: 777 smoke capabilities,
368 independent negative elaboration fixtures and 164 Python tests
(including sixteen public-infrastructure tests and five fermion-word regressions).
The full dependency audit covered 354 modules, 16,663 declarations
and 464 private declarations. The library has 353 sources,
64,401 lines and 69 example modules. Its compiled index contains
9,055 public entries and 4,224 theorems. Counts are not
a measure of theoretical-physics completeness.

Validation used the pinned Lean/mathlib toolchain:

```bash
LEANPHY_BUILD_ROOT=/tmp/leanphy-ghost-validation.3zioi127 bash scripts/verify.sh
```

Log: `/tmp/leanphy-fermion-words-full-verify.log`. The 429 frozen source,
configuration, script and data files match the canonical worktree and build mirror.
Both guide snippets compile. All existing generator and downstream checks remain
enabled; the optional clean scaffold build with fresh fetching was not enabled.

Four public modules prove terminating CAR normalization, strictly ordered output,
coefficient interpretation, adjoints, injective local-mode embedding and sound
identity checking. Actual occupation operators, interacting thermal states and
initial unitary-observable derivatives consume these operations. The physical
client retains seven claims and three open tasks; strict mode rejects it.

Independent regressions compare all 341 two-mode words of length zero through four
on four occupation states, check 68 reorderings in Lean, retain complex adjoints,
and exercise a 32-letter ordered word over 1024 possible labels and zero modes.
The large label space is a symbolic check, not a many-body matrix benchmark.
Ten rejection fixtures protect signs, contractions, Pauli, adjoints, independent
mode assignment and interaction coefficients.

Normal ordering includes contractions; it is not vacuum subtraction or a Wick
theorem. Actual-state Gaussian moment factorization, bosonic cutoff corrections,
efficient large-system operations and thermodynamic limits remain open.
Existing default/broad profile counts remain unchanged.

After the full run, source-matched artifacts were synchronized to the canonical
`/mnt/data/tingchia/Lean_PHY` workspace. The fermion client integration test and
both guide snippets passed again there. All 429 frozen files still match the
canonical workspace and build mirror. The global inventory retains 28 capabilities,
seven tracks and fourteen deliveries. Its current overview precedes historical
batch records; planning covers both physics areas, shared evidence and exploration.
The isolated self-consistency draft is not part of this accepted public scope.

See the [fermion expression guide](docs/fermion-words.md).

## Actual fields, interval actions and integrated current bounds

The complete `scripts/verify.sh` run passed: 777 smoke capabilities,
358 independent negative elaboration fixtures and 158 Python tests
(including fifteen public-infrastructure tests). The full dependency audit covered
349 modules, 16,468 declarations and 447 private declarations.
The library has 348 sources, 63,611 lines and 68 example modules.
The compiled index contains 8,951 public entries and 4,160 theorems.
These counts do not measure theoretical-physics completeness.

Validation used the pinned Lean/mathlib toolchain:

```bash
LEANPHY_BUILD_ROOT=/tmp/leanphy-ghost-validation.3zioi127 bash scripts/verify.sh
```

Log: `/tmp/leanphy-action-evaluation-full-verify.log`. The 422 frozen
source/configuration/script/data hashes match the canonical worktree and build
mirror. Both guide snippets compile. All existing generator and downstream-project
checks remain enabled; the optional clean scaffold build with fresh dependency
fetching was not enabled.

Five public modules and the physical client passed the full release checks.
The client retains nine claims and four open tasks. Its counterexample with
varying endpoint field values is recorded as refuted without closing the original
positive goal. The integration interval remains fixed under this variation. The other open tasks concern solution existence/stability, multidimensional
spacetime boundaries/charges, and covariant/graded fields. Strict mode rejects
the unfinished project. An off-shell quadratic profile retains current budget two.

Ten new rejection fixtures protect endpoint assumptions, regularity, interval
orientation, actual field/jet identity, cross-component accelerations, nonzero
current budgets, Noether equation premises and exploration target binding.
Existing default/broad profile counts remain unchanged.

After the full run, source-matched build artifacts were synchronized to
`/mnt/data/tingchia/Lean_PHY`. The actual-action client integration test and both
guide snippets passed again from that canonical workspace. The frozen 422-file
snapshot still matches both locations. Planning retains 28 capabilities, seven
tracks and fourteen deliveries; this batch only completes its stated action scope.

Actual C² fields support local first variation in explicit constant directions.
For one-dimensional profiles, the library differentiates an actual polynomial
action integral, retains endpoint flux, connects smooth formal jets to actual
Euler residuals, and derives Noether balance and integrated residual error.
Compactness supplies the domination needed for differentiating polynomial
integrals. Boundary stationarity does not imply minimization or solution existence.
General spacetime boundary integration, covariant/graded fields, field replacements
and local regularity adapters remain open. See the [action guide](docs/action-evaluation.md).

## Checked complex matrix residuals, spectral domains and effective readouts

The complete `scripts/verify.sh` run passed: 777 smoke capabilities,
348 independent negative elaboration fixtures and 157 Python tests,
including fourteen public-infrastructure and nine matrix-certificate tests. The full
dependency audit covered 343 modules, 16,372 declarations and
447 private declarations. The worktree contains 342 library sources
(62,777 lines, 67 example modules); its compiled public index has
8,880 entries, including 4,113 theorems. Counts measure verification
and discovery, not theoretical-physics completeness.

Validation used the pinned Lean/mathlib toolchain:

```bash
LEANPHY_BUILD_ROOT=/tmp/leanphy-ghost-validation.3zioi127 bash scripts/verify.sh
```

Log: `/tmp/leanphy-matrix-certificates-full-verify.log`. Library/root Lean sources,
configuration, verification scripts and the input/report JSON match the frozen
snapshot and build mirror. Both Lean snippets in the [matrix-certificate guide](docs/matrix-certificates.md)
compile. All existing generator and downstream-project checks remain enabled; the
optional clean scaffold build with fresh dependency fetching was not enabled.

The verified build artifacts were synchronized to the canonical worktree after
checking source identity. The physical-client report and strict-mode regression
passed there, and both guide snippets compiled there without changes. The 415
frozen source/configuration/script/data hashes were checked again in both trees.

Five public modules now connect rational real/imaginary matrix data to actual
complex inverses, inverse norm/error bounds, spectral exclusion disks and
rectangular elimination. The residual is recomputed in Lean. Model uncertainty
is added before testing a strict margin below one. The producer is untrusted;
`decide +kernel` proves the finite rational acceptance predicate without a native
decision axiom. The envelope checker binds both nominal data and the exact candidate.

The physical client uses a complex Hermitian heavy block and different light/heavy
dimensions. It has nine claims, including a uniform effective-Hamiltonian error
on a closed energy disk, and three open tasks: physical model enclosure, unitary
low-energy dynamics, and large-system/continuum validity. Strict mode rejects those
tasks. The actual spectral-domain question is closed through indexed goal resolution.
Sources, reconstruction and linear readouts retain their error bounds.

Nine generator regression groups cover exact complex arithmetic, empty/scalar and
non-normal inputs, independent kernel rejection of forged data, strict margin,
operator versus entrywise bounds, parser and provenance handling, and actual model
premises. Ten added public rejection fixtures protect complex residuals, uncertainty,
energy domains and conclusion binding. Earlier default/broad profile counts remain
unchanged. Two new example modules are consumers of the five shared operations.

R11/R08 remain partially delivered. General interval arithmetic, automatically
proved floating-point/physical enclosures, individual eigenvalue certificates,
sparse scalability, propagating-field matching, energy-independent unitary reduction
and continuum limits are not established. A failed residual test does not prove
singularity. The certified spectral disk belongs to the declared heavy block,
not automatically to the full coupled Hamiltonian; every bound uses the stated
L-infinity operator/vector norm.

## Predicate-bound exploratory branches and model revisions

The complete `scripts/verify.sh` run passed: 777 smoke capabilities,
338 independent negative elaboration fixtures and 147 Python tests,
including thirteen public-infrastructure tests. The complete dependency audit covered
336 modules, 16,216 declarations and 447 private declarations.
The verified worktree contains 335 library sources (62,074 lines,
65 example modules). Its compiled public index has 8,780 entries,
including 4,066 theorems. These are verification and discovery counts,
not a measure of theoretical-physics completeness.

Validation command, with the pinned Lean/mathlib toolchain:

```bash
LEANPHY_BUILD_ROOT=/tmp/leanphy-ghost-validation.3zioi127 bash scripts/verify.sh
```

Log: `/tmp/leanphy-exploration-full-verify.log`. All library, root Lean, configuration
and verification-script hashes matched the frozen source snapshot and build mirror.
The two Lean snippets in the [exploration guide](docs/exploratory-workflow.md) compile. Existing generated
and downstream-project checks remain enabled; the optional clean scaffold build
that fetches fresh dependencies was not enabled.

After source-matched artifact synchronization, both guide snippets also compiled
directly in the workspace. The workspace client passed its report, revision-history
and strict-mode checks; the frozen source/configuration/script snapshot remained intact.

`Workflow.Exploration` binds questions and branches to actual model/parameter
predicates. Restriction, condition discharge, exhaustive cases, parameter pullback
and explicit implication transport are proved. Counterexamples refute the stored
branch goal; a failed attempt carries no logical evidence. Revisions archive old
propositions and evidence, then create a pending root. Package completion requires
the root answer and retains the original obligation proof.

The independent physical client reuses complex pairing and auxiliary heavy-field
elimination. Its default report has seven claims and two open positive goals;
strict mode rejects it. The three proved revised/covered questions have three
claims and no open goals, and pass strict mode. Thirteen new rejection fixtures
protect conditional/root distinction, model revision, exact indexed updates,
coverage, counterexample domains and label reuse. Text/JSON reports preserve
history and expose outcome types; existing empty-record JSON shapes and default
physics package counts remain unchanged.

R12 is partially delivered. Semantic condition/convention search, automatic
cross-project change impact analysis, and automated discovery of suitable branch
conditions remain open. The ledger is an immutable Lean value, not a tamper-proof
external audit log. This batch adds no continuum physics or new elimination
validity assumptions; nonzero auxiliary coefficients do not establish stability
or a controlled large-mass expansion.

## Actual finite quantum dynamics and noncommuting thermal response

The complete `scripts/verify.sh` run passed: 777 smoke capabilities,
325 independent negative elaboration fixtures and 145 Python tests,
including eleven public-infrastructure tests. The complete dependency audit covered
334 modules, 15,923 declarations and 443 private declarations.
The verified worktree contains 333 library sources (61,538 lines,
64 example modules). Its compiled public index has 8,613 entries,
including 4,043 theorems. These counts describe verification and discovery,
not the fraction of theoretical physics covered.

Validation used the pinned Lean/mathlib toolchain:

```bash
LEANPHY_BUILD_ROOT=/tmp/leanphy-ghost-validation.3zioi127 bash scripts/verify.sh
```

Log: `/tmp/leanphy-dynamics-full-verify.log`. The full audit checked library and
configuration hashes against the workspace and build mirror. The two Lean snippets
in the [response guide](docs/quantum-response.md) compile. All existing generator and downstream-project
checks remain enabled; the optional fresh dependency-resolution scaffold build
was not enabled.

After source-matched artifact synchronization, both guide snippets also compiled
directly in the workspace. The workspace response client passed its report and
strict-mode obligation checks. The library/configuration snapshot remained unchanged.

The three public modules derive actual exponential differences, noncommuting
perturbation derivatives, Heisenberg/density time derivatives, picture equivalence,
finite-time integrated-commutator response, and a constant source switched on at
zero. Moving probes retain contact terms. Normalized Gibbs expectations are
differentiated for general Hermitian perturbations without a moving eigenbasis;
normalization and beta factors are retained, and the ordinary covariance reduction
has an explicit commutation premise.

The independent client consumes arbitrary-mode constructed CAR Hamiltonians and
thermal initial states. It has ten proved claims and three open obligation groups:
general drives and frequency response, controlled perturbation remainder, and
continuum limits. Strict mode rejects those tasks. Ten new rejection fixtures
protect time/source signs, commutation conditions, normalization, contact terms,
beta, causality and Hermitian couplings. Default profile counts remain unchanged.

R06 is a partial delivery: arbitrary time-dependent drives, stationary/spectral
and frequency representations, finite-amplitude error bounds, unbounded operators,
infinite volume and infinite time are not established. The broader dynamics/Wick
obligations in earlier clients remain open. High-energy action operations,
physical numerical certificates and exploratory branches remain separate priorities.

## Constructed finite fermion models and physical conventions

The finite-fermion source snapshot passed the complete `scripts/verify.sh` run:
777 smoke capabilities, 315 independent negative elaboration fixtures and
144 Python tests, including ten public-infrastructure checks. The complete
library dependency audit covered 330 modules, 15,799 declarations and
443 private declarations. There are 329 library Lean sources (60,932 lines,
63 example modules), and the compiled public index contains 8,539 entries,
including 3,989 theorems. These counts describe regression and discovery
coverage, not the percentage of theoretical physics formalized.

Validation used the pinned toolchain and the command:

```bash
LEANPHY_BUILD_ROOT=/tmp/leanphy-ghost-validation.3zioi127 bash scripts/verify.sh
```

The complete log is `/tmp/leanphy-fermion-full-verify.log`. Library source and
configuration hashes were checked against the workspace before and after the
full audit. Both Lean snippets in the [fermion guide](docs/fermion-models.md) elaborate;
twelve new rejection fixtures protect conjugation, normal-ordering constants,
parity strings, mode isometry and representation dimensions. Existing Lie/ghost
and generated downstream-project tests remain enabled. The optional fresh
dependency-resolution scaffold build was not enabled.

The new constructor supplies actual CAR matrices, adjoints and parity strings
for arbitrary finite mode counts, on an occupation space of dimension `2^n`.
Quadratic coefficient tables yield Hermitian many-body Hamiltonians and thermal
states. The full Nambu commutator equation and energy relation, orbital basis
transport, particle-hole conjugation and Majorana occupation convention are
proved. Complex pairing uses its norm squared; the legacy complex-symmetric
block remains available with corrected scope descriptions. Berry geometry is
no longer described as a constructed selected-band curvature.

The independent client has ten proved claims and three open obligation groups:
interacting self-consistency, dynamical correlations, and continuum/topology.
Strict mode rejects those unresolved tasks. Default and broad package counts
remain unchanged. General interacting expressions, arbitrary-word normal
ordering, actual-state Wick bridges, time-derivative response and large-system
numerical performance are not established by this batch.

The [capability inventory](docs/capabilities.md) and [roadmap](docs/roadmap.md) record this as the
first finite-fermion delivery within R01/R03/R04. Those tracks retain their
remaining requirements; high-energy action operations, physical certificates,
noncommuting response and exploratory branches remain project priorities.

## Effective operations and global capability review

The effective-operations baseline passed the complete `scripts/verify.sh` run with the
pinned Lean/mathlib toolchain: 777 smoke capabilities, 303 independent negative
elaboration fixtures and 143 Python tests, including nine public-infrastructure
checks. The full dependency audit covered 321 modules, 15,545 declarations and
430 private declarations. That baseline contains 320 Lean sources (59,800 lines,
62 example modules); the compiled public index has 8,406 entries, including
3,910 theorems. These are regression and discovery counts, not physics coverage
percentages.

Validation command, executed from the workspace root:

```bash
LEANPHY_BUILD_ROOT=/tmp/leanphy-ghost-validation.3zioi127 bash scripts/verify.sh
```

The mirror's library/configuration hashes were checked against the workspace
before and after the complete declaration audit. The verification log is
`/tmp/leanphy-effective-full-verify.log`. Both Lean snippets in the
[effective-operation guide](docs/effective-theory.md) elaborate. The existing
Lie/ghost, generated downstream-project and audit checks remain enabled; the
optional fresh dependency-resolution scaffold build was not enabled.

New public operations preserve noncommutative formal coefficients, actual
block solutions, transformed sources and linear probes. Quantum elimination
is energy dependent and transports both quadratic probes and the reconstructed
state norm. Polynomial heavy-field elimination handles one algebraic auxiliary
field with arbitrary light polynomials; it does not integrate propagating or
loop fields. Norm estimates come from actual inverse residuals in a normed
ring, separately from formal truncation. The eight-claim client retains three
open obligations: the low-energy domain, propagating/loop fields, and
energy-independent unitary dynamics; strict mode rejects these open tasks.

The [capability inventory](docs/capabilities.md) now tracks this scope alongside
all other research capabilities. The [global roadmap](docs/roadmap.md) records
seven development tracks and fourteen delivery items, with implementation
maturity kept separate from verification status. General many-body construction,
dynamical/noncommuting response, physical numerical certification and exploratory
branching remain open; passing this batch does not complete those tracks.

## Finite source and thermal integration

The complete `scripts/verify.sh` run passed: 777 smoke capabilities, 291
independent negative elaboration fixtures and 142 Python tests, including eight
public-infrastructure checks. All twelve new rejection fixtures passed. The
full library audit covered 313 modules, 15,349 declarations and 427 private
declarations. The 312 library sources contain 58,805 lines; the compiled public
index has 8,275 entries, including 3,832 theorems. These counts track regression
coverage, not the percentage of physics formalized.

Verification ran with the pinned toolchain in a build mirror matched to the
workspace source hashes. Both [source/thermal guide](docs/source-response.md)
Lean snippets elaborate. Existing generator and downstream-project checks
remain enabled; the optional fresh dependency-resolution scaffold build was
not enabled. The ordinary generated-project tests build real downstream sources.

The implemented boundary is finite: actual normalized source derivatives,
static susceptibility, contact terms, action coupling insertions and uniform
finite-source error bounds. Arbitrary finite Hermitian Hamiltonians now have
positive trace-one Gibbs densities equal to their normalized matrix exponential.
Stationarity, basis covariance and energy-temperature derivatives are proved;
Hamiltonian/probe parameter derivatives presently use a fixed common basis.
The source client has ten claims and retains thermodynamic-limit and dynamical
response obligations; strict mode rejects those open tasks. No new default
profile claim is used to hide these conditions.

## Shared-core and coupled-action integration

The previous shared-core/action snapshot passed the full `scripts/verify.sh` run:
777 smoke capabilities, 279 independent negative elaboration fixtures, and
141 Python test cases (including seven new research-core/index/client tests).
The complete library dependency audit covered 304 source modules, 15,131 declarations
and 427 private declarations. The local build mirror was checked against the
workspace's source hashes; all existing Lie/ghost generator, declaration-audit
and downstream-project tests remained enabled. The optional fresh dependency
resolution build (`LEANPHY_VERIFY_SCAFFOLD_BUILD=1`) was not enabled; the
regular generated-project audit tests did build and check downstream sources.

The implemented boundary is first-order, commuting polynomial fields in flat
coordinates with constant scalar coefficients. General coupled actions yield
local first variation, Euler equations, Noether currents and canonical stress
identities. Equation/variation/breaking bounds yield a local current-defect
certificate; neither smooth jet realization nor integrated charge conservation
is inferred. The old mechanical residual now advances every component, with
a theorem connecting it to the new first-order action representation.

Registered obligation targets are retained in their package and resolution
requires their proof through a package-indexed reference. Original target
proofs remain in history, and related evidence does not close textual tasks.
The public declaration index exposes 8,136 entries including 3,728 theorems;
it is discovery metadata, separate from the more comprehensive audit.

Default/extended/broad profiles retain respectively 8/11/13 packages,
15/25/28 claims, and 8/12/14 open obligations. The variational client has four
claims and two open tasks (smooth solutions and integrated charges); strict
mode rejects those open tasks. Both public-guide Lean snippets were elaborated.
See [core migration](docs/research-core.md), [variational tools](docs/variational.md),
and [remaining capabilities](docs/capabilities.md).

## The one invariant

Every theorem in this repository is checked by the Lean 4 kernel against
mathlib.  There is **no `sorry` and no `axiom`** anywhere in the library or
in the acceptance test `Main.lean`.  You can re-check this yourself:

```bash
lake build                      # every file must compile
lake exe leanphy_smoke          # prints the capability report
lake exe leanphy_prototype      # runs the compact end-to-end workflow
lake exe leanphy_check          # renders the eight proof-bearing theory packages
lake exe leanphy_check --json   # emits the same compiled ledgers as JSON
grep -rn 'sorry\|admit\|axiom' LeanPhy Main.lean Prototype.lean   # only prose in comments
```

The semantics are **conditional correctness**: a theorem always has the shape
"given these hypotheses, this conclusion follows".  LeanPhy never claims
physical truth, convergence of a limit, or the validity of an unbounded-operator
or path-integral manipulation.

The sections below describe previously integrated coverage. Current counts and
release evidence are recorded at the top of this file. Cross-domain additions include:

- Finite even ghost images extend to odd polynomial derivations with an exact
  finite nilpotency criterion. Increasing-pair/triple coordinates now prove both
  degree-one and degree-two CE bridges, and Jacobi via d2 d1 = 0 supplies canonical
  nilpotency over every commutative ring. The rational generator retains checked
  Lie laws and explicit images while reusing this universal theorem. A parameter
  family has an exact pair-closedness locus valid with zero divisors. The research
  report contains fifty-four claims and one physical obligation. Twenty-two generator
  regressions cover edge dimensions, dense basis changes, characteristic two,
  ZMod 6, polynomial rings and forged candidates. Actual integer ghost degrees,
  finite homogeneous decomposition, shifted BRST/Koszul differentials and
  degree-specific boundary criteria are now proved. The actual degree-two ghost
  quotient is linearly equivalent to scalar CE H2 over any commutative ring.
  Complete Heisenberg and parameter-family examples distinguish boundaries from
  nonzero classes, including characteristic two and zero divisors. Full chain equivalences,
  negative-degree antighosts and higher matter cohomology computations remain separate.
  Lie-module tensor differentials now have derived nilpotency, integer degree +1,
  CE d0/d1 bridges and complete degree-zero invariant-vector and boundary criteria. See the
  [Lie ghost guide](docs/capabilities.md).

- Generated research projects now include a standalone project verifier and
  mandatory declaration auditing before their CLI reports. Every local source
  under the recorded source directories is built, including unimported drafts
  and executable roots. Per-source Lake artifacts are explicitly bound to
  avoid same-named dependency imports. Source, configuration, verifier, compiled
  artifact and log hashes are recorded; changes during verification reject the
  receipt. Sixteen downstream regressions exercise actual generated projects,
  a physical algebra claim, a generated joint-search candidate and rejection of
  hidden assumptions, proof holes and native-computation axioms. The empty
  template still reports zero claims and an open physical obligation. See the
  [project verification guide](docs/research-project-verification.md).


- `LeanPhy.Verification` and `scripts/audit_library.py` now audit declarations
  in every library source module, including imported/private declarations and
  declarations in external namespaces. The only permitted axiom dependencies
  are `propext`, `Classical.choice`, and `Quot.sound`. The driver checks source
  hashes before/after validation and rejects stale mirrors. Fifteen regressions
  exercise real imported proof holes, private/custom/native-computation axioms,
  type-level dependencies, unexported modules, empty selections and failed runs.
  **Coverage correction:** the former `constants.map₂` scan selected zero
  imported declarations; its old full-audit success message was vacuous.
  Representative theorem audits and compilation remain separate evidence.
  See the [audit guide](docs/declaration-auditing.md).


- Joint second/third correction search now covers every correction pair for a
  fixed rational first direction, with full coordinate and block-map bridges,
  checked image certificates, actual model constructors and all-solutions kernel
  criteria. It repairs a blocked Heisenberg second choice and proves that a
  four-dimensional filiform direction extends to second order but no choice of
  second correction reaches third order. Closedness remains necessary even with
  zero projection. Four generated models, fourteen report claims, ten generator
  regressions and eight new negative fixtures check these boundaries. The block
  cokernel is not asserted to be CE H3. See the [joint search guide](docs/capabilities.md).

- Third-order deformation models now prove the full jet Jacobi criterion and
  the intrinsic H3 obstruction criterion for a specified valid second-order
  choice. The polarized and self Bianchi identities work over any commutative
  ring. Existing rational and parameter H3 reductions construct actual third
  models and characterize all third corrections. The Heisenberg example proves
  that a blocked second-order choice can be replaced by an extendable one,
  with a necessary nonzero third correction. The research report retains thirteen
  proved claims and one physical interpretation obligation. No all-orders or
  third-order gauge-classification claim follows. See the
  [third-order guide](docs/capabilities.md).

- Parameter-dependent actual H3 now derives d2/d3 from polynomial brackets
  and representations, checks complete branch coverage and transports each
  reduction to the actual quotient over characteristic-zero fields. Adjoint
  output provides intrinsic obstruction coordinates, H2 representative tests,
  corrections and actual second-order models. The Heisenberg family proves that
  a displayed direction extends exactly when g is nonzero or t*u vanishes.
  Four-dimensional scalar/vector examples retain resonance intersections and
  discovered representation conditions. The research executable reports sixteen
  proved claims and one physical interpretation obligation. Eight generator
  regressions include 35 rational specializations, edge spaces, field instances
  and three tampered proof candidates. See the [parameter obstruction guide](docs/roadmap.md).

- `LeanPhy.Mathematics.LieCohomology3` and `LieDeformationObstruction`:
  alternating three-cochains, the next CE differential and d3 d2 = 0 define the
  actual H3 quotient. The quadratic obstruction of a closed adjoint direction
  is closed, scales quadratically, descends to H2, and vanishes exactly when a
  second-order Lie model exists. A rational generator checks full coordinates,
  both differentials and actual H3 dimensions. Four examples include a
  four-dimensional scalar model with nonzero d3, separating H3 from coker d2.
  `leanphy_third_cohomology` reports fourteen checked claims and one physical
  interpretation obligation. Eight generator tests include direct differential
  comparisons, edge dimensions, a nontrivial character and forged candidates.
  See the [H3 guide](docs/capabilities.md).

- `LeanPhy.Mathematics.LieDeformationGauge`: explicit second-order generator
  changes include the quadratic inverse and composition terms. First-order
  equivalence preserves the complete second-order residual after transporting
  the correction, and preserves projected obstruction coordinates. Extendability
  is therefore a property of the actual H2 class. Generated solvers emit
  representative obstruction polynomials, a transported correction and an actual
  second-order equivalence. The Heisenberg workflow reduces nine coordinates to
  five and distinguishes different valid corrections; every closed sl2 direction
  is proved extendable through order two. `leanphy_deformation_gauge` reports
  fifteen claims and one physical interpretation obligation. The second-order
  test suite now has nine tests, including forty closed boundary-shifted samples,
  characteristic-two inverses and four tampered candidates. See the
  [generator-change guide](docs/capabilities.md).

- `LeanPhy.Mathematics.LieDeformationSecondOrder`: a complete image solver
  decides second-order extension for arbitrary adjoint two-cochains, computes
  one correction and describes every correction up to a two-cocycle. The new
  rational generator checks quadratic Jacobi polynomials, full residual detection
  and image certificates. Abelian and Heisenberg examples distinguish a nonzero
  but cancellable raw Jacobi term from a nonzero projected obstruction; a zero
  projection alone does not replace first-order closedness. `leanphy_second_order`
  reports thirteen proved claims and one physical interpretation obligation.
  Nine generator tests include exact arithmetic, dimensions zero through two,
  fractional brackets, reproducibility, CLI provenance and four tampered
  candidates. Its target remains coker d2; the new intrinsic H3 layer proves equivalence of their zero tests on closed directions. See the
  [second-order guide](docs/capabilities.md).

- `LeanPhy.Mathematics.LieDeformationReduction`: complete adjoint reductions
  provide unique first-order representative coordinates and actual invertible
  normalizing/trivializing generator changes. Both Lie generators accept
  `coefficient_mode: adjoint`, derive the action from the brackets and use the
  canonical Lean module. Reproducible affine/Heisenberg parameter models include
  degeneration, and the rational sl2 model proves first-order rigidity with an
  explicit primitive for every closed direction. `leanphy_adjoint_deformations`
  reports twelve proved claims and one open physical interpretation task.
  Seven new generator tests cover twelve parameter specializations, four compiled
  numerical edge models, domain discovery, real/complex instances, reproduction,
  CLI protections and two forged adjoint/CE rejection cases. No all-orders or
  analytic rigidity is asserted to follow from the reported first-order dimensions.
  See [the computed adjoint guide](docs/capabilities.md).

- `LeanPhy.Mathematics.LieDeformation`: first-order jets satisfy Jacobi exactly
  for adjoint two-cocycles; actual H2 equality classifies bracket equivalences
  fixing reduction and tangent inclusion. Second-order jets form actual Lie
  algebras exactly when d2(omega)=0 and d2(nu)+Q(omega)=0. A worked two-parameter
  family has all first-order directions but only a*b=0 extends through order
  two, even allowing arbitrary corrections. Legal axes have explicit polynomial
  Lie families; an affine scaling cochain is nonzero yet removable by a proved
  invertible generator change. The new intrinsic layer supplies the H3 obstruction criterion;
  higher-order extension, convergence and group integration remain open.
  `leanphy_deformations` reports 14 proved claims and one open interpretation task.
  See [the deformation guide](docs/capabilities.md).

- `LeanPhy.Mathematics.SymmetryReduction`: constrained state predicates,
  group-orbit equivalence, physical-state quotients, orbit-invariant
  observables, and equivariant finite dynamics.  The preservation and
  invariance proofs are explicit and kernel-checked.  The module does not
  construct gauge fixing, quotient regularity, anomaly cancellation, or a
  physical interpretation of the symmetry.

- `LeanPhy.Mathematics.ConstraintAlgebra`: a commutative Poisson algebra can
  declare constraint generators, their generated ideal, first-class closure,
  weak equality modulo that ideal, and the Dirac-observable normalizer.  The
  kernel checks closure of the constraint ideal and of Dirac observables under
  the algebraic operations exposed by the module.  Constraint classification,
  gauge fixing, quotient regularity, Hamiltonian flow, and physical reduction
  remain separate obligations.

- `LeanPhy.Mathematics.ConstraintMap`: a composable Poisson algebra map can
  preserve the generated constraint ideal and therefore transport weak
  equality.  Dirac-observable transport requires an explicit witness that the
  target constraint ideal is covered by the image of the source ideal.  The
  module does not infer surjectivity, gauge fixing, quotient regularity,
  anomaly cancellation, or physical equivalence.

- `LeanPhy.Mathematics.BRST`: an explicit derivation together with a
  kernel-checked nilpotency proof defines closed, exact, and cohomologous
  elements.  Optional Poisson compatibility closes brackets of closed
  elements, and explicit preservation of a constraint ideal transports weak
  equality.  This is an ungraded algebraic seed.  It does not provide ghost
  number, Koszul signs, a BV antibracket, a gauge-fixing fermion, a path
  integral measure, anomaly cancellation, or a theorem identifying BRST
  cohomology with physical observables.

- `LeanPhy.Mathematics.GradedBRST`: homogeneous pieces, an explicitly odd
  degree shift, and the parity-dependent signed Leibniz law are explicit
  fields.  A square-zero graded derivation derives closed, exact, and
  cohomologous predicates and closed products of homogeneous factors.  The
  module is an algebraic host for later ghost-polynomial models; it does not
  construct a ghost algebra, BV antibracket, gauge fixing, a path-integral
  measure, anomaly cancellation, or physical equivalence.

- `LeanPhy.GaugeTheory.FiniteGhost`: a finite `2 × 2` matrix adapter provides
  square-zero ghost and antighost generators, their CAR anticommutator, an
  explicit even/odd grading, and a concrete odd square-zero differential with
  the signed Leibniz law.  The adapter supports kernel-checked ghost
  closedness and exactness of the identity.  It is a finite algebraic witness;
  it does not construct a full ghost-polynomial algebra, BV antibracket, gauge
  fixing, path-integral measure, anomaly cancellation, continuum field, or
  physical BRST-cohomology equivalence.

- `LeanPhy.GaugeTheory.FiniteGhostPolynomial`: the exterior algebra of an
  arbitrary finite family of Grassmann generators, their square-zero and
  anticommutation identities, and a parity-involution grading. The pure
  exterior inner differential is proved identically zero. Parity eigenspaces
  may overlap in rings with 2-torsion; `GhostDegree` supplies the separate
  integer grading from actual exterior powers.

- `LeanPhy.GaugeTheory.GhostKoszul`: covector contraction, Grassmann left
  derivatives, signed product rules, nilpotency, CAR identities and a
  contraction homotopy. Closed-to-exact conversion requires a unit-pairing
  witness. Zero constraints have only zero as an exact element.
  `koszulOfConstraints` accepts finite constraints in any commutative ring,
  including polynomial rings, and derives elementary constraint syzygies.
  Acyclicity for general constraints and regular-sequence properties are not
  inferred.

- `LeanPhy.GaugeTheory.QuadraticGhost`: the operator `c_i c_j partial_j` is a
  square-zero odd derivation for distinct indices. Its nonzero action is
  independently proved over any nontrivial coefficient ring. A general
  Lie-cochain identification, matter representation, BV bracket, gauge
  fixing and physical cohomology remain open. `Examples.GhostResearch`
  exports eleven proved claims and two explicit obligations through
  `leanphy_ghost_research`; see [the worked guide](docs/capabilities.md).

- `LeanPhy.GaugeTheory.GhostDegree`: actual exterior-power components define
  natural and integer ghost degrees over any commutative ring. Nonzero
  homogeneous elements have unique degree; arbitrary elements decompose into
  finitely many projected components. Lie BRST raises degree by one; Koszul
  contraction lowers it by one. Closed components, preceding-degree primitives,
  scalar exactness iff zero and top-degree closedness are proved. Characteristic
  two parity overlap does not collapse this grading. Negative pure-ghost pieces
  are zero; negative-degree antighosts require a separate algebra.

- `LeanPhy.GaugeTheory.LieGhostCohomology`: ordered contractions recover scalar
  two- and three-cochain coordinates. All homogeneous quadratic ghosts have
  unique two-cochain coordinates. Closedness, exactness with arbitrary polynomial
  primitives, and the cohomologous relation reflect CE conditions. The actual
  degree-two ghost quotient is linearly equivalent to scalar CE H2; supplied
  reductions transfer class coordinates and normal forms. `Examples.GhostCohomology`
  computes Heisenberg ghost H2 and the complete weight-dependent family dimension
  over fields, and proves nonzero resonant classes over nontrivial commutative
  rings. This scalar H2 equivalence does not assert a higher matter quotient equivalence.

- `LeanPhy.GaugeTheory.LieGhostMatter` and `LieGhostMatterCohomology`: a supplied
  Lie module defines the differential on exterior ghosts tensored with matter.
  Nilpotency follows from Jacobi and the representation law, with the signed module
  product rule and integer degree +1. Coefficients recover CE one- and two-cochains
  without finite-dimensionality, freeness or flatness assumptions on matter.
  CE d0/d1 bridges reflect one-cocycle closure. Every degree-zero cycle uniquely
  corresponds to an invariant matter vector, and only the zero constant is exact,
  even allowing arbitrary tensor primitives. `Examples.GhostMatter` computes the
  parameter-dependent adjoint center and character annihilators, with closed
  non-exact torsion examples over ZMod 6. Generated rational models expose this
  extension for a separately certified Lean LieModule; JSON action input, higher
  matter quotient computations and physical observable identification remain open.

- `LeanPhy.Mathematics.LieCohomology`: explicit Lie-module action and
  representation law, degree-zero and degree-one CE maps, `d₁ d₀ = 0`, and
  witness-level cocycle, coboundary and cohomology relations.
- `LeanPhy.Mathematics.LieCohomology2`: explicit adapters to mathlib's native
  Lie structures and alternating two-cochains, the next differential,
  `d₂ d₁ = 0`, cocycle/boundary submodules, and the actual quotient module
  `H²`. Equality and vanishing of quotient classes have coboundary criteria.
  The differential's target is a trilinear-map space; a full all-degree
  alternating complex and general dimension computations are not supplied.
- `LeanPhy.Mathematics.CentralExtension`: trivial coefficient action,
  cocycle-derived Jacobi identity on `V × M`, central inclusion and exact
  base projection, explicit coboundary shears, and an equivalence criterion:
  two supplied cocycles represent the same `H²` class exactly when their
  product-carrier extensions are equivalent fixing the base and center.
  This is not a classification of arbitrary topological extensions.
- `LeanPhy.Examples.LieCohomologyResearch`: the abelian-plane area cocycle
  gives a nonzero Heisenberg class; a nonzero affine coboundary has zero class
  and a removable central term. The affine degree-one CE differential agrees
  with the quadratic ghost differential under explicit ghost maps.
  `leanphy_lie_research` exports sixteen proved claims and two open obligations;
  see [the worked guide](docs/capabilities.md). General ghost/CE chain equivalence,
  Lie-group integration, physical anomaly interpretation and cancellation
  remain outside these algebraic proofs.

- `LeanPhy.Mathematics.CohomologyReduction`: five linear identities certify
  representatives, class coordinates, primitives and completeness for the
  middle cohomology of a declared complex. They construct a quotient linear
  equivalence, an exactness test and a normal form. The matrix adapter checks
  the same identities; over general rings a split reduction may not exist.
- `LeanPhy.Mathematics.LieCohomologyReduction`: connects these reductions to
  the actual `H2` quotient and provides complete one-cochain coordinates and
  three-dimensional two-cochain coordinates. Transport requires checked
  differential compatibility and detection of vanishing in the next degree.
- `LeanPhy.Examples.HeisenbergCohomology`: identifies generated matrices with
  the declared three-dimensional rational Heisenberg CE differential and
  proves `H2 ≃ₗ[ℚ] (Fin 2 → ℚ)`, dimension two, the exactness criterion, a
  computed normal form and the complete pair of central-extension parameters.
- Historical `reduce_cohomology.py` (removed in v1.1): exact rational elimination produces Lean
  certificate candidates for finite input differential matrices. The output
  report remains `candidate_requires_lean_check` until the source is compiled.
  Regression checks include zero dimensions, acyclic and nonclosed cases,
  fractional entries, generated-source reproducibility and tamper rejection.
  Arbitrary input matrices still need a proof of identification with a physical
  model or Lie differential; the Heisenberg example supplies that proof.
  See [the computation guide](docs/capabilities.md).

- `LeanPhy.Mathematics.FiniteLieCohomology`: alternation of the degree-two
  CE differential for arbitrary supplied coefficient modules; checking its
  values on increasing basis triples detects vanishing on the entire carrier.
- Historical `lie_cohomology.py` (removed in v1.1): rational structure constants and optional finite
  representation matrices produce both CE tables and generated Lean proofs
  of Jacobi, the representation law, complete cochain coordinate equivalences,
  and both differential-identification theorems. An exact reduction is then
  transferred to the actual `H2`. Reports remain candidates until compiled.
  Input dimensions are not hard-coded; regression includes eleven models in
  Lie dimensions zero through four, zero/scalar/vector coefficients, nonzero
  next differentials and fractional entries. Three tampered generated models
  test CE-sign, Jacobi and representation rejection by Lean independently of
  Python's input checks. This is degree-two rational cohomology, not a symbolic
  parameter solver, an all-degree BRST complex or a physical anomaly claim.
- `LeanPhy.Examples.StructureConstantResearch`: generated affine models use
  the identical bracket but have `H2` dimensions zero and one under different
  coefficient actions. A solvable three-dimensional model with vector
  coefficients has four class parameters. A nonclosed cochain with zero
  parameter projection demonstrates the essential closedness premise.
  `leanphy_structure_research` exports ten proved claims and one open physical
  interpretation obligation. See [the guide](docs/capabilities.md).

- `LeanPhy.Mathematics.DiagonalCohomology`: over any field, diagonal complex
  weights `u,v` with `vᵢuᵢ=0` admit a complete reduction at every parameter
  value. Surviving coordinates satisfy `uᵢ=vᵢ=0`; the quotient equivalence,
  exactness criterion, dimension count and same-pattern equivalence are proved.
  Total inverses do not justify cancellation at zero; the reduction explicitly
  accounts for the representative term on each exceptional coordinate.
- `LeanPhy.Mathematics.SolvableLieFamily`: the bracket `[e₀,e₁]=a e₁`,
  `[e₀,e₂]=b e₂`, `[e₁,e₂]=0` and scalar character `t` are proved Lie/module
  structures over any field. Both CE bridges identify an actual `H2` quotient
  with surviving coordinates. Its dimension is `[t=a]+[t=b]+[t=a+b]`, with
  coinciding conditions counted separately. Closedness, exactness, safe
  primitives, uniform normal forms, class jumps, same-pattern equivalences
  and field-extension dimension invariance are verified for all parameters.
  No continuous bundle trivialization or Lie-algebra isomorphism is inferred.
- `LeanPhy.Examples.ParameterCohomologyResearch`: generic vanishing,
  dimension-two and dimension-one resonances, the dimension-three zero model,
  and failure of a generic primitive at resonance. `leanphy_parameter_research`
  exports twelve proved claims and one physical-interpretation obligation.
  The rational CE solver independently checks 125 parameter points; extra
  compiled specializations exercise rational, real, complex and finite fields.
  See [the parameter guide](docs/roadmap.md). The numeric generators remain
  rational; this handwritten API covers the declared family and diagonal
  complexes. The separate polynomial-matrix generator is described below.

- Historical `stratify_cohomology.py` (removed in v1.1): exact symbolic pivot search for finite
  polynomial matrix complexes over characteristic-zero fields. The generator
  retains explicit polynomial equations/nonzero assumptions, explores both
  pivot cases, and emits all five reduction proofs on every leaf plus a Lean
  proof covering the entire decision tree. Branch budgets fail explicitly;
  partial trees are never emitted as complete results. Reports remain unchecked
  candidates until Lean compilation. Branches need not be minimal or nonempty.
- `LeanPhy.Examples.Generated.SolvableStrata` and `DeterminantStrata`: reproducible
  eight- and five-branch certificates, respectively. Each exports an actual
  quotient equivalence, dimension theorem, exactness criterion and normal form.
  The determinant example includes both exceptional lines and their intersection.
- `LeanPhy.Examples.AutomatedParameterResearch`: the generated solvable matrices
  are identified with both actual CE differentials, including zero detection.
  The transported equivalence computes actual `H2`; the entire generated tree is
  proved equal to the independent resonance formula at all parameters. The CLI
  `leanphy_automatic_parameters` carries thirteen proved claims and one physical
  interpretation obligation. Eight generator tests include 209 valid rational
  specialization checks, nonlinear loci and a complex exceptional point, empty
  spaces, constrained complexes, reproducibility and three proof-tamper checks.
  See [automatic parameter cohomology](docs/roadmap.md).
  This matrix-level interface requires supplied matrices; the symbolic Lie
  frontend below now generates them. Positive-characteristic automatic
  stratification remains future work.

- Historical `symbolic_lie_cohomology.py` (removed in v1.1): accepts polynomial Lie structure
  constants and finite coefficient actions over characteristic-zero fields,
  derives both CE matrices using the numeric generator's coordinate/sign
  convention, and generates model laws, complete coordinates and both bridges.
  Declared polynomial equations and nonzero conditions become explicit fields
  of `Conditions p`; both Lie/module construction and H2 theorems require the
  corresponding proof. In default mode the generator diagnoses missing Jacobi
  and representation conditions. The optional discovery mode below now extracts
  an exact validity locus. General domain nonemptiness is not inferred.
- `LeanPhy.Examples.Generated.HeisenbergParameter`, `AffineVectorParameters` and
  `JacobiParameters`: complete actual H2 calculations for polynomial bracket
  degeneration, a constrained noncommuting vector representation, and a bracket
  constrained to `a*b=0`. Results include quotient equivalences, dimensions,
  exactness criteria and primitives on the declared parameter domains.
- `LeanPhy.Examples.SymbolicLieResearch`: the Heisenberg dimension jumps from
  two to three at zero bracket; the constrained affine-vector dimension is one
  at zero and zero otherwise; the Jacobi family has dimension three at its
  origin and one elsewhere on the constraint locus. Input-domain equivalences
  and excluded points are proved. `leanphy_symbolic_lie` reports fourteen
  checked claims and one physical-interpretation obligation. Eight generator
  tests cover 144 valid rational specializations, ten compiled models, a complex
  instance, a universal resonance-formula comparison and three model/CE tamper
  rejections. See [the symbolic Lie guide](docs/capabilities.md).
  This is finite degree-two algebraic cohomology, not a general deformation,
  anomaly, or physical phase-transition classification.

- Symbolic Lie `--discover-conditions`: enumerates independent Jacobi and
  representation residuals, removes zero/repeated equations and divides only
  by nonzero rational constants. Each equation retains basis provenance.
  The generated `conditions_iff` proves equivalence with full laws on arbitrary
  vectors; `conditions_iff_model` proves equivalence with actual Lie algebra
  and module existence with the supplied operations, relative to separately
  preserved user restrictions. Constant predicates are explicitly typed in K.
- `--conditions-only` produces validity proofs without cohomology or a dimension
  tree, including a fixed invalid bracket whose discovered equation is `1=0`.
  `DiscoveredLieDomain`, `DiscoveredVectorDomain` and `ImpossibleLieDomain` are
  reproducibly generated checked examples. The combined model discovers
  `a*b=0` and `a*t=0`; it retains both the plane `a=0` and the line `b=t=0`.
- `LeanPhy.Examples.ModelDomainResearch`: exact model-existence loci, valid and
  excluded parameter points, the complete H2 formula on the discovered domain,
  and nonexistence of a model with a supplied invalid bracket. The CLI
  `leanphy_model_domains` reports twelve checked claims and one interpretation
  obligation. Seven discovery tests compare 150 valid/invalid parameter points
  (34 legal), compile eight domain examples including constant constraints, and
  reject missing-law and unnecessarily restrictive equation forgeries.
  See [model-domain discovery](docs/capabilities.md). No minimal ideal,
  irreducible decomposition, general nonemptiness, topology or physical
  interpretation is inferred.

- `LeanPhy.Mathematics.OperatorConvergence`: uniform operator-norm and strong
  operator convergence certificates.  A radius tending to zero yields
  vector-level and bounded-observable limits, while the strong form records
  pointwise convergence directly.  These interfaces cover Galerkin, lattice,
  finite-volume and regulator approximations; they do not infer compactness,
  spectral convergence or a continuum limit.

- `LeanPhy.Mathematics.EnergyDissipation`: integrated energy and residual
  budgets for dissipative PDE, finite-volume schemes, Langevin dynamics and
  turbulence closures.  Nonnegativity and interval integrability are explicit
  fields, and residuals remain part of the final error bound.  The certificate
  does not construct a PDE solution or prove well-posedness.

- `LeanPhy.Mathematics.UnboundedOperator`: dense-domain operators, symmetry on
  the declared domain and two-sided domain-valued resolvents.  The inverse is
  stored as actual domain data, so uniqueness is kernel-checked.  The
  `LinearPMap` bridge exposes mathlib's graph and formal-adjoint API without
  erasing the declared domain.  Closedness, closability, self-adjointness,
  graph-norm relative bounds, and bounded domain-preserving composition are
  available as explicit certificates.  Essential self-adjointness, general
  self-adjoint extensions, Stone's theorem, spectral measures, and resolvent
  existence remain separate obligations.

- `LeanPhy.Mathematics.Renormalization`: regulator-wise bare/counterterm/
  renormalized relations, supplied renormalized limits, limit uniqueness and
  scheme-independence lemmas.  The module accepts explicit limits and vanishing
  scheme differences; it does not construct a path measure, prove BPHZ or
  establish a non-perturbative QFT limit.

- `LeanPhy.HighEnergy.EffectiveTheory`: finite EFT expansions expose an explicit
  amplitude/retained-amplitude decomposition, a power-counting tail bound,
  and a coefficient-matching `ErrorCertificate` for bounded finite observables.
  The module does not construct a UV completion, a continuum limit, or a
  regulator-independent matching theorem.

- `LeanPhy.Mathematics.Contraction`: `ContractionCertificate` wraps the Banach
  contraction theorem for nonempty complete metric spaces.  The kernel checks
  the unique fixed point, convergence of Picard iterates, a priori and
  a posteriori error bounds, and the `C / (1 - K)` stability bound under a
  uniformly perturbed map.  `InvariantContractionCertificate` handles a
  complete forward-invariant subset.  Contractivity and model adequacy remain
  explicit hypotheses; this is an analytic fixed-point bridge, not a theorem
  that a physical RG or turbulence map is contractive.

- `LeanPhy.Mathematics.InfiniteSpectrum`: in addition to checked two-sided
  resolvents and the resolvent identity, `resolvent_perturbation_bound` turns
  explicit inverse and operator-difference norm envelopes into the quantitative
  estimate `‖R_A - R_B‖ ≤ r_A * δ * r_B`.  `resolvent_of_neumann` additionally
  turns the explicit condition `‖A‖ < 1` into a checked inverse for `1 - A`.
  Both results are conditional on every displayed bound; they do not infer a
  numerical spectrum from sampled data or extend to unbounded operators.

- `LeanPhy.Mathematics.SpectralCalculus`: bounded complex operators now have a
  kernel-checked polynomial spectral-mapping theorem, the Gelfand spectral-radius
  limit, and a polynomial-on-eigenvector action rule.  A finite-dimensional
  symmetric linear operator can additionally be packaged as a certificate exposing
  a real eigenvalue list, orthonormal eigenbasis, characteristic-polynomial and
  determinant identities, with optional explicit interval bounds.  This bridge is
  intentionally limited to bounded operators and polynomial functions: it does not
  implement a general Borel functional calculus, spectral measures, unbounded
  self-adjoint spectral theory, or infer eigenvalue bounds from numerical samples.

- `LeanPhy.Mathematics.SpectralGap`: an explicit invariant projection and
  one-step residual contraction yield a geometric bound for every discrete
  iterate, convergence to the projected state, and convergence after any
  bounded linear observable.  This is a reusable certificate for mixing and
  dissipative finite models; it does not construct the projection from sampled
  eigenvalues, prove semigroup generation, or establish a thermodynamic-limit
  gap.

- `LeanPhy.Mathematics.Hilbert.FlowNormCertificate`: an explicit time-indexed
  operator-norm envelope for a bounded semigroup yields checked state-norm and
  composition bounds.  This is a stability contract; continuity, generators,
  positivity and unbounded domains remain separate hypotheses.

- `LeanPhy.Mathematics.ContinuousEvolution`: `IntervalIntegralCertificate`
  records Bochner interval integrability and an integral equality, with checked
  add/scalar/map constructors. `VariationOfConstantsCertificate` records the
  supplied Duhamel endpoint identity and forcing integrability; together with a
  `FlowNormCertificate` and `SourceNormCertificate`, `norm_error_le` derives
  the explicit convolution bound. The module never constructs an ODE/PDE
  solution or hides generator, domain, or continuity assumptions.

- `LeanPhy.Mathematics.Model`: `PhysicalModel` binds admissible states,
  proof-preserving evolution and typed observables. `ModelMap` requires both
  a dynamics intertwining proof and an observable pullback proof; composition,
  independent products, invariant pullback and finite-time readout transport
  are checked once in the shared layer. `QuantumInfo.Model` and `StatMech.Model`
  connect finite CPTP/Kraus channels and stochastic kernels to this interface.
  A model map is an exact simulation under its hypotheses, not an automatic
  assertion of physical equivalence or convergence of a truncation. Product
  models here are Cartesian independent systems, not general quantum tensor
  products with entangled states.

- `LeanPhy.Mathematics.ApproximateModel`: `ApproximateModelMap` records a
  state-map Lipschitz modulus, target-step stability, one-step residuals and
  observable residual/Lipschitz certificates. `stateRadius`, `iterate_error`
  and `evaluate_error` propagate these budgets over every finite horizon.
  `ApproximateModelMap.compose` composes two adapters while retaining the
  intermediate state error; `toExact` requires zero radii plus an explicit
  separation proof for the pseudometric spaces before producing an exact
  `ModelMap`. This is a finite error contract for truncations and
  discretisations, not a convergence or continuum-equivalence theorem.

- `LeanPhy.Mathematics.ParametricModel`: `ParametricModel` represents families
  indexed by couplings, temperatures, mesh sizes or truncation labels while
  keeping state and observable representations typed. `ParametricModelMap` and
  `ParametricApproximateMap` lift finite-time transport and explicit error
  propagation pointwise in the parameter; `UniformBudget` gives a common
  finite-horizon bound only after one is supplied for every parameter and
  initial state. QuantumInfo and StatMech expose parameter-family constructors.
  This layer does not infer parameter continuity, limits or physical calibration.

- The negative elaboration suite is executed by
  `scripts/run_negative_tests.py`: it runs the 291 independent fixtures in
  parallel, accepts only a source-located Lean elaboration error, rejects
  import/API/compiler failures, and cleans up child compiler groups on
  interruption. This keeps a broken regression fixture from being reported as
  a proof-safety success.

- `LeanPhy.Dimensions`: `Quantity` now supports dimension-changing division,
  explicit inverse and natural powers, together with coefficient scalar action
  and reusable frequency/momentum/energy/action/charge aliases.  The inverse is
  intentionally a function with result type `Quantity (-d) α`, so Lean's
  same-type `Inv` shortcut cannot erase a physical dimension.

- `LeanPhy.Workflow`: `TheoryPackage` keeps assumptions, heterogeneous
  proof-bearing claims and explicit scope boundaries in one reusable research
  ledger. `TheoryPackage.ofModel`, `addTheorem`,
  `addTheoremWithAssumptions`, proof-producing `addDerivedTheorem`/
  `addDerivedTheorem2` and `append` support replacing
  a model or combining independent packages without changing the reporting
  interface. Eight compiled adapters cover quantum, finite PDE/Euclidean,
  classical, gauge, condensed-matter, relativity and statistical-mechanics
  layers; `lake exe leanphy_check` reports their conditional status and
  `--json` emits a machine-readable projection with theorem provenance and
  unresolved-assumption-link, claim-dependency and open-obligation diagnostics. A
  claim cannot be inserted without its Lean proof field; optional assumption
  names are rendered as audit cross-references and do not replace hypotheses.
  The report
  executable only renders compiled metadata. The copyable
  `LeanPhy.Examples.ResearchPackageTemplate` demonstrates the same interface
  for a new domain.
  `addTheoremUnderAssumptionRegistered` combines typed-assumption registration with
  proof consumption; `addObligationWitness` stores the original target, and
  `resolveObligation` requires that target's proof through a package-indexed
  `ObligationRef`, removes only that entry, and retains its proof in history.
  Related evidence cannot close a text-only task; see
  [the migration guide](docs/research-core.md).

- `LeanPhy.Mathematics.FiniteProcess`: `StateMap.compose_assoc` and
  `Process.iterate_add` make proof-preserving finite dynamics compositional.
  Quantum channels, Markov kernels, positive lattice steps and finite unitaries
  share this interface, while `ObservableTransport` composes expectation and
  Heisenberg pullbacks.

- `LeanPhy.Workflow.AssumptionWitness`: when a model assumption is available
  as an explicit proposition, `addAssumptionWitness` records its metadata and
  `addTheoremUnderAssumption`/`addTheoremUnderAssumptions2` pass the witness
  proof into the derived theorem.  This closes the proof-level link between a
  named assumption and a claim; metadata-only assumptions remain available for
  genuinely external physical or analytic premises.

- `Mathematics.ExternalCertificate`: external CAS or numerical output is kept
  as a provenance-bearing `CertificateEnvelope`. A `CertificateChecker` must
  prove its `sound` theorem before `VerifiedCertificate.proof` can be inserted
  into a `CheckedClaim`; a returned runtime Boolean is never evidence. The
  matrix equality adapter is data-only and receives the checker proof
  separately. `ResearchProject` additionally audits `package::claim` links and
  duplicate package names. `LeanPhy.Minimal`, `Entry.Quantum`,
  `Entry.FieldTheory`, `Entry.Condensed`, `Entry.Gauge`, `Entry.HighEnergy`,
  `Entry.Classical`, `Entry.Relativity`, `Entry.StatMech`, `Entry.FinitePDE`,
  `Entry.Analysis` and `Entry.Research` provide selective import profiles.
  `encodeEnvelope` and
  `decodeEnvelope` add a typed JSON data boundary; decoding never creates a
  `VerifiedCertificate` without a separate checker proof.

- `ResearchProject.addDerivedTheorem` and `addDerivedTheorem2`: a target
  package can consume one or two source-package `CheckedClaim.proof` terms.
  Qualified dependencies are generated automatically, and a missing source
  package/claim makes the assembled project invalid rather than silently
  accepting metadata-only provenance.

- `LeanPhy.Examples.ClosedLoop`: `lake exe leanphy_prototype` compiles and
  reports one finite oscillator identity, one shared evolution/energy bound,
  one two-node finite-difference heat step with maximum-principle and mass
  certificates, one positive finite path measure and one reflected weighted
  Gram proof.  The
  executable is a workflow check; the actual obligations are theorem fields
  in `VerifiedPrototype` and are checked by the kernel during compilation.

- `Mathematics.Approximation`: finite truncations, finite-volume or lattice
  replacements, and numerical equation residuals are represented by explicit
  nonnegative distance bounds.  The kernel checks triangle-inequality
  composition, additive error budgets in seminormed groups, and transport
  through a user-supplied Lipschitz certificate; no convergence, continuum
  limit or stability estimate is invented.

- `Mathematics.ApproximationBridge`: `CrossSpaceApproximation` makes the
  reconstruction map between two different Lean types explicit, then reuses
  the ordinary error-certificate lemmas for observables and multistage
  discretisations.  `ReconstructionBridge` supplies a zero-radius certificate
  only after an explicit encode/decode round trip has been proved.  This is a
  reusable boundary for truncated Fock spaces, lattice-to-continuum maps,
  finite-band interpolation and thermodynamic post-processing; it does not
  identify two representations or infer a limit theorem implicitly.

- `Mathematics.ApproximationAdapters`: quantum state/operator, field-theory
  mode, gauge-lattice, condensed band/lattice, statistical finite-volume and
  classical discretisation names are aliases of the same certificate API, so
  downstream proofs can move between subfields without changing the trusted
  semantics.

- `Mathematics.CertifiedResidual`: approximate matrix eigenpairs and one-step
  equation defects are explicit `ErrorCertificate` bounds, with vocabulary
  aliases for QM, BdG, transfer matrices, finite modes and ODE discretisation.
  The interface does not infer spectral error or convergence.

- `Mathematics.FiniteDivergence`: an arbitrary finite oriented graph has a
  kernel-checked incoming-minus-outgoing divergence whose total cancels on
  internal edges.  `ConservationCertificate` records a pointwise continuity
  equation and derives the zero-total source constraint; gauge-lattice,
  condensed-matter, finite-volume, statistical and measurement-flow aliases
  reuse this theorem.  Boundary fluxes and continuum divergence results remain
  explicit inputs.

- `StatMech.FiniteCurrent`: a finite Markov kernel and input distribution
  induce a current on the complete directed state graph.  Its divergence is
  definitionally checked as `K.step p - p`, so the Markov step receives a
  `ConservationCertificate` and a zero-total source theorem from the common
  incidence layer.  Continuous-time processes, stationary limits and mixing
  estimates remain outside this finite bridge.

- `Mathematics.ConservationResidual`: local continuity equations may carry
  explicit nonnegative residual radii.  The kernel derives
  `|∑ source| ≤ ∑ radius` and the cardinality-scaled uniform-radius bound,
  providing a shared error budget for finite-volume, lattice, truncated-field,
  Markov and measurement calculations without inferring convergence or
  stability.

- `Mathematics.FiniteRepresentation`: finite monoid/group actions are stored
  as matrix homomorphisms.  Characters are invariant under conjugation,
  representations pull back along homomorphisms, intertwiners compose, and a
  unitary representation proves inverse equals adjoint.  These are shared
  algebraic contracts for gauge, particle, point-group and quantum-symmetry
  adapters; irreducibility and Haar/Schur analysis are not inferred.

- `Mathematics.FiniteGroupAverage`: finite group sums are invariant under left
  and right reindexing.  For any finite matrix representation, the conjugation
  twirl is invariant under the represented group and commutes with it.  Quantum
  twirling, finite gauge averages and point-group orbit sums therefore share
  one proof, while Haar measure and compact-group analysis remain external.

- `Workflow.ExternalObligationWitness`: registration stores its proposition
  in the package. `resolveObligationWitness` reads that original target from
  an `ObligationRef`, requires its proof, and retains it even if the derived
  claim is weaker. Text-only obligations remain open when evidence is added.

- `Mathematics.FiniteChainComplex`: finite boundary tables carry an explicit
  boundary-of-boundary cancellation certificate.  The kernel derives the
  boundary and coboundary square-zero laws, a finite discrete Stokes pairing,
  and vanishing of an exact cochain on an explicitly supplied cycle.  Lattice
  gauge, Berry meshes, finite elements and network models use the same
  contract; homology, Chern quantisation, integration and continuum limits
  remain outside the finite theorem.

- `Mathematics.FiniteChainAdapters`: the incidence boundary of a finite
  directed graph is connected by an equality theorem to the existing finite
  divergence contract.  A conservation certificate can therefore be consumed
  as a chain-boundary equation, with domain aliases for gauge, hopping,
  finite-volume and network calculations.

- `StatMech.FiniteDetailedBalance`: a pairwise detailed-balance certificate for
  a finite kernel proves stationarity of the reference finite probability and
  symmetry of the kernel pullback in the weighted expectation pairing.  The
  module does not infer irreducibility, mixing, spectral gaps or any
  continuous-time limit.

- `StatMech.FiniteDirichlet`: defines the finite Dirichlet energy associated
  with a probability and a row-normalized nonnegative kernel.  The kernel
  proves symmetry in the observables, nonnegative quadratic energy, vanishing
  on constant observables and bilinearity in each slot.  This is the shared
  finite algebraic layer for reversible Markov, lattice hopping, graph,
  finite-element and measurement post-processing models.  Reversibility,
  spectral gaps, Poincare inequalities, mixing rates and continuum limits are
  not inferred.

- `StatMech.FiniteDirichletLaplacian`: defines the finite discrete Laplacian
  `I - K` and proves, under detailed balance, that the edge Dirichlet form is
  exactly the probability-weighted pairing with that Laplacian.  This is an
  algebraic bridge between reversible Markov dynamics, graph/finite-element
  stiffness forms and lattice hopping.  Spectral-gap and continuum estimates
  remain outside the theorem.
- `Mathematics.FinitePathIntegral`: finite complex weighted path sums require
  an explicit nonzero partition certificate.  The kernel checks normalized
  expectations, finite reindexing and exact push-forward coarse graining;
  continuum measures, oscillatory limits, reflection positivity and RG
  universality are not claimed.  `fromAction` supplies complex action weights
  and proves normalized expectation invariance under a constant action shift;
  `fromRealAction` obtains a strictly positive finite Euclidean partition real
  part on a nonempty space, and `IsFixedPoint` records exact same-label finite
  blocking invariance without claiming a continuum critical point. A
  `ScalingCertificate` additionally proves finite insertion/expectation
  scaling for an explicit factor, with no hidden critical-exponent claim.
  For a real finite action, `fromRealAction_partition_lower_bound` turns any
  chosen configuration into the explicit positive bound
  `exp (-S i₀) ≤ ‖Z‖`, which can feed a normalized-error certificate; this
  construction does not extend to cancelling complex weights.

- `Mathematics.FiniteReflection`: a finite reflection certificate supplies a
  permutation of labels and an explicit Gram feature factorisation.  The kernel
  expands the reflected quadratic form into a finite sum of squares and proves
  its non-negativity.  This is a finite positivity certificate for lattice or
  truncated models; it does not prove the continuum
  Osterwalder--Schrader axiom, Hilbert-space reconstruction, existence of a
  continuous measure, or Euclidean QFT existence.  The kernel double-sum
  presentation is now proved equal to the supplied Gram square-sum
  factorisation, and the reflection involution is an explicit certificate
  field; this finite bridge still does not reconstruct a continuum theory.

- `Mathematics.FinitePathReflection`: a real nonnegative finite weight table
  constructs a complex finite path integral with a positive real partition
  part, while a weighted feature table proves the usual kernel double sum is a
  nonnegative weighted sum of squares.  `FiniteWeightedReflectionCertificate`
  combines these contracts and retains the reflection involution.  This is a
  reusable lattice/truncated-Euclidean adapter; positivity of a continuum
  measure and the Osterwalder--Schrader axioms remain external obligations.

- `Mathematics.FiniteEnergy`: `FiniteEnergyStep` requires a nonnegative energy,
  a nonnegative one-step amplification factor and an explicit one-step energy
  inequality.  The kernel propagates it to a finite-time factor-power bound and
  derives non-increase when the factor is at most one.  An explicit one-step
  equality constructs the factor-one conservation form.  Physics aliases make
  the same contract available to wave/PDE, Maxwell, lattice, BdG, dissipative
  and finite-mode adapters; no CFL condition, continuum energy identity,
  well-posedness result or mesh limit is inferred.

- `Mathematics.FiniteEnergy` also defines `FiniteEvolutionEnergyStep`, which
  binds one state step to both a discrete-Grönwall trajectory certificate and
  an energy amplification certificate.  The coupled theorems expose state
  error and exact-trajectory energy bounds from one shared step map; they do
  not infer a PDE energy estimate, CFL condition or continuum stability
  theorem.
- `Mathematics.FiniteElliptic`: finite incidence tables provide a `BᵀB`
  weak Laplacian.  Nonnegative energy, summation by parts, constant zero modes
  and exact Poisson/matrix-PDE residual certificates are checked; regularity,
  boundary-value theory, mesh convergence and continuum estimates remain
  external obligations.  An explicit `CoercivityCertificate` is sufficient
  for the finite uniqueness theorem, and `FiniteBoundaryData` records
  Dirichlet values without treating them as hidden assumptions.  A boundary
  coercivity certificate proves uniqueness on the homogeneous Dirichlet
  perturbation space.  `FiniteBoundaryResidualCertificate` records pointwise
  boundary error, while `FiniteEllipticApproximationCertificate` binds it to
  the equation residual, supports explicit budget combination and recovers an
  exact solution only when both radii are zero.  `FiniteEllipticCertificate`
  remains the exact-boundary form, while `FinitePDEResidualStability` turns
  that residual into a solution error only when the user supplies a
  residual-to-solution modulus; no mesh convergence or continuum stability is
  inferred.  A
  `FinitePDELeftInverseCertificate` can produce that stability object from an
  explicit finite left inverse, homogeneous-Dirichlet left-inverse identity
  and Lipschitz bound; the kernel does not infer an inverse or condition
  number.  `FiniteEllipticResidualStability` is the boundary-aware extension:
  it takes separate equation and boundary moduli plus an explicit total bound,
  and converts the joint certificate into one solution-error budget.  The
  boundary budget is a finite sum over marked nodes and is proved nonnegative;
  no continuous trace theorem or mesh estimate is hidden in it.

- `AdditiveLeftInverseCertificate`: a domain-neutral additive operator
  contract records a left inverse and Lipschitz modulus, then turns an
  operator `ErrorCertificate` into a checked `FiniteApproximation`.  Named
  adapters expose the same contract for quantum operators, field modes,
  lattice/gauge discretisations, condensed bands, transfer matrices and
  classical dynamics; no condition number or convergence theorem is inferred.

- `Mathematics.FinitePathApproximation`: numerical or truncated finite path
  integrals carry insertion and partition `ErrorCertificate`s, positive lower
  bounds for both exact and approximate denominators, and an upper bound for
  the approximate insertion.  The kernel derives an explicit normalized
  expectation error bound.  Pointwise weight certificates are aggregated into
  partition and insertion budgets before normalization.  The separate
  `ObservableApproximationCertificate` handles pointwise observable error, and
  `FiniteRGStep.coarse_approximation_certificate` assembles a full coarse
  weight certificate from those pointwise bounds.  No denominator stability
  beyond the supplied lower bounds, sampling concentration or continuum limit
  is inferred.

- `FiniteRGStep.coarsenMany`: a finite list of blocking maps is reduced to one
  auditable push-forward.  Partition sums, pulled-back insertions, normalized
  expectations and explicit finite scaling certificates compose over the list;
  this is not a continuum RG semigroup or a critical-exponent theorem.
- `FiniteRGStep.coarsen_weight_eq_pushforward_coarseWeight` and
  `coarsen_weight_assoc` check the intermediate-weight and coarse-map
  composition laws pointwise.  `ScalingCertificate.compose` combines two
  explicit finite operator-scaling hypotheses with factor `lambda * mu`;
  the intermediate scaling equation remains a required input.

- `Mathematics.FiniteParabolic`: `FinitePositiveStep` packages a nonnegative
  row-stochastic matrix and proves constant preservation, positivity and a
  finite discrete maximum principle for one step and all finite iterates.
  `MassConservationCertificate` separately supplies column sums to prove
  preservation of the unweighted total; row sums alone are not treated as a
  conservation law.

- `FinitePathIntegral.multiCorrelator`: a list of observables gives an
  explicit finite n-point insertion.  The kernel checks the empty insertion,
  permutation symmetry, product concatenation and exact coarse-map pullback;
  continuum time ordering and distributional products remain outside scope.

- `FinitePositiveStep.UniformError` is a componentwise absolute-error ledger
  for finite fields.  A nonnegative row-stochastic step is nonexpansive for
  this ledger, and the ledger composes by an explicit triangle budget.

- `FinitePositiveStep.TrajectoryCertificate` requires an initial error, an
  exact finite recurrence and a residual certificate at every step.  Its
  `bound` theorem produces the componentwise propagated radius at every finite
  time; no residual may be omitted during elaboration.

- `FiniteDrivenParabolic` extends the positive-step ledger to an explicitly
  forced update `u_(n+1) = K u_n + f_n`.  The kernel proves the nonhomogeneous
  maximum-value budget, cancellation of a common source term in the error
  difference, and the finite-time `DrivenTrajectoryCertificate` bound.  The
  certificate must contain the exact source recurrence and every approximate
  step residual; CFL conditions, continuous maximum principles and PDE
  stability are not inferred.

- `FiniteDrivenParabolic` also provides `SourceDrivenTrajectoryCertificate`:
  an independently approximated forcing field has its own pointwise error
  radius, which is added to the state and local-step budgets at every finite
  time.  Omitting the source-error field prevents construction of the
  certificate; this still says nothing about continuous forcing convergence.

- `FiniteSchwingerDyson` defines finite source polynomials, moments and an
  involutive variation with an explicit Jacobian.  A weight-balance field is
  required before the kernel derives the finite Schwinger--Dyson insertion and
  normalized expectation identity.  This does not provide a continuous
  functional derivative, integration-by-parts theorem or nonperturbative path
  integral.

- `FiniteRGDiagnostics` packages a pointwise finite RG fixed-point defect into
  partition-function and normalized-observable error certificates.  Exact
  fixed points have zero radius, while approximate conclusions require user
  supplied denominator lower bounds and insertion upper bounds.  Continuum
  fixed points, critical exponents, universality and RG convergence remain
  outside the verified layer.

- `FiniteRGDiagnostics.FixedPointDefect.compose` combines two consecutive
  finite blocking defects only when the second step's fine weights are
  explicitly identified with the first step's coarse weights.  The resulting
  pointwise and partition radii are the sum of both ledgers, so an intermediate
  numerical mismatch cannot be silently dropped.

- `FinitePathIntegral.WeightSymmetry` records pointwise invariance of finite
  weights under a permutation.  It proves insertion reindexing, expectation
  invariance and a zero weighted insertion difference, giving a finite Ward
  identity while leaving continuum changes of variables and anomalies
  explicit.

- `NormalizedExpectationCertificate`: a single-step normalized expectation
  error becomes a composable object.  `compose` adds nonnegative radii through
  the triangle inequality, and the RG coarse-weight constructor exposes its
  result through `coarse_expectation_certificate`; each denominator bound and
  insertion bound remains an explicit input.

- `ExpectationComparisonCertificate`: source and target finite configuration
  spaces and observables may have different types.  The kernel composes two
  comparisons through their shared intermediate observable, adding the two
  radii.  This is the finite error signal needed for a multi-level blocking
  chain; it does not certify that a continuum observable has been matched.

- `FiniteRGStep.coarsen_expectation_preserved`: a single blocking map may
  change the finite label type.  Partition and insertion preservation still
  yield an exact normalized-expectation equality after pulling the final
  observable back through the full map; no continuum RG law is inferred.

- `StatMech.ConductanceModel`: positive site weights and symmetric nonnegative
  conductances construct a normalized finite kernel and its equilibrium
  probability.  The kernel proves detailed balance and stationarity by
  cancellation, while Metropolis acceptance, irreducibility, mixing and
  thermodynamic/continuum limits remain explicit model obligations.  Hopping,
  gauge-lattice and reversible-network aliases reuse the same contract.
  `ConductanceModel.fromWeights` additionally constructs a rank-one symmetric
  conductance directly from any positive finite Gibbs weight family, providing
  a checked Gibbs-to-Markov bridge without hiding normalization assumptions.

- `Mathematics.FiniteResponse`: the finite weighted commutator response
  `Tr (rho [A,B])` expands into ordered correlators, is antisymmetric under
  probe exchange, is linear in its probes, vanishes under an explicit
  commutation certificate, and has the cyclic Kubo identity
  `Tr (rho [A,B]) = Tr ([rho,A] B)`.  Time ordering, response kernels,
  positivity and thermodynamic limits are not inferred.  Quantum-information,
  condensed-matter, statistical, high-energy and classical aliases share the
  same algebra.

- `Mathematics.FiniteChainComplex` additionally exposes `IsCycle2` and a
  closed-surface pairing theorem: an exact two-cochain has zero pairing on a
  supplied closed finite surface, so adding it leaves a discrete flux/Chern
  pairing unchanged.  Gauge, Berry/Chern, finite-element and discrete-fluid
  aliases reuse this identity; homology quotients and continuum Chern
  quantization remain outside the theorem.

- The cycle/cocycle portion of `Mathematics.FiniteChainComplex` is
  quotient-free by design: it defines finite cycles, boundaries, cocycles and
  exact cochains; proves boundary-is-cycle and exact-is-cocycle; and checks the
  degree-one Stokes identity.  Consequently a supplied cocycle annihilates
  every supplied boundary and a supplied exact cochain annihilates every
  supplied cycle.  Homology quotients, ranks and Chern quantisation are not
  inferred from these predicates.

- `Mathematics.DiscretePlaquette`: the oriented four-edge flux is invariant
  under an exact vertex shift and reverses sign only with a supplied edge
  antisymmetry law, so gauge, Berry, fluid and lattice adapters share one
  checked boundary identity.

- `Mathematics.Hilbert`: complete inner-product spaces carry bounded
  self-adjoint and two-sided unitary operators with kernel-checked expectation,
  inner-product and norm laws.  `matrixOperator` exposes finite matrices as
  bounded operators.  `Quantum.HilbertBridge` additionally checks matrix
  multiplication/composition and conjugate-transpose/adjoint equality, and
  transports finite unitary and Hermitian certificates to `EuclideanSpace`;
  the adapter is polymorphic over `RCLike`, so real classical/relativistic
  matrices and complex quantum matrices use the same checked construction;
  unbounded domains, spectral measures and time evolution remain explicit
  analysis obligations.

- `Mathematics.LinearFlow`: `FiniteMatrixFlow` checks zero-time, semigroup
  composition, vector propagation and inverse matrix-exponential evolution
  over real or complex `RCLike` scalars.  `Quantum.HamiltonianFlow` instantiates
  this interface; the module does not infer ODE differentiability, positivity,
  stability or a continuum limit.

- `Mathematics.FlowInvariant`: a commuting observable is fixed by a finite
  matrix-exponential conjugation.  The theorem is shared by quantum,
  classical, BdG, transfer-matrix and finite-mode field-theory vocabulary
  aliases; it requires an explicit commutation certificate and checked inverse
  law, and does not infer stability, positivity or continuous-time dynamics.

- `FieldTheory.FermionicWick`: the finite four-point fermionic contraction is
  the sign-correct Pfaffian, with adjacent-slot antisymmetry and zero-diagonal
  repeated-slot exclusion.  It is a finite CAR/BdG/QFT algebra kernel; it does
  not assert Grassmann integration, time ordering or continuum Fock theory.

- `Mathematics.DiscreteHigherCochain`: the alternating finite `d₁` and `d₂`
  operators satisfy `d₂ d₁ = 0`, and finite face sums are congruent under
  pointwise equality.  This is a reusable discrete Bianchi layer for gauge,
  Berry, fluid and finite-element models; topology and integration are not
  inferred.

- `Mathematics.PeriodicPlaquette`: two commuting finite translations define a
  periodic plaquette curl.  The kernel checks exact vertex-gauge invariance,
  total-curl telescoping and zero curl for an exact potential; transition
  patches and Chern quantisation remain explicit higher-level inputs.

- `FieldTheory.MultiWick`: a finite covariance-kernel recursion over typed
  bosonic field slots.  The four-slot result expands all three pairings.  It
  does not assert time ordering, distributional products, fermionic signs,
  renormalisation or a continuum limit.

- `FieldTheory.MultiCAR`: finite fermionic mode families carry explicit CAR
  relations and the kernel proves the individual and total number-operator
  ladder identities.  Fock completion, domains and continuum distributions
  are not inferred.

- `Mathematics.Winding`: an integer lift on a finite permuted cycle can carry a
  checked winding/flux/circulation value.  Integer gauge coboundaries preserve
  that value.  This is a finite certificate for Berry, lattice-gauge and fluid
  adapters; Chern integrals and continuum homotopy classes remain outside it.

- `Mathematics.Holonomy`: endpoint-indexed finite paths compose associatively;
  group-valued transport composes, open paths transform by endpoint
  conjugation, closed holonomies transform by base-point conjugation, and
  Abelian or class-function observables are gauge invariant.  The legacy
  four-link Wilson plaquette is connected to this generic path API.  This is a
  finite algebraic bridge for lattice Wilson loops, discrete Berry phases and
  graph connections; path-ordered exponentials, continuum limits and Chern or
  winding integrals remain explicit future layers.

- `Condensed.Berry.discreteBerryHolonomy`: finite-mesh Berry link products
  reuse the same Abelian closed-path theorem; smooth eigenvector patches and
  Chern-number integration remain explicit analytic/topological obligations.

- `Mathematics.AdditivePath`: additive link transport, endpoint gauge
  telescoping and the additive plaquette-flux bridge are checked for every
  closed finite path.  This is the common finite layer for lattice flux,
  discrete one-forms and angle-valued phases.

- `Mathematics.DiscreteCochain`: arbitrary vertex/edge/triangle labels carry
  `d0` and oriented `d1`; the kernel proves `d1(d0 φ)=0`, exact fields are
  closed, and curvature is unchanged by an exact gauge shift.  Maxwell's
  finite-difference adapter and the discrete Berry-curvature adapter reuse
  these theorems.

- `DiscreteCochain.cycleSum`: a finite permutation-indexed cycle sum cancels
  every additive gauge coboundary.  This is only a finite algebraic flux
  certificate; winding numbers, Chern integers and continuum integration still
  require separate topological hypotheses.

- `Classical.discreteVorticity`: lattice/network velocity one-forms reuse the
  exact-shift invariance of the cochain curvature.  This connects the fluid
  adapter to the same kernel theorem used by discrete Maxwell and Berry layers;
  Navier--Stokes dynamics and continuum limits remain outside the module.

- `Quantum.SpectralGap` and `Quantum.ParametricSpectralGap`: explicit
  two-sided finite resolvents are equivalent to nonzero determinants and
  exclusion from the finite spectrum; quadratic operator relations yield
  certified inverse formulas and real interval gaps.  Finite unitary
  similarity preserves the gap, and one radius can be checked uniformly over
  a finite momentum, flavor, boundary or volume family.  The real BdG and
  real Bloch modules instantiate this family interface.  Continuity,
  compactness and thermodynamic-limit gaps remain explicit analysis inputs.

- `Quantum.FiniteDensity`: the common `IsFiniteDensity` predicate and
  `FiniteDensity` bundle identify `IsDensity` and `IsNamedDensity` as the same
  finite matrix invariant; finite-unitary conjugation and named Kraus channels
  preserve it for any finite label type.

- `Quantum.HamiltonianFlow`: a finite Hermitian Hamiltonian produces the
  matrix exponential `exp(i t H)` as a unitary; time addition, trace and
  positive-semidefinite preservation are checked.  If `[H,O]=0`, the finite
  Heisenberg conjugation fixes `O`.  This is a finite matrix theorem; it does
  not assert Stone's theorem, unbounded-operator dynamics or a continuum
  limit.

- `QuantumInfo.Measurement`: one-Kraus-per-outcome and finite general
  multi-Kraus instruments, branch positivity, Born traces, total normalization
  and normalized conditional states;
- `Mathematics.LieRepresentation`: a reusable linear Lie-algebra/
  representation interface whose explicit compatibility field transports the
  Jacobi identity to matrices or operators;
- `Mathematics.LieAdapters`: the coefficient-space `su(2)` bracket and the
  explicit spin-one matrix family are packaged as a concrete representation;
  a table-level Jacobi theorem is shared by the Lorentz and colour families;
  the explicit Lorentz `so(3,1)` family is also packaged with its structure
  constants;
- `QuantumInfo.Channel`: every finite Kraus family has a kernel-checked
  ancillary extension `I ⊗ K` that preserves positive semidefiniteness, giving
  the finite complete-positivity property used by CPTP calculations;
- `QuantumInfo.KrausBundle`: `KrausChannel` stores the completeness relation,
  derives trace preservation and finite complete positivity, and composes with
  a product Kraus family whose completeness is checked by the kernel.
- `QuantumInfo.Heisenberg`: the finite dual action
  `A ↦ sum_i K_i† A K_i` satisfies the trace-pairing identity, is unital under
  Kraus completeness, and reverses product-channel composition.
- `QuantumInfo.POVMDistribution`: a finite POVM applied to a density matrix is
  packaged as a normalized finite classical distribution, allowing measurement
  outcomes to reuse the statistical and Markov APIs.
- `StatMech.Entropy`: finite second moments and collision probability are
  exposed as a shared algebraic API.  Nonnegativity, the `[0,1]` bound and the
  uniform-distribution value are kernel-checked; logarithmic Renyi entropy and
  continuum entropy remain explicit analysis boundaries.  The POVM adapter
  exposes the same collision probability for measurement outcomes.
- `StatMech.FiniteProbability`: the same finite probability semantics now work
  over any `Fintype` outcome type, with expectation, second moments and
  collision bounds.  This avoids encoding named lattice, spin, band, or colour
  labels as `Fin n` merely to use the probability API.
- `StatMech.FiniteKernel`: arbitrary finite labels support normalized state
  push-forward, observable pullback, composition, and preservation of the
  uniform state for doubly-stochastic kernels.
- `StatMech.TransferKernel`: arbitrary finite nonnegative transfer weights with
  positive row sums normalize to a finite Markov kernel; probability
  preservation and the expectation pullback identity are checked through the
  shared kernel API.  Perron--Frobenius asymptotics and thermodynamic limits
  remain outside the finite layer.
- `StatMech.FiniteGibbs`: arbitrary finite labels support positive partition
  functions, normalized Gibbs probabilities and invariance under an additive
  energy shift; thermodynamic limits remain outside the layer.
- `Quantum.NamedChannel`: arbitrary finite label types support Kraus CPTP
  maps, an explicit finite ancillary complete-positivity property, density
  preservation and channel composition.  A Gibbs state represented in a named
  basis can therefore pass through the same channel invariant.
- `QuantumInfo.TypedChannel`: rectangular Kraus operators `Matrix κ ι ℂ`
  support channels whose input and output labels differ.  Input completeness
  proves output positivity, trace preservation, finite-density transport and
  composition across an intermediate finite space.  The same module checks
  the cross-dimensional Schrödinger/Heisenberg trace pairing and dual
  unitality; this remains a finite matrix adapter rather than an
  infinite-dimensional trace-class theorem.
- `Quantum.NamedClassical`: finite Markov state propagation on named labels is
  embedded into diagonal density matrices, with expectation pullback and
  purity/collision identities checked by the kernel.
- `Quantum.DiagonalState`: a finite classical distribution is embedded as a
  diagonal density matrix; its trace, positivity, matrix purity and diagonal
  observable expectations are identified with the corresponding classical
  normalization, collision probability and finite expectation.  This is a
  finite interoperability adapter, not a claim about general spectral theory.
- `QuantumInfo.POVMDistribution`: the preceding adapter is composed with a
  finite POVM, so its classical output distribution can be viewed as a diagonal
  state whose matrix purity is the measurement collision probability.
- `Quantum.Unitary`: finite unitary operators preserve ket inner products and
  density-matrix validity; conjugation and unitary composition are checked by
  the kernel; the corresponding finite Schrödinger/Heisenberg trace pairing
  is also checked.
- `QuantumInfo.UnitaryChannel`: a finite unitary is exposed as a singleton
  Kraus/CPTP channel, reusing trace, positivity and channel-composition laws;
  its state-level composition agrees with direct unitary conjugation.
- `Particles.ckm_unitaryOperator`: converts CKM right-unitarity into the shared
  `UnitaryOperator` object used by finite quantum dynamics.
- `Quantum.FiniteUnitary`: a generic finite-index unitary structure with a
  kernel-checked tensor-product constructor and inner-product-preserving
  finite-index evolution.
- `Mathematics.BilinearIsometry`: a generic finite `Aᵀ G A = G` structure with
  kernel-checked composition closure.
- `Mathematics.FiniteFourier`: a finite complex kernel with explicit left and
  right orthogonality has a kernel-checked forward/inverse transform; concrete
  roots of unity and continuum limits remain explicit inputs; the two-point
  Hadamard and four-point periodic kernels are concrete checked instances; the
  same interface proves the unnormalised finite Parseval identity.
- `FiniteFourierSystem.normalizedUnitary`: an explicit normalization
  hypothesis produces a generic finite unitary; the four-site periodic
  instance is checked.
- `Quantum.SpectralModels`: computational qubit projectors form a complete
  finite spectral family, reconstruct Pauli Z, and certify both eigenvalue
  branches; the adapter is reusable for two-band and BdG models.
- `Quantum.SpectralDecomposition`: complete pairwise-orthogonal finite
  projector families reconstruct operators and act with the prescribed
  eigenvalue on each projector range; spectral existence is kept explicit.
- `QuantumInfo.Lindblad`: the finite-dimensional Hamiltonian plus dissipator
  generator has zero trace for every matrix, proved from cyclicity; positivity
  of a generated semigroup and master-equation existence remain explicit
  analytic obligations;
- `GaugeTheory.Maxwell`: the Abelian potential construction proves
  antisymmetry, gauge invariance under commuting derivations and the cyclic
  Bianchi identity.  Its component field strength is definitionally the
  `Mathematics.Exterior` finite `d` of a one-form, and a second theorem
  reuses the generic `d² = 0` result to reprove the cyclic identity;
  smoothness and PDE existence remain outside the algebraic layer;
- `Mathematics.Exterior`: finite one-, two- and three-form coefficient APIs,
  commutative-coefficient wedge antisymmetry, and a finite `d² = 0` theorem
  under an explicit commuting-derivation hypothesis.  This shared algebraic
  layer is intended for Maxwell, discrete differential forms and future
  geometric/fluid adapters; manifolds, integration and regularity are not
  inferred;
- `Classical.Vorticity`: a finite/discrete velocity one-form is mapped to
  vorticity `d u`; its closedness and exact-potential-shift invariance reuse
  the exterior layer. Navier--Stokes dynamics, Hodge theory and continuum
  limits remain outside the algebraic module;
- `GaugeTheory.YangMills`: a noncommutative matrix-valued connection carries
  explicit Leibniz derivations; `dA + [A,A]`, the adjoint covariant derivative,
  curvature antisymmetry and the covariant Bianchi identity are checked by the
  kernel.  Gauge-group global analysis remains outside the layer;
- `Mathematics.AlgebraicDerivation` and `Mathematics.NoncommExterior`: the
  additive Leibniz interface and finite-index noncommutative connection are
  separated from the four-dimensional adapter. Curvature antisymmetry and the
  covariant Bianchi identity are proved for arbitrary finite index sets, and
  `YangMillsConnection.bianchi_via_noncommExterior` reuses that theorem;
  `innerDerivation` supplies a concrete commutator action, and
  `innerConnection` constructs a finite connection when its generators
  commute pairwise;
- `Quantum.Spectral`: finite characteristic-polynomial monicity, degree and
  Cayley–Hamilton are exposed alongside exact eigenvector and ladder results;
- `Quantum.HermitianSpectrum`: the mathlib Hermitian spectral theorem is
  exposed for finite operators and density matrices; density eigenvalues are
  nonnegative, sum to one, and have an explicit unitary diagonalization.
- `Quantum.NamedFinite`: arbitrary finite basis labels index diagonal density
  matrices and observables; named finite-state purity and expectation reduce to
  collision probability and classical expectation.
- `Quantum.NamedFinite` also exposes a finite Gibbs-to-density-state adapter:
  thermal expectations and purity reuse the generic finite Gibbs/probability
  interfaces.
- `StatMech.Probability`: finite normalized distributions, expectation
  linearity, positivity and variance nonnegativity;
- `Surface.HigherTensor`: rank-three/rank-four variance-aware contractions and
  compile-time rejection of same-variance contractions.
- `Mathematics.Derivation`: explicit Leibniz derivations, covariant curvature,
  antisymmetry and pointwise Bianchi identity;
- `Mathematics.Poisson`: a reusable Poisson-algebra interface with explicit
  bilinearity, Jacobi and Leibniz laws, plus conservation closure under
  products, powers, linear combinations and brackets.  The Hamiltonian action
  is packaged as a mathlib Leibniz derivation for reuse by continuum layers;
- `Classical.PolynomialPhaseSpace`: a concrete polynomial phase space whose
  commuting formal partial derivatives construct the canonical Poisson bracket
  and prove `{q,p}=1`.
- `Mathematics.PoissonAlgebra.hamiltonianDerivation_commutator`: Hamiltonian
  derivations reproduce the Poisson bracket under commutator, giving a checked
  classical Lie action.
- `Classical.PolynomialPhaseSpace`: the formal derivative construction is
  parameterized by any selected pair of variables in a larger polynomial
  algebra, not only the two-variable oscillator example.
- `Classical.PolynomialPhaseSpace`: the normalized polynomial oscillator has
  kernel-checked Hamiltonian equations `{H,q}=-p`, `{H,p}=q`, and conserved H.
- `Quantum.Spectral`: exact finite eigenvector, commuting-operator and ladder
  eigenvalue-shift theorems.
- `Classical.Lagrangian`: finite jet-polynomial total derivatives and the
  Euler–Lagrange residual; the oscillator gives `q+a=0`, while componentwise
  field/lattice jets reuse the same derivation constructor.
- `Quantum.Projector`: rank-one ket-bra projectors satisfy the Dirac action
  rule, positivity, Hermiticity, normalized idempotence and trace identities;
  spectral completeness remains an explicit analysis layer.
- `StatMech.Markov`: finite nonnegative row-normalized kernels preserve finite
  distributions, compose by finite sums, and doubly-stochastic kernels preserve
  the uniform state; ergodicity and mixing remain analysis assumptions.
- `StatMech.Gibbs`: a nonempty finite state space has a strictly positive
  partition function; Gibbs weights form a normalized finite distribution and
  are invariant under an additive shift of all energies.  Thermodynamic limits,
  entropy derivatives and phase transitions remain analysis assumptions.
- `StatMech.Entropy`: finite second moments and collision probability provide a
  common second-order interface for statistical and measurement distributions;
  nonnegativity, the `[0,1]` bound, the expectation identity and the uniform
  value are checked by the kernel.  Logarithmic Renyi entropy and continuum
  entropy remain outside the finite algebraic layer.

These modules widen the common layer used by quantum, gauge, high-energy,
condensed-matter, classical and statistical models.  Measurement instruments
remain finite-dimensional and use a finite internal Kraus index; complete
positivity on arbitrary ancillary systems, infinite-dimensional probability,
and entropy/capacity results remain explicit future layers.  The Lie
representation fields remain explicit model hypotheses.

As a stronger check than a text search, `#print axioms` on the load-bearing
theorems reports only Lean's three standard axioms — `propext`,
`Classical.choice`, `Quot.sound` — which are the same ones mathlib itself
rests on.  No theorem depends on `sorryAx`.  For example:

```
'LeanPhy.FieldTheory.Pairing.wick_pairing_count' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.HighEnergy.tr4_slash_mul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.HighEnergy.ward_identity' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.HighEnergy.mass_shell' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Condensed.CliffordPair.bogoliubov_rotation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Condensed.bdg_sq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.HighEnergy.SusyQM.H_commutator_Q' depends on axioms:
  [propext]
'LeanPhy.Einstein.einsum_mul_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.QuantumInfo.kraus_trace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.QuantumInfo.kraus_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.GaugeTheory.loop_conj' depends on axioms:
  [propext]
'LeanPhy.GaugeTheory.wilson_loop_invariant' depends on axioms:
  [propext]
'LeanPhy.Condensed.bloch_sq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.HighEnergy.mandelstam' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.StatMech.isingTransferMatrix_charpoly' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.GaugeTheory.bianchi' depends on axioms:
  [propext]
'LeanPhy.HighEnergy.sigma_antisym' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Particles.smGen_anomalyFree' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Particles.gm_fierz' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.HighEnergy.cov_fierz_expansion' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Quantum.pauli_twirl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Quantum.pauli_twirl_depolarise' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Particles.ckm_unitary' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.QuantumInfo.mermin_ghz_eigen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Relativity.boost_lorentz' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Condensed.berry_density' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Condensed.jwHop_eq_xy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Condensed.car_zero_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Quantum.spinOne_casimir' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Quantum.S3_commutator_Jplus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.QuantumInfo.no_cloning' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Relativity.B1_commutator_B2' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Relativity.metric_B3' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.QuantumInfo.stab1_code' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.QuantumInfo.xx2_syndrome1' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.QuantumInfo.teleportation_identity' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Tensor.raise_lower' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Tensor.contractUD_lower' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'LeanPhy.Classical.symplectic_iff_det' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

## What is proved (kernel-checked)

Finite-dimensional quantum mechanics

- the Pauli matrices: `X^2 = Y^2 = Z^2 = I`, the cyclic products, and the
  commutators `[X,Y] = 2iZ` and partners;
- the spin-vector identity `(σ·a)(σ·b) = (a·b) I + i σ·(a×b)`;
- spin-1/2 su(2): `J_i = σ_i/2`, `[J_x, J_y] = i J_z`, and the Casimir
  `J^2 = (3/4) I`;
- the **Pauli group** `{1, sigma_x, sigma_y, sigma_z}`: each element squares to
  the identity, the four elements are **trace-orthogonal**
  (`tr (sigma_a sigma_b) = 2 delta_ab`), and the **Pauli twirl**
  `sum_a sigma_a M sigma_a = 2 tr (M) 1` holds for every `2 x 2` matrix `M`;
  the normalised twirl `(1/4) sum_a sigma_a M sigma_a` preserves the trace and
  equals `(tr M / 2) 1`, the completely depolarising channel in Pauli form.
  This is the algebraic core of Pauli channels and of Bell-diagonalising a
  two-qubit state; the twirl constant `2` is a kernel-evaluated trace, not a
  convention.
- coupled spins: total su(2) on the two-spin space, the singlet
  `|01> - |10>` annihilated by every total generator, and the total Casimir
  identity `J^4 = 2 J^2` (spectrum `{0, 2}`).

Angular momentum one (spin-1 representation)

- the Cartesian generators `S_1, S_2, S_3` as explicit `3 x 3` matrices satisfying
  the `su(2)` relations `[S_1, S_2] = i S_3`, `[S_2, S_3] = i S_1`, `[S_3, S_1] = i S_2`,
  checked entrywise (`S1_commutator_S2` and partners);
- the **Casimir** `S . S = 2 * 1 = l(l+1) 1` at `l = 1` (`spinOne_casimir`),
  exactly `2` rather than the spin-1/2 value `3/4`;
- the **cubic identity** `S_i^3 = S_i` (`S1_cubed`, `S2_cubed`, `S3_cubed`), whose
  eigenvalues are `{-1, 0, 1}`;
- the **ladder operators** `J_+ = S_1 + i S_2`, `J_- = S_1 - i S_2` raise and lower the
  `S_3` eigenvalue (`S3_commutator_Jplus`, `S3_commutator_Jminus`), and
  `J_+ J_- = S_1^2 + S_2^2 + S_3` (`Jplus_mul_Jminus`).  All entrywise; the general
  spin-`l` representation and the Clebsch-Gordan decomposition are out of scope.

Quantum information

- the Bell state, its EPR correlations, and the reduced density matrix;
- the CHSH operator, the Tsirelson square identity
  `S^2 = 4 I + 4 (σ_y ⊗ σ_y)`, and the Tsirelson value on the Bell state;
- entanglement measures: the purity `tr (ρ^2)` of the maximally mixed qubit (1/2),
  of a pure projector (1), and of the Bell marginal (2, the maximum at its trace),
  the algebraic core of the Renyi-2 entropy.
- tensor products: bilinearity, the mixed-product law, partial trace and its
  trace preservation.

- finite POVMs: a family of positive semidefinite effects whose sum is the
  identity; the finite-dimensional matrix order bridge proves that Born
  weights are real and nonnegative, and that their sum is one on every valid
  density matrix.  The order bridge is proved from the matrix square-root
  theorem and is not an application-specific axiom.

- three-qubit **GHZ / Mermin** nonlocality: the Mermin operator
  `M = X Y Y + Y X Y + Y Y X - X X X` on the explicit `8 x 8` Pauli matrices is
  symmetric (`mermin_symm`); it maps the GHZ vector `|000> + |111>` to `-4` times
  itself (`mermin_ghz_eigen`); and its GHZ expectation is `-8` (`ghzExpect_mermin`),
  i.e. `-4` on the normalised state.  This is the multipartite Bell combination
  (quantum value `4` versus the local-hidden-variable bound `2`).


No-cloning theorem

- a linear `U` copying both basis states, `U (|0> (x) b) = |0> (x) |0>` and
  `U (|1> (x) b) = |1> (x) |1>`, is forced by linearity to send `|0> + |1>` to the
  entangled `|00> + |11>` (`clone_zero_one_form`);
- that output is not a product `(|0> + |1>) (x) P` for any `P` (`sum_clone_ne`),
  so no linear operation clones every state (`no_cloning`).  Everything is over `ℂ` on
  the explicit qubit vectors `e0, e1`; the unitary completion and the
  density-matrix (mixed-state) formulation are out of scope.

Three-qubit bit-flip code

- the encoded vector `a |000> + b |111>` for arbitrary complex amplitudes is fixed by both stabilizers
  `Z Z I` and `I Z Z` (`stab1_code`, `stab2_code`);
- the first physical bit flip `X_1` has syndrome `(-1, +1)` (`xx1_syndrome`, `xx1_syndrome2`),
  the second `X_2` has `(-1, -1)` (`xx2_syndrome1`, `xx2_syndrome2`), and the third
  `X_3` has `(+1, -1)` (`xx3_syndrome1`, `xx3_syndrome2`);
- these are exact `8 x 8` matrix-vector identities over `ℂ`, the stabilizer error-detection table.
  The recovery circuit, phase noise and general quantum channels are out of scope; the proved
  statement is conditional on the bit-flip noise model.

Quantum teleportation

- the Bell-basis expansion for an arbitrary input `|psi> = a|0> + b|1>` and the unnormalised
  resource `|Phi+>`:
  `|psi> (x) |Phi+> = 1/2 [ |Phi+> (x) |psi> + |Phi-> (x) Z|psi> + |Psi+> (x) X|psi>`,
  `|Psi-> (x) XZ|psi> ]` (`teleportation_identity`), checked entrywise over `ℂ`;
- the `Z`, `X` and `ZX` corrections recover the original state exactly on the three
  nontrivial branches (`teleport_correction_Z`, `teleport_correction_X`, `teleport_correction_ZX`).  Normalisation,
  measurement probabilities and the classical communication channel are out of scope.

Quantum channels (Kraus operator sum)

- the channel `applyKraus K rho = sum_k K_k rho K_k†` is additive and
  homogeneous in the state;
- **trace preservation**: `sum_k K_k† K_k = 1` implies
  `tr (applyKraus K rho) = tr rho`, proved by cyclicity of the trace;
- **unitality**: `sum_k K_k K_k† = 1` implies `applyKraus K 1 = 1`;
- **composition**: applying `K` then `L` equals the Kraus family
  `(j, k) |-> L_j K_k`, so channels compose;
- **state validity**: each term `K ρ K†` preserves positive semidefiniteness,
  finite sums preserve it, and a trace-preserving Kraus family maps an
  `IsDensity` state (Hermitian, positive semidefinite, trace one) to another
  `IsDensity` state;
- **bundled channels**: `FiniteChannel` stores positivity and trace preservation
  as fields, together with additivity and scalar homogeneity; the identity,
  Kraus constructor and composition preserve all fields, and composition maps
  an `IsDensity` state to an `IsDensity` state;
- the single-qubit **amplitude-damping** channel `K0 = diag (1, c)`,
  `K1 = [[0, s], [0, 0]]` satisfies the Kraus completeness relation
  `sum_k K_k† K_k = 1` exactly when `c^2 + s^2 = 1`, hence is trace
  preserving on every state;
- the qubit **depolarising** channel `rho |-> (1 - 4p/3) rho + (4p/3) (I/2)`:
  it is the identity at `p = 0`, total decoherence to `I/2` at `p = 3/4`, and
  has the stated trace.  Every Kraus family also has a finite ancillary-system
  complete-positivity theorem, by applying the same operator-sum to `I ⊗ K`;
  infinite-dimensional operator-algebraic versions remain out of scope.

Lindblad generators

- `lindbladGenerator H L rho` is the finite matrix expression
  `-i[H,rho] + sum_k (L_k rho L_k† - 1/2 {L_k†L_k,rho})`;
- `trace_commutator_zero` and `trace_lindblad_dissipator` prove the two
  cancellation identities by cyclicity of the finite trace;
- `lindblad_trace_zero` proves the complete finite sum has zero trace.  This is
  the invariant needed by master-equation derivations, while positivity of the
  semigroup and long-time limits are deliberately not claimed.

Finite Gibbs ensembles

- `partitionFunction β E` is a finite exponential sum and is strictly positive
  whenever `Fin n` is nonempty;
- `gibbsWeight` is nonnegative and its finite sum is exactly one, so
  `gibbsDistribution` reuses the common `FiniteDistribution` API;
- `gibbsWeight_shift` proves that `E -> E + c` leaves the Gibbs distribution
  unchanged.  Thermodynamic limits and differentiating `log Z` are out of scope.

Bosonic field algebra

- the CCR `[a, a†] = 1` implies `[a†a, a†] = a†` and `[a†a, a] = -a`;
- finite multi-mode CCR: the total number operator is a ladder for every mode;
- Wick's theorem for one free mode: the contraction recursion
  `<φ^{n+2}> = (n+1) <φ^n>`, the even-point closed form `<φ^{2k}> = (2k-1)!!`,
  the vanishing of all odd moments `<φ^{2k+1}> = 0`, and the explicit
  pairing statement: the perfect matchings of 2k objects are enumerated as a
  concrete list whose length is proved to be (2k-1)!!, and the (2k)-point
  function equals that count.

Fermionic / condensed-matter algebra

- one fermionic mode: `{c, c†} = 1`, `c^2 = 0`, `N = c†c` is a projector
  and a ladder;
- the Hubbard site: commuting spin projectors, the double-occupancy projector,
  the nilpotent Cooper-pair operator `P = c↑† c↓†` with `[D, P] = P`, and
  the total number operator as a ladder;
- Majorana fermions: the two real Majorana combinations of one Dirac mode
  satisfy `g1^2 = 1`, `g2^2 = -1`, `{g1, g2} = 0` (Cl(1,1)), and the Dirac
  number operator is recovered as `c†c = (1 + i gamma1 gamma2)/2, with gamma2 = -i (c-c†)`;
- Legacy BCS coefficient algebra: a complex-orthogonal rotation preserves
  Clifford relations without asserting self-adjointness (`(c g1 + s g2)^2 = 1` and the rotated anticommutator
  vanishes); the BdG matrix `[[eps, Delta], [Delta, -eps]]` squares to
  `(eps^2 + Delta^2) 1`, is traceless with determinant `-(eps^2 + Delta^2)`
  (symmetric spectrum `± sqrt (eps^2 + Delta^2)`), equals `eps sigma_z + Delta sigma_x`,
  and reflects correctly under `sigma_x`/`sigma_z` conjugation.  A real finite
  family of BdG blocks instantiates the common uniform spectral-gap certificate
  from `Quantum.ParametricSpectralGap`; the mean-field gap equation
  `gap = -g * pairingAmp` is carried as an explicit hypothesis;
- finite lattice hopping and occupation sums.

Topological band structure (two-band Bloch Hamiltonians)

- the Bloch Hamiltonian `H = d1 sigma_x + d2 sigma_y + d3 sigma_z` shown equal to
  its explicit `2 x 2` matrix form (`bloch_eq_pauli`);
- `H^2 = (d . d) 1` (`bloch_sq`), so the spectrum is the symmetric pair
  `± sqrt (d . d)`; `tr H = 0` and `det H = -(d . d)`;
- over complex coefficients, **the determinant criterion** is
  `det H = 0 ↔ d . d = 0` (`bloch_gap_closed_iff`); for real coefficients,
  `bloch_real_det_zero_iff` additionally proves the Hermitian criterion
  `det H = 0 ↔ d1 = d2 = d3 = 0`.  The complex null counterexample is checked
  explicitly, so a bilinear square is not silently treated as a positive norm;
- the spectral polynomial: any `lam` with `lam^2 = d . d` satisfies
  `(H - lam)(H + lam) = 0` (`bloch_spectral_poly`);
- **chiral (sublattice) symmetry**: when the `d3` term is absent,
  `sigma_z H sigma_z = -H`, the symmetry that protects a zero mode in
  SSH-type models, forcing the spectrum symmetric about zero;
- concrete gapped (`d = (0,0,1)`) and gap-closing (`d = 0`) witnesses
  evaluated by the kernel.  A gap closing alone does not prove a topological
  transition; winding, Chern and bulk-boundary claims remain outside scope.

Spherical Bloch-vector geometry

- the spherical Bloch vector has unit norm (`dhat_unit`);
- its displayed tangents are orthogonal to the vector and to each other;
  `dTheta` has unit norm and `dPhi` has squared norm `sin theta ^ 2`;
- `berry_density` proves the scalar triple product is `sin theta`, the
  spherical area Jacobian. It does not construct a selected-band projector,
  Berry connection, curvature normalization or topological integral. The
  theorem name is retained for compatibility.

Jordan-Wigner transformation (two-site fermion chain)

- the annihilation operators `c_0 = sigma^- (x) 1`, `c_1 = sigma^z (x) sigma^-` as explicit
  `4 x 4` matrices, with `c_j^dag` proved to be the conjugate transpose of `c_j`;
- the full two-site **CAR**, checked entrywise: `{c_0, c_0^dag} = 1` (`car_zero`),
  `{c_1, c_1^dag} = 1` (`car_one`), `{c_0, c_1^dag} = 0` (`car_zero_one`),
  `{c_1, c_0^dag} = 0` (`car_one_zero`), the nilpotency `c_0^2 = c_1^2 = 0` and
  `{c_0, c_1} = 0`;
- **the string is load-bearing** (`naive_anticommutator`, `naive_anticommutator_ne_zero`): without
  the `sigma^z` factors the cross-site anticommutator is `2 (sigma^- (x) sigma^+) != 0`, so
  the transform is not a relabelling;
- each number operator `n_j = c_j^dag c_j` is a projector (`jwN0_projector`, `jwN1_projector`),
  and the two commute (`jwN0_comm_jwN1`);
- **number conservation**: the hopping term `c_0^dag c_1 + c_1^dag c_0` commutes with the total
  number `n_0 + n_1` (`jwHop_num_comm`);
- **spin-chain map**: the hopping term equals
  `(1/2)(sigma^x (x) sigma^x + sigma^y (x) sigma^y)` (`jwHop_eq_xy`), the XY coupling.
  The general `N`-site string, momentum space and the interacting chain are out of scope.

Lattice gauge theory (Wilson loops)

- **gauge covariance**: under a link transformation
  `U_i -> g_i U_i g_{i+1}^{-1}` the ordered loop product conjugates,
  `W -> g W g^{-1}` (`loop_conj`), i.e. a Wilson loop transforms in the
  adjoint representation;
- for an **abelian** gauge group the conjugation is trivial and the Wilson loop
  is gauge invariant (`wilson_loop_invariant`);
- additively, the **plaquette flux** `U_0 + U_1 + U_2 + U_3` is invariant under
  the finite-difference gauge transformation `U_i -> g_i + U_i - g_{i+1}`
  (`plaquette_flux_gauge_invariant`), with a kernel-evaluated `ZMod 7` witness;
- a group homomorphism respects the loop product (`loop_map`), so any **class
  function** of the loop is automatically gauge invariant
  (`classFunction_invariant`), the shape of every gauge-invariant observable;
  finite matrix representations additionally prove trace invariance under an
  explicitly `IsUnit` conjugating matrix (`matrix_trace_conjugate`);
- a concrete nonabelian witness shows the covariance is not vacuous.

The lattice action, the strong-coupling expansion and the continuum limit are
not attempted; the group-level covariance above is the input they consume.
- **Continuum field strength** (`LeanPhy.GaugeTheory.fieldStrength`): with the
  field strength defined as the commutator `F_{mu nu} = [D_mu, D_nu]` of
  covariant derivatives, it is antisymmetric (`fieldStrength_antisym`),
  vanishes on the diagonal, satisfies the **algebraic Bianchi identity** (the
  cyclic sum of `[F, D]` vanishes, `bianchi`), and is forced to zero for
  commuting (abelian) derivatives (`fieldStrength_abelian`).  A `2 x 2` matrix
  witness shows `F_01 != 0` for a nonabelian choice, so the module is not
  vacuous; all in an abstract ring with no representation assumed.

High energy / gamma algebra

- the explicit chiral gamma matrices, their squares, and the Clifford relation
  `{γ^μ, γ^ν} = 2 η^{μν}` as a single indexed statement;
- `γ^5`: it squares to 1, anticommutes with every `γ^μ`, is Hermitian, and
  the chiral projectors are idempotent, orthogonal, and sum to 1;
- gamma-matrix traces: every gamma is traceless, `tr (γ^μ γ^ν) = 4 η^{μν}`,
  the four-point trace `tr (γ^μ γ^ν γ^ρ γ^σ) = 4 (η^{μν} η^{ρσ} - η^{μρ} η^{νσ} + η^{μσ} η^{νρ})`,
  and the chiral traces `tr γ^5 = 0`, `tr (γ^5 γ^μ γ^ν) = 0`;
- supersymmetry: for a nilpotent supercharge `Q`, the Hamiltonian `H = {Q, Q†}`
  commutes with both supercharges and annihilates any state killed by both
  (the BPS condition), with a concrete 2x2 realization `H = 1`;
- Dirac bilinears: the Feynman slash and its two-point trace
  `tr (a̸ b̸) = 4 (a·b)`, the vanishing of traces with an odd number of
  slashes, and `tr (γ^5 a̸) = 0`;
- the Ward identity: with the Feynman slash shown to be linear, the photon
  vertex `vertexAmplitude eps ub u = sum_mu eps_mu (ubar γ^μ u)` is proved to
  equal the slash sandwich `ubar slash(eps) u` and to be linear in `eps`.  With
  both legs on shell (`slash p u = 0` and `ubar slash p' = 0`, explicit
  hypotheses) the longitudinal polarisation `p' - p` decouples
  (`ward_identity`), so `eps -> eps + lam (p' - p)` leaves the amplitude fixed
  (`gauge_invariance`).  A concrete lightlike configuration
  (`wardP = (1,0,0,1)`) solves both on-shell equations, so the hypotheses are
  satisfiable and the identity is not vacuous;
- spinor kinematics: the Feynman slash squares to the invariant
  `a̸ p * a̸ p = (p·p) 1`, with trace shadow `tr (a̸ p a̸ p) = 4 (p·p)`;
  from the Dirac equation `a̸ p u = m u` the momentum is forced on shell,
  `(p·p - m m) • u = 0`, and a massless on-shell spinor has lightlike momentum;
- the Lorentz algebra `so(1,3)`: the boost/rotation generators `J_i`, `K_i`
  with all nine commutators, tied to `(i/4)[γ^μ, γ^ν]`.
- spinor covariants: the antisymmetric tensor generator
  `sigma^{mu nu} = (i/2)[gamma^mu, gamma^nu]` is antisymmetric
  (`sigma_antisym`), vanishes on the diagonal (`sigma_self`), and
  commutes with `gamma^5` (`gamma5_commute_sigma`), which is exactly the
  property that makes the tensor a genuine Lorentz covariant rather than
  mixing with the pseudotensor.  Completeness of the five-covariant basis (the
  Fierz expansion, which needs a `+/- 4` weighting) is not proved here.


Standard Model anomaly cancellation (particle physics)

- the fermion content of one generation is a five-element list with the quantum
  numbers `(3,2,1/6)` (Q), `(3,1,-2/3)` (U), `(3,1,1/3)` (D),
  `(1,2,-1/2)` (L), `(1,1,1)` (E), each entry a `(colour, isospin, hypercharge)` triple
  over `ℚ`;
- **all four gauge-anomaly coefficients vanish**, evaluated by the kernel over `ℚ`
  (`smGen_anomalyFree`): the mixed gravitational-`U(1)` coefficient
  `∑ (colour)(isospin) Y`, the `SU(3)^2 U(1)` and `SU(2)^2 U(1)` coefficients (the two
  second-Casimir-weighted sums), and the `U(1)^3` coefficient `∑ (colour)(isospin) Y^3`;
- **any number `n` of identical generations** is anomaly free (`smContent_anomalyFree`):
  the sum of `n` copies of a zero coefficient is zero;
- **hypercharge rigidity**: under a uniform shift `Y -> Y + eps` the `U(1)^3` coefficient
  becomes the cubic `15 eps^3 + 10 eps` (`smGen_accU1cubed_shift`) and the gravitational
  coefficient becomes `15 eps` (`smGen_accGrav_shift`); the general affine and cubic
  transformation laws of these coefficients under the shift are stated and proved as
  `accGrav_hyperShift` and `accU1cubed_hyperShift`.  Hence the only rational shift that
  keeps the content anomaly free is `eps = 0` (`smGen_shift_rigid`, `smGen_grav_shift_rigid`),
  the algebraic statement that the hypercharge normalisation is fixed by the content.

  **Hypothesis boundary**: the fermion content (the quantum-number table) is the
  input.  The statement is conditional correctness — *given* these quantum numbers,
  the anomaly coefficients vanish — not a derivation of the content from a deeper
  principle.  The colour and isospin representation dimensions enter only through
  their Casimir weights `(colour-1)/2` and `(isospin-1)`, so the module checks the
  arithmetic of the anomaly conditions, not the group theory that produces the
  weights.

Particle physics: colour algebra and Dirac covariants

- **SU(3) colour algebra** (Gell-Mann matrices, integer normalisation with
  `1/sqrt 3` in `lam_8`): every `lam_a` is traceless (`gm_traceless`);
  **trace orthonormality** `tr (lam_a lam_b) = 2 delta_ab` (`gm_trace_orthonormal`);
  the **fundamental quadratic Casimir** `sum_a lam_a lam_a = (16/3) 1`
  (`gm_casimir`), whose coefficient is `4 C_F` with the quark colour factor
  `C_F = 4/3`; the **Fierz completeness** relation
  `sum_a (lam_a)_{ij} (lam_a)_{kl} = 2 delta_il delta_jk - (2/3) delta_ij delta_kl`
  (`gm_fierz`), the identity that rearranges a four-quark operator into
  colour-singlet and colour-octet channels with the weights `2` and `-2/3`; and
  the **colour-singlet trace** `sum_a tr (lam_a lam_a) = 16` (`gm_casimir_trace`).
  The `sqrt 3` is an explicit algebraic symbol (`sqrt3 * sqrt3 = 3`), never
  approximated.
- **Dirac covariant completeness** (the sixteen `Gamma_A`): the covariants are
  **trace-orthogonal** with the definite Fierz weight `w_A = tr (Gamma_A Gamma_A)/4`,
  `+1` on the scalar, pseudoscalar, vector and tensor families and `-1` on the
  axial-vector family, so `tr (Gamma_A Gamma_B) = 4 w_A delta_AB`
  (`cov_trace_orthonormal`); **Fierz completeness** holds entrywise,
  `sum_A w_A (Gamma_A)_{ij} (Gamma_A)_{kl} = 4 delta_il delta_jk` (`cov_fierz`);
  and the **closure form** `sum_A w_A tr (Gamma_A M) Gamma_A = 4 M` holds for any
  `4 x 4` matrix `M` (`cov_fierz_expansion`), the identity a Fierz
  rearrangement of an operator product is read off from.  The axial-vector signs
  (the `w_A = -1` cases) are precisely where a Fierz computation is most often done
  wrong, so each is kernel-checked rather than assumed.  What is *not* proved:
  the covariant expansion of a specific bilinear product (a rewriting, not a new
  identity) and the group-theoretic Casimir ratio `C_A = 3` from the structure constants,
  which is left to the anomaly module's arithmetic.
Particle physics: CKM quark mixing

- the Cabibbo-Kobayashi-Maskawa matrix in the product parametrisation
  `V = R_23 (gamma) P (delta) R_12 (theta)` (`ckm`): each of the two real
  rotations (`rot12`, `rot23`) is **unitary** (`rot12_unitary`,
  `rot23_unitary`) and the phase-carrying rotation is unitary from the unit modulus
  of the phase (`phaseRot13_unitary`); a product of three unitary matrices is unitary
  (`unitary_mul3`), so `V Vᴴ = 1` (`ckm_unitary`);
- the **unitarity-triangle** relation: the rows are orthonormal,
  `sum_k V_ik (V_jk)^* = delta_ij` (`ckm_row_orthonormal`), whose
  `(i, j) = (0, 2)` case is the closure of the standard CP-violation triangle.
  The phase is carried as an abstract unit-modulus complex number (`u^* u = 1`) rather
  than `exp (i delta)`, so no analysis enters; the mixing angles are hypotheses, so
  this is conditional correctness.  The Jarlskog invariant and the explicit Wolfenstein
  expansion are out of scope.

Scattering kinematics (Mandelstam invariants)

- the Minkowski product `minkowskiDot` is symmetric and bilinear, with the
  sign law under negation;
- **Mandelstam identity, off shell**: the defect
  `s + t + u - (m1^2 + m2^2 + m3^2 + m4^2)` equals
  `2 p1 . (p1 + p2 - p3 - p4)`, which vanishes on four-momentum
  conservation (`mandelstam_defect`);
- **on shell** (`p1 + p2 = p3 + p4`) the invariants obey
  `s + t + u = m1^2 + m2^2 + m3^2 + m4^2` (`mandelstam`), with a
  concrete massless configuration evaluated by the kernel.  Crossing,
  dispersion relations and the optical theorem are out of scope.

Symplectic canonical transformations (classical mechanics and optics)

- the canonical form `J = [[0,1],[-1,0]]` and the two-dimensional condition `A^T J A = J`;
- **symplectic iff determinant one** (`symplectic_iff_det`): for every real `2 x 2` matrix,
  `A^T J A = J ↔ det A = 1`;
- symplectic maps compose (`symplectic_mul`), and the phase-space rotation and free-particle
  shear families preserve `J` (`rotation_symplectic`, `shear_symplectic`);
- this is finite linear algebra shared by Hamiltonian mechanics, paraxial optics, accelerator
  lattices and bosonic Gaussian systems.

Generic finite typed tensors

- `Tensor2N n up/down` carries the variance of both rank-two slots for any
  finite `Fin n` index;
- mixed composition is associative, has a typed identity, and its trace is
  cyclic (`mixedTraceN_comp_comm`);
- the same-variance trace is rejected by the elaborator, before proof search;
  no metric is assumed in this generic layer, so it can be reused for Lorentz,
  colour, lattice and finite Hilbert-space indices.

Associative-algebra Lie core and conserved observables

- `commutator_jacobi` proves the Jacobi identity for commutators in every ring;
  the adjoint action is additive and obeys the Leibniz rule;
- `Conserved H O := [H,O] = 0` is closed under sums, products, powers,
  commutators and natural scalar multiples; linear combinations with arbitrary
  coefficients require explicit centrality hypotheses. This is the shared algebraic
  conservation layer for spin, Lorentz, gauge, QFT and lattice models. The
  commutator and conservation interfaces are universe-polymorphic, so named
  finite-index matrices are not forced into `Fin n`.

The reusable low-degree cohomology layer builds on this core.  A declared
`LieModule` supplies the action, linearity, and representation compatibility;
`differential0` and `differential1` then expose the first two
Chevalley--Eilenberg maps.  The checked statements are cochain-level
statements (`d₁ d₀ = 0`, coboundaries are cocycles, and cohomology witnesses
compose). `LieCohomology2` extends this with `d₂ d₁ = 0` and the quotient
`H²`; `CentralExtension` proves the class-equality criterion for supplied
product-carrier extensions preserving base and center. `LieCohomology3`
adds d₃ d₂ = 0 and actual H³; `LieDeformationObstruction` identifies the intrinsic
second-order obstruction. General complexes beyond these degrees, Lie-group integration, anomaly cancellation, and physical meaning
remain separate obligations.

Hamiltonian interface (finite algebraic layer)

- `Quantum.HamiltonianFlow` turns a finite Hermitian matrix into the checked
  propagator `exp(i t H)`, proves composition at times `t+s`, and proves that
  any `O` with `[H,O]=0` is invariant under `U_t O U_t†`. Continuous-time
  differentiability, Stone's theorem, unbounded operators and continuum
  limits remain explicit analysis obligations.
- affine phase-space observables `a q + b p + c` with the canonical Poisson bracket;
  in particular `{q,p} = 1`, antisymmetry and bilinearity are kernel-checked;
- the normalized harmonic-oscillator rotation flow is symplectic and preserves the exact
  quadratic energy `q² + p²`;
- derivatives, nonlinear flows, generating functions, and ODE existence/uniqueness remain
  outside this layer and must be supplied by a future analysis module or explicit hypotheses.

Statistical mechanics (Ising transfer matrix)

- the symmetric transfer matrix `T = c I + s sigma_x` (`isingTransferMatrix_eq_pauli`);
- **composition law**: `T(c,s) T(c2,s2) = T(c c2 + s s2, c s2 + s c2)`, so the
  parameters combine by the addition (rapidity) formulas;
- all symmetric transfer matrices **commute** (`isingTransferMatrix_comm`), so a
  chain diagonalises in one fixed basis;
- the **characteristic polynomial** `T^2 - 2 c T + (c^2 - s^2) 1 = 0`, giving the
  spectrum `{c + s, c - s}` (`isingTransferMatrix_charpoly`);
- trace identities: `tr T = 2c` (`isingTransferMatrix_trace`) and the two-site
  partition function `tr (T^2) = 2 (c^2 + s^2) = (c+s)^2 + (c-s)^2`
  (`isingTransferMatrix_trace_sq`), with `det T = c^2 - s^2`
  (`isingTransferMatrix_det`), plus a kernel-evaluated diagonal witness.  The
  thermodynamic limit (free energy per site, the `N -> infinity` analysis) is
  out of scope.

Lorentz boosts (1+1 dimensions)

- the one-axis boost `B(c, s) = [[c, -s], [-s, c]]` (`boost`), with the Minkowski
  metric `eta = diag (1, -1)` (`etaM`) carried as an explicit matrix;
- **rapidity addition** (`boost_mul`): `B(c1,s1) B(c2,s2) = B(c1 c2 + s1 s2, c1 s2 + s1 c2)`,
  the relativistic velocity-addition law, so the boosts form a one-parameter group
  (`boost_one_mul`);
- **the Lorentz condition** (`boost_lorentz`): `B^T eta B = eta` holds exactly when
  `c^2 - s^2 = 1`, the invariance of the interval `t^2 - x^2`; a real rapidity
  (`c = cosh phi`, `s = sinh phi`) supplies that hypothesis, so this is
  conditional correctness;
- `det B = c^2 - s^2` (`boost_det`) and `B(c,s) B(c,-s) = 1` on the mass shell
  (`boost_inv`).  No hyperbolic functions enter; the parameters are abstract
  complex numbers under the single hypothesis `c^2 - s^2 = 1`.  The full Lorentz
  group, boosts along arbitrary axes, and the spinor representation are out of scope.

The Lorentz algebra so(3,1)

- the six generators as explicit `4 x 4` matrices: rotations `R_1, R_2, R_3` and boosts
  `B_1, B_2, B_3`;
- the rotations close on `so(3)`: `[R_1, R_2] = R_3` (`R1_commutator_R2`) and partners;
- rotations act on boosts as vectors: `[R_1, B_2] = B_3` (`R1_commutator_B2`) and partners;
- **two boosts close into a rotation**: `[B_1, B_2] = - R_3` (`B1_commutator_B2`) and
  partners, the Thomas-Wigner precession statement;
- every generator is **metric-antisymmetric**, `X^T eta + eta X = 0` with
  `eta = diag (1, -1, -1, -1)` (`metric_R1` ... `metric_B3`), the defining condition of
  `so(3,1)`.  Exponentiation to finite transformations, the spinor representation and
  the Poincare group are out of scope.

Relativity and dimensions

- the `(+---)` Minkowski metric and the lightlike relation;
- SI dimensions as a type index, so adding mismatched dimensions is a type error.

Variance-aware Lorentz tensors

- `UpVec` and `DownVec` are distinct four-component complex-vector types, so a term` contractUD x y`,
  where both arguments are upper vectors, is rejected by the type checker before proof search;
- `lower : UpVec -> DownVec` and `raise : DownVec -> UpVec` use the explicit `(+---)` metric and
  are inverse (`raise_lower`, `lower_raise`);
- only upper-lower contractions are exposed (`contractUD`, `contractDU`), with bilinearity and
  the symmetric Minkowski scalar `x^mu y_mu` expanded to `x0*y0 - x1*y1 - x2*y2 - x3*y3`;
- this is the first typed step toward automatic index variance checking.  Rank-2 tensors,
  finite covariant derivatives and finite differential forms now have separate
  kernel-checked interfaces; manifold-valued forms, continuous Stokes theory
  and a fully automatic Einstein elaborator remain future work.

Surface layer

- Dirac notation as a real elaborator: `|k⟩`, `⟨u|`, `⟨u|v⟩`, `⟨u|A|v⟩`,
  `⟨u|A` and `|u⟩⟨v|` infer the Hilbert-space dimension `n` from context and
  check every slot against it, so a dimension clash is a Chinese diagnostic
  rather than a silent mis-elaboration.  Orthonormal basis kets, completeness
  `∑_k |k⟩⟨k| = 1`, and the composition rule `|u⟩⟨v| |w⟩ = ⟨v|w⟩ |u⟩` are
  proved through it, and each positive form is shown by `rfl` to be the thin
  underlying definition.  The three dimension-clash diagnostics are pinned by
  `#guard_msgs` tests;
- index calculus: the Kronecker delta, finite Einstein sums and contractions,
  the Levi-Civita symbol with its antisymmetry, and the epsilon-delta identity.
- Einstein summation elaborator: `einsum k, M i k * N k j` is real syntax whose
  index type is inferred from context and whose result is the kernel-checked
  finite sum; the delta contraction (`∑_j δ_ij v_j = v_i`), the delta chain, the
  dot and cross products in index notation, and the matrix product and trace
  identities.  Its three diagnostics (index type not inferable, index type not
  finite, index absent from the summand) are pinned by `#guard_msgs` tests.

End-to-end example

- the harmonic-oscillator ladder identity `[a†a, a†] = a†` as an abstract ring
  theorem (CCR as hypothesis), and its concrete finite shadow on a two-level
  truncation, given both as a matrix identity and in Dirac notation.

## What is assumed, and where

Nothing is assumed silently.  Every hypothesis is a named field of a structure
or an explicit function argument, so a reader can see exactly what a proof
consumes.  The recurring hypotheses are:

```
FermionicMode / HubbardSite   the canonical anticommutation relations
                              {c, c†} = 1, c^2 = 0 and the cross relations
MultiModeCCR                  [a_i, a_j†] = δ_ij and mutual commutativity
FreeMode                      [a, a†] = 1 and a vacuum functional ω that is
                              additive, normalised (ω 1 = 1), and annihilates
                              a on the right and a† on the left
cliffordRelation              the Clifford bilinear form
CliffordPair / MeanField      the Majorana Clifford relations g1² = g2² = 1,
                              {g1,g2} = 0 with central ℂ coefficients, and the
                              mean-field gap equation gap = -g * pairingAmp
on-shell legs (Ward)           slash p u = 0 and ubar slash p' = 0, i.e. the
                              two electron legs solve the Dirac equation
Kraus completeness             sum_k K_k† K_k = 1 (trace preservation) and
                              sum_k K_k K_k† = 1 (unitality) are hypotheses,
                              not derived from a dilation of the channel
```

These are the physics input.  In particular the vacuum functional is an
*assumption* about a linear functional, not a construction of a Hilbert space;
the CCR is an algebraic relation in a ring, not an operator-domain statement.

## What is deliberately out of scope

The following are not attempted, and are not hidden behind a `sorry` or an
`axiom`.  They are listed so that a user knows the edge of the verified region.

- General model-specific **analytic realization**. Existing finite exponentials,
  source derivatives, formal series and conditional convergence tools use
  mathlib analysis; they do not establish every proposed continuum field model
  or the convergence of a formal perturbative expansion.
- **Infinite-dimensional Hilbert spaces** and the functional-analytic theory of
  **unbounded operators** (domains, closures, self-adjointness).
- General **continuum path-integral construction** and its quantisation
  interpretation. Finite weighted sums and source derivatives are implemented;
  the continuum measure and limits require separate proofs.
- General **renormalisation** constructions and regulator independence.
  Finite blocking and conditional limit-transport tools do not establish a
  renormalised continuum theory without their model-specific inputs.
- The **topological invariant itself**: the winding number of the Bloch vector,
  the Brillouin-zone integral, and the bulk-boundary correspondence.  The
  linear algebra of gap closing and chiral symmetry is proved in
  `LeanPhy.Condensed.Topological`, but assigning an integer invariant
  needs the topological input on top.
- **Crossing, dispersion relations and the optical theorem** for scattering
  amplitudes.  The kinematic Mandelstam identity is proved in
  `LeanPhy.HighEnergy.Scattering`, but the analytic continuation is not.
- The **thermodynamic limit**: the free energy per site of a statistical
  model.  The transfer-matrix algebra is proved in
  `LeanPhy.StatMech.TransferMatrix`, but the `N -> infinity` limit and the
  phase-transition analysis need the analytic layer.
- The general **actual-state Wick bridge**. Multi-field contraction recursions,
  finite fermionic signs and a single free-mode moment theorem are available;
  they do not prove that an arbitrary supplied many-body state is Gaussian or
  quasi-free, or satisfies the corresponding time-ordered moment formula.

Missing input should remain an explicit theorem parameter or registered open
obligation in the research development. Declaring a new axiom is not a substitute
for discharging that input: the complete library and project audits reject
application-specific axioms, including those reached through dependencies.

## How to read a LeanPhy theorem

When you see a theorem such as

```lean
theorem wick_even_moment (k : ℕ) : ω (φ ^ (2*k)) = (doubleFact k : ℂ)
```

read it as: *for any structure `M` of type `FreeMode` — that is, for any ring
with a pair of operators satisfying the CCR and any additive, normalised
functional annihilating the ladder directions — the equality holds.*  If your
physical situation satisfies those hypotheses, the conclusion is not merely
plausible; it is checked by the kernel.  If it does not, the theorem says
nothing about your situation, and that gap is the physics you still owe.

## Current worktree: nonautonomous driven response (2026-10-08)

`Quantum.TimeDependentEvolution` now represents an actual finite evolution by a common initial value and the differential equation `U' = -i H(t) U`. The kernel derives unitarity, adjoint transport, transport composition and uniqueness from those premises. It does not identify an inverse with negative-time evolution for a general drive.

`Quantum.DrivenResponse` compares an actual jointly continuous amplitude family and derives the two-time first response from the comparison integral. Initial-state and probe derivative contact terms are retained, switched reads are causal before the preparation time, and source changes outside the observed interval are proved irrelevant to the first response. `Quantum.DrivenPulse` constructs a continuous rotating-frame pulse family over an arbitrary background evolution and consumes it in the finite CAR/Gibbs client.

The canonical library, four domain entries and dynamics client build after this increment. `scripts/test_driven_response.py` passes three focused checks (client report, strict rejection of the still-open general ODE obligation, and an independently compiled public-family snippet). The client has 18 claims and three open obligations. The focused result does not certify general ODE existence, arbitrary laboratory-frame drives, finite-amplitude remainders, continuous frequency limits, unbounded operators or thermodynamic limits. A complete `scripts/verify.sh` run has not been claimed for this increment.
