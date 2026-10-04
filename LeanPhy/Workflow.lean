import LeanPhy.Quantum.Pauli
import LeanPhy.FieldTheory.CCR
import LeanPhy.FieldTheory.MultiWick
import LeanPhy.HighEnergy.Gamma
import LeanPhy.HighEnergy.EffectiveTheory
import LeanPhy.Mathematics.FiniteParabolic
import LeanPhy.Mathematics.FiniteEnergy
import LeanPhy.Mathematics.FinitePathReflection
import LeanPhy.Mathematics.Hilbert
import LeanPhy.Mathematics.SpectralCalculus
import LeanPhy.Mathematics.SpectralGap
import LeanPhy.Classical.Symplectic
import LeanPhy.Condensed.BCS
import LeanPhy.GaugeTheory.FieldStrength
import LeanPhy.Relativity.Minkowski
import LeanPhy.StatMech.FiniteGibbs
import LeanPhy.Mathematics.ExternalCertificate
import LeanPhy.Mathematics.ParametricModel
import LeanPhy.Entry.Optics
import LeanPhy.Entry.Fluid

/-!
# Research-package workflow

This module is the public boundary between the checked library and a physics
researcher's theory file.  A package is a small, inspectable ledger: prose
metadata records assumptions and scope boundaries, while every checked claim
contains an ordinary Lean proposition together with its kernel-checked proof;
open external obligations are tracked separately so a finite theorem is not
mistaken for a completed continuum result.
The reporting functions below only display an already compiled package; they
never turn a boolean or a string into evidence.

The interfaces are intentionally domain-neutral.  Quantum mechanics, finite
PDE/lattice models and finite Euclidean path models all submit the same package
shape, so a project can replace one model without changing its verification
and reporting workflow.
-/

namespace LeanPhy.Workflow

open scoped Matrix
open Polynomial

structure Assumption where
  name : String
  statement : String
  source : String
  deriving Repr

/- A proof-bearing model assumption.  The ordinary `Assumption` record remains
   metadata-only because many physical assumptions are deliberately discharged
   outside Lean.  When an assumption is available as an explicit proposition,
   this witness lets a package step consume its proof and still retain the
   human-readable ledger entry. -/
structure AssumptionWitness where
  metadata : Assumption
  proposition : Prop
  proof : proposition

structure ScopeBoundary where
  label : String
  explanation : String
  deriving Repr

/-- A research task that is deliberately outside the current kernel theorem
    layer.  It is tracked separately from a scope boundary so a project can
    distinguish “not claimed here” from “must be discharged before a physical
    conclusion is published”.  This structure contains no proof field. -/
structure ExternalObligation where
  name : String
  statement : String
  source : String
  deriving Repr

/- A typed view of an open research obligation.  `ExternalObligation` remains
   metadata-only for genuinely external analysis tasks, while this witness
   lets a project state the Lean proposition that a later bridge must prove.
   The proposition is intentionally proof-free here: it is an open goal until
   `resolveObligationWitness` receives its proof. -/
structure ExternalObligationWitness where
  metadata : ExternalObligation
  proposition : Prop

/-- Severity of a research-ledger diagnostic. Diagnostics concern the
    metadata graph only; a `CheckedClaim.proof` remains the source of
    mathematical trust. -/
inductive DiagnosticSeverity where
  | warning
  | error
  deriving Repr, DecidableEq

structure LedgerDiagnostic where
  code : String
  severity : DiagnosticSeverity
  entry : String
  message : String
  deriving Repr

/-- A heterogeneous entry in a theory ledger.  The proposition is stored as a
field so different claims can share one list; its proof field forces the Lean
kernel to check the corresponding proof term when the package is compiled. -/
structure CheckedClaim where
  name : String
  statement : String
  /-- Human-readable provenance.  This is metadata only; trust comes from
  the dependent `proof` field below. -/
  source : String
  /-- Names in the package assumption ledger that this claim consumes.  This
      is a cross-reference for audit tools; actual assumptions must still
      occur as hypotheses in `proposition`. -/
  requiredAssumptions : List String
  /-- Names of earlier ledger claims used in the derivation narrative.  Lean's
      proof term remains authoritative; this list makes the intended
      research-facing dependency graph inspectable. -/
  dependencies : List String
  /-- Names of registered models used by this claim.  This is an audit link;
      the dependent `proof` field remains the mathematical evidence. -/
  models : List String
  proposition : Prop
  proof : proposition

namespace CheckedClaim

/-- A deterministic local identifier for a claim.  It is metadata only: the
    proposition and its proof remain the dependent fields below.  Projects
    should use `ResearchProject.qualifiedClaimId` when a globally unique
    identifier is needed. -/
def stableId (c : CheckedClaim) : String :=
  "leanphy.claim:" ++ c.name

/-- A claim identifier qualified by its package. -/
def stableIdIn (packageName : String) (c : CheckedClaim) : String :=
  "leanphy.claim:" ++ packageName ++ "::" ++ c.name

def ofTheoremFromWithAssumptions (name statement source : String)
    (requiredAssumptions : List String) {P : Prop} (h : P) : CheckedClaim where
  name := name
  statement := statement
  source := source
  requiredAssumptions := requiredAssumptions
  dependencies := []
  models := []
  proposition := P
  proof := h

def ofTheoremFromWithDependencies (name statement source : String)
    (requiredAssumptions dependencies : List String) {P : Prop} (h : P) :
    CheckedClaim where
  name := name
  statement := statement
  source := source
  requiredAssumptions := requiredAssumptions
  dependencies := dependencies
  models := []
  proposition := P
  proof := h

def ofTheorem (name statement : String) {P : Prop} (h : P) : CheckedClaim :=
  ofTheoremFromWithAssumptions name statement "Lean theorem" [] h

def ofTheoremFrom (name statement source : String) {P : Prop} (h : P) :
    CheckedClaim :=
  ofTheoremFromWithAssumptions name statement source [] h

def ofTheoremWithAssumptions (name statement : String)
    (requiredAssumptions : List String) {P : Prop} (h : P) : CheckedClaim :=
  ofTheoremFromWithAssumptions name statement "Lean theorem"
    requiredAssumptions h

def ofTheoremWithDependencies (name statement : String)
    (requiredAssumptions dependencies : List String) {P : Prop} (h : P) :
    CheckedClaim :=
  ofTheoremFromWithDependencies name statement "Lean theorem"
    requiredAssumptions dependencies h

def withModels (c : CheckedClaim) (models : List String) : CheckedClaim :=
  { c with models := models }

def ofTheoremFromWithAssumptionsAndModels (name statement source : String)
    (requiredAssumptions models : List String) {P : Prop} (h : P) : CheckedClaim :=
  (ofTheoremFromWithAssumptions name statement source requiredAssumptions h).withModels models

def ofTheoremFromWithDependenciesAndModels (name statement source : String)
    (requiredAssumptions dependencies models : List String) {P : Prop} (h : P) :
    CheckedClaim :=
  withModels
    (ofTheoremFromWithDependencies name statement source requiredAssumptions dependencies h)
    models

/-- Promote a certificate only after its Lean-side checker has produced the
    proposition.  The envelope metadata is retained as provenance, while the
    dependent `proof` field remains the sole source of mathematical trust. -/
def ofVerifiedCertificate {P : Prop} {C : Type*}
    (checker : LeanPhy.Mathematics.CertificateChecker P C)
    (certificate : LeanPhy.Mathematics.VerifiedCertificate checker)
    (name statement source : String)
    (requiredAssumptions : List String) : CheckedClaim :=
  ofTheoremFromWithAssumptions name statement source requiredAssumptions
    (LeanPhy.Mathematics.VerifiedCertificate.proof checker certificate)

end CheckedClaim

/-! ## Typed model registrations

The proof-bearing model itself lives in `Mathematics.PhysicalModel` or
`Mathematics.ParametricModel`; heterogeneous research ledgers cannot store
those dependent values directly.  `ModelRegistration` is the stable metadata
boundary around such a model.  Its constructors accept a typed model, so a
registration cannot be created for a nonexistent interface, while the
registration remains serialisable and usable by a project containing many
different state and scalar types.
-/

structure ModelRegistration where
  name : String
  kind : String
  parameterSpace : String
  stateSpace : String
  observableSpace : String
  evolution : String
  assumptions : List String
  deriving Repr

namespace ModelRegistration

def stableId (M : ModelRegistration) : String :=
  "leanphy.model:" ++ M.name

def text (name kind parameterSpace stateSpace observableSpace evolution : String)
    (assumptions : List String) : ModelRegistration where
  name := name
  kind := kind
  parameterSpace := parameterSpace
  stateSpace := stateSpace
  observableSpace := observableSpace
  evolution := evolution
  assumptions := assumptions

def fromParametric {P R : Type*} (name kind parameterSpace stateSpace
    observableSpace evolution : String) (assumptions : List String)
    (_model : LeanPhy.Mathematics.ParametricModel P R) : ModelRegistration :=
  text name kind parameterSpace stateSpace observableSpace evolution assumptions

def fromPhysical {R : Type*} (name kind stateSpace observableSpace evolution : String)
    (assumptions : List String)
    (_model : LeanPhy.Mathematics.PhysicalModel R) : ModelRegistration :=
  text name kind "fixed" stateSpace observableSpace evolution assumptions

end ModelRegistration

structure TheoryPackage where
  name : String
  domain : String
  assumptions : List Assumption
  claims : List CheckedClaim
  models : List ModelRegistration
  outOfScope : List ScopeBoundary
  obligations : List ExternalObligation

namespace TheoryPackage

/-- A deterministic package identifier suitable for manifests and graph
    consumers.  Duplicate names are still rejected by the ledger diagnostics,
    so this function never hides an ambiguous package. -/
def stableId (P : TheoryPackage) : String :=
  "leanphy.package:" ++ P.name

def empty (name domain : String) : TheoryPackage where
  name := name
  domain := domain
  assumptions := []
  claims := []
  models := []
  outOfScope := []
  obligations := []

/- Start a package from a model declaration in one expression.  The list
   arguments are metadata only; checked mathematics still enters through
   `addClaim`/`addTheorem`, whose dependent proof field is kernel-checked. -/
def ofModel (name domain : String) (assumptions : List Assumption)
    (outOfScope : List ScopeBoundary) : TheoryPackage where
  name := name
  domain := domain
  assumptions := assumptions
  claims := []
  models := []
  outOfScope := outOfScope
  obligations := []

def addAssumption (P : TheoryPackage) (a : Assumption) : TheoryPackage :=
  { P with assumptions := P.assumptions ++ [a] }

def addAssumptionWitness (P : TheoryPackage) (w : AssumptionWitness) : TheoryPackage :=
  P.addAssumption w.metadata

def addBoundary (P : TheoryPackage) (b : ScopeBoundary) : TheoryPackage :=
  { P with outOfScope := P.outOfScope ++ [b] }

def addObligation (P : TheoryPackage) (o : ExternalObligation) : TheoryPackage :=
  { P with obligations := P.obligations ++ [o] }

def addClaim (P : TheoryPackage) (c : CheckedClaim) : TheoryPackage :=
  { P with claims := P.claims ++ [c] }

def addModel (P : TheoryPackage) (model : ModelRegistration) : TheoryPackage :=
  { P with models := P.models ++ [model] }

def addModelText (P : TheoryPackage)
    (name kind parameterSpace stateSpace observableSpace evolution : String)
    (assumptions : List String) : TheoryPackage :=
  P.addModel (ModelRegistration.text name kind parameterSpace stateSpace
    observableSpace evolution assumptions)

def modelNames (P : TheoryPackage) : List String :=
  P.models.map ModelRegistration.name

def addTheoremForModels (P : TheoryPackage) (modelNames : List String)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop} (h : Q) : TheoryPackage :=
  P.addClaim ((CheckedClaim.ofTheoremFromWithAssumptions
    name statement source requiredAssumptions h).withModels modelNames)

def addTheoremForModel (P : TheoryPackage) (modelName : String)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop} (h : Q) : TheoryPackage :=
  P.addTheoremForModels [modelName] name statement source requiredAssumptions h

/-! ## Elaboration-time registration guards

The metadata report deliberately keeps a string based boundary so packages can
be merged and serialised.  A research file should nevertheless be able to ask
Lean to reject a misspelled local model before it reaches the report command.
The following constructors take an explicit membership proof.  For a concrete
package this is normally discharged with `by simp [package, ...]`; for a
cross-package link the project-level diagnostics remain the appropriate check.
The proof is only a ledger guard: the theorem's dependent `proof` field still
contains the mathematical evidence.
-/

def addModelTextRegistered (P : TheoryPackage)
    (name kind parameterSpace stateSpace observableSpace evolution : String)
    (assumptions : List String)
    (_assumptionsRegistered : ∀ assumption ∈ assumptions,
      assumption ∈ P.assumptions.map Assumption.name) : TheoryPackage :=
  P.addModelText name kind parameterSpace stateSpace observableSpace evolution assumptions

def addTheoremForModelsRegistered (P : TheoryPackage) (modelNames : List String)
    (_modelsRegistered : ∀ modelName ∈ modelNames, modelName ∈ P.modelNames)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop} (h : Q) : TheoryPackage :=
  P.addTheoremForModels modelNames name statement source requiredAssumptions h

def addTheoremForModelRegistered (P : TheoryPackage) (modelName : String)
    (registered : modelName ∈ P.modelNames)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop} (h : Q) : TheoryPackage :=
  P.addTheoremForModelsRegistered [modelName]
    (by
      intro candidate hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact registered
      · simp at hc)
    name statement source requiredAssumptions h

def addTheoremWithAssumptionsRegistered (P : TheoryPackage)
    (requiredAssumptions : List String)
    (_assumptionsRegistered : ∀ assumption ∈ requiredAssumptions,
      assumption ∈ P.assumptions.map Assumption.name)
    (name statement source : String) {Q : Prop} (h : Q) : TheoryPackage :=
  P.addClaim (CheckedClaim.ofTheoremFromWithAssumptions
    name statement source requiredAssumptions h)

def addTheoremWithDependenciesRegistered (P : TheoryPackage)
    (dependencies : List String)
    (_dependenciesRegistered : ∀ dependency ∈ dependencies,
      dependency ∈ P.claims.map CheckedClaim.name)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop} (h : Q) : TheoryPackage :=
  P.addClaim (CheckedClaim.ofTheoremFromWithDependencies
    name statement source requiredAssumptions dependencies h)

def addParametricModel {P R : Type*} (package : TheoryPackage)
    (modelName kind parameterSpace stateSpace observableSpace evolution : String)
    (assumptions : List String) (model : LeanPhy.Mathematics.ParametricModel P R) :
    TheoryPackage :=
  package.addModel (ModelRegistration.fromParametric modelName kind parameterSpace
    stateSpace observableSpace evolution assumptions model)

def addPhysicalModel {R : Type*} (package : TheoryPackage)
    (modelName kind stateSpace observableSpace evolution : String)
    (assumptions : List String) (model : LeanPhy.Mathematics.PhysicalModel R) :
    TheoryPackage :=
  package.addModel (ModelRegistration.fromPhysical modelName kind stateSpace
    observableSpace evolution assumptions model)

def addTheorem (P : TheoryPackage) (name statement source : String)
    {Q : Prop} (h : Q) : TheoryPackage :=
  P.addClaim (CheckedClaim.ofTheoremFrom name statement source h)

def addTheoremWithAssumptions (P : TheoryPackage)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop} (h : Q) : TheoryPackage :=
  P.addClaim (CheckedClaim.ofTheoremFromWithAssumptions
    name statement source requiredAssumptions h)

def addTheoremWithDependencies (P : TheoryPackage)
    (name statement source : String) (requiredAssumptions dependencies : List String)
    {Q : Prop} (h : Q) : TheoryPackage :=
  P.addClaim (CheckedClaim.ofTheoremFromWithDependencies
    name statement source requiredAssumptions dependencies h)

/-- Insert a theorem obtained from a proof-producing external certificate. -/
def addExternalCertificate {P : Prop} {C : Type*} (Pckg : TheoryPackage)
    (checker : LeanPhy.Mathematics.CertificateChecker P C)
    (certificate : LeanPhy.Mathematics.VerifiedCertificate checker)
    (name statement source : String)
    (requiredAssumptions : List String) : TheoryPackage :=
  Pckg.addClaim (CheckedClaim.ofVerifiedCertificate checker certificate
    name statement source requiredAssumptions)

/-- Add a derived theorem while generating the dependency link from the
    preceding checked claim. This keeps the paper-style derivation chain
    inspectable without asking users to repeat a string name by hand. -/
def addTheoremAfter (P : TheoryPackage) (prior : CheckedClaim)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop} (h : Q) : TheoryPackage :=
  P.addClaim (CheckedClaim.ofTheoremFromWithDependencies
    name statement source requiredAssumptions [prior.name] h)

/- A proof-producing variant of `addTheoremAfter`.  The older function is
   useful when a paper step is already proved elsewhere and only its provenance
   needs recording.  This variant makes the dependency semantic: the caller
   supplies a function from the previous claim's proposition to the new one,
   and the package stores the result of applying that function to the previous
   claim's kernel-checked proof.  Consequently a later step cannot merely
   mention a predecessor in metadata while silently proving an unrelated
   proposition. -/
def addDerivedTheorem (P : TheoryPackage) (prior : CheckedClaim)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop} (derive : prior.proposition → Q) : TheoryPackage :=
  P.addClaim
    { name := name
      statement := statement
      source := source
      requiredAssumptions := requiredAssumptions
      dependencies := [prior.name]
      models := []
      proposition := Q
      proof := derive prior.proof }

def addDerivedTheoremForModels (P : TheoryPackage) (prior : CheckedClaim)
    (modelNames : List String)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop} (derive : prior.proposition → Q) : TheoryPackage :=
  P.addClaim (({
      name := name
      statement := statement
      source := source
      requiredAssumptions := requiredAssumptions
      dependencies := [prior.name]
      models := modelNames
      proposition := Q
      proof := derive prior.proof } : CheckedClaim))

/- The explicit name makes the proof-level nature discoverable in editors and
   keeps a migration path for projects that already use `addTheoremAfter`. -/
def addTheoremAfterProof (P : TheoryPackage) (prior : CheckedClaim)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop} (derive : prior.proposition → Q) : TheoryPackage :=
  P.addDerivedTheorem prior name statement source requiredAssumptions derive

/- A registered variant closes a metadata gap that is easy to hit in a long
   research file: the predecessor value must actually occur in the current
   package before a local dependency can be added.  The membership proof is
   checked during elaboration; the proposition proof is still supplied to
   `addDerivedTheorem`, so this adds an audit guard without weakening trust. -/
def addDerivedTheoremRegistered (P : TheoryPackage) (prior : CheckedClaim)
    (_registered : prior.name ∈ P.claims.map CheckedClaim.name)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop} (derive : prior.proposition → Q) : TheoryPackage :=
  P.addDerivedTheorem prior name statement source requiredAssumptions derive

/- The two-predecessor form covers the common case in which a paper step
   combines, for example, an algebraic identity with a conservation lemma.
   Both predecessor proof terms are passed to `derive`; the dependency list is
   generated at the same time, so metadata and kernel evidence cannot drift
   apart. -/
def addDerivedTheorem2 (P : TheoryPackage)
    (first second : CheckedClaim)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop}
    (derive : first.proposition → second.proposition → Q) : TheoryPackage :=
  P.addClaim
    { name := name
      statement := statement
      source := source
      requiredAssumptions := requiredAssumptions
      dependencies := [first.name, second.name]
      models := []
      proposition := Q
      proof := derive first.proof second.proof }

def addDerivedTheorem2ForModels (P : TheoryPackage)
    (first second : CheckedClaim) (modelNames : List String)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop}
    (derive : first.proposition → second.proposition → Q) : TheoryPackage :=
  P.addClaim (({
      name := name
      statement := statement
      source := source
      requiredAssumptions := requiredAssumptions
      dependencies := [first.name, second.name]
      models := modelNames
      proposition := Q
      proof := derive first.proof second.proof } : CheckedClaim))

def addTheoremAfterProof2 (P : TheoryPackage)
    (first second : CheckedClaim)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop}
    (derive : first.proposition → second.proposition → Q) : TheoryPackage :=
  P.addDerivedTheorem2 first second name statement source requiredAssumptions derive

def addDerivedTheorem2Registered (P : TheoryPackage)
    (first second : CheckedClaim)
    (_firstRegistered : first.name ∈ P.claims.map CheckedClaim.name)
    (_secondRegistered : second.name ∈ P.claims.map CheckedClaim.name)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop}
    (derive : first.proposition → second.proposition → Q) : TheoryPackage :=
  P.addDerivedTheorem2 first second name statement source requiredAssumptions derive

/- Proof-producing assumption APIs.  The caller explicitly registers the
   witness with `addAssumptionWitness`; omitting that registration leaves a
   missing-assumption diagnostic in the package report, while the theorem proof
   itself still consumes the witness's proposition. -/
def addTheoremUnderAssumption (P : TheoryPackage) (w : AssumptionWitness)
    (name statement source : String) {Q : Prop}
    (derive : w.proposition → Q) : TheoryPackage :=
  P.addClaim
    { name := name
      statement := statement
      source := source
      requiredAssumptions := [w.metadata.name]
      dependencies := []
      models := []
      proposition := Q
      proof := derive w.proof }

def addTheoremUnderAssumptions2 (P : TheoryPackage)
    (first second : AssumptionWitness)
    (name statement source : String) {Q : Prop}
    (derive : first.proposition → second.proposition → Q) : TheoryPackage :=
  P.addClaim
    { name := name
      statement := statement
      source := source
      requiredAssumptions := [first.metadata.name, second.metadata.name]
      dependencies := []
      models := []
      proposition := Q
      proof := derive first.proof second.proof }

/-- Register a proof-bearing assumption and consume it in one operation.

The older `addAssumptionWitness` followed by `addTheoremUnderAssumption`
remains available for ledgers that intentionally keep registration and proof
steps separate.  This convenience constructor is the safer default for a
research notebook: the metadata link and the proposition consumed by the
proof cannot accidentally be separated. -/
def addTheoremUnderAssumptionRegistered (P : TheoryPackage)
    (w : AssumptionWitness) (name statement source : String) {Q : Prop}
    (derive : w.proposition → Q) : TheoryPackage :=
  (P.addAssumptionWitness w).addTheoremUnderAssumption w
    name statement source derive

def addTheoremUnderAssumptions2Registered (P : TheoryPackage)
    (first second : AssumptionWitness)
    (name statement source : String) {Q : Prop}
    (derive : first.proposition → second.proposition → Q) : TheoryPackage :=
  ((P.addAssumptionWitness first).addAssumptionWitness second)
    |>.addTheoremUnderAssumptions2 first second name statement source derive

/-- Close an external research obligation with a kernel-checked claim.

The membership proof is deliberate: resolving a misspelled obligation name is
an elaboration error, rather than a silent metadata edit.  The new claim is
ordinary dependent Lean data, so the external obligation is removed only when
the supplied proof term has already type-checked. -/
def resolveObligation (P : TheoryPackage) (obligationName : String)
    (_registered : obligationName ∈ P.obligations.map ExternalObligation.name)
    (name statement source : String) (requiredAssumptions dependencies : List String)
    {Q : Prop} (proof : Q) : TheoryPackage :=
  let claim : CheckedClaim :=
    { name := name
      statement := statement
      source := source
      requiredAssumptions := requiredAssumptions
      dependencies := dependencies
      models := []
      proposition := Q
      proof := proof }
  { P with
      claims := P.claims ++ [claim]
      obligations := P.obligations.filter (fun obligation =>
        obligation.name != obligationName) }

/- Close a typed obligation through a proof-producing derivation.  Unlike the
   legacy metadata-only `resolveObligation`, this API cannot accept an
   unrelated proposition: the supplied derivation must consume the explicit
   `witness.proposition` proof.  This is the recommended interface for a
   numerical convergence, self-adjointness, or continuum bridge that has
   reached the Lean layer. -/
def resolveObligationWitness (P : TheoryPackage)
    (witness : ExternalObligationWitness)
    (_registered : witness.metadata.name ∈
      P.obligations.map ExternalObligation.name)
    (name statement source : String)
    (requiredAssumptions dependencies : List String)
    {Q : Prop} (derive : witness.proposition → Q)
    (proof : witness.proposition) : TheoryPackage :=
  let claim : CheckedClaim :=
    { name := name
      statement := statement
      source := source
      requiredAssumptions := requiredAssumptions
      dependencies := dependencies
      models := []
      proposition := Q
      proof := derive proof }
  { P with
      claims := P.claims ++ [claim]
      obligations := P.obligations.filter (fun obligation =>
        obligation.name != witness.metadata.name) }

def addAssumptionText (P : TheoryPackage)
    (name statement source : String) : TheoryPackage :=
  P.addAssumption { name := name, statement := statement, source := source }

def addBoundaryText (P : TheoryPackage)
    (label explanation : String) : TheoryPackage :=
  P.addBoundary { label := label, explanation := explanation }

def addObligationText (P : TheoryPackage)
    (name statement source : String) : TheoryPackage :=
  P.addObligation { name := name, statement := statement, source := source }

/-- Combine independently developed ledgers while retaining every entry. -/
def append (P Q : TheoryPackage) : TheoryPackage where
  name := P.name ++ " + " ++ Q.name
  domain := P.domain ++ " / " ++ Q.domain
  assumptions := P.assumptions ++ Q.assumptions
  claims := P.claims ++ Q.claims
  models := P.models ++ Q.models
  outOfScope := P.outOfScope ++ Q.outOfScope
  obligations := P.obligations ++ Q.obligations

def assumptionCount (P : TheoryPackage) : Nat := P.assumptions.length

def claimCount (P : TheoryPackage) : Nat := P.claims.length

def boundaryCount (P : TheoryPackage) : Nat := P.outOfScope.length

def obligationCount (P : TheoryPackage) : Nat := P.obligations.length

def assumptionNames (P : TheoryPackage) : List String :=
  P.assumptions.map Assumption.name

/- Metadata links are intentionally checked separately from propositions.  A
   misspelled ledger name cannot invalidate a Lean theorem, but it must be
   visible to a reviewer instead of silently disappearing from the report. -/
def missingAssumptionReferences (P : TheoryPackage) : List String :=
  List.flatMap (fun c =>
    c.requiredAssumptions.filter (fun required =>
      !(P.assumptionNames.contains required))) P.claims

def missingAssumptionReferenceCount (P : TheoryPackage) : Nat :=
  P.missingAssumptionReferences.length

def missingModelReferences (P : TheoryPackage) : List String :=
  List.flatMap (fun c =>
    c.models.filter (fun model => !(P.modelNames.contains model))) P.claims

def missingModelReferenceCount (P : TheoryPackage) : Nat :=
  P.missingModelReferences.length

def missingModelAssumptionReferences (P : TheoryPackage) : List String :=
  List.flatMap (fun model =>
    model.assumptions.filter (fun assumption =>
      !(P.assumptionNames.contains assumption))) P.models

def missingModelAssumptionReferenceCount (P : TheoryPackage) : Nat :=
  P.missingModelAssumptionReferences.length

def claimNames (P : TheoryPackage) : List String :=
  P.claims.map CheckedClaim.name

private def hasQualifiedMarkerAux : List Char → Bool
  | [] => false
  | first :: rest =>
      match rest with
      | [] => false
      | second :: _ =>
          if first = ':' && second = ':' then true
          else hasQualifiedMarkerAux rest

private def hasQualifiedMarker (dependency : String) : Bool :=
  hasQualifiedMarkerAux dependency.toList

def missingClaimReferences (P : TheoryPackage) : List String :=
  List.flatMap (fun c =>
    c.dependencies.filter (fun dependency =>
      !hasQualifiedMarker dependency && !(P.claimNames.contains dependency))) P.claims

def missingClaimReferenceCount (P : TheoryPackage) : Nat :=
  P.missingClaimReferences.length

/-! ## Ledger quality checks

The dependent proof field checks the mathematics, while these small checks
protect the research-facing index around it. Keeping the two layers separate
means a typo in a provenance string cannot manufacture a theorem, but it also
cannot silently disappear from a review report. -/

private def duplicateNames : List String → List String → List String
  | _, [] => []
  | seen, name :: rest =>
      let tail := duplicateNames (name :: seen) rest
      if seen.contains name then
        if tail.contains name then tail else name :: tail
      else tail

private def nameIndex (name : String) : List String → Nat → Option Nat
  | [], _ => none
  | candidate :: rest, index =>
      if candidate = name then some index
      else nameIndex name rest (index + 1)

private def duplicateDiagnostics (kind : String) (names : List String) :
    List LedgerDiagnostic :=
  (duplicateNames [] names).map (fun name =>
    { code := "duplicate-" ++ kind
      severity := .error
      entry := name
      message := "重复的" ++ kind ++ "名称；请使用稳定且唯一的标识" })

private def dependencyDiagnostics (names : List String)
    (claims : List CheckedClaim) (index : Nat) : List LedgerDiagnostic :=
  match claims with
  | [] => []
  | claim :: rest =>
      let current := claim.name
      let own := claim.dependencies.filterMap (fun dependency =>
        if dependency = current then
          some { code := "self-dependency"
                 severity := .error
                 entry := current
                 message := "结论不能依赖自身" }
        else
          match nameIndex dependency names 0 with
          | none => none
          | some dependencyIndex =>
              if index ≤ dependencyIndex then
                some { code := "forward-dependency"
                       severity := .error
                       entry := current
                       message := "依赖的结论必须先于当前结论登记：" ++ dependency }
              else none)
      own ++ dependencyDiagnostics names rest (index + 1)

private def obligationDiagnostics (names : List String) : List LedgerDiagnostic :=
  (duplicateNames [] names).map (fun name =>
    { code := "duplicate-obligation"
      severity := .error
      entry := name
      message := "重复的外部义务名称；请为每个义务分配唯一标识" })

/-- All structural diagnostics for a theory package. This does not inspect
    proof terms (Lean already did that during elaboration); it validates the
    names and ordering used by research tooling. -/
def diagnostics (P : TheoryPackage) : List LedgerDiagnostic :=
  let assumptionNames := P.assumptionNames
  let claimNames := P.claimNames
  let obligationNames := P.obligations.map ExternalObligation.name
  let missingAssumptions := P.missingAssumptionReferences.map (fun name =>
    { code := "missing-assumption"
      severity := .error
      entry := name
      message := "结论引用了未登记的假设" })
  let missingClaims := P.missingClaimReferences.map (fun name =>
    { code := "missing-claim"
      severity := .error
      entry := name
      message := "结论引用了未登记的前置结论" })
  let missingModels := P.missingModelReferences.map (fun name =>
    { code := "missing-model"
      severity := .error
      entry := name
      message := "结论引用了未登记的模型" })
  let missingModelAssumptions := P.missingModelAssumptionReferences.map (fun name =>
    { code := "missing-model-assumption"
      severity := .error
      entry := name
      message := "模型引用了未登记的假设" })
  duplicateDiagnostics "assumption" assumptionNames ++
    duplicateDiagnostics "claim" claimNames ++
    duplicateDiagnostics "model" P.modelNames ++
    obligationDiagnostics obligationNames ++
    missingAssumptions ++ missingClaims ++ missingModels ++ missingModelAssumptions ++
    dependencyDiagnostics claimNames P.claims 0

def diagnosticCount (P : TheoryPackage) : Nat := P.diagnostics.length

def errorDiagnostics (P : TheoryPackage) : List LedgerDiagnostic :=
  P.diagnostics.filter (fun diagnostic => diagnostic.severity == .error)

def hasErrors (P : TheoryPackage) : Bool := !P.errorDiagnostics.isEmpty

def isWellFormed (P : TheoryPackage) : Bool := !P.hasErrors

def status (P : TheoryPackage) : String :=
  if P.hasErrors then "INVALID-LEDGER"
  else if P.claims.isEmpty then "UNVERIFIED" else "VERIFIED-CONDITIONAL"

private def renderAssumptions : List Assumption → String
  | [] => ""
  | a :: rest => s!"  - {a.name}: {a.statement} [{a.source}]\n" ++
      renderAssumptions rest

private def renderClaims : List CheckedClaim → String
  | [] => ""
  | c :: rest => s!"  - {c.name}: {c.statement} [{c.source}]" ++
      (if c.requiredAssumptions.isEmpty then "" else
        " (requires " ++ String.intercalate ", " c.requiredAssumptions ++ ")") ++
      (if c.dependencies.isEmpty then "" else
        " (depends on " ++ String.intercalate ", " c.dependencies ++ ")") ++
      (if c.models.isEmpty then "" else
        " (models " ++ String.intercalate ", " c.models ++ ")") ++
      "\n" ++
      renderClaims rest

private def renderModels : List ModelRegistration → String
  | [] => ""
  | m :: rest => s!"  - {m.name}: {m.kind}; parameters={m.parameterSpace}; state={m.stateSpace}; observables={m.observableSpace}; evolution={m.evolution}\n" ++
      renderModels rest

private def renderBoundaries : List ScopeBoundary → String
  | [] => ""
  | b :: rest => s!"  - {b.label}: {b.explanation}\n" ++
      renderBoundaries rest

private def renderObligations : List ExternalObligation → String
  | [] => ""
  | o :: rest => s!"  - {o.name}: {o.statement} [{o.source}]\n" ++
      renderObligations rest

private def severityText : DiagnosticSeverity → String
  | .warning => "warning"
  | .error => "error"

private def renderDiagnostics : List LedgerDiagnostic → String
  | [] => ""
  | diagnostic :: rest =>
      s!"  - [{severityText diagnostic.severity}] {diagnostic.code} " ++
        s!"({diagnostic.entry}): {diagnostic.message}\n" ++
        renderDiagnostics rest

/-! The text report is intended for a researcher reading a build log.  The
    JSON report below is deliberately implemented without a serializer or a
    runtime reflection trick: it is a pure rendering of already elaborated
    values.  In particular, the literal `"kernel_checked"` marker is emitted
    only for entries whose dependent `proof` field made the package compile. -/

private def jsonHex4 (n : Nat) : String :=
  let digits := Nat.toDigits 16 n
  String.ofList (List.replicate (4 - digits.length) '0' ++ digits)

private def jsonEscapeChar (c : Char) : String :=
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c = '\n' then "\\n"
  else if c = '\r' then "\\r"
  else if c = '\t' then "\\t"
  else if c.toNat < 32 then "\\u" ++ jsonHex4 c.toNat
  else c.toString

private def jsonEscape (s : String) : String :=
  (s.toList.map jsonEscapeChar).foldl (· ++ ·) ""

def jsonString (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

def renderStringListJson : List String → String
  | [] => ""
  | [s] => jsonString s
  | s :: rest => jsonString s ++ "," ++ renderStringListJson rest

private def renderAssumptionsJson : List Assumption → String
  | [] => ""
  | [a] => "{" ++ jsonString "name" ++ ":" ++ jsonString a.name ++
      "," ++ jsonString "statement" ++ ":" ++ jsonString a.statement ++
      "," ++ jsonString "source" ++ ":" ++ jsonString a.source ++ "}"
  | a :: rest =>
      ("{" ++ jsonString "name" ++ ":" ++ jsonString a.name ++
        "," ++ jsonString "statement" ++ ":" ++ jsonString a.statement ++
        "," ++ jsonString "source" ++ ":" ++ jsonString a.source ++ "},") ++
        renderAssumptionsJson rest

private def renderClaimsJson (packageName : String) : List CheckedClaim → String
  | [] => ""
  | [c] => "{" ++ jsonString "name" ++ ":" ++ jsonString c.name ++
      "," ++ jsonString "id" ++ ":" ++ jsonString (c.stableIdIn packageName) ++
      "," ++ jsonString "statement" ++ ":" ++ jsonString c.statement ++
      "," ++ jsonString "source" ++ ":" ++ jsonString c.source ++
      "," ++ jsonString "requires" ++ ":[" ++
        renderStringListJson c.requiredAssumptions ++ "]" ++
      "," ++ jsonString "depends_on" ++ ":[" ++
        renderStringListJson c.dependencies ++ "]" ++
      "," ++ jsonString "models" ++ ":[" ++
        renderStringListJson c.models ++ "]" ++
      "," ++ jsonString "status" ++ ":" ++ jsonString "kernel_checked" ++ "}"
  | c :: rest =>
      ("{" ++ jsonString "name" ++ ":" ++ jsonString c.name ++
        "," ++ jsonString "id" ++ ":" ++ jsonString (c.stableIdIn packageName) ++
        "," ++ jsonString "statement" ++ ":" ++ jsonString c.statement ++
        "," ++ jsonString "source" ++ ":" ++ jsonString c.source ++
        "," ++ jsonString "requires" ++ ":[" ++
          renderStringListJson c.requiredAssumptions ++ "]" ++
        "," ++ jsonString "depends_on" ++ ":[" ++
          renderStringListJson c.dependencies ++ "]" ++
        "," ++ jsonString "models" ++ ":[" ++
          renderStringListJson c.models ++ "]" ++
        "," ++ jsonString "status" ++ ":" ++ jsonString "kernel_checked" ++ "},") ++
        renderClaimsJson packageName rest

private def renderBoundariesJson : List ScopeBoundary → String
  | [] => ""
  | [b] => "{" ++ jsonString "label" ++ ":" ++ jsonString b.label ++
      "," ++ jsonString "explanation" ++ ":" ++ jsonString b.explanation ++ "}"
  | b :: rest =>
      ("{" ++ jsonString "label" ++ ":" ++ jsonString b.label ++
        "," ++ jsonString "explanation" ++ ":" ++ jsonString b.explanation ++ "},") ++
        renderBoundariesJson rest

private def renderObligationsJson : List ExternalObligation → String
  | [] => ""
  | [o] => "{" ++ jsonString "name" ++ ":" ++ jsonString o.name ++
      "," ++ jsonString "statement" ++ ":" ++ jsonString o.statement ++
      "," ++ jsonString "source" ++ ":" ++ jsonString o.source ++ "}"
  | o :: rest =>
      ("{" ++ jsonString "name" ++ ":" ++ jsonString o.name ++
        "," ++ jsonString "statement" ++ ":" ++ jsonString o.statement ++
        "," ++ jsonString "source" ++ ":" ++ jsonString o.source ++ "},") ++
        renderObligationsJson rest

private def renderModelsJson : List ModelRegistration → String
  | [] => ""
  | [m] => "{" ++ jsonString "name" ++ ":" ++ jsonString m.name ++
      "," ++ jsonString "id" ++ ":" ++ jsonString m.stableId ++
      "," ++ jsonString "kind" ++ ":" ++ jsonString m.kind ++
      "," ++ jsonString "parameter_space" ++ ":" ++ jsonString m.parameterSpace ++
      "," ++ jsonString "state_space" ++ ":" ++ jsonString m.stateSpace ++
      "," ++ jsonString "observable_space" ++ ":" ++ jsonString m.observableSpace ++
      "," ++ jsonString "evolution" ++ ":" ++ jsonString m.evolution ++
      "," ++ jsonString "assumptions" ++ ":[" ++
        renderStringListJson m.assumptions ++ "]}"
  | m :: rest =>
      ("{" ++ jsonString "name" ++ ":" ++ jsonString m.name ++
        "," ++ jsonString "id" ++ ":" ++ jsonString m.stableId ++
        "," ++ jsonString "kind" ++ ":" ++ jsonString m.kind ++
        "," ++ jsonString "parameter_space" ++ ":" ++ jsonString m.parameterSpace ++
        "," ++ jsonString "state_space" ++ ":" ++ jsonString m.stateSpace ++
        "," ++ jsonString "observable_space" ++ ":" ++ jsonString m.observableSpace ++
        "," ++ jsonString "evolution" ++ ":" ++ jsonString m.evolution ++
        "," ++ jsonString "assumptions" ++ ":[" ++
          renderStringListJson m.assumptions ++ "]},") ++
        renderModelsJson rest

private def renderDiagnosticsJson : List LedgerDiagnostic → String
  | [] => ""
  | [diagnostic] => "{" ++ jsonString "code" ++ ":" ++
      jsonString diagnostic.code ++ "," ++ jsonString "severity" ++ ":" ++
      jsonString (severityText diagnostic.severity) ++ "," ++
      jsonString "entry" ++ ":" ++ jsonString diagnostic.entry ++ "," ++
      jsonString "message" ++ ":" ++ jsonString diagnostic.message ++ "}"
  | diagnostic :: rest =>
      ("{" ++ jsonString "code" ++ ":" ++ jsonString diagnostic.code ++ "," ++
        jsonString "severity" ++ ":" ++
        jsonString (severityText diagnostic.severity) ++ "," ++
        jsonString "entry" ++ ":" ++ jsonString diagnostic.entry ++ "," ++
        jsonString "message" ++ ":" ++ jsonString diagnostic.message ++ "},") ++
        renderDiagnosticsJson rest

/-- Render a human-readable report from compiled package metadata. -/
def render (P : TheoryPackage) : String :=
  s!"Theory: {P.name}\n" ++
  s!"Domain: {P.domain}\n" ++
  s!"Assumptions: {P.assumptionCount}\n" ++
  renderAssumptions P.assumptions ++
  s!"Registered models: {P.models.length}\n" ++
  renderModels P.models ++
  s!"Kernel-checked claims: {P.claimCount}\n" ++
  renderClaims P.claims ++
  s!"Unresolved assumption links: {P.missingAssumptionReferenceCount}\n" ++
  s!"Unresolved model links: {P.missingModelReferenceCount}\n" ++
  s!"Unresolved model-assumption links: {P.missingModelAssumptionReferenceCount}\n" ++
  s!"Unresolved claim links: {P.missingClaimReferenceCount}\n" ++
  s!"Open external obligations: {P.obligationCount}\n" ++
  renderObligations P.obligations ++
  s!"Ledger diagnostics: {P.diagnosticCount}\n" ++
  renderDiagnostics P.diagnostics ++
  s!"Explicitly out of scope: {P.boundaryCount}\n" ++
  renderBoundaries P.outOfScope ++
  s!"Status: {P.status}\n"

/- A stable, machine-readable projection for CI dashboards and downstream
   research notebooks.  Proposition terms are intentionally not serialized:
   their presence and validity are guaranteed by the compiled `CheckedClaim`,
   while the JSON carries names, statements, provenance and scope metadata. -/
def renderJson (P : TheoryPackage) : String :=
  "{" ++ jsonString "name" ++ ":" ++ jsonString P.name ++
    "," ++ jsonString "id" ++ ":" ++ jsonString P.stableId ++
    "," ++ jsonString "domain" ++ ":" ++ jsonString P.domain ++
    "," ++ jsonString "status" ++ ":" ++ jsonString P.status ++
    "," ++ jsonString "unresolved_assumption_links" ++ ":[" ++
      renderStringListJson P.missingAssumptionReferences ++ "]," ++
    jsonString "unresolved_model_links" ++ ":[" ++
      renderStringListJson P.missingModelReferences ++ "]," ++
    jsonString "unresolved_model_assumption_links" ++ ":[" ++
      renderStringListJson P.missingModelAssumptionReferences ++ "]," ++
    jsonString "unresolved_claim_links" ++ ":[" ++
      renderStringListJson P.missingClaimReferences ++ "]," ++
    jsonString "assumptions" ++ ":[" ++
      renderAssumptionsJson P.assumptions ++ "]," ++
    jsonString "models" ++ ":[" ++ renderModelsJson P.models ++ "]," ++
    jsonString "claims" ++ ":[" ++ renderClaimsJson P.name P.claims ++ "]," ++
    jsonString "diagnostics" ++ ":[" ++ renderDiagnosticsJson P.diagnostics ++ "]," ++
    jsonString "open_obligations" ++ ":[" ++
      renderObligationsJson P.obligations ++ "]," ++
    jsonString "out_of_scope" ++ ":[" ++ renderBoundariesJson P.outOfScope ++ "]}"

def summary (P : TheoryPackage) : String :=
  s!"Theory: {P.name}\n" ++
  s!"Domain: {P.domain}\n" ++
  s!"Assumptions: {P.assumptionCount}\n" ++
  s!"Registered models: {P.models.length}\n" ++
  s!"Kernel-checked claims: {P.claimCount}\n" ++
  s!"Explicitly out of scope: {P.boundaryCount}\n" ++
  s!"Status: {P.status}"

end TheoryPackage

/-! ## Multi-package research projects

Actual papers often combine a quantum model, a lattice discretisation and a
statistical post-processing argument. `ResearchProject` keeps those ledgers
separate while providing one validation boundary for CI and notebooks. -/

structure ResearchProject where
  name : String
  packages : List TheoryPackage

namespace ResearchProject

/-- Schema version for machine-readable project and manifest reports.  It is
    intentionally a literal so downstream CI can pin a report contract. -/
def schemaVersion : String := "1"

def empty (name : String) : ResearchProject := { name := name, packages := [] }

def ofPackages (name : String) (packages : List TheoryPackage) : ResearchProject :=
  { name := name, packages := packages }

def addPackage (P : ResearchProject) (package : TheoryPackage) : ResearchProject :=
  { P with packages := P.packages ++ [package] }

private def replacePackageByName (name : String) (replacement : TheoryPackage) :
    List TheoryPackage → List TheoryPackage
  | [] => [replacement]
  | package :: rest =>
      if package.name = name then replacement :: rest
      else package :: replacePackageByName name replacement rest

def packageCount (P : ResearchProject) : Nat := P.packages.length

def claimCount (P : ResearchProject) : Nat :=
  P.packages.foldl (fun n package => n + package.claimCount) 0

/-! A project-level claim index.  The proof-bearing `CheckedClaim` remains in
   the returned value, so this index is safe to use from Lean code as well as
   from the JSON projection below.  Search only filters claims that already
   elaborated; it never interprets a statement string as a proposition. -/

structure IndexedClaim where
  package : String
  claim : CheckedClaim

private def containsSub (needle haystack : String) : Bool :=
  if needle.isEmpty then true
  else
    let n := needle.toList
    let rec loop : List Char → Bool
      | [] => false
      | rest@(_ :: tail) =>
          if n.isPrefixOf rest then true else loop tail
    loop haystack.toList

private def claimMatches (query : String) (entry : IndexedClaim) : Bool :=
  query.isEmpty ||
    containsSub query entry.package ||
    containsSub query entry.claim.name ||
    containsSub query entry.claim.statement ||
    containsSub query entry.claim.source ||
    entry.claim.requiredAssumptions.any (containsSub query) ||
    entry.claim.dependencies.any (containsSub query) ||
    entry.claim.models.any (containsSub query)

def indexedClaims (P : ResearchProject) : List IndexedClaim :=
  P.packages.flatMap (fun package =>
    package.claims.map (fun claim => { package := package.name, claim := claim }))

/-- Search the compiled project claims by package, name, statement, source,
    assumptions, dependencies or model tags.  The result still contains the
    original dependent proof field, which makes accidental “metadata-only”
    use visible to Lean callers. -/
def searchClaims (P : ResearchProject) (query : String := "") : List IndexedClaim :=
  (P.indexedClaims).filter (claimMatches query)

private def renderIndexedClaimJson (entry : IndexedClaim) : String :=
  let c := entry.claim
  "{" ++ TheoryPackage.jsonString "package" ++ ":" ++
    TheoryPackage.jsonString entry.package ++
    "," ++ TheoryPackage.jsonString "name" ++ ":" ++
    TheoryPackage.jsonString c.name ++
    "," ++ TheoryPackage.jsonString "id" ++ ":" ++
    TheoryPackage.jsonString (CheckedClaim.stableIdIn entry.package c) ++
    "," ++ TheoryPackage.jsonString "statement" ++ ":" ++
    TheoryPackage.jsonString c.statement ++
    "," ++ TheoryPackage.jsonString "source" ++ ":" ++
    TheoryPackage.jsonString c.source ++
    "," ++ TheoryPackage.jsonString "requires" ++ ":[" ++
    TheoryPackage.renderStringListJson c.requiredAssumptions ++ "]" ++
    "," ++ TheoryPackage.jsonString "depends_on" ++ ":[" ++
    TheoryPackage.renderStringListJson c.dependencies ++ "]" ++
    "," ++ TheoryPackage.jsonString "models" ++ ":[" ++
    TheoryPackage.renderStringListJson c.models ++ "]" ++
    "," ++ TheoryPackage.jsonString "status" ++ ":" ++
    TheoryPackage.jsonString "kernel_checked" ++ "}"

private def renderIndexedClaimsJson : List IndexedClaim → String
  | [] => ""
  | [entry] => renderIndexedClaimJson entry
  | entry :: rest => renderIndexedClaimJson entry ++ "," ++
      renderIndexedClaimsJson rest

/- A flat claim projection is useful to theorem-search and notebook tooling:
   consumers need not understand the nested package report just to build an
   index.  It is metadata about proof terms compiled into the project. -/
def renderClaimsJson (P : ResearchProject) (query : String := "") : String :=
  "[" ++ renderIndexedClaimsJson (P.searchClaims query) ++ "]"

def obligationCount (P : ResearchProject) : Nat :=
  P.packages.foldl (fun n package => n + package.obligationCount) 0

def invalidPackages (P : ResearchProject) : List TheoryPackage :=
  P.packages.filter TheoryPackage.hasErrors

/-! A dependency written as `package::claim` is resolved at project scope.  A
    plain name remains a package-local dependency and is checked by
    `TheoryPackage.diagnostics`.  Keeping the syntax in the existing string
    field preserves compatibility with old ledgers while allowing a paper to
    combine independently compiled packages. -/

def qualifiedDependency (packageName claimName : String) : String :=
  packageName ++ "::" ++ claimName

/-- A globally qualified stable identifier for a claim in a project. -/
def qualifiedClaimId (packageName claimName : String) : String :=
  "leanphy.claim:" ++ qualifiedDependency packageName claimName

/- A cross-package derivation keeps the proof-producing discipline of
`TheoryPackage.addDerivedTheorem`, while adding a qualified provenance edge.
The caller passes the source `CheckedClaim` value explicitly; its proposition
and proof are therefore available to `derive` at elaboration time.  The
project-level diagnostics still verify that the source package and claim name
are present in the assembled project.  If the target package is not present,
the updated package is appended, so a missing source/claim remains visible as
an invalid project instead of being silently dropped. -/
def addDerivedTheorem (P : ResearchProject)
    (sourcePackageName : String) (prior : CheckedClaim)
    (target : TheoryPackage)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop} (derive : prior.proposition → Q) : ResearchProject :=
  let claim : CheckedClaim :=
    { name := name
      statement := statement
      source := source
      requiredAssumptions := requiredAssumptions
      dependencies := [qualifiedDependency sourcePackageName prior.name]
      models := []
      proposition := Q
      proof := derive prior.proof }
  let updated := target.addClaim claim
  { P with packages := replacePackageByName target.name updated P.packages }

def addDerivedTheoremForModels (P : ResearchProject)
    (sourcePackageName : String) (prior : CheckedClaim)
    (target : TheoryPackage) (modelNames : List String)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop} (derive : prior.proposition → Q) : ResearchProject :=
  let claim : CheckedClaim :=
    { name := name
      statement := statement
      source := source
      requiredAssumptions := requiredAssumptions
      dependencies := [qualifiedDependency sourcePackageName prior.name]
      models := modelNames
      proposition := Q
      proof := derive prior.proof }
  let updated := target.addClaim claim
  { P with packages := replacePackageByName target.name updated P.packages }

/- Two source packages cover a common paper step combining, for example, a
quantum algebra identity with a finite-PDE stability result. -/
def addDerivedTheorem2 (P : ResearchProject)
    (firstPackageName : String) (first : CheckedClaim)
    (secondPackageName : String) (second : CheckedClaim)
    (target : TheoryPackage)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop}
    (derive : first.proposition → second.proposition → Q) : ResearchProject :=
  let claim : CheckedClaim :=
    { name := name
      statement := statement
      source := source
      requiredAssumptions := requiredAssumptions
      dependencies := [qualifiedDependency firstPackageName first.name,
        qualifiedDependency secondPackageName second.name]
      models := []
      proposition := Q
      proof := derive first.proof second.proof }
  let updated := target.addClaim claim
  { P with packages := replacePackageByName target.name updated P.packages }

def addDerivedTheorem2ForModels (P : ResearchProject)
    (firstPackageName : String) (first : CheckedClaim)
    (secondPackageName : String) (second : CheckedClaim)
    (target : TheoryPackage) (modelNames : List String)
    (name statement source : String) (requiredAssumptions : List String)
    {Q : Prop}
    (derive : first.proposition → second.proposition → Q) : ResearchProject :=
  let claim : CheckedClaim :=
    { name := name
      statement := statement
      source := source
      requiredAssumptions := requiredAssumptions
      dependencies := [qualifiedDependency firstPackageName first.name,
        qualifiedDependency secondPackageName second.name]
      models := modelNames
      proposition := Q
      proof := derive first.proof second.proof }
  let updated := target.addClaim claim
  { P with packages := replacePackageByName target.name updated P.packages }

private def duplicatePackageNames : List String → List String → List String
  | _, [] => []
  | seen, name :: rest =>
      let tail := duplicatePackageNames (name :: seen) rest
      if seen.contains name then
        if tail.contains name then tail else name :: tail
      else tail

private def duplicatePackageDiagnostics (names : List String) :
    List LedgerDiagnostic :=
  (duplicatePackageNames [] names).map (fun name =>
    { code := "duplicate-package"
      severity := .error
      entry := name
      message := "重复的理论包名称；跨包依赖无法唯一解析" })

private def hasQualifiedProjectMarkerAux : List Char → Bool
  | [] => false
  | first :: rest =>
      match rest with
      | [] => false
      | second :: _ =>
          if first = ':' && second = ':' then true
          else hasQualifiedProjectMarkerAux rest

private def hasQualifiedProjectMarker (dependency : String) : Bool :=
  hasQualifiedProjectMarkerAux dependency.toList

private def splitQualifiedChars : List Char → List Char → Option (String × String)
  | [], _ => none
  | first :: rest, reversedPackage =>
      match rest with
      | second :: tail =>
          if first = ':' && second = ':' then
            some (String.ofList reversedPackage.reverse, String.ofList tail)
          else splitQualifiedChars rest (first :: reversedPackage)
      | [] => none

private def splitQualifiedDependency (dependency : String) :
    Option (String × String) :=
  splitQualifiedChars dependency.toList []

/-- A machine-readable edge in the paper-level derivation graph.  `target` is
    always qualified; a package-local dependency is qualified with the target
    package name while an explicit `package::claim` dependency is preserved.
    The edge is metadata only: the dependent proof fields remain the source of
    mathematical trust. -/
structure DependencyEdge where
  target : String
  dependency : String
  deriving Repr, DecidableEq

def dependencyEdges (P : ResearchProject) : List DependencyEdge :=
  P.packages.flatMap (fun package =>
    package.claims.flatMap (fun claim =>
      claim.dependencies.map (fun dependency =>
        { target := qualifiedDependency package.name claim.name
          dependency :=
            if hasQualifiedProjectMarker dependency then dependency
            else qualifiedDependency package.name dependency })))

def dependencyEdgeCount (P : ResearchProject) : Nat :=
  P.dependencyEdges.length

private def crossPackageDiagnostics (P : ResearchProject) :
    List LedgerDiagnostic :=
  let qualifiedClaims := P.packages.flatMap (fun package =>
    package.claims.map (fun claim =>
      qualifiedDependency package.name claim.name))
  P.packages.flatMap (fun package =>
    package.claims.flatMap (fun claim =>
      claim.dependencies.filterMap (fun dependency =>
        if hasQualifiedProjectMarker dependency then
          if qualifiedClaims.contains dependency then none
          else some
            { code := "missing-cross-package-claim"
              severity := .error
              entry := dependency
              message := "跨包依赖引用了未登记的理论包或结论" }
        else none)))

/- A qualified edge may intentionally point back into the target package (for
   example when a client builds all names mechanically).  In that case it
   must obey the same declaration-order rule as a plain package-local edge;
   otherwise a self-reference or forward edge could disappear merely because
   it was written with `package::claim` syntax. -/
private def samePackageQualifiedDiagnostics (packageName : String)
    (names : List String) : List CheckedClaim → Nat → List LedgerDiagnostic
  | [], _ => []
  | claim :: rest, index =>
      let own := claim.dependencies.filterMap (fun dependency =>
        match splitQualifiedDependency dependency with
        | some (sourcePackage, sourceClaim) =>
            if sourcePackage = packageName then
              if sourceClaim = claim.name then
                some { code := "qualified-self-dependency"
                       severity := .error
                       entry := claim.name
                       message := "限定依赖不能引用当前结论自身" }
              else
                match List.findIdx? (fun name => name == sourceClaim) names with
                | some dependencyIndex =>
                    if index ≤ dependencyIndex then
                      some { code := "qualified-forward-dependency"
                             severity := .error
                             entry := claim.name
                             message := "限定依赖的结论必须先于当前结论登记：" ++
                               dependency }
                    else none
                | none => none
            else none
        | none => none)
      own ++ samePackageQualifiedDiagnostics packageName names rest (index + 1)

private def qualifiedOrderDiagnostics (P : ResearchProject) :
    List LedgerDiagnostic :=
  P.packages.flatMap (fun package =>
    samePackageQualifiedDiagnostics package.name
      (package.claims.map CheckedClaim.name) package.claims 0)

/-- Diagnostics whose scope is the project rather than one package. -/
def diagnostics (P : ResearchProject) : List LedgerDiagnostic :=
  duplicatePackageDiagnostics (P.packages.map TheoryPackage.name) ++
    crossPackageDiagnostics P ++ qualifiedOrderDiagnostics P

def diagnosticCount (P : ResearchProject) : Nat := P.diagnostics.length

def errorDiagnostics (P : ResearchProject) : List LedgerDiagnostic :=
  P.diagnostics.filter (fun diagnostic => diagnostic.severity == .error)

def hasErrors (P : ResearchProject) : Bool :=
  !(P.errorDiagnostics.isEmpty) || !(P.invalidPackages.isEmpty)

def isWellFormed (P : ResearchProject) : Bool := !P.hasErrors

def status (P : ResearchProject) : String :=
  if P.packages.isEmpty then "EMPTY-PROJECT"
  else if P.hasErrors then "INVALID-PROJECT"
  else if P.packages.all (fun package => package.claims.isEmpty) then "UNVERIFIED"
  else "VERIFIED-CONDITIONAL"

private def renderPackages : List TheoryPackage → String
  | [] => ""
  | package :: rest =>
      TheoryPackage.render package ++ "\n" ++ renderPackages rest

/-- Human-readable project report, suitable for a CI artifact or a paper's
    reproducibility bundle. -/
def render (P : ResearchProject) : String :=
  s!"Project: {P.name}\n" ++
  s!"Packages: {P.packageCount}\n" ++
  s!"Kernel-checked claims: {P.claimCount}\n" ++
  s!"Dependency edges: {P.dependencyEdgeCount}\n" ++
  s!"Open external obligations: {P.obligationCount}\n" ++
  s!"Project diagnostics: {P.diagnosticCount}\n" ++
  (P.diagnostics.foldl (init := "") (fun text diagnostic =>
    text ++ s!"  - {diagnostic.code} ({diagnostic.entry}): {diagnostic.message}\n")) ++
  s!"Status: {P.status}\n\n" ++
  renderPackages P.packages

private def renderProjectDiagnosticJson (diagnostic : LedgerDiagnostic) : String :=
  "{" ++ TheoryPackage.jsonString "code" ++ ":" ++
      TheoryPackage.jsonString diagnostic.code ++ "," ++
      TheoryPackage.jsonString "severity" ++ ":" ++
      TheoryPackage.jsonString (match diagnostic.severity with
        | .warning => "warning" | .error => "error") ++ "," ++
      TheoryPackage.jsonString "entry" ++ ":" ++
      TheoryPackage.jsonString diagnostic.entry ++ "," ++
      TheoryPackage.jsonString "message" ++ ":" ++
      TheoryPackage.jsonString diagnostic.message ++ "}"

private def renderProjectDiagnosticsJson : List LedgerDiagnostic → String
  | [] => ""
  | [diagnostic] => renderProjectDiagnosticJson diagnostic
  | diagnostic :: rest =>
      renderProjectDiagnosticJson diagnostic ++ "," ++
        renderProjectDiagnosticsJson rest

private def renderDependencyEdgesJson : List DependencyEdge → String
  | [] => ""
  | [edge] => "{" ++ TheoryPackage.jsonString "target" ++ ":" ++
      TheoryPackage.jsonString edge.target ++ "," ++
      TheoryPackage.jsonString "dependency" ++ ":" ++
      TheoryPackage.jsonString edge.dependency ++ "}"
  | edge :: rest =>
      ("{" ++ TheoryPackage.jsonString "target" ++ ":" ++
        TheoryPackage.jsonString edge.target ++ "," ++
        TheoryPackage.jsonString "dependency" ++ ":" ++
        TheoryPackage.jsonString edge.dependency ++ "},") ++
        renderDependencyEdgesJson rest

/-! DOT is deliberately a second, presentation-only projection of the same
    dependency metadata.  Node labels are escaped with the JSON string
    renderer; JSON and DOT use the same escaping for the characters that can
    occur in names, which keeps this small exporter dependency-free. -/

private def renderDotClaims (packageName : String) : List CheckedClaim → String
  | [] => ""
  | claim :: rest =>
      "  " ++ TheoryPackage.jsonString (qualifiedDependency packageName claim.name) ++
        " [label=" ++ TheoryPackage.jsonString
          (claim.name ++ "\n" ++ packageName) ++ ", shape=box];\n" ++
        renderDotClaims packageName rest

private def renderDotNodes : List TheoryPackage → String
  | [] => ""
  | package :: rest =>
      renderDotClaims package.name package.claims ++ renderDotNodes rest

private def renderDotEdges : List DependencyEdge → String
  | [] => ""
  | edge :: rest =>
      "  " ++ TheoryPackage.jsonString edge.dependency ++ " -> " ++
        TheoryPackage.jsonString edge.target ++ ";\n" ++
        renderDotEdges rest

/-- Render the paper-level derivation graph as Graphviz DOT.  The output is
    metadata only; each node still corresponds to a compiled
    `CheckedClaim.proof`, and unresolved edges remain visible for the caller to
    reject through `hasErrors`. -/
def renderDot (P : ResearchProject) : String :=
  "digraph LeanPhy {\n" ++
    "  rankdir=LR;\n" ++
    renderDotNodes P.packages ++
    renderDotEdges P.dependencyEdges ++
    "}\n"

/-- Machine-readable projection. Each package retains its own assumptions,
    claims, diagnostics and open obligations. -/
def renderJson (P : ResearchProject) : String :=
  "{" ++ TheoryPackage.jsonString "name" ++ ":" ++
    TheoryPackage.jsonString P.name ++ "," ++
    TheoryPackage.jsonString "schema_version" ++ ":" ++
    TheoryPackage.jsonString schemaVersion ++ "," ++
    TheoryPackage.jsonString "status" ++ ":" ++
    TheoryPackage.jsonString P.status ++ "," ++
    TheoryPackage.jsonString "package_count" ++ ":" ++
    ToString.toString P.packageCount ++ "," ++
    TheoryPackage.jsonString "claim_count" ++ ":" ++
    ToString.toString P.claimCount ++ "," ++
    TheoryPackage.jsonString "dependency_edge_count" ++ ":" ++
    ToString.toString P.dependencyEdgeCount ++ "," ++
    TheoryPackage.jsonString "open_obligation_count" ++ ":" ++
    ToString.toString P.obligationCount ++ "," ++
    TheoryPackage.jsonString "dependency_edges" ++ ":[" ++
    renderDependencyEdgesJson P.dependencyEdges ++ "]," ++
    TheoryPackage.jsonString "diagnostics" ++ ":[" ++
    renderProjectDiagnosticsJson P.diagnostics ++ "]," ++
    TheoryPackage.jsonString "invalid_packages" ++ ":[" ++
    TheoryPackage.renderStringListJson (P.invalidPackages.map TheoryPackage.name) ++ "]," ++
    TheoryPackage.jsonString "packages" ++ ":[" ++
    String.intercalate "," (P.packages.map TheoryPackage.renderJson) ++ "]}"

end ResearchProject

/-! ## Reproducibility manifests

The Lean source remains the authoritative proof artifact, but a research
project also needs a small, reviewable record of the toolchain and import
profiles used to compile it.  `ResearchManifest` keeps that record next to
the proof-bearing `ResearchProject`; its JSON projection is metadata only and
cannot create a theorem.  A manifest is therefore useful for CI, paper
supplements and archival bundles without weakening the kernel boundary. -/

structure ToolchainMetadata where
  lean : String
  mathlib : String
  leanPhy : String
  deriving Repr

namespace ToolchainMetadata

def current : ToolchainMetadata where
  lean := "v4.34.0"
  mathlib := "v4.34.0"
  leanPhy := "0.1.0"

end ToolchainMetadata

structure ResearchManifest where
  name : String
  project : ResearchProject
  toolchain : ToolchainMetadata
  profiles : List String
  sourceEntries : List String
  externalTools : List String

namespace ResearchManifest

/-- Manifest schema version.  A downstream parser can reject an unknown
    version before interpreting any optional metadata fields. -/
def schemaVersion : String := "1"

def ofProject (name : String) (project : ResearchProject) : ResearchManifest where
  name := name
  project := project
  toolchain := ToolchainMetadata.current
  profiles := []
  sourceEntries := []
  externalTools := []

/-- Override the detected/default toolchain description for archived or
    cross-version projects.  This changes reproducibility metadata only; it
    cannot change the Lean environment or any proof term. -/
def withToolchain (M : ResearchManifest) (toolchain : ToolchainMetadata) :
    ResearchManifest :=
  { M with toolchain := toolchain }

def withProfiles (M : ResearchManifest) (profiles : List String) : ResearchManifest :=
  { M with profiles := profiles }

def withSources (M : ResearchManifest) (sources : List String) : ResearchManifest :=
  { M with sourceEntries := sources }

def withExternalTools (M : ResearchManifest) (tools : List String) : ResearchManifest :=
  { M with externalTools := tools }

def status (M : ResearchManifest) : String := M.project.status

def claimCount (M : ResearchManifest) : Nat :=
  M.project.claimCount

def obligationCount (M : ResearchManifest) : Nat :=
  M.project.obligationCount

def hasErrors (M : ResearchManifest) : Bool := M.project.hasErrors

private def renderToolchainJson (T : ToolchainMetadata) : String :=
  "{" ++ TheoryPackage.jsonString "lean" ++ ":" ++
    TheoryPackage.jsonString T.lean ++ "," ++
    TheoryPackage.jsonString "mathlib" ++ ":" ++
    TheoryPackage.jsonString T.mathlib ++ "," ++
    TheoryPackage.jsonString "leanphy" ++ ":" ++
    TheoryPackage.jsonString T.leanPhy ++ "}"

def renderJson (M : ResearchManifest) : String :=
  "{" ++ TheoryPackage.jsonString "name" ++ ":" ++
    TheoryPackage.jsonString M.name ++ "," ++
    TheoryPackage.jsonString "schema_version" ++ ":" ++
    TheoryPackage.jsonString schemaVersion ++ "," ++
    TheoryPackage.jsonString "status" ++ ":" ++
    TheoryPackage.jsonString M.status ++ "," ++
    TheoryPackage.jsonString "toolchain" ++ ":" ++
    renderToolchainJson M.toolchain ++ "," ++
    TheoryPackage.jsonString "profiles" ++ ":[" ++
    TheoryPackage.renderStringListJson M.profiles ++ "]," ++
    TheoryPackage.jsonString "source_entries" ++ ":[" ++
    TheoryPackage.renderStringListJson M.sourceEntries ++ "]," ++
    TheoryPackage.jsonString "external_tools" ++ ":[" ++
    TheoryPackage.renderStringListJson M.externalTools ++ "]," ++
    TheoryPackage.jsonString "claim_count" ++ ":" ++
    ToString.toString M.claimCount ++ "," ++
    TheoryPackage.jsonString "open_obligation_count" ++ ":" ++
    ToString.toString M.obligationCount ++ "," ++
    TheoryPackage.jsonString "project" ++ ":" ++
    ResearchProject.renderJson M.project ++ "}"

def render (M : ResearchManifest) : String :=
  s!"Manifest: {M.name}\n" ++
  s!"Schema version: {schemaVersion}\n" ++
  s!"Toolchain: Lean {M.toolchain.lean}, mathlib {M.toolchain.mathlib}, LeanPhy {M.toolchain.leanPhy}\n" ++
  s!"Profiles: {String.intercalate ", " M.profiles}\n" ++
  s!"Source entries: {String.intercalate ", " M.sourceEntries}\n" ++
  s!"External tools: {String.intercalate ", " M.externalTools}\n" ++
  s!"Kernel-checked claims: {M.claimCount}\n" ++
  s!"Open external obligations: {M.obligationCount}\n" ++
  s!"Status: {M.status}\n"

end ResearchManifest

/-! ## Shared proof-bearing claims

These universal claims deliberately retain their hypotheses.  A package can
therefore document an algebraic, stochastic or positivity assumption without
silently promoting it to a theorem.
-/

theorem ccr_number_claim :
    ∀ {A : Type} [Ring A] (a adag : A),
      LeanPhy.Quantum.commutator a adag = 1 →
      LeanPhy.Quantum.commutator (LeanPhy.FieldTheory.number adag a) adag = adag := by
  intro A _ a adag h
  exact LeanPhy.FieldTheory.number_commutator a adag h

theorem ccr_number_lowering_claim :
    ∀ {A : Type} [Ring A] (a adag : A),
      LeanPhy.Quantum.commutator a adag = 1 →
      LeanPhy.Quantum.commutator (LeanPhy.FieldTheory.number adag a) a = -a := by
  intro A _ a adag h
  exact LeanPhy.FieldTheory.number_commutator_a a adag h

theorem finite_step_bounds_claim :
    ∀ {ι : Type} [Fintype ι]
      (K : LeanPhy.Mathematics.FinitePositiveStep ι)
      (u : ι → ℝ) (lower upper : ℝ),
      (∀ j, lower ≤ u j) → (∀ j, u j ≤ upper) →
      ∀ i, lower ≤ K.step u i ∧ K.step u i ≤ upper := by
  intro ι _ K u lower upper hlo hhi
  exact K.step_bounds u lower upper hlo hhi

theorem finite_mass_preservation_claim :
    ∀ {ι : Type} [Fintype ι]
      (K : LeanPhy.Mathematics.FinitePositiveStep ι)
      (_C : LeanPhy.Mathematics.FinitePositiveStep.MassConservationCertificate K)
      (u : ι → ℝ),
      ∑ i, K.step u i = ∑ i, u i := by
  intro ι _ K C u
  exact K.sum_preserved C u

theorem finite_energy_bound_claim :
    ∀ {X : Type} (S : LeanPhy.Mathematics.FiniteEnergyStep X)
      (n : ℕ) (x : X),
      S.energy (S.iterate n x) ≤ S.factor ^ n * S.energy x := by
  intro X S n x
  exact S.iterate_energy_bound n x

theorem finite_positive_partition_claim :
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] (S : ι → ℝ),
      0 < (LeanPhy.Mathematics.FinitePositivePathIntegral.fromRealAction S).toComplex.partition.re := by
  intro ι _ _ S
  exact LeanPhy.Mathematics.FinitePositivePathIntegral.toComplex_partition_pos
    (LeanPhy.Mathematics.FinitePositivePathIntegral.fromRealAction S)

theorem finite_gram_positivity_claim :
    ∀ {ι α : Type} [Fintype ι] [Fintype α]
      (G : LeanPhy.Mathematics.FiniteWeightedGramKernel ι α)
      (f : ι → ℝ),
      0 ≤ G.kernelQuadratic f := by
  intro ι α _ _ G f
  exact G.kernelQuadratic_nonneg f

theorem finite_reflection_positivity_claim :
    ∀ {ι α : Type} [Fintype ι] [Fintype α]
      (C : LeanPhy.Mathematics.FiniteWeightedReflectionCertificate ι α)
      (f : ι → ℝ),
      0 ≤ C.reflectedKernelQuadratic f := by
  intro ι α _ _ C f
  exact C.reflectedKernelQuadratic_nonneg f

/-! Explicit proposition annotations keep polymorphic theorem schemas from
being prematurely instantiated while they are inserted into the heterogeneous
claim list. -/

def ccrRaisingChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "number raising" "[N, a†] = a† under CCR"
    "LeanPhy.FieldTheory.CCR" ["CCR", "finite operators", "scalar field"]
    (P := ∀ {A : Type} [Ring A] (a adag : A),
      LeanPhy.Quantum.commutator a adag = 1 →
      LeanPhy.Quantum.commutator (LeanPhy.FieldTheory.number adag a) adag = adag)
    ccr_number_claim

def ccrLoweringChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "number lowering" "[N, a] = -a under CCR"
    "LeanPhy.FieldTheory.CCR" ["CCR", "finite operators", "scalar field"]
    (P := ∀ {A : Type} [Ring A] (a adag : A),
      LeanPhy.Quantum.commutator a adag = 1 →
      LeanPhy.Quantum.commutator (LeanPhy.FieldTheory.number adag a) a = -a)
    ccr_number_lowering_claim

def finiteStepBoundsChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "maximum principle"
    "positive row-stochastic steps preserve pointwise bounds"
    "LeanPhy.Mathematics.FiniteParabolic"
    ["finite mesh", "positive step"]
    (P := ∀ {ι : Type} [Fintype ι]
      (K : LeanPhy.Mathematics.FinitePositiveStep ι)
      (u : ι → ℝ) (lower upper : ℝ),
      (∀ j, lower ≤ u j) → (∀ j, u j ≤ upper) →
      ∀ i, lower ≤ K.step u i ∧ K.step u i ≤ upper)
    finite_step_bounds_claim

def finiteMassChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "mass conservation"
    "a column-sum certificate preserves the finite total"
    "LeanPhy.Mathematics.FiniteParabolic"
    ["finite mesh", "conservation"]
    (P := ∀ {ι : Type} [Fintype ι]
      (K : LeanPhy.Mathematics.FinitePositiveStep ι)
      (_C : LeanPhy.Mathematics.FinitePositiveStep.MassConservationCertificate K)
      (u : ι → ℝ), ∑ i, K.step u i = ∑ i, u i)
    finite_mass_preservation_claim

def finiteEnergyChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "finite energy propagation"
    "one-step energy bounds propagate to every finite iterate"
    "LeanPhy.Mathematics.FiniteEnergy"
    ["finite mesh", "energy estimate"]
    (P := ∀ {X : Type} (S : LeanPhy.Mathematics.FiniteEnergyStep X)
      (n : ℕ) (x : X),
      S.energy (S.iterate n x) ≤ S.factor ^ n * S.energy x)
    finite_energy_bound_claim

def finitePartitionChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "positive partition"
    "a nonempty finite real-action model has positive partition"
    "LeanPhy.Mathematics.FinitePathReflection"
    ["finite configuration space", "positive weights"]
    (P := ∀ {ι : Type} [Fintype ι] [Nonempty ι] (S : ι → ℝ),
      0 < (LeanPhy.Mathematics.FinitePositivePathIntegral.fromRealAction S).toComplex.partition.re)
    finite_positive_partition_claim

def finiteGramChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "Gram positivity"
    "a finite weighted Gram kernel is positive"
    "LeanPhy.Mathematics.FinitePathReflection"
    ["finite configuration space", "Gram factorisation"]
    (P := ∀ {ι α : Type} [Fintype ι] [Fintype α]
      (G : LeanPhy.Mathematics.FiniteWeightedGramKernel ι α)
      (f : ι → ℝ), 0 ≤ G.kernelQuadratic f)
    finite_gram_positivity_claim

def finiteReflectionChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "reflection positivity"
    "an involutive reflected Gram kernel is nonnegative"
    "LeanPhy.Mathematics.FinitePathReflection"
    ["finite configuration space", "reflection", "Gram factorisation"]
    (P := ∀ {ι α : Type} [Fintype ι] [Fintype α]
      (C : LeanPhy.Mathematics.FiniteWeightedReflectionCertificate ι α)
      (f : ι → ℝ), 0 ≤ C.reflectedKernelQuadratic f)
    finite_reflection_positivity_claim

def classicalSymplecticChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "symplectic composition"
    "the product of two finite canonical transformations preserves the symplectic form"
    "LeanPhy.Classical.Symplectic"
    ["finite phase space", "canonical form"]
    (P := ∀ (A B : LeanPhy.Classical.M2R),
      Aᵀ * LeanPhy.Classical.symplecticJ * A = LeanPhy.Classical.symplecticJ →
      Bᵀ * LeanPhy.Classical.symplecticJ * B = LeanPhy.Classical.symplecticJ →
      (A * B)ᵀ * LeanPhy.Classical.symplecticJ * (A * B) =
        LeanPhy.Classical.symplecticJ)
    LeanPhy.Classical.symplectic_mul

def gaugeFieldStrengthChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "gauge curvature antisymmetry"
    "the finite algebraic field strength is antisymmetric in its directions"
    "LeanPhy.GaugeTheory.FieldStrength"
    ["covariant derivatives", "finite directions"]
    (P := ∀ {A : Type} [Ring A] (D : Fin 4 → A) (mu nu : Fin 4),
      LeanPhy.GaugeTheory.fieldStrength D mu nu =
        -LeanPhy.GaugeTheory.fieldStrength D nu mu)
    LeanPhy.GaugeTheory.fieldStrength_antisym

def condensedBdGChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "BdG quadratic identity"
    "a finite BdG block squares to (ε² + Δ²) times the identity"
    "LeanPhy.Condensed.BCS"
    ["finite block", "parameters"]
    (P := ∀ (eps Delta : ℂ),
      LeanPhy.Condensed.bdg eps Delta * LeanPhy.Condensed.bdg eps Delta =
        (eps ^ 2 + Delta ^ 2) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ))
    LeanPhy.Condensed.bdg_sq

def relativityMetricChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "Minkowski signature"
    "the finite (+---) metric has the declared diagonal signature"
    "LeanPhy.Relativity.Minkowski"
    ["signature", "integer witness"]
    LeanPhy.Relativity.metric_diagonal

def gibbsPartitionChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "finite Gibbs partition"
    "a nonempty finite Gibbs partition function is strictly positive"
    "LeanPhy.StatMech.FiniteGibbs"
    ["finite state space", "Boltzmann weight"]
    (P := ∀ {ι : Type} [Fintype ι] [Nonempty ι] (β : ℝ) (E : ι → ℝ),
      0 < LeanPhy.StatMech.finitePartitionFunction β E)
    LeanPhy.StatMech.finitePartitionFunction_pos

def multiWickFourChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "four-point Wick contraction"
    "the finite four-point Gaussian moment is the sum of its three pairings"
    "LeanPhy.FieldTheory.MultiWick"
    ["finite field labels", "commutative coefficient algebra"]
    (P := ∀ (C : Fin 4 → Fin 4 → ℂ),
      LeanPhy.FieldTheory.MultiWick.gaussianMoment C [0, 1, 2, 3] =
        C 0 1 * C 2 3 + C 0 2 * C 1 3 + C 0 3 * C 1 2)
    LeanPhy.FieldTheory.MultiWick.gaussianMoment_four

def gammaCliffordChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "Dirac Clifford anticommutation"
    "γ⁰γ¹ + γ¹γ⁰ = 0 in the explicit 4 × 4 representation"
    "LeanPhy.HighEnergy.Gamma"
    ["finite spinor representation", "metric convention"]
    LeanPhy.HighEnergy.gamma0_anticommutes_gamma1

theorem finite_eft_truncation_claim
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : LeanPhy.HighEnergy.ExpansionParameter)
    (T : LeanPhy.HighEnergy.FiniteEFT ι) (S : Finset ι) (cutoff : ℕ)
    (horder : ∀ i ∈ Finset.univ \ S, cutoff ≤ T.order i) :
    LeanPhy.Mathematics.ErrorCertificate (T.amplitude E)
      (T.retainedAmplitude E S)
      (((Finset.univ \ S).card : ℝ) * T.coefficientBound * E.value ^ cutoff) :=
  T.truncation_error_certificate E S cutoff horder

def finiteEftTruncationChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "finite EFT truncation error"
    "the omitted finite operator tail is bounded by its cardinality, coefficient bound, and cutoff power"
    "LeanPhy.HighEnergy.EffectiveTheory"
    ["finite operator basis", "expansion parameter hierarchy", "coefficient bound"]
    (P := ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (E : LeanPhy.HighEnergy.ExpansionParameter)
      (T : LeanPhy.HighEnergy.FiniteEFT ι) (S : Finset ι) (cutoff : ℕ)
      (horder : ∀ i ∈ Finset.univ \ S, cutoff ≤ T.order i),
      LeanPhy.Mathematics.ErrorCertificate (T.amplitude E)
        (T.retainedAmplitude E S)
        (((Finset.univ \ S).card : ℝ) * T.coefficientBound * E.value ^ cutoff))
    finite_eft_truncation_claim

theorem finite_eft_matching_claim
    {ι : Type} [Fintype ι]
    (M : LeanPhy.HighEnergy.FiniteEFT.MatchingCertificate ι)
    (weights : ι → ℝ) (S : Finset ι) (weightBound : ℝ)
    (weightBound_nonneg : 0 ≤ weightBound)
    (weight_abs_le : ∀ i ∈ S, |weights i| ≤ weightBound) :
    LeanPhy.Mathematics.ErrorCertificate
      (LeanPhy.HighEnergy.FiniteEFT.MatchingCertificate.observable
        M.uvCoefficient weights S)
      (LeanPhy.HighEnergy.FiniteEFT.MatchingCertificate.observable
        M.irCoefficient weights S)
      ((S.card : ℝ) * weightBound * M.uniformError) :=
  M.error_certificate weights S weightBound weightBound_nonneg weight_abs_le

def finiteEftMatchingChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "finite EFT matching error"
    "a uniform coefficient-matching error yields an observable error budget for every bounded finite weighting"
    "LeanPhy.HighEnergy.EffectiveTheory"
    ["finite operator basis", "matching certificate", "observable weight bound"]
    (P := ∀ {ι : Type} [Fintype ι]
      (M : LeanPhy.HighEnergy.FiniteEFT.MatchingCertificate ι)
      (weights : ι → ℝ) (S : Finset ι) (weightBound : ℝ),
      0 ≤ weightBound →
      (∀ i ∈ S, |weights i| ≤ weightBound) →
      LeanPhy.Mathematics.ErrorCertificate
        (LeanPhy.HighEnergy.FiniteEFT.MatchingCertificate.observable
          M.uvCoefficient weights S)
        (LeanPhy.HighEnergy.FiniteEFT.MatchingCertificate.observable
          M.irCoefficient weights S)
        ((S.card : ℝ) * weightBound * M.uniformError))
    finite_eft_matching_claim

theorem bounded_unitary_norm_claim
    {𝕜 E : Type} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (U : LeanPhy.Mathematics.Hilbert.Unitary (𝕜 := 𝕜) (E := E)) (x : E) :
    ‖U.op x‖ = ‖x‖ := U.norm_preserved x

def boundedUnitaryNormChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "bounded unitary norm"
    "a bounded unitary preserves the Hilbert-space norm"
    "LeanPhy.Mathematics.Hilbert"
    ["complete inner-product space", "bounded unitary"]
    (P := ∀ {𝕜 E : Type} [RCLike 𝕜] [NormedAddCommGroup E]
      [InnerProductSpace 𝕜 E] [CompleteSpace E]
      (U : LeanPhy.Mathematics.Hilbert.Unitary (𝕜 := 𝕜) (E := E)) (x : E),
      ‖U.op x‖ = ‖x‖)
    bounded_unitary_norm_claim

theorem polynomial_spectral_mapping_claim {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Nontrivial E] (A : E →L[ℂ] E) (p : Polynomial ℂ) :
    spectrum ℂ (aeval A p) = (fun z => p.eval z) '' spectrum ℂ A :=
  LeanPhy.Mathematics.polynomial_spectrum_map A p

def polynomialSpectralMappingChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "polynomial spectral mapping"
    "the spectrum of a bounded complex operator polynomial is the polynomial image of the spectrum"
    "LeanPhy.Mathematics.SpectralCalculus"
    ["complete inner-product space", "bounded complex operator"]
    (P := ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
      [CompleteSpace E] [Nontrivial E] (A : E →L[ℂ] E) (p : Polynomial ℂ),
      spectrum ℂ (aeval A p) = (fun z => p.eval z) '' spectrum ℂ A)
    polynomial_spectral_mapping_claim

theorem spectral_gap_iterate_claim {𝕜 E : Type} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (T P : E →L[𝕜] E) (rho : ℝ)
    (h : LeanPhy.Mathematics.SpectralGapCertificate T P rho)
    (n : ℕ) (x : E) :
    ‖(T ^ n) x - P x‖ ≤ rho ^ n * ‖x - P x‖ :=
  h.iterate_decay n x

def spectralGapIterateChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "spectral-gap iterate decay"
    "an explicit invariant projection and one-step residual contraction give a geometric bound for every iterate"
    "LeanPhy.Mathematics.SpectralGap"
    ["complete inner-product space", "bounded spectral gap"]
    (P := ∀ {𝕜 E : Type} [RCLike 𝕜] [NormedAddCommGroup E]
      [NormedSpace 𝕜 E] [CompleteSpace E]
      (T P : E →L[𝕜] E) (rho : ℝ)
      (h : LeanPhy.Mathematics.SpectralGapCertificate T P rho)
      (n : ℕ) (x : E),
      ‖(T ^ n) x - P x‖ ≤ rho ^ n * ‖x - P x‖)
    spectral_gap_iterate_claim

theorem finite_fluid_conservation_claim
    {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V]
    [AddCommGroup A] (tail head : E → V) (current : E → A) :
    ∑ v, LeanPhy.Mathematics.FiniteDivergence.divergence tail head current v = 0 :=
  LeanPhy.Mathematics.FiniteDivergence.total_divergence_zero tail head current

def fluidConservationChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "closed finite-volume conservation"
    "the total source of a closed finite-volume current vanishes"
    "LeanPhy.Mathematics.FiniteDivergence"
    ["finite mesh", "closed internal edges"]
    (P := ∀ {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V]
      [AddCommGroup A] (tail head : E → V) (current : E → A),
      ∑ v, LeanPhy.Mathematics.FiniteDivergence.divergence tail head current v = 0)
    finite_fluid_conservation_claim

def opticsCanonicalChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "ABCD canonical composition"
    "the product of two paraxial canonical transfer matrices is canonical"
    "LeanPhy.Entry.Optics"
    ["finite paraxial phase space", "canonical optical form"]
    (P := ∀ (A B : LeanPhy.Optics.ABCD),
      LeanPhy.Optics.isCanonical A → LeanPhy.Optics.isCanonical B →
      LeanPhy.Optics.isCanonical (A * B))
    LeanPhy.Optics.compose_isCanonical

def opticsJonesChecked : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions "Jones intensity preservation"
    "a finite lossless Jones element preserves the complex inner product"
    "LeanPhy.Entry.Optics"
    ["finite polarisation space", "lossless element"]
    (P := ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (U : LeanPhy.Optics.JonesElement ι) (v w : ι → ℂ),
      dotProduct (star (U.evolve v)) (U.evolve w) =
        dotProduct (star v) w)
    LeanPhy.Optics.jones_preserves_inner

/-! ## Domain adapters

Each adapter is a real package value, so downstream theory files can import
one package and add their own claims with the same `CheckedClaim.ofTheorem`
constructor.  The metadata names exactly which assumptions and limits remain
conditional.
-/

def finiteQuantumModel : ModelRegistration :=
  ModelRegistration.text "finite-pauli" "finite quantum / quantum-information model"
    "finite coupling or gate labels" "finite matrices / density operators"
    "Pauli observables and finite expectations" "matrix multiplication or CPTP step"
    ["finite operators", "scalar field"]

def finiteCCRModel : ModelRegistration :=
  ModelRegistration.text "finite-ccr" "truncated oscillator / CCR algebra"
    "finite mode or truncation index" "abstract ring or truncated Fock space"
    "operator polynomials" "creation-annihilation algebra step"
    ["CCR", "finite operators", "scalar field"]

def finitePDEModel : ModelRegistration :=
  ModelRegistration.text "finite-positive-step" "finite PDE / lattice evolution"
    "mesh and time-step labels" "finite-index scalar fields"
    "pointwise fields and finite sums" "positive row-stochastic update"
    ["finite mesh", "positive step"]

def finiteEnergyModel : ModelRegistration :=
  ModelRegistration.text "finite-energy-step" "finite stable evolution"
    "time-step and truncation labels" "finite or truncated state"
    "energy and residual observables" "certified one-step evolution"
    ["finite mesh", "energy estimate"]

def finiteEuclideanModel : ModelRegistration :=
  ModelRegistration.text "finite-euclidean" "finite Euclidean / lattice path model"
    "finite configuration labels" "finite configurations"
    "correlators and reflected observables" "finite weighted sum"
    ["finite configuration space", "positive weights", "reflection"]

def finiteClassicalModel : ModelRegistration :=
  ModelRegistration.text "finite-symplectic" "finite classical mechanics"
    "finite matrix parameters" "finite phase-space vectors"
    "quadratic forms and symplectic observables" "matrix composition"
    ["finite phase space", "canonical form"]

def finiteGaugeModel : ModelRegistration :=
  ModelRegistration.text "finite-gauge" "finite gauge curvature algebra"
    "finite direction labels" "abstract covariant-derivative algebra"
    "curvature components" "commutator difference"
    ["covariant derivatives", "finite directions"]

def finiteCondensedModel : ModelRegistration :=
  ModelRegistration.text "finite-bdg" "finite condensed-matter block"
    "momentum or coupling labels" "finite BdG matrices"
    "band, gap and quadratic observables" "finite matrix block update"
    ["finite block", "parameters"]

def finiteRelativityModel : ModelRegistration :=
  ModelRegistration.text "finite-lorentz" "finite relativity convention model"
    "finite component labels" "finite component vectors"
    "metric contractions" "finite Lorentz matrix action"
    ["signature", "integer witness"]

def finiteStatMechModel : ModelRegistration :=
  ModelRegistration.text "finite-gibbs" "finite Gibbs / Markov model"
    "temperature and finite state labels" "finite probability vectors"
    "partition functions and expectations" "finite kernel transition"
    ["finite state space", "Boltzmann weight"]

def finiteCliffordModel : ModelRegistration :=
  ModelRegistration.text "finite-clifford" "finite high-energy Clifford model"
    "finite representation labels" "finite spinor vectors and matrices"
    "Dirac bilinears and traces" "gamma-matrix multiplication"
    ["finite spinor representation", "metric convention"]

def finiteEFTModel : ModelRegistration :=
  ModelRegistration.text "finite-eft" "finite effective-theory expansion model"
    "finite operator labels and a dimensionless expansion parameter"
    "finite real coefficient vectors"
    "truncated amplitudes and matching observables" "power counting and finite weighted sums"
    ["finite operator basis", "expansion parameter hierarchy", "coefficient bound",
      "matching certificate", "observable weight bound"]

def boundedHilbertModel : ModelRegistration :=
  ModelRegistration.text "bounded-hilbert" "bounded Hilbert/numerical bridge"
    "operator and discretisation labels" "complete inner-product space"
    "norms and residual observables" "bounded linear operator action"
    ["complete inner-product space", "bounded unitary"]

def finiteOpticsModel : ModelRegistration :=
  ModelRegistration.text "finite-optics" "finite paraxial and polarisation optics"
    "ray, focal-length and polarisation labels" "2 × 2 transfer matrices / finite Jones vectors"
    "ray coordinates and polarisation inner products" "ABCD composition or Jones action"
    ["finite paraxial phase space", "finite polarisation space"]

def finiteFluidModel : ModelRegistration :=
  ModelRegistration.text "finite-fluid" "finite-volume fluid / plasma transport"
    "finite mesh and edge labels" "finite cell fields and currents"
    "mass, charge and vorticity residuals" "incidence divergence or discrete exterior derivative"
    ["finite mesh", "closed internal edges"]

def QuantumTheoryPackage : TheoryPackage where
  name := "finite quantum algebra"
  domain := "quantum mechanics / quantum information"
  assumptions := [
    { name := "CCR", statement := "[a, a†] = 1 is supplied for the abstract algebra", source := "research model" },
    { name := "finite operators", statement := "operator identities are checked in an abstract ring or finite matrix model", source := "kernel boundary" },
    { name := "scalar field", statement := "ℂ and order properties are used through imported algebraic structures", source := "mathlib" }
  ]
  claims := [
    (CheckedClaim.ofTheoremFromWithAssumptions "Pauli product" "σx σy = i σz"
      "LeanPhy.Quantum.Pauli" ["finite operators", "scalar field"]
      LeanPhy.Quantum.pauliX_pauliY).withModels ["finite-pauli"],
    (CheckedClaim.ofTheoremFromWithAssumptions "Pauli commutator" "[σx, σy] = 2 i σz"
      "LeanPhy.Quantum.Pauli" ["finite operators", "scalar field"]
      LeanPhy.Quantum.pauliXY_commutator).withModels ["finite-pauli"],
    ccrRaisingChecked.withModels ["finite-ccr"],
    ccrLoweringChecked.withModels ["finite-ccr"]
  ]
  models := [finiteQuantumModel, finiteCCRModel]
  outOfScope := [
    { label := "unbounded operators", explanation := "domains, self-adjoint extensions and spectral theorems require a separate analytic layer" },
    { label := "continuum limits", explanation := "infinite-dimensional Hilbert spaces and continuous spectra are not inferred" },
    { label := "measurement statistics", explanation := "physical interpretation still requires explicit state and probability assumptions" }
  ]
  obligations := [
    { name := "operator-domain analysis", statement := "provide domains and self-adjointness before claiming an unbounded-operator result", source := "external analysis / Physlib" }
  ]

def FinitePDETheoryPackage : TheoryPackage where
  name := "finite evolution and PDE certificates"
  domain := "finite-difference / finite-element / lattice PDE"
  assumptions := [
    { name := "finite mesh", statement := "the index type is finite and all sums are finite", source := "model declaration" },
    { name := "positive step", statement := "the update kernel is nonnegative and row stochastic", source := "scheme certificate" },
    { name := "conservation", statement := "mass conservation uses a separately supplied column-sum certificate", source := "model declaration" },
    { name := "energy estimate", statement := "one-step energy amplification is supplied explicitly", source := "stability certificate" }
  ]
  claims := [
    finiteStepBoundsChecked.withModels ["finite-positive-step"],
    finiteMassChecked.withModels ["finite-positive-step"],
    finiteEnergyChecked.withModels ["finite-energy-step"]
  ]
  models := [finitePDEModel, finiteEnergyModel]
  outOfScope := [
    { label := "CFL and mesh convergence", explanation := "stability and convergence of a continuum discretisation must be proved by an external numerical-analysis development" },
    { label := "continuum well-posedness", explanation := "Sobolev estimates, boundary regularity and infinite-dimensional existence are outside this package" },
    { label := "model adequacy", explanation := "the package checks the supplied scheme, not whether it models a physical system" }
  ]
  obligations := [
    { name := "scheme convergence", statement := "supply a CFL/stability and mesh-convergence theorem for the chosen discretisation", source := "external numerical analysis" }
  ]

def FiniteEuclideanTheoryPackage : TheoryPackage where
  name := "finite Euclidean path and reflection certificates"
  domain := "lattice field theory / finite statistical mechanics"
  assumptions := [
    { name := "finite configuration space", statement := "the path/configuration type is finite", source := "model declaration" },
    { name := "positive weights", statement := "real-action weights are nonnegative with a positive finite partition", source := "measure certificate" },
    { name := "reflection", statement := "the reflection is an explicit involutive permutation", source := "model declaration" },
    { name := "Gram factorisation", statement := "the correlator kernel is given by a finite weighted feature factorisation", source := "positivity certificate" }
  ]
  claims := [
    finitePartitionChecked.withModels ["finite-euclidean"],
    finiteGramChecked.withModels ["finite-euclidean"],
    finiteReflectionChecked.withModels ["finite-euclidean"]
  ]
  models := [finiteEuclideanModel]
  outOfScope := [
    { label := "continuum measure", explanation := "measure existence and Osterwalder–Schrader reconstruction are not inferred" },
    { label := "oscillatory path integrals", explanation := "complex cancellation requires an explicit nonzero partition certificate" },
    { label := "renormalisation", explanation := "continuum limits, universality and counterterms need a separate analytic layer" }
  ]
  obligations := [
    { name := "OS reconstruction", statement := "connect the finite reflection certificate to a continuum measure and reconstruction theorem", source := "external constructive QFT" }
  ]

def ClassicalMechanicsTheoryPackage : TheoryPackage where
  name := "finite classical mechanics"
  domain := "Hamiltonian mechanics / symplectic linear algebra"
  assumptions := [
    { name := "finite phase space", statement := "phase-space maps are represented by 2 × 2 real matrices", source := "model declaration" },
    { name := "canonical form", statement := "the symplectic matrix is the declared dq ∧ dp form", source := "convention" }
  ]
  claims := [classicalSymplecticChecked.withModels ["finite-symplectic"]]
  models := [finiteClassicalModel]
  outOfScope := [
    { label := "nonlinear flows", explanation := "generating functions, ODE existence and nonlinear symplectic geometry remain external" },
    { label := "continuum phase space", explanation := "the package checks finite matrices, not smooth manifolds" }
  ]
  obligations := [
    { name := "flow existence", statement := "prove existence and regularity of the intended nonlinear Hamiltonian flow", source := "external ODE / symplectic geometry" }
  ]

def GaugeTheoryPackage : TheoryPackage where
  name := "finite gauge curvature algebra"
  domain := "Yang–Mills / lattice gauge algebra"
  assumptions := [
    { name := "covariant derivatives", statement := "directions are elements of an abstract ring", source := "algebraic model" },
    { name := "finite directions", statement := "the displayed curvature uses four finite direction labels", source := "model declaration" }
  ]
  claims := [gaugeFieldStrengthChecked.withModels ["finite-gauge"]]
  models := [finiteGaugeModel]
  outOfScope := [
    { label := "gauge group geometry", explanation := "principal bundles, global gauge fixing and path-integral measures are external" },
    { label := "field equations", explanation := "Yang–Mills dynamics and boundary conditions require additional certificates" }
  ]
  obligations := [
    { name := "gauge dynamics", statement := "connect the algebraic curvature identity to a well-posed gauge-field model and boundary problem", source := "external gauge geometry / PDE" }
  ]

def CondensedMatterTheoryPackage : TheoryPackage where
  name := "finite condensed-matter blocks"
  domain := "BdG / superconductivity / finite band algebra"
  assumptions := [
    { name := "finite block", statement := "the BdG Hamiltonian is a 2 × 2 complex block", source := "model declaration" },
    { name := "parameters", statement := "ε and Δ are model parameters in the coefficient field", source := "research model" }
  ]
  claims := [condensedBdGChecked.withModels ["finite-bdg"]]
  models := [finiteCondensedModel]
  outOfScope := [
    { label := "thermodynamic limit", explanation := "gap closing, phase transitions and infinite lattice limits are external" },
    { label := "self-consistency", explanation := "gap equations and microscopic derivations need explicit additional inputs" }
  ]
  obligations := [
    { name := "band-limit passage", statement := "provide the finite-volume or momentum-mesh convergence argument for the claimed phase", source := "external condensed-matter analysis" }
  ]

def RelativityTheoryPackage : TheoryPackage where
  name := "finite relativity conventions"
  domain := "special relativity / Lorentz algebra"
  assumptions := [
    { name := "signature", statement := "the metric convention is (+---)", source := "model convention" },
    { name := "integer witness", statement := "the smoke layer uses a finite integer component model", source := "regression model" }
  ]
  claims := [relativityMetricChecked.withModels ["finite-lorentz"]]
  models := [finiteRelativityModel]
  outOfScope := [
    { label := "spacetime analysis", explanation := "smooth manifolds, causal PDE and general relativity are not inferred" },
    { label := "physical units", explanation := "component identities do not establish experimental calibration" }
  ]
  obligations := [
    { name := "geometric lift", statement := "supply the manifold and causal-analytic hypotheses when lifting the component identity", source := "external differential geometry" }
  ]

def StatisticalMechanicsTheoryPackage : TheoryPackage where
  name := "finite statistical mechanics"
  domain := "Gibbs ensembles / finite Markov models"
  assumptions := [
    { name := "finite state space", statement := "the configuration type is finite and nonempty", source := "model declaration" },
    { name := "Boltzmann weight", statement := "weights use the real exponential of a finite energy", source := "ensemble definition" }
  ]
  claims := [gibbsPartitionChecked.withModels ["finite-gibbs"]]
  models := [finiteStatMechModel]
  outOfScope := [
    { label := "thermodynamic limit", explanation := "phase transitions, free-energy limits and ensemble equivalence are external" },
    { label := "mixing", explanation := "irreducibility and Markov mixing rates require separate certificates" }
  ]
  obligations := [
    { name := "equilibrium limit", statement := "prove irreducibility, mixing or thermodynamic-limit estimates for the intended ensemble", source := "external probability / statistical mechanics" }
  ]

def FieldTheoryPackage : TheoryPackage where
  name := "finite field-theory algebra"
  domain := "CCR/CAR / finite Fock space / Wick contractions"
  assumptions := [
    { name := "finite field labels", statement := "all displayed fields and contractions use a finite index type", source := "model declaration" },
    { name := "commutative coefficient algebra", statement := "the covariance coefficients form a commutative semiring for the finite Wick normaliser", source := "algebraic model" },
    { name := "CCR", statement := "the creation and annihilation symbols satisfy the supplied canonical commutation relation", source := "research model" },
    { name := "finite operators", statement := "operator identities are checked in an abstract finite algebra or truncated mode", source := "kernel boundary" },
    { name := "scalar field", statement := "the coefficient ring supplies the required additive and multiplicative laws", source := "mathlib" }
  ]
  claims := [multiWickFourChecked.withModels ["finite-ccr"],
    ccrRaisingChecked.withModels ["finite-ccr"],
    ccrLoweringChecked.withModels ["finite-ccr"]]
  models := [finiteCCRModel]
  outOfScope := [
    { label := "operator domains", explanation := "unbounded creation and annihilation operators require domain and closure theorems" },
    { label := "continuum distributions", explanation := "delta distributions, time ordering and infinite-volume limits are not inferred" },
    { label := "renormalisation", explanation := "counterterms and regulator independence remain external obligations" }
  ]
  obligations := [
    { name := "continuum Wick bridge", statement := "connect the finite contraction normaliser to the chosen continuum distributional theorem", source := "external constructive QFT / analysis" }
  ]

def HighEnergyTheoryPackage : TheoryPackage where
  name := "finite high-energy algebra"
  domain := "Dirac/Clifford matrices / spinor identities / finite EFT power counting"
  assumptions := [
    { name := "finite spinor representation", statement := "spinors are represented by explicit 4-component complex vectors and matrices", source := "model declaration" },
    { name := "metric convention", statement := "the gamma-matrix signs encode the declared (+---) convention", source := "physics convention" },
    { name := "finite operator basis", statement := "the EFT coefficient basis and every omitted sector are finite index sets", source := "model declaration" },
    { name := "expansion parameter hierarchy", statement := "the dimensionless expansion parameter lies in [0,1] and omitted terms have the declared cutoff order", source := "power-counting hypothesis" },
    { name := "coefficient bound", statement := "Wilson coefficients have the supplied uniform absolute bound", source := "matching or model certificate" },
    { name := "matching certificate", statement := "UV and IR coefficients have the supplied uniform difference bound", source := "matching calculation" },
    { name := "observable weight bound", statement := "the finite observable weights have the supplied absolute bound", source := "observable definition" }
  ]
  claims := [gammaCliffordChecked.withModels ["finite-clifford"],
    finiteEftTruncationChecked.withModels ["finite-eft"],
    finiteEftMatchingChecked.withModels ["finite-eft"]]
  models := [finiteCliffordModel, finiteEFTModel]
  outOfScope := [
    { label := "scattering analysis", explanation := "asymptotic states, distributions and cross-section limits are not inferred" },
    { label := "gauge dynamics", explanation := "renormalisation and non-perturbative dynamics require separate inputs" },
    { label := "continuum EFT", explanation := "the finite bounds do not establish existence of a UV completion, continuum limit, or regulator-independent matching" }
  ]
  obligations := [
    { name := "spinor-to-field bridge", statement := "supply the analytic and representation-theoretic hypotheses connecting finite matrices to the target field theory", source := "external QFT analysis" },
    { name := "EFT continuum bridge", statement := "supply the model-specific operator basis, matching derivation, and regulator or continuum estimates before interpreting the finite error budget physically", source := "external EFT analysis" }
  ]

def AnalysisBridgeTheoryPackage : TheoryPackage where
  name := "bounded analysis and numerical bridges"
  domain := "bounded Hilbert operators / residual and approximation certificates"
  assumptions := [
    { name := "complete inner-product space", statement := "the operator acts on a complete normed inner-product space", source := "mathlib typeclasses" },
    { name := "bounded complex operator", statement := "the spectral expression is a bounded continuous complex-linear operator", source := "spectral calculus certificate" },
    { name := "bounded spectral gap", statement := "an invariant projection and a strict one-step residual contraction are supplied", source := "spectral gap certificate" },
    { name := "bounded unitary", statement := "both adjoint-sided inverse equations are supplied", source := "model certificate" },
    { name := "finite mesh", statement := "finite evolution claims use a finite or truncated state index", source := "model declaration" },
    { name := "energy estimate", statement := "the one-step energy amplification inequality is supplied", source := "stability certificate" }
  ]
  claims := [boundedUnitaryNormChecked.withModels ["bounded-hilbert"],
    polynomialSpectralMappingChecked.withModels ["bounded-hilbert"],
    spectralGapIterateChecked.withModels ["bounded-hilbert"],
    finiteEnergyChecked.withModels ["finite-energy-step"]]
  models := [boundedHilbertModel, finiteEnergyModel]
  outOfScope := [
    { label := "unbounded operators", explanation := "domains, self-adjoint extensions and spectral measures are not inferred" },
    { label := "convergence", explanation := "mesh, truncation and continuum convergence require explicit approximation certificates" },
    { label := "well-posedness", explanation := "PDE existence and semigroup generation remain external" }
  ]
  obligations := [
    { name := "analytic completion", statement := "supply the continuity, domain and convergence arguments needed by the target research theorem", source := "external analysis / numerical analysis" }
  ]

def OpticsTheoryPackage : TheoryPackage where
  name := "finite optics and AMO"
  domain := "paraxial optics / polarisation / finite AMO control"
  assumptions := [
    { name := "finite paraxial phase space", statement := "ray transfer matrices use a two-component finite phase space", source := "optical model" },
    { name := "canonical optical form", statement := "lossless paraxial elements preserve the declared symplectic form", source := "ABCD certificate" },
    { name := "finite polarisation space", statement := "Jones vectors use a finite index type", source := "polarisation model" },
    { name := "lossless element", statement := "a Jones element supplies a finite unitary certificate", source := "optical model" }
  ]
  claims := [
    opticsCanonicalChecked.withModels ["finite-optics"],
    opticsJonesChecked.withModels ["finite-optics"]
  ]
  models := [finiteOpticsModel]
  outOfScope := [
    { label := "Maxwell boundary problem", explanation := "continuous electromagnetic boundary conditions and dispersion require an analytic field theory" },
    { label := "diffraction and Fourier limits", explanation := "integral transforms, apertures and propagation limits are not inferred" },
    { label := "atomic calibration", explanation := "the finite unitary certificate does not establish experimental calibration" }
  ]
  obligations := [
    { name := "optical continuum bridge", statement := "connect the finite ABCD/Jones model to the intended Maxwell or atomic Hamiltonian calculation", source := "external optics / AMO analysis" }
  ]

def FluidTheoryPackage : TheoryPackage where
  name := "finite fluid and plasma transport"
  domain := "finite-volume fluids / plasma currents / discrete vorticity"
  assumptions := [
    { name := "finite mesh", statement := "the cell and edge types are finite", source := "discretisation declaration" },
    { name := "closed internal edges", statement := "every edge is internal, so boundary fluxes are included explicitly or absent", source := "finite-volume model" },
    { name := "discrete derivatives", statement := "vorticity uses commuting finite/discrete derivations when invoked", source := "discrete differential model" }
  ]
  claims := [fluidConservationChecked.withModels ["finite-fluid"]]
  models := [finiteFluidModel]
  outOfScope := [
    { label := "continuum Navier--Stokes", explanation := "existence, regularity, turbulence closure and continuum limits require external analysis" },
    { label := "kinetic closure", explanation := "Vlasov, gyrokinetic and collision operators need separately certified approximations" },
    { label := "physical boundary modelling", explanation := "wall, sheath and open-boundary fluxes must be represented by explicit certificates" }
  ]
  obligations := [
    { name := "fluid continuum bridge", statement := "provide stability, consistency and convergence certificates for the selected finite-volume or plasma discretisation", source := "external fluid / numerical analysis" }
  ]

def defaultPackages : List TheoryPackage :=
  [QuantumTheoryPackage, FinitePDETheoryPackage, FiniteEuclideanTheoryPackage,
    ClassicalMechanicsTheoryPackage, GaugeTheoryPackage,
    CondensedMatterTheoryPackage, RelativityTheoryPackage,
    StatisticalMechanicsTheoryPackage]

def defaultProject : ResearchProject :=
  ResearchProject.ofPackages "LeanPhy default domains" defaultPackages

def extendedPackages : List TheoryPackage :=
  defaultPackages ++ [FieldTheoryPackage, HighEnergyTheoryPackage,
    AnalysisBridgeTheoryPackage]

def extendedProject : ResearchProject :=
  ResearchProject.ofPackages "LeanPhy extended domains" extendedPackages

def broadPackages : List TheoryPackage :=
  extendedPackages ++ [OpticsTheoryPackage, FluidTheoryPackage]

def broadProject : ResearchProject :=
  ResearchProject.ofPackages "LeanPhy broad applied domains" broadPackages

def defaultManifest : ResearchManifest :=
  (ResearchManifest.ofProject "LeanPhy default reproducibility manifest"
    defaultProject).withProfiles [
      "LeanPhy.Entry.Research", "LeanPhy.Entry.Quantum",
      "LeanPhy.Entry.FinitePDE", "LeanPhy.Entry.StatMech",
      "LeanPhy.Entry.Gauge", "LeanPhy.Entry.Condensed",
      "LeanPhy.Entry.Classical", "LeanPhy.Entry.Relativity"]
    |>.withSources ["LeanPhy.Workflow", "lakefile.toml", "lean-toolchain"]
    |>.withExternalTools ["Lean kernel", "mathlib", "lake"]

def extendedManifest : ResearchManifest :=
  (ResearchManifest.ofProject "LeanPhy extended reproducibility manifest"
    extendedProject).withProfiles [
      "LeanPhy.Entry.Research", "LeanPhy.Entry.Quantum",
      "LeanPhy.Entry.FieldTheory", "LeanPhy.Entry.HighEnergy",
      "LeanPhy.Entry.Analysis", "LeanPhy.Entry.FinitePDE",
      "LeanPhy.Entry.StatMech", "LeanPhy.Entry.Gauge",
      "LeanPhy.Entry.Condensed", "LeanPhy.Entry.Classical",
      "LeanPhy.Entry.Relativity"]
    |>.withSources ["LeanPhy.Workflow", "lakefile.toml", "lean-toolchain"]
    |>.withExternalTools ["Lean kernel", "mathlib", "lake"]

def broadManifest : ResearchManifest :=
  (ResearchManifest.ofProject "LeanPhy broad reproducibility manifest"
    broadProject).withProfiles [
      "LeanPhy.Entry.Research", "LeanPhy.Entry.Quantum",
      "LeanPhy.Entry.FieldTheory", "LeanPhy.Entry.HighEnergy",
      "LeanPhy.Entry.Analysis", "LeanPhy.Entry.FinitePDE",
      "LeanPhy.Entry.StatMech", "LeanPhy.Entry.Gauge",
      "LeanPhy.Entry.Condensed", "LeanPhy.Entry.Classical",
      "LeanPhy.Entry.Relativity", "LeanPhy.Entry.Optics",
      "LeanPhy.Entry.Fluid"]
    |>.withSources ["LeanPhy.Workflow", "lakefile.toml", "lean-toolchain"]
    |>.withExternalTools ["Lean kernel", "mathlib", "lake"]

end LeanPhy.Workflow
