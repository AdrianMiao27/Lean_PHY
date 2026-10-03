import LeanPhy.Entry.Research
import LeanPhy.Entry.Quantum

/-!
# Research-package template

Copy this file into a project and replace the model metadata and theorem
proofs.  The imports show the normal Lean workflow: choose one or more
`Entry.*` profiles, write ordinary `def`/`theorem` declarations, and register
the resulting proof terms in a package.  A failed proof stops elaboration; a
missing continuum or numerical obligation remains visible in `outOfScope` or
`obligations`.
-/

namespace LeanPhy.Examples

open LeanPhy.Workflow

def researchBase : TheoryPackage :=
  TheoryPackage.addObligationText
    (TheoryPackage.ofModel
      "replaceable research model"
      "finite algebra / discretised dynamics"
      [
        { name := "model domain", statement := "state labels and operators are finite", source := "model declaration" },
        { name := "coefficient field", statement := "all scalar identities use the declared ring or field", source := "model declaration" }
      ]
      [
        { label := "continuum limit", explanation := "a finite proof does not establish existence or convergence of the continuum model" },
        { label := "numerical soundness", explanation := "rounding, solver error and conditioning need separate certificates" }
      ])
    "continuum bridge"
    "supply the analysis or numerical certificate needed to interpret the finite result in the target theory"
    "research project"

/- Add a real theorem from any imported domain module.  The final argument is
   an ordinary Lean proof term, so this function cannot create evidence from
   a string or a runtime flag. -/
def researchClaim {P : Prop} (proof : P) : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions
    "replaceable theorem"
    "write the physical statement in readable notation"
    "module.path.to_theorem"
    ["model domain", "coefficient field"]
    proof

def researchWithClaim {P : Prop} (proof : P) : TheoryPackage :=
  researchBase.addClaim (researchClaim proof)

def researchClaimEntry {P : Prop} (proof : P) : CheckedClaim :=
  researchClaim proof

def researchWithDerivedClaim {P : Prop} (proof : P) : TheoryPackage :=
  (researchWithClaim proof).addDerivedTheoremRegistered (researchClaimEntry proof)
    (by
      simp [researchWithClaim, researchClaimEntry, researchClaim, researchBase,
        TheoryPackage.addObligationText, TheoryPackage.addObligation,
        TheoryPackage.ofModel, TheoryPackage.addClaim])
    "derived theorem"
    "the next paper step reuses the preceding ledger claim"
    "research_project.lean"
    ["model domain", "coefficient field"]
    (fun h => h)

/- When a model premise is already represented by a Lean proposition, use an
   `AssumptionWitness` so the premise proof is passed into the theorem step.
   External analytic premises can continue to use the metadata-only records
   above. -/
def modelWitness : AssumptionWitness where
  metadata :=
    { name := "typed model premise"
      statement := "the model premise supplied to this finite derivation"
      source := "model declaration" }
  proposition := True
  proof := True.intro

def witnessedResearch : TheoryPackage :=
  TheoryPackage.empty "witnessed research model" "finite algebra"
    |>.addTheoremUnderAssumptionRegistered modelWitness
      "witnessed theorem" "the theorem consumes the typed model premise"
      "research_project.lean" (fun h => h)

/- An external obligation can later be closed by a proof-bearing claim.  The
   membership argument makes a misspelled obligation name a Lean error. -/
def closedResearch : TheoryPackage :=
  researchBase.resolveObligation "continuum bridge" (by
    simp [researchBase, TheoryPackage.addObligationText,
      TheoryPackage.addObligation, TheoryPackage.ofModel])
    "finite bridge theorem"
    "the declared finite result is transported through the supplied bridge"
    "research_project.lean"
    ["model domain", "coefficient field"] [] True.intro

/- The typed form binds the open obligation to a Lean proposition.  In a real
   project replace `True` with the convergence, domain, or numerical theorem
   that the external bridge is required to establish. -/
def continuumBridgeWitness : ExternalObligationWitness where
  metadata :=
    { name := "continuum bridge"
      statement := "supply the analysis or numerical certificate needed to interpret the finite result in the target theory"
      source := "research project" }
  proposition := True

def typedClosedResearch : TheoryPackage :=
  researchBase.resolveObligationWitness continuumBridgeWitness (by
    simp [researchBase, TheoryPackage.addObligationText,
      TheoryPackage.addObligation, TheoryPackage.ofModel,
      continuumBridgeWitness])
    "typed finite bridge theorem"
    "the declared finite result is transported through the typed bridge"
    "research_project.lean" ["model domain", "coefficient field"] []
    (fun h => h) True.intro

example : researchBase.status = "UNVERIFIED" := rfl
example : (researchWithClaim True.intro).status = "VERIFIED-CONDITIONAL" := rfl
example : (researchWithClaim True.intro).assumptionCount = 2 := rfl
example : (researchWithClaim True.intro).boundaryCount = 2 := rfl
example : (researchWithClaim True.intro).claimCount = 1 := rfl
example : researchBase.obligationCount = 1 := rfl
example : (researchWithClaim True.intro).obligationCount = 1 := rfl
example : (researchWithDerivedClaim True.intro).claimCount = 2 := rfl
example : (researchWithDerivedClaim True.intro).missingClaimReferenceCount = 0 := rfl
example : witnessedResearch.claimCount = 1 := rfl
example : witnessedResearch.missingAssumptionReferenceCount = 0 := rfl
example : closedResearch.claimCount = 1 := rfl
example : closedResearch.obligationCount = 0 := rfl
example : closedResearch.status = "VERIFIED-CONDITIONAL" := rfl
example : typedClosedResearch.claimCount = 1 := rfl
example : typedClosedResearch.obligationCount = 0 := rfl

/- The same API also gives a cheap quality gate for a hand-edited ledger.  The
   malformed package below is useful in downstream projects' unit tests: its
   proof is valid, but the metadata graph is rejected because it repeats an
   assumption name and points to a claim that has not been registered. -/
def malformedLedger : TheoryPackage :=
  (TheoryPackage.empty "malformed" "test")
    |>.addAssumptionText "duplicate" "first declaration" "test"
    |>.addAssumptionText "duplicate" "second declaration" "test"
    |>.addTheoremWithDependencies "claim" "valid proof, invalid links" "test"
      ["missing assumption"] ["missing claim"] True.intro

example : malformedLedger.hasErrors = true := by decide
example : malformedLedger.isWellFormed = false := by decide
example : malformedLedger.diagnosticCount = 3 := by decide

/- A claim can also be tied to a model by name.  The package quality gate
   rejects a misspelled model reference even though the proposition itself is
   a valid kernel proof. -/
def malformedModelLedger : TheoryPackage :=
  (TheoryPackage.empty "missing model" "test")
    |>.addTheoremForModel "unregistered-model" "claim" "model link is invalid" "test" []
      True.intro

example : malformedModelLedger.hasErrors = true := by decide
example : malformedModelLedger.missingModelReferenceCount = 1 := by decide

def malformedModelAssumptionLedger : TheoryPackage :=
  (TheoryPackage.empty "missing model assumption" "test")
    |>.addModelText "model" "finite test" "P" "X" "O" "step" ["unregistered assumption"]

example : malformedModelAssumptionLedger.hasErrors = true := by decide
example : malformedModelAssumptionLedger.missingModelAssumptionReferenceCount = 1 := by decide

def projectLedger : ResearchProject :=
  ResearchProject.empty "template project"
    |>.addPackage (researchWithClaim True.intro)

/- A reproducibility manifest is optional but recommended for papers.  It
  records the selected profiles and external tools while keeping the project
  proof terms in the compiled Lean artifact.  Use `withToolchain` when an
  archived bundle needs to record an older toolchain; the project CLI also
  supports `--dot` for a Graphviz view of the dependency edges. -/
def projectManifest : ResearchManifest :=
  let base := ResearchManifest.ofProject "template reproducibility manifest" projectLedger
  let profiled := ResearchManifest.withProfiles base
    ["LeanPhy.Entry.Research", "LeanPhy.Entry.Quantum"]
  let sourced := ResearchManifest.withSources profiled
    ["research_project.lean", "lakefile.toml", "lean-toolchain"]
  ResearchManifest.withExternalTools sourced ["Lean kernel", "mathlib", "lake"]

example : projectManifest.status = "VERIFIED-CONDITIONAL" := rfl
example : projectManifest.claimCount = 1 := rfl
example : projectManifest.obligationCount = 1 := rfl
example : projectManifest.toolchain.lean = "v4.34.0" := rfl

example : projectLedger.packageCount = 1 := rfl
example : projectLedger.status = "VERIFIED-CONDITIONAL" := rfl

end LeanPhy.Examples
