import Lean.Elab.Command
import Lean.Elab.AuxDef
import Lean.Util.CollectAxioms
import Lean.Data.Json

/-!
# Declaration and dependency auditing

These commands inspect the checked Lean environment, including imported
declarations. They are verification tooling, not mathematical soundness theorems.
The permitted foundational axioms are propext, Classical.choice and Quot.sound.
An explicit hypothesis in a theorem remains a hypothesis; a new global axiom
is rejected. A successful audit does not discharge physical modelling premises.

Library selection uses defining modules, so private declarations and declarations
in other namespaces cannot escape the scan. Dependencies are checked transitively,
including dependencies on axioms declared outside the selected modules.
-/
namespace LeanPhy.Verification
open Lean Elab Command

def allowedAxiom (name : Name) : Bool :=
  name == ``propext || name == ``Classical.choice || name == ``Quot.sound

/-- An imported declaration's defining module, or the current module for local ones. -/
def definingModule (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.modules[index.toNat]!.module
  | none => env.mainModule

private def namesJson (names : Array Name) : Json :=
  toJson ((names.qsort Name.lt).map Name.toString)

/-- Reject empty selections and any dependency beyond the stated foundations. -/
def audit (scope : String) (select : Environment → Name → Bool) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let mut count := 0
  let mut privateCount := 0
  let mut theoremCount := 0
  let mut modules : NameSet := {}
  let mut used : NameSet := {}
  let mut failures : Array (Name × Array Name) := #[]
  -- SMap.map₁ holds imports, map₂ holds declarations in this file. Both matter.
  for (name, info) in env.constants do
    if select env name then
      count := count + 1
      if isPrivateName name then privateCount := privateCount + 1
      if info matches .thmInfo _ then theoremCount := theoremCount + 1
      modules := modules.insert (definingModule env name)
      let axs ← liftCoreM <| Lean.collectAxioms name
      for ax in axs do used := used.insert ax
      let forbidden := axs.filter (fun ax => !allowedAxiom ax)
      if !forbidden.isEmpty then failures := failures.push (name, forbidden)
  if count == 0 then
    throwError "LeanPhy dependency audit rejected an empty declaration selection ({scope})"
  if !failures.isEmpty then
    throwError "LeanPhy dependency audit rejected {failures.size} declarations with forbidden dependencies: {failures}"
  let summary := Json.mkObj [
    ("status", toJson "axiom_audit_passed"), ("scope", toJson scope),
    ("declarations_audited", toJson count), ("theorems_audited", toJson theoremCount),
    ("private_declarations_audited", toJson privateCount),
    ("defining_modules", namesJson modules.toArray),
    ("axioms_used", namesJson used.toArray),
    ("allowed_axioms", namesJson #[``propext, ``Classical.choice, ``Quot.sound])]
  logInfo m!"LeanPhy dependency audit: {summary.compress}"

/-- Audit all declarations whose defining module is LeanPhy or a submodule. -/
elab "#leanphy_audit_library" : command =>
  audit "imported LeanPhy modules and current LeanPhy module" fun env name =>
    (`LeanPhy).isPrefixOf (definingModule env name)

/-- Place at the end of a research file to audit every declaration preceding it. -/
elab "#leanphy_audit_module" : command =>
  audit "current module up to this command" fun env name =>
    definingModule env name == env.mainModule

/-- Audit specified imported module trees without relying on declaration namespaces. -/
elab "#leanphy_audit_modules" "[" prefixes:ident,+ "]" : command => do
  let env ← getEnv
  let requested := prefixes.getElems.map Syntax.getId
  for modulePrefix in requested do
    unless env.header.moduleNames.any modulePrefix.isPrefixOf || modulePrefix.isPrefixOf env.mainModule do
      throwError "LeanPhy dependency audit: module prefix {modulePrefix} is not loaded"
  audit s!"module prefixes: {requested}" fun env name =>
    requested.any (·.isPrefixOf (definingModule env name))

end LeanPhy.Verification
