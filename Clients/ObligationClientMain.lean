import LeanPhy.Examples.ObligationWorkflow
import LeanPhy.CLI.Core

open LeanPhy.Workflow LeanPhy.Examples.ObligationWorkflow

/-- A downstream-style client using only the independent workflow and CLI. -/
def main (args : List String) : IO Unit := do
  let package := if args.contains "--open" then withEvidence
    else if args.contains "--duplicate" then oneClosed
    else closed 0
  let manifest := ResearchManifest.ofProject "obligation client"
    (ResearchProject.ofPackages "registered targets" [package])
  LeanPhy.CLI.runWithCatalog manifest
    (args.filter fun a => a != "--open" && a != "--duplicate")
