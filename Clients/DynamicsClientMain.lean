import LeanPhy.Examples.DynamicsResearch
import LeanPhy.CLI.Core

private def manifest : LeanPhy.Workflow.ResearchManifest :=
  LeanPhy.Workflow.ResearchManifest.ofProject "finite quantum response"
    (LeanPhy.Workflow.ResearchProject.ofPackages "actual dynamics and normalized thermal perturbations"
      [LeanPhy.Examples.DynamicsResearch.package])

def main (args : List String) : IO Unit := LeanPhy.CLI.runWithCatalog manifest args
