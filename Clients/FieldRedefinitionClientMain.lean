import LeanPhy.Examples.FieldRedefinitionResearch
import LeanPhy.CLI.Core

private def manifest : LeanPhy.Workflow.ResearchManifest :=
  LeanPhy.Workflow.ResearchManifest.ofProject "point field transformations"
    (LeanPhy.Workflow.ResearchProject.ofPackages "sources, actions and first-order boundary conditions"
      [LeanPhy.Examples.FieldRedefinitionResearch.package])

def main (args : List String) : IO Unit := LeanPhy.CLI.runWithCatalog manifest args
