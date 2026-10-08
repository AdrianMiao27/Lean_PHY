import LeanPhy.Examples.SelfConsistencyResearch
import LeanPhy.CLI.Core

private def manifest : LeanPhy.Workflow.ResearchManifest :=
  LeanPhy.Workflow.ResearchManifest.ofProject "finite-source self-consistency"
    (LeanPhy.Workflow.ResearchProject.ofPackages "actual closures and residual budgets"
      [LeanPhy.Examples.SelfConsistencyResearch.package])

def main (args : List String) : IO Unit := LeanPhy.CLI.runWithCatalog manifest args
