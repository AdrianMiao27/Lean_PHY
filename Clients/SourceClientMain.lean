import LeanPhy.Examples.SourceResponseResearch
import LeanPhy.CLI.Core

private def manifest : LeanPhy.Workflow.ResearchManifest :=
  LeanPhy.Workflow.ResearchManifest.ofProject "source response research"
    (LeanPhy.Workflow.ResearchProject.ofPackages "finite sources and fluctuations"
      [LeanPhy.Examples.SourceResponseResearch.package])

def main (args : List String) : IO Unit := LeanPhy.CLI.runWithCatalog manifest args
