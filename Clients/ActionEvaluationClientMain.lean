import LeanPhy.Examples.ActionEvaluationResearch
import LeanPhy.CLI.Core

private def manifest : LeanPhy.Workflow.ResearchManifest :=
  LeanPhy.Workflow.ResearchManifest.ofProject "actual action and field evaluation"
    (LeanPhy.Workflow.ResearchProject.ofPackages "variations, boundary flux and profile currents"
      [LeanPhy.Examples.ActionEvaluationResearch.package])

def main (args : List String) : IO Unit := LeanPhy.CLI.runWithCatalog manifest args
