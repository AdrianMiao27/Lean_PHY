import LeanPhy.Examples.EffectiveResearch
import LeanPhy.CLI.Core

private def manifest : LeanPhy.Workflow.ResearchManifest :=
  LeanPhy.Workflow.ResearchManifest.ofProject "effective theory research"
    (LeanPhy.Workflow.ResearchProject.ofPackages "elimination and effective readouts"
      [LeanPhy.Examples.EffectiveResearch.package])

def main (args : List String) : IO Unit := LeanPhy.CLI.runWithCatalog manifest args
