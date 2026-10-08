import LeanPhy.Examples.FermionResearch
import LeanPhy.CLI.Core

private def manifest : LeanPhy.Workflow.ResearchManifest :=
  LeanPhy.Workflow.ResearchManifest.ofProject "finite fermion research"
    (LeanPhy.Workflow.ResearchProject.ofPackages "operators, states and physical conventions"
      [LeanPhy.Examples.FermionResearch.package])

def main (args : List String) : IO Unit := LeanPhy.CLI.runWithCatalog manifest args
