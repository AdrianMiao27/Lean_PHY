import LeanPhy.Examples.FermionWordResearch
import LeanPhy.CLI.Core

private def manifest : LeanPhy.Workflow.ResearchManifest :=
  LeanPhy.Workflow.ResearchManifest.ofProject "interacting fermion expressions"
    (LeanPhy.Workflow.ResearchProject.ofPackages "normal ordering and actual many-body equations"
      [LeanPhy.Examples.FermionWordResearch.package])

def main (args : List String) : IO Unit := LeanPhy.CLI.runWithCatalog manifest args
