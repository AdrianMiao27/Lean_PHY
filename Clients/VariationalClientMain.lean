import LeanPhy.Examples.VariationalResearch
import LeanPhy.CLI.Core

private def manifest : LeanPhy.Workflow.ResearchManifest :=
  LeanPhy.Workflow.ResearchManifest.ofProject "variational research"
    ((LeanPhy.Workflow.ResearchProject.empty "variational research")
      |>.addPackage LeanPhy.Examples.VariationalResearch.package)

def main (args : List String) : IO Unit :=
  LeanPhy.CLI.runWithCatalog manifest args
