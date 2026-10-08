import LeanPhy.Examples.MatrixCertificateResearch
import LeanPhy.CLI.Core

private def manifest : LeanPhy.Workflow.ResearchManifest :=
  LeanPhy.Workflow.ResearchManifest.ofProject "certified complex matrix data"
    (LeanPhy.Workflow.ResearchProject.ofPackages "resolvent domain and effective readouts"
      [LeanPhy.Examples.MatrixCertificateResearch.package])

def main (args : List String) : IO Unit := LeanPhy.CLI.runWithCatalog manifest args
