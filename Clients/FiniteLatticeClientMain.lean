import LeanPhy.Examples.FiniteLatticeResearch
import LeanPhy.CLI.Core

private def manifest : LeanPhy.Workflow.ResearchManifest :=
  LeanPhy.Workflow.ResearchManifest.ofProject "finite lattice RG and Ward diagnostics"
    (LeanPhy.Workflow.ResearchProject.ofPackages
      "finite blocking, symmetry insertions and observable error budgets"
      [LeanPhy.Examples.FiniteLatticeResearch.package])

def main (args : List String) : IO Unit :=
  LeanPhy.CLI.runWithCatalog manifest args
