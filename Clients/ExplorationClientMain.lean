import LeanPhy.Examples.ExplorationResearch
import LeanPhy.CLI.Core

open LeanPhy.Workflow LeanPhy.Examples.ExplorationResearch

private def manifest (closed : Bool) : ResearchManifest :=
  ResearchManifest.ofProject "exploratory physics"
    (ResearchProject.ofPackages "parameter domains and model revisions"
      (if closed then [pairingClosed, massClosed, coveredPackage]
       else [pairingOpen, massOpen, pairingClosed, massClosed, coveredPackage]))

def main (args : List String) : IO Unit := do
  if args.contains "--help" then
    IO.println "Exploration: --closed selects the three proved revised/covered questions."
  LeanPhy.CLI.runWithCatalog (manifest (args.contains "--closed"))
    (args.filter (· != "--closed"))
