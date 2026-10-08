import LeanPhy.CLI.Core
import LeanPhy.Workflow.DefaultPackages
import LeanPhy.Library

namespace LeanPhy.CLI

open LeanPhy.Workflow

def runProject (M : ResearchManifest) (args : List String) : IO Unit :=
  runWithCatalog M args LeanPhy.Library.catalog

/-- Run a client-supplied manifest.  The manifest's project is the only source
of claims; profile and toolchain fields remain reproducibility metadata. -/
def run (M : ResearchManifest) (args : List String := []) : IO Unit :=
  runWithCatalog M args LeanPhy.Library.catalog

/-- Convenience entry point for LeanPhy's built-in catalogue.  `--extended`
selects the eleven-package cross-domain profile and `--broad` adds the
optics/AMO and fluid/plasma adapters; all other flags match `run`. -/
def runDefault (args : List String := []) : IO Unit := do
  let outputArgs := args.filter (fun arg => arg != "--extended" && arg != "--broad")
  if args.any (fun arg => arg == "--broad") then
    run broadManifest outputArgs
  else if args.any (fun arg => arg == "--extended") then
    run extendedManifest outputArgs
  else
    run defaultManifest outputArgs
  if outputArgs == ["--help"] then
    IO.println ("Built-in profiles:\n" ++
      "  --extended       use the eleven-package built-in profile\n" ++
      "  --broad          add optics/AMO and fluid/plasma profiles")

end LeanPhy.CLI
