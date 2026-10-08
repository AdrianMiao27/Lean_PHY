import LeanPhy.Workflow.Core
import LeanPhy.Library.Core

/-!
# Reusable research-project CLI

The library owns the proof terms; a client project should only provide its own
`ResearchManifest`.  This module factors the report and quality-gate logic out
of the repository's demo executable so a downstream Lean project can write

```lean
import LeanPhy.CLI.Core

def main (args : List String) : IO Unit :=
  LeanPhy.CLI.runWithCatalog myManifest args
```

and keep the ordinary `lake exe` workflow.  The command never constructs a
proof from text or a runtime boolean: it rejects an invalid ledger first and
then renders metadata for proof terms that were already checked while Lean
compiled the client module.
-/

namespace LeanPhy.CLI

open LeanPhy.Workflow

private def invalidProjectMessage (P : ResearchProject) : String :=
  let names := P.invalidPackages.map TheoryPackage.name
  let projectIssues := P.errorDiagnostics.map (fun diagnostic =>
    diagnostic.code ++ ":" ++ diagnostic.entry)
  "LeanPhy ledger validation failed: " ++
    String.intercalate ", " (names ++ projectIssues)

private def printPackageJson (P : ResearchProject) : IO Unit :=
  IO.println ("[" ++ String.intercalate ","
    (P.packages.map TheoryPackage.renderJson) ++ "]")

private inductive OutputMode where
  | text
  | packageJson
  | projectJson
  | dot
  | manifestJson
  | catalogJson
  | claimsJson
  | help

structure ParsedOptions where
  mode : Option OutputMode := none
  strict : Bool := false

private def selectMode (opts : ParsedOptions) (mode : OutputMode) :
    Except String ParsedOptions :=
  match opts.mode with
  | none => .ok { opts with mode := some mode }
  | some _ => .error "unknown or conflicting output options"

private def parseMode : List String → ParsedOptions → Except String ParsedOptions
  | [], opts => .ok opts
  | "--strict" :: rest, opts =>
      if opts.strict then .error "--strict was provided more than once"
      else parseMode rest { opts with strict := true }
  | "--help" :: [], opts =>
      if opts.mode.isSome || opts.strict then
        .error "--help cannot be combined with another option"
      else .ok { opts with mode := some .help }
  | "--json" :: rest, opts => selectMode opts .packageJson |>.bind (parseMode rest)
  | "--project-json" :: rest, opts =>
      selectMode opts .projectJson |>.bind (parseMode rest)
  | "--dot" :: rest, opts => selectMode opts .dot |>.bind (parseMode rest)
  | "--manifest-json" :: rest, opts =>
      selectMode opts .manifestJson |>.bind (parseMode rest)
  | "--catalog-json" :: rest, opts =>
      selectMode opts .catalogJson |>.bind (parseMode rest)
  | "--claims-json" :: rest, opts =>
      selectMode opts .claimsJson |>.bind (parseMode rest)
  | option :: _, _ => .error ("unknown or conflicting option: " ++ option)

private def usage : String :=
  "LeanPhy project report\n" ++
  "  --json           render the package array\n" ++
  "  --project-json   render one project object\n" ++
  "  --dot            render the dependency graph as Graphviz DOT\n" ++
  "  --manifest-json  render the reproducibility manifest\n" ++
  "  --catalog-json   render the kernel-checked reusable-lemma catalogue\n" ++
  "  --claims-json    render the flat kernel-checked claim index\n" ++
  "  --strict         fail when external research obligations remain open\n" ++
  "  --help           show this help\n"

/-- Render one compiled project according to the usual `leanphy_check` flags.

The project is deliberately taken from the manifest itself.  Accepting a
separate `ResearchProject` here would allow a client to print metadata for a
different project from the one whose toolchain and source entries it reports.
Keeping one value at this boundary makes that class of bookkeeping error
unrepresentable for downstream clients. -/
def runWithCatalog (M : ResearchManifest) (args : List String)
    (catalog : List LeanPhy.Library.CheckedLemma := []) : IO Unit := do
  let P := M.project
  if P.hasErrors then
    throw <| IO.userError (invalidProjectMessage P)
  match parseMode args {} with
  | .error message => throw <| IO.userError (message ++ "\n\n" ++ usage)
  | .ok parsed =>
      if parsed.strict && P.claimCount == 0 then
        throw <| IO.userError
          "LeanPhy strict verification failed: no kernel-checked claims are registered"
      else if parsed.strict && P.obligationCount != 0 then
        throw <| IO.userError
          ("LeanPhy strict verification failed: " ++
            toString P.obligationCount ++ " external obligation(s) remain open")
      else
        match parsed.mode.getD .text with
        | .help => IO.println usage
        | .manifestJson => IO.println (ResearchManifest.renderJson M)
        | .catalogJson => IO.println (LeanPhy.Library.renderJsonIn catalog)
        | .claimsJson => IO.println (ResearchProject.renderClaimsJson P)
        | .projectJson => IO.println (ResearchProject.renderJson P)
        | .dot => IO.println (ResearchProject.renderDot P)
        | .packageJson => printPackageJson P
        | .text => IO.println (ResearchProject.render P)

end LeanPhy.CLI
