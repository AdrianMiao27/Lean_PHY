import LeanPhy.CLI

/-!
# Downstream project scaffolding

`leanphy_init` creates a small, ordinary Lean project.  The generated files
use the same `lake build` and `lake exe` workflow as any Lean 4 project; the
scaffolder only writes source and configuration files and never fabricates a
proof.  A researcher can therefore replace the placeholder theorem and let
the kernel reject an incomplete derivation in the usual way.
-/

namespace LeanPhy.Scaffold

structure Options where
  target : String
  projectName : String := "physics_research"
  leanphyPath : String := "../Lean_phy"
  profile : String := "quantum"
  force : Bool := false

private def validName (name : String) : Bool :=
  !name.isEmpty && name.toList.all (fun c =>
    Char.isAlphanum c || c == '_' || c == '-')

private def tomlString (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\""

private def usage : String :=
  "LeanPhy project scaffold\n" ++
  "  leanphy_init TARGET [--name NAME] [--profile PROFILE]\n" ++
  "               [--leanphy-path PATH] [--force]\n\n" ++
  "PROFILE is one of minimal, quantum, optics, fluid, physics, research (default: quantum).\n" ++
  "The generated project uses the ordinary lake build/check workflow."

private def parseLoop : List String → Options → Except String Options
  | [], opts =>
      if validName opts.projectName then .ok opts
      else .error "project name must contain only letters, digits, '_' or '-'."
  | "--help" :: _, _ => .error usage
  | "--force" :: rest, opts => parseLoop rest { opts with force := true }
  | "--name" :: name :: rest, opts => parseLoop rest { opts with projectName := name }
  | "--profile" :: profile :: rest, opts =>
      if ["minimal", "quantum", "optics", "fluid", "physics", "research"].contains profile then
        parseLoop rest { opts with profile := profile }
      else .error ("unknown profile: " ++ profile)
  | "--leanphy-path" :: path :: rest, opts =>
      parseLoop rest { opts with leanphyPath := path }
  | option :: _, _ => .error ("unknown or incomplete option: " ++ option ++ "\n\n" ++ usage)

private def parseArgs : List String → Except String Options
  | [] => .error ("missing TARGET\n\n" ++ usage)
  | target :: rest => parseLoop rest { target := target }

private def profileImport (profile : String) : String :=
  match profile with
  | "minimal" => "LeanPhy.Minimal"
  | "quantum" => "LeanPhy.Entry.Quantum"
  | "optics" => "LeanPhy.Entry.Optics"
  | "fluid" => "LeanPhy.Entry.Fluid"
  | "physics" => "LeanPhy.Entry.Physics"
  | "research" => "LeanPhy.Entry.Research"
  | _ => "LeanPhy.Entry.Quantum"

private def lakefile (opts : Options) : String :=
  let name := opts.projectName
  "name = \"" ++ tomlString name ++ "\"\n" ++
  "version = \"0.1.0\"\n" ++
  "defaultTargets = [\"" ++ tomlString (name ++ "_check") ++ "\"]\n\n" ++
  "[[lean_lib]]\n" ++
  "name = \"Research\"\n\n" ++
  "[[lean_exe]]\n" ++
  "name = \"" ++ tomlString (name ++ "_check") ++ "\"\n" ++
  "root = \"Main\"\n\n" ++
  "[[require]]\n" ++
  "name = \"LeanPhy\"\n" ++
  "path = \"" ++ tomlString opts.leanphyPath ++ "\"\n"

private def leanToolchain : String :=
  "leanprover/lean4:v4.34.0\n"

private def researchFile (opts : Options) : String :=
  "import " ++ profileImport opts.profile ++ "\n" ++
  "import LeanPhy.Workflow\n" ++
  "import LeanPhy.CLI\n\n" ++
  "namespace Research\n\n" ++
  "open LeanPhy.Workflow\n\n" ++
  "/-- Replace the placeholder model assumptions with the assumptions of the paper. -/\n" ++
  "def package : TheoryPackage :=\n" ++
  "  TheoryPackage.empty \"" ++ opts.projectName ++ " model\" \"theory\"\n" ++
  "    |>.addAssumptionText \"finite-model\"\n" ++
  "      \"the current development uses a finite or explicitly truncated representation\"\n" ++
  "      \"model declaration\"\n" ++
  "    |>.addBoundaryText \"continuum bridge\"\n" ++
  "      \"continuum limits, domains and physical calibration require explicit theorems\"\n" ++
  "    |>.addObligationText \"continuum bridge\"\n" ++
  "      \"prove the analysis or numerical result that connects this finite model to the target theory\"\n" ++
  "      \"research project\"\n\n" ++
  "/-- A real theorem must be supplied as an ordinary Lean proof term. -/\n" ++
  "def packageWithClaim {P : Prop} (proof : P) : TheoryPackage :=\n" ++
  "  package.addTheoremWithAssumptions\n" ++
  "    \"first theorem\" \"replace with the statement proved in this file\"\n" ++
  "    \"Research.lean\" [\"finite-model\"] proof\n\n" ++
  "def manifest : ResearchManifest :=\n" ++
  "  let base := ResearchManifest.ofProject \"" ++ opts.projectName ++ " manifest\"\n" ++
  "    (ResearchProject.empty \"" ++ opts.projectName ++ " project\"\n" ++
  "      |>.addPackage package)\n" ++
  "  let profiled := ResearchManifest.withProfiles base [\"" ++ profileImport opts.profile ++ "\"]\n" ++
  "  ResearchManifest.withSources profiled [\"Research.lean\", \"Main.lean\", \"lakefile.toml\"]\n\n" ++
  "end Research\n"

private def mainFile : String :=
  "import LeanPhy.CLI\n" ++
  "import Research\n\n" ++
  "/- `lake exe PROJECT_check --project-json` emits the machine-readable ledger. -/\n" ++
  "def main (args : List String) : IO Unit :=\n" ++
  "  LeanPhy.CLI.run Research.manifest args\n"

private def readme (opts : Options) : String :=
  "# " ++ opts.projectName ++ "\n\n" ++
  "This project was created by `leanphy_init`.  Edit `Research.lean`, replace\n" ++
  "the placeholder proof with ordinary Lean declarations, and run:\n\n" ++
  "```text\n" ++
  "lake build\n" ++
  "lake exe " ++ opts.projectName ++ "_check --project-json\n" ++
  "```\n\n" ++
  "A successful report is conditional on the assumptions and open obligations\n" ++
  "recorded in the package.  Runtime output is metadata; theorem proof terms\n" ++
  "are checked while Lean compiles the source.\n\n" ++
  "For routine algebraic derivations, a theorem body can start with `by physics`;\n" ++
  "the tactic is only a composition of ordinary kernel-checked Lean tactics.\n" ++
  "Use `by physics_search` to ask Lean's ordinary theorem search for a reusable\n" ++
  "lemma before falling back to that algebraic normalizer.  The catalogue can\n" ++
  "be exported with `--catalog-json`; the project's flat claim index is\n" ++
  "available with `--claims-json`.  Both contain only compiled proof entries.\n\n" ++
  "The scaffold also includes scripts/verify-leanphy.sh and a GitHub Actions\n" ++
  "workflow.  Both run the same lake build and machine-readable report checks.\n"

private def verifyScript (opts : Options) : String :=
  "#!/usr/bin/env bash\n" ++
  "set -euo pipefail\n\n" ++
  "lake build\n" ++
  "lake exe " ++ opts.projectName ++ "_check --project-json\n" ++
  "lake exe " ++ opts.projectName ++ "_check --manifest-json\n"

private def workflow : String :=
  "name: LeanPhy verification\n\n" ++
  "on:\n  push:\n  pull_request:\n\n" ++
  "jobs:\n  verify:\n    runs-on: ubuntu-latest\n    steps:\n" ++
  "      - uses: actions/checkout@v4\n" ++
  "      - uses: leanprover/lean-action@v1\n" ++
  "      - run: bash scripts/verify-leanphy.sh\n"

private def writeOne (root : System.FilePath) (name content : String) : IO Unit :=
  IO.FS.writeFile (root.join name) content

def create (opts : Options) : IO Unit := do
  let root := System.FilePath.mk opts.target
  let alreadyThere ← root.pathExists
  /- A common shell workflow creates the destination with `mktemp -d` or
     `mkdir` before invoking a generator.  Treat an existing *empty*
     directory as a fresh target, while retaining the safety guard for any
     directory that already contains user files. -/
  if alreadyThere && !opts.force then
    let entries ← System.FilePath.readDir root
    if !entries.isEmpty then
      throw <| IO.userError ("target already exists and is not empty: " ++ opts.target ++
        " (use --force only to overwrite the generated files)")
  IO.FS.createDirAll root
  IO.FS.createDirAll (root.join ".github" |>.join "workflows")
  IO.FS.createDirAll (root.join "scripts")
  writeOne root "lakefile.toml" (lakefile opts)
  writeOne root "lean-toolchain" leanToolchain
  writeOne root "Research.lean" (researchFile opts)
  writeOne root "Main.lean" mainFile
  writeOne root "README.md" (readme opts)
  writeOne root ".gitignore" ".lake/\n"
  writeOne (root.join "scripts") "verify-leanphy.sh" (verifyScript opts)
  writeOne (root.join ".github" |>.join "workflows") "leanphy.yml" workflow
  IO.println ("Created LeanPhy project at " ++ opts.target)
  IO.println ("Next: cd " ++ opts.target ++ " && lake build")

def run (args : List String) : IO Unit := do
  if args == ["--help"] then
    IO.println usage
  else
    match parseArgs args with
    | .error message =>
        if message == usage then IO.println message
        else throw <| IO.userError message
    | .ok opts => create opts

end LeanPhy.Scaffold
