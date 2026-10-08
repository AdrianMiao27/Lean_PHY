import Lean
import Lean.Util.CollectAxioms
import Lean.DeclarationRange
import Lean.DocString

/-!
# Declaration discovery from the compiled Lean environment

Unlike a manually labelled catalogue, this index reads actual declarations,
types, defining modules and axiom dependencies. It is navigation metadata;
using an entry in a proof still requires elaboration against its actual type.
`physics_index entries` generates a serializable declaration list at build time.
Only declarations in the current import closure are indexed.
-/

namespace LeanPhy.Library

open Lean Elab Command Meta

structure DeclarationEntry where
  name : String
  kind : String
  moduleName : String
  sourceFile : String
  line : Option Nat
  leanType : String
  doc : String
  axioms : List String
  typeDependencies : List String
  proofDependencies : List String
  bodyDependencies : List String
  deriving ToJson, FromJson, ToExpr, Inhabited

private def localNames (names : Array Name) : List String :=
  (names.toList.filter (fun n => (`LeanPhy).isPrefixOf n && !n.isInternal)).map Name.toString
    |>.mergeSort (· ≤ ·)

/-- Build an index from real, public physics declarations in the environment.
Unsafe definitions and compiler-private declarations are excluded. A theorem
with an untrusted axiom aborts generation rather than receiving a checked label. -/
def declarationEntries : CommandElabM (Array DeclarationEntry) := do
  let env ← getEnv
  let mut entries := #[]
  for (name, info) in env.constants do
    if !((`LeanPhy).isPrefixOf name) || name.isInternal || info.isUnsafe then continue
    let kind ← match info with
      | .thmInfo _ => pure "theorem"
      | .defnInfo _ => pure "definition"
      | .inductInfo _ => pure (if isStructure env name then "structure" else "inductive")
      | .ctorInfo _ => pure "constructor"
      | _ => continue
    let moduleName := match env.getModuleIdxFor? name with
      | some i => env.header.moduleNames[i.toNat]!
      | none => env.mainModule
    if moduleName == `LeanPhy.Library.Index then continue
    let ranges ← findDeclarationRanges? name
    -- Generated helpers have no source declaration location.
    if ranges.isNone then continue
    let axs ← liftCoreM <| Lean.collectAxioms name
    if axs.any (fun n => n != ``propext && n != ``Classical.choice && n != ``Quot.sound) then
      throwError "physics_index: untrusted proof dependency in {name}"
    let typeText ← liftTermElabM <| withOptions (fun o => o.setBool `pp.fullNames true) do
      return (← ppExpr info.type).pretty 120
    let doc := (← findDocString? env name).getD ""
    let bodyDeps := localNames ((info.value? true).map Expr.getUsedConstants |>.getD #[])
    entries := entries.push {
      name := name.toString, kind := kind, moduleName := moduleName.toString,
      sourceFile := moduleName.toString.replace "." "/" ++ ".lean",
      line := ranges.map (·.range.pos.line), leanType := typeText, doc := doc,
      axioms := (axs.toList.map Name.toString).mergeSort (· ≤ ·),
      typeDependencies := localNames info.type.getUsedConstants,
      proofDependencies := if info.isTheorem then bodyDeps else [],
      bodyDependencies := bodyDeps }
  return entries.qsort (fun a b => a.name < b.name)

/-- Generate the index as ordinary data in the client module. -/
elab "physics_index " id:ident : command => do
  let entries ← declarationEntries
  let declName := (← getCurrNamespace) ++ id.getId
  -- Keep generated proof-free data in small definitions. One enormous nested
  -- array literal otherwise exhausts kernel/compiler recursion on a full library.
  let mut chunks : Array Expr := #[]
  for i in [: (entries.size + 31) / 32] do
    let chunkName := Name.num (declName ++ `_chunk) i
    let value := toExpr (entries.extract (i * 32) ((i + 1) * 32))
    liftCoreM <| addAndCompile <| .defnDecl {
      name := chunkName, levelParams := [], type := toTypeExpr (Array DeclarationEntry),
      value := value, hints := .regular 0, safety := .safe }
    chunks := chunks.push (mkConst chunkName)
  let value ← liftTermElabM do
    let array ← mkArrayLit (toTypeExpr (Array DeclarationEntry)) chunks.toList
    mkAppM ``Array.flatten #[array]
  liftCoreM <| addAndCompile <| .defnDecl {
    name := declName, levelParams := [], type := toTypeExpr (Array DeclarationEntry),
    value := value, hints := .regular 0, safety := .safe }

private def containsText (query text : String) : Bool :=
  (text.toLower.splitOn query.toLower).length > 1

/-- Case-insensitive, whitespace-separated conjunction over actual names,
types, modules and documentation. No remote service or proof generation. -/
def DeclarationEntry.matches (entry : DeclarationEntry) (query : String) : Bool :=
  let text := entry.name ++ " " ++ entry.leanType ++ " " ++ entry.moduleName ++ " " ++ entry.doc
  (query.splitOn " ").all (fun word => word.isEmpty || containsText word text)

structure IndexOptions where
  query : String := ""
  moduleFilter : String := ""
  kind : String := ""
  json : Bool := false
  help : Bool := false

private def parseOptions : List String → IndexOptions → Except String IndexOptions
  | [], opts => .ok opts
  | "--query" :: q :: rest, opts => parseOptions rest { opts with query := q }
  | "--module" :: m :: rest, opts => parseOptions rest { opts with moduleFilter := m }
  | "--kind" :: k :: rest, opts =>
      if ["theorem", "definition", "structure", "inductive", "constructor"].contains k then
        parseOptions rest { opts with kind := k }
      else .error "--kind expects theorem, definition, structure, inductive or constructor"
  | "--json" :: rest, opts => parseOptions rest { opts with json := true }
  | "--help" :: rest, opts => parseOptions rest { opts with help := true }
  | arg :: _, _ => .error ("unknown or incomplete option: " ++ arg)

def runIndex (entries : Array DeclarationEntry) (args : List String) : IO Unit := do
  let opts ← match parseOptions args {} with
    | .ok opts => pure opts
    | .error message => throw <| IO.userError message
  if opts.help then
    IO.println "leanphy_index [--query 'words'] [--module LeanPhy.Condensed] [--kind theorem|definition|structure|inductive|constructor] [--json]"
    return
  let selected := entries.filter fun e =>
    e.matches opts.query && (opts.moduleFilter.isEmpty || e.moduleName.startsWith opts.moduleFilter) &&
      (opts.kind.isEmpty || e.kind == opts.kind)
  if opts.json then
    IO.println <| (Json.mkObj [("schema_version", toJson "1"),
      ("scope", toJson "public declarations in the compiled import closure"),
      ("entry_count", toJson selected.size), ("entries", toJson selected)]).compress
  else
    for e in selected do
      IO.println s!"{e.name} [{e.kind}]\n  import {e.moduleName}\n  {e.sourceFile}:{e.line.getD 0}\n  {e.leanType}\n"
    IO.println s!"{selected.size} declaration(s). Types retain all hypotheses; index metadata is not a proof."

end LeanPhy.Library
