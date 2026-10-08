import Lean.Data.Json

namespace LeanPhy.Library

structure CheckedLemma where
  name : String
  domain : String
  statement : String
  source : String
  tags : List String
  proposition : Prop
  proof : proposition

namespace CheckedLemma

def ofTheorem (name domain statement source : String) (tags : List String)
    {P : Prop} (h : P) : CheckedLemma where
  name := name
  domain := domain
  statement := statement
  source := source
  tags := tags
  proposition := P
  proof := h

def stableId (entry : CheckedLemma) : String :=
  "leanphy.lemma:" ++ entry.name

end CheckedLemma

private def containsSub (needle haystack : String) : Bool :=
  if needle.isEmpty then true
  else
    let n := needle.toList
    let rec loop : List Char → Bool
      | [] => false
      | rest@(_ :: tail) =>
          if n.isPrefixOf rest then true else loop tail
    loop haystack.toList

private def matchesQuery (query : String) (entry : CheckedLemma) : Bool :=
  query.isEmpty ||
    containsSub query entry.name ||
    containsSub query entry.domain ||
    containsSub query entry.statement ||
    entry.tags.any (containsSub query)

/-- Case-sensitive substring search over the checked catalogue.  Search is
    intentionally metadata-only; callers still use `source`/`name` with the
    ordinary theorem namespace to write a proof. -/
def searchIn (entries : List CheckedLemma) (query : String) : List CheckedLemma :=
  entries.filter (matchesQuery query)

def namesIn (lemmas : List CheckedLemma) : List String :=
  lemmas.map CheckedLemma.name

private def jsonEscapeChar (c : Char) : String :=
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c = '\n' then "\\n"
  else if c = '\r' then "\\r"
  else if c = '\t' then "\\t"
  else c.toString

private def jsonString (s : String) : String :=
  "\"" ++ (s.toList.map jsonEscapeChar).foldl (· ++ ·) "" ++ "\""

private def renderTags : List String → String
  | [] => ""
  | [tag] => jsonString tag
  | tag :: rest => jsonString tag ++ "," ++ renderTags rest

private def renderOne (entry : CheckedLemma) : String :=
  "{" ++ jsonString "name" ++ ":" ++ jsonString entry.name ++
    "," ++ jsonString "id" ++ ":" ++ jsonString entry.stableId ++
    "," ++ jsonString "domain" ++ ":" ++ jsonString entry.domain ++
    "," ++ jsonString "statement" ++ ":" ++ jsonString entry.statement ++
    "," ++ jsonString "source" ++ ":" ++ jsonString entry.source ++
    "," ++ jsonString "tags" ++ ":[" ++ renderTags entry.tags ++ "]" ++
    "," ++ jsonString "status" ++ ":" ++ jsonString "kernel_checked" ++ "}"

private def renderMany : List CheckedLemma → String
  | [] => ""
  | [entry] => renderOne entry
  | entry :: rest => renderOne entry ++ "," ++ renderMany rest

def renderJsonIn (lemmas : List CheckedLemma) : String :=
  "[" ++ renderMany lemmas ++ "]"

end LeanPhy.Library
