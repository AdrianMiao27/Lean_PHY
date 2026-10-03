import LeanPhy.Quantum.Pauli
import LeanPhy.FieldTheory.CCR
import LeanPhy.GaugeTheory.FieldStrength
import LeanPhy.HighEnergy.Gamma
import LeanPhy.Classical.Symplectic
import LeanPhy.Relativity.Minkowski
import LeanPhy.StatMech.FiniteGibbs

/-!
# Kernel-checked physics lemma library

Long research developments need a way to find a reusable theorem without
turning a text search result into evidence.  `CheckedLemma` is the small
bridge used here: every entry contains the original proposition and its proof
as dependent fields, so the catalogue cannot contain a claim that did not
elaborate in Lean.  Search only filters already compiled entries and returns
metadata for navigation; it never constructs a proof from a string.

The catalogue is deliberately small and representative.  Domain packages can
extend it with `CheckedLemma.ofTheorem` in their own source files, while the
ordinary Lean theorem namespace remains the authoritative API.  This keeps
the feature compatible with `#check`, `exact?`, editor completion and normal
imports rather than introducing a second theorem language.
-/

namespace LeanPhy.Library

open scoped Matrix

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

/-! Explicitly typed wrappers keep polymorphic theorem constants from leaving
typeclass metavariables unresolved while the catalogue is elaborated.  The
wrappers are themselves ordinary kernel-checked theorems and preserve the
universal hypotheses for downstream users. -/

theorem number_commutator_universal :
    ∀ {A : Type} [Ring A] (a adag : A),
      LeanPhy.Quantum.commutator a adag = 1 →
      LeanPhy.Quantum.commutator (LeanPhy.FieldTheory.number adag a) adag = adag := by
  intro A _ a adag h
  exact LeanPhy.FieldTheory.number_commutator a adag h

theorem fieldStrength_antisym_universal :
    ∀ {A : Type} [Ring A] (D : Fin 4 → A) (mu nu : Fin 4),
      LeanPhy.GaugeTheory.fieldStrength D mu nu =
        -LeanPhy.GaugeTheory.fieldStrength D nu mu := by
  intro A _ D mu nu
  exact LeanPhy.GaugeTheory.fieldStrength_antisym D mu nu

theorem symplectic_mul_universal :
    ∀ (A B : Matrix (Fin 2) (Fin 2) ℝ),
      Matrix.transpose A * LeanPhy.Classical.symplecticJ * A = LeanPhy.Classical.symplecticJ →
      Matrix.transpose B * LeanPhy.Classical.symplecticJ * B = LeanPhy.Classical.symplecticJ →
      Matrix.transpose (A * B) * LeanPhy.Classical.symplecticJ * (A * B) =
        LeanPhy.Classical.symplecticJ := by
  intro A B hA hB
  exact LeanPhy.Classical.symplectic_mul A B hA hB

theorem finiteGibbsWeight_nonneg_universal :
    ∀ {ι : Type} [Fintype ι] [Nonempty ι]
      (β : ℝ) (E : ι → ℝ) (i : ι),
      0 ≤ LeanPhy.StatMech.finiteGibbsWeight β E i := by
  intro ι _ _ β E i
  exact LeanPhy.StatMech.finiteGibbsWeight_nonneg β E i

def numberCommutatorEntry : CheckedLemma where
  name := "number_commutator"
  domain := "field-theory"
  statement := "[a†a, a†] = a† under [a,a†] = 1"
  source := "LeanPhy.FieldTheory.CCR"
  tags := ["CCR", "ladder", "commutator"]
  proposition := ∀ {A : Type} [Ring A] (a adag : A),
    LeanPhy.Quantum.commutator a adag = 1 →
      LeanPhy.Quantum.commutator (LeanPhy.FieldTheory.number adag a) adag = adag
  proof := number_commutator_universal

def fieldStrengthEntry : CheckedLemma where
  name := "fieldStrength_antisym"
  domain := "gauge"
  statement := "F μ ν = - F ν μ"
  source := "LeanPhy.GaugeTheory.FieldStrength"
  tags := ["gauge", "curvature", "indices"]
  proposition := ∀ {A : Type} [Ring A] (D : Fin 4 → A) (mu nu : Fin 4),
    LeanPhy.GaugeTheory.fieldStrength D mu nu =
      -LeanPhy.GaugeTheory.fieldStrength D nu mu
  proof := fieldStrength_antisym_universal

def symplecticEntry : CheckedLemma where
  name := "symplectic_mul"
  domain := "classical"
  statement := "the product of canonical matrices is canonical"
  source := "LeanPhy.Classical.Symplectic"
  tags := ["Hamiltonian", "symplectic", "canonical"]
  proposition := ∀ (A B : Matrix (Fin 2) (Fin 2) ℝ),
    Matrix.transpose A * LeanPhy.Classical.symplecticJ * A =
        LeanPhy.Classical.symplecticJ →
      Matrix.transpose B * LeanPhy.Classical.symplecticJ * B =
        LeanPhy.Classical.symplecticJ →
      Matrix.transpose (A * B) * LeanPhy.Classical.symplecticJ * (A * B) =
        LeanPhy.Classical.symplecticJ
  proof := symplectic_mul_universal

def gibbsEntry : CheckedLemma where
  name := "finiteGibbsWeight_nonneg"
  domain := "stat-mech"
  statement := "finite Gibbs weights are nonnegative"
  source := "LeanPhy.StatMech.FiniteGibbs"
  tags := ["Gibbs", "probability", "statistical"]
  proposition := ∀ {ι : Type} [Fintype ι] [Nonempty ι]
      (β : ℝ) (E : ι → ℝ) (i : ι),
      0 ≤ LeanPhy.StatMech.finiteGibbsWeight β E i
  proof := finiteGibbsWeight_nonneg_universal

/-! The concrete entries use polymorphic theorems directly.  A universal
theorem is still a useful result in the catalogue: its proposition remains a
Pi type and its proof is the theorem constant that Lean checked. -/

def catalog : List CheckedLemma := [
  CheckedLemma.ofTheorem "pauliXY_commutator" "quantum"
    "[σx, σy] = 2 i σz" "LeanPhy.Quantum.Pauli" ["pauli", "commutator"]
    LeanPhy.Quantum.pauliXY_commutator,
  numberCommutatorEntry,
  fieldStrengthEntry,
  CheckedLemma.ofTheorem "clifford_gamma1" "high-energy"
    "γ₁² = -1" "LeanPhy.HighEnergy.Gamma" ["Dirac", "Clifford", "gamma"]
    LeanPhy.HighEnergy.clifford_gamma1,
  symplecticEntry,
  CheckedLemma.ofTheorem "metric_diagonal" "relativity"
    "the declared Minkowski metric has signature (+---)" "LeanPhy.Relativity.Minkowski"
    ["Lorentz", "metric", "relativity"] LeanPhy.Relativity.metric_diagonal,
  gibbsEntry
]

def all : List CheckedLemma := catalog

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

def search (query : String) : List CheckedLemma :=
  searchIn catalog query

def names (lemmas : List CheckedLemma := catalog) : List String :=
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

def renderJson (lemmas : List CheckedLemma := catalog) : String :=
  "[" ++ renderMany lemmas ++ "]"

end LeanPhy.Library
