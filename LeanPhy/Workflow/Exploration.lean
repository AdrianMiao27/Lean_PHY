import LeanPhy.Workflow.Core

set_option autoImplicit false

/-!
# Parameter domains, hypothesis branches and exploratory revisions

A question binds its domain and target to actual Lean data. A branch theorem
quantifies over that domain *and* its additional conditions. A failed attempt
has no logical meaning; a counterexample proves the negation of that precise
branch goal. Covering cases and changing a model both require ordinary proofs.

Notebooks are immutable values, not tamper-proof audit logs. Historical labels
and source strings are metadata. Their propositions and dependent evidence,
and the registered root obligation, are the mathematical trust boundary.
-/

namespace LeanPhy.Workflow.Exploration

universe u v

structure Question (α : Type u) where
  name : String
  revision : String
  statement : String
  domainDescription : String
  source : String
  domain : α → Prop
  target : α → Prop

namespace Question

def Answer {α : Type u} (Q : Question α) : Prop := ∀ x, Q.domain x → Q.target x

def obligation {α : Type u} (Q : Question α) : ExternalObligationWitness where
  metadata := { name := Q.name, statement := Q.statement, source := Q.source }
  proposition := Q.Answer

end Question

structure Condition (α : Type u) where
  name : String
  statement : String
  predicate : α → Prop

namespace Condition

def Holds {α : Type u} (conditions : List (Condition α)) (x : α) : Prop :=
  ∀ c ∈ conditions, c.predicate x

@[simp] theorem holds_nil {α : Type u} (x : α) : Holds [] x := by
  simp [Holds]

@[simp] theorem holds_cons {α : Type u} (c : Condition α)
    (cs : List (Condition α)) (x : α) :
    Holds (c :: cs) x ↔ c.predicate x ∧ Holds cs x := by
  simp [Holds]

def negate {α : Type u} (c : Condition α) : Condition α where
  name := "not " ++ c.name
  statement := "not (" ++ c.statement ++ ")"
  predicate := fun x => ¬ c.predicate x

end Condition

structure Branch {α : Type u} (Q : Question α) where
  name : String
  conditions : List (Condition α)

namespace Branch

variable {α : Type u} {Q : Question α}

def root (Q : Question α) : Branch Q := ⟨"root", []⟩

def Goal (B : Branch Q) : Prop :=
  ∀ x, Q.domain x → Condition.Holds B.conditions x → Q.target x

/-- A witness is optional: a proved implication can be vacuous. This predicate
lets a researcher separately certify that the branch has physical inputs. -/
def Feasible (B : Branch Q) : Prop :=
  ∃ x, Q.domain x ∧ Condition.Holds B.conditions x

@[simp] theorem root_goal (Q : Question α) : (root Q).Goal ↔ Q.Answer := by
  simp [Goal, root, Question.Answer]

def refine (B : Branch Q) (name : String) (c : Condition α) : Branch Q :=
  ⟨name, c :: B.conditions⟩

/-- Results on a larger domain restrict to any stronger hypothesis branch. -/
theorem restrict (B : Branch Q) (name : String) (c : Condition α)
    (h : B.Goal) : (B.refine name c).Goal := by
  intro x hx hc
  exact h x hx ((Condition.holds_cons _ _ _).mp hc).2

/-- Discharge every extra condition before promoting a branch result. -/
theorem discharge (B : Branch Q) (h : B.Goal)
    (conditions : ∀ x, Q.domain x → Condition.Holds B.conditions x) : Q.Answer := by
  intro x hx
  exact h x hx (conditions x hx)

/-- General case coverage is a proof, not a count of successful branches.
Children may overlap and may be infeasible; coverage still has to hold. -/
theorem cover {ι : Type v} (B : Branch Q) (children : ι → Branch Q)
    (coverage : ∀ x, Q.domain x → Condition.Holds B.conditions x →
      ∃ i, Condition.Holds (children i).conditions x)
    (proofs : ∀ i, (children i).Goal) : B.Goal := by
  intro x hx hc
  obtain ⟨i, hi⟩ := coverage x hx hc
  exact proofs i x hx hi

/-- A condition and its negation cover their parent branch. -/
theorem joinSplit (B : Branch Q) (c : Condition α) (yesName noName : String)
    (yes : (B.refine yesName c).Goal)
    (no : (B.refine noName c.negate).Goal) : B.Goal := by
  intro x hx hc
  by_cases h : c.predicate x
  · exact yes x hx ((Condition.holds_cons _ _ _).mpr ⟨h, hc⟩)
  · exact no x hx ((Condition.holds_cons _ _ _).mpr ⟨h, hc⟩)

/-- Reuse under a changed target is explicit. Identical revision labels do
not supply the domain inclusion or implication required by `transport`. -/
def withQuestion (B : Branch Q) (Q' : Question α) : Branch Q' :=
  ⟨B.name, B.conditions⟩

theorem transport (B : Branch Q) (Q' : Question α)
    (domain : ∀ x, Q'.domain x → Q.domain x)
    (target : ∀ x, Q'.domain x → Condition.Holds B.conditions x →
      Q.target x → Q'.target x)
    (h : B.Goal) : (B.withQuestion Q').Goal := by
  intro x hx hc
  exact target x hx hc (h x (domain x hx) hc)

/-- Parameter/model substitution pulls back the actual predicates. -/
def reindex {β : Type v} (B : Branch Q) (f : β → α) :
    Branch { Q with domain := fun x => Q.domain (f x), target := fun x => Q.target (f x) } :=
  ⟨B.name, B.conditions.map fun c => { c with predicate := fun x => c.predicate (f x) }⟩

theorem reindex_proof {β : Type v} (B : Branch Q) (f : β → α)
    (h : B.Goal) : (B.reindex f).Goal := by
  intro x hx hc
  apply h (f x) hx
  intro c hm
  exact hc { c with predicate := fun x => c.predicate (f x) }
    (List.mem_map.mpr ⟨c, hm, rfl⟩)

end Branch

/-- A physical input violating the target on the claimed branch domain. -/
structure Counterexample {α : Type u} {Q : Question α} (B : Branch Q) where
  input : α
  inDomain : Q.domain input
  inBranch : Condition.Holds B.conditions input
  violates : ¬ Q.target input

theorem Counterexample.refutes {α : Type u} {Q : Question α} {B : Branch Q}
    (w : Counterexample B) : ¬ B.Goal :=
  fun h => w.violates (h w.input w.inDomain w.inBranch)

structure Candidate {α : Type u} (Q : Question α) where
  branch : Branch Q
  evidence : ExplorationEvidence branch.Goal := .pending
  history : List (ExplorationEvidence branch.Goal) := []

namespace Candidate

variable {α : Type u} {Q : Question α}

def propose (B : Branch Q) : Candidate Q := ⟨B, .pending, []⟩

/-- All transitions retain the earlier outcome, including failed attempts. -/
def record (C : Candidate Q) (e : ExplorationEvidence C.branch.Goal) : Candidate Q :=
  { C with evidence := e, history := C.history ++ [C.evidence] }

def prove (C : Candidate Q) (h : C.branch.Goal) : Candidate Q := C.record (.checked h)

def refute (C : Candidate Q) (w : Counterexample C.branch) : Candidate Q :=
  C.record (.refuted w.refutes)

def fail (C : Candidate Q) (reason : String) : Candidate Q := C.record (.failed reason)

def records (C : Candidate Q) : List ExplorationRecord :=
  let make := fun e historical =>
    { question := Q.name, revision := Q.revision, branch := C.branch.name,
      statement := Q.statement, domain := Q.domainDescription,
      conditions := C.branch.conditions.map fun c => c.name ++ ": " ++ c.statement,
      source := Q.source, goal := C.branch.Goal, evidence := e,
      historical := historical : ExplorationRecord }
  C.history.map (fun e => make e true) ++ [make C.evidence false]

/-- Only current proved or refuted goals become claims. A refutation is
exported as a negative theorem, never as a proof of the positive goal. -/
def claim (C : Candidate Q) (index : Nat) : Option CheckedClaim :=
  let name := Q.name ++ "@" ++ Q.revision ++ "/" ++ C.branch.name ++ "#" ++ toString index
  let scope := " [domain: " ++ Q.domainDescription ++ "; conditions: " ++
    String.intercalate "; " (C.branch.conditions.map fun c => c.name ++ ": " ++ c.statement) ++ "]"
  match C.evidence with
  | .checked h => some (CheckedClaim.ofTheoremFrom name
      ("Conditional branch result: " ++ Q.statement ++ scope) Q.source h)
  | .refuted h => some (CheckedClaim.ofTheoremFrom name
      ("Refuted branch goal: " ++ Q.statement ++ scope) Q.source h)
  | _ => none

end Candidate

structure Notebook {α : Type u} (Q : Question α) where
  candidates : List (Candidate Q)
  archive : List ExplorationRecord := []

namespace Notebook

variable {α : Type u} {Q : Question α}

def start (Q : Question α) : Notebook Q := ⟨[Candidate.propose (Branch.root Q)], []⟩

def add (N : Notebook Q) (C : Candidate Q) : Notebook Q :=
  { N with candidates := N.candidates ++ [C] }

/-- An exact position in an immutable notebook, not a lookup by branch name. -/
structure Ref (N : Notebook Q) where
  index : Fin N.candidates.length

def Ref.candidate {N : Notebook Q} (r : N.Ref) : Candidate Q := N.candidates[r.index]

def Ref.branch {N : Notebook Q} (r : N.Ref) : Branch Q := r.candidate.branch

/-- Replace one candidate with evidence for its stored branch goal. -/
def record (N : Notebook Q) (r : N.Ref) (e : ExplorationEvidence r.branch.Goal) : Notebook Q :=
  { N with candidates := N.candidates.set r.index.val (r.candidate.record e) }

def records (N : Notebook Q) : List ExplorationRecord :=
  N.archive ++ N.candidates.flatMap Candidate.records

/-- Changes to the parameter type, model, domain or target start a fresh root.
Previous evidence is retained with its old proposition and revision. -/
def revise {β : Type v} (N : Notebook Q) (Q' : Question β) : Notebook Q' where
  candidates := [Candidate.propose (Branch.root Q')]
  archive := N.records.map fun r =>
    { r with
      historical := true
      supersededBy := r.supersededBy.or (some (Q'.name ++ "@" ++ Q'.revision)) }

/-- The root obligation is registered even when every listed candidate has
been checked or refuted. Listing branches alone proves no domain coverage. -/
def toPackage (N : Notebook Q) (name physicsDomain : String) : TheoryPackage :=
  let base : TheoryPackage :=
    { (TheoryPackage.empty name physicsDomain) with
      claims := (N.candidates.zipIdx).filterMap fun (c, i) => c.claim i,
      explorations := N.records }
  base.addObligationWitness Q.obligation

@[simp] theorem toPackage_open (N : Notebook Q) (name domain : String) :
    (N.toPackage name domain).obligationCount = 1 := rfl

/-- Completing a question consumes its actual quantified root answer and uses
existing indexed obligation resolution. Conditional evidence alone cannot pass. -/
def complete (N : Notebook Q) (name physicsDomain : String) (h : Q.Answer) : TheoryPackage :=
  let answer : ExplorationRecord :=
    { question := Q.name, revision := Q.revision, branch := "root",
      statement := Q.statement, domain := Q.domainDescription, conditions := [],
      source := Q.source, goal := Q.Answer, evidence := .checked h }
  let P := { (N.toPackage name physicsDomain) with
    explorations := N.records.map (fun r => { r with historical := true }) ++ [answer] }
  let r : ObligationRef P := ⟨⟨0, by simp [P, toPackage, TheoryPackage.addObligationWitness,
    TheoryPackage.addObligation, TheoryPackage.empty]⟩⟩
  P.resolveObligation r (Q.name ++ "@" ++ Q.revision ++ "/answer")
    Q.statement Q.source [] [] h

@[simp] theorem complete_open (N : Notebook Q) (name domain : String) (h : Q.Answer) :
    (N.complete name domain h).obligationCount = 0 := rfl

end Notebook

end LeanPhy.Workflow.Exploration
