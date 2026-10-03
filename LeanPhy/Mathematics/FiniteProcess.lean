import Mathlib.Tactic

/-!
# Proof-preserving state maps and finite processes

Physics developments repeatedly use the same proof obligation under different
names: a quantum channel maps density matrices to density matrices, a Markov
kernel maps probabilities to probabilities, and a discretised evolution maps
admissible numerical states to admissible numerical states.  Before this file
each domain exposed that fact through a separate wrapper, which made it hard to
compose a derivation across domains.

`StateMap` is the small common contract.  Its `preserves` field is a dependent
proof, so composition cannot forget validity.  `Process` is the endomap case;
its finite iterates and invariant laws are proved once here.  The definitions
do not assert that a continuum, an infinite-dimensional state space, or a
physical model exists.  Those objects enter through an explicit state
predicate and an adapter theorem.
-/

namespace LeanPhy.Mathematics

universe u v w

/-! ## Maps carrying a state invariant -/

/-- A map whose source and target satisfy explicit admissibility predicates. -/
structure StateMap (S : Type u) (T : Type v)
    (ValidS : S → Prop) (ValidT : T → Prop) where
  toFun : S → T
  preserves : ∀ s, ValidS s → ValidT (toFun s)

instance {S : Type u} {T : Type v} {ValidS : S → Prop} {ValidT : T → Prop} :
    CoeFun (StateMap S T ValidS ValidT) (fun _ => S → T) :=
  ⟨StateMap.toFun⟩

namespace StateMap

variable {S : Type u} {T : Type v} {U : Type w} {V : Type*}
variable {ValidS : S → Prop} {ValidT : T → Prop} {ValidU : U → Prop}
variable {ValidV : V → Prop}

/-- Identity on an explicitly admissible state space. -/
def identity (S : Type u) (Valid : S → Prop) :
    StateMap S S Valid Valid where
  toFun := id
  preserves := by intro s hs; exact hs

/- Composition is typed at the state-predicate boundary.  A map whose
   intermediate invariant is weaker or stronger simply cannot be composed
   until the caller supplies the corresponding adapter proof. -/
def compose (after : StateMap T U ValidT ValidU)
    (before : StateMap S T ValidS ValidT) :
    StateMap S U ValidS ValidU where
  toFun := fun s => after (before s)
  preserves := by
    intro s hs
    exact after.preserves (before s) (before.preserves s hs)

@[simp] theorem compose_apply (after : StateMap T U ValidT ValidU)
    (before : StateMap S T ValidS ValidT) (s : S) :
    after.compose before s = after (before s) := rfl

@[simp] theorem compose_identity_left (M : StateMap S T ValidS ValidT) (s : S) :
    (M.compose (identity S ValidS)) s = M s := rfl

@[simp] theorem compose_identity_right (M : StateMap S T ValidS ValidT) (s : S) :
    ((identity T ValidT).compose M) s = M s := rfl

theorem compose_assoc
    (L : StateMap U V ValidU ValidV)
    (M : StateMap T U ValidT ValidU)
    (N : StateMap S T ValidS ValidT) :
    (L.compose M).compose N = L.compose (M.compose N) := by
  cases L
  cases M
  cases N
  rfl

theorem valid_apply (M : StateMap S T ValidS ValidT) {s : S}
    (hs : ValidS s) : ValidT (M s) :=
  M.preserves s hs

/-! A product map is the generic composition boundary for independent
   subsystems. Its validity predicate is a conjunction, so tensor-product
   adapters and hybrid finite models can compose without duplicating proofs. -/

def product (left : StateMap S T ValidS ValidT)
    (right : StateMap U V ValidU ValidV) :
    StateMap (S × U) (T × V)
      (fun p => ValidS p.1 ∧ ValidU p.2)
      (fun p => ValidT p.1 ∧ ValidV p.2) where
  toFun := fun p => (left p.1, right p.2)
  preserves := by
    intro p hp
    exact ⟨left.preserves p.1 hp.1, right.preserves p.2 hp.2⟩

@[simp] theorem product_apply (left : StateMap S T ValidS ValidT)
    (right : StateMap U V ValidU ValidV) (s : S) (u : U) :
    product left right (s, u) = (left s, right u) := rfl

theorem product_compose
    {X : Type*} {Y : Type*} {ValidX : X → Prop} {ValidY : Y → Prop}
    (leftAfter : StateMap T X ValidT ValidX)
    (rightAfter : StateMap V Y ValidV ValidY)
    (leftBefore : StateMap S T ValidS ValidT)
    (rightBefore : StateMap U V ValidU ValidV) :
    (product leftAfter rightAfter).compose
        (product leftBefore rightBefore) =
      product (leftAfter.compose leftBefore)
        (rightAfter.compose rightBefore) := by
  cases leftAfter
  cases rightAfter
  cases leftBefore
  cases rightBefore
  rfl

end StateMap

/-! ## Endomorphisms and finite iterates -/

/-- A proof-preserving endomorphism.  The name refers to finite iterates, not
    to a hidden finiteness assumption on the underlying type. -/
abbrev Process (S : Type u) (Valid : S → Prop) :=
  StateMap S S Valid Valid

namespace Process

variable {S : Type u} {Valid : S → Prop}

def identity : Process S Valid := StateMap.identity S Valid

def compose (after before : Process S Valid) : Process S Valid :=
  StateMap.compose after before

/-! Independent processes form a process on the product state. This is the
   reusable law behind tensor-product channels, hybrid bookkeeping models and
   finite multi-mode evolutions. -/

def parallel {T : Type*} {ValidT : T → Prop}
    (left : Process S Valid) (right : Process T ValidT) :
    Process (S × T) (fun p => Valid p.1 ∧ ValidT p.2) :=
  StateMap.product left right

@[simp] theorem parallel_apply {T : Type*} {ValidT : T → Prop}
    (left : Process S Valid) (right : Process T ValidT) (s : S) (t : T) :
    parallel left right (s, t) = (left s, right t) := rfl

@[simp] theorem compose_apply (after before : Process S Valid) (s : S) :
    compose after before s = after (before s) := rfl

def iterate (P : Process S Valid) : Nat → S → S
  | 0, s => s
  | n + 1, s => P (iterate P n s)

@[simp] theorem iterate_zero (P : Process S Valid) (s : S) :
    iterate P 0 s = s := rfl

@[simp] theorem iterate_succ (P : Process S Valid) (n : Nat) (s : S) :
    iterate P (n + 1) s = P (iterate P n s) := rfl

theorem iterate_add (P : Process S Valid) (m n : Nat) (s : S) :
    iterate P (m + n) s = iterate P m (iterate P n s) := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Nat.succ_add, iterate_succ]
      rw [ih]


theorem iterate_valid (P : Process S Valid) (n : Nat) {s : S}
    (hs : Valid s) : Valid (iterate P n s) := by
  induction n with
  | zero => exact hs
  | succ n ih =>
      simpa only [iterate_succ] using P.preserves _ ih

theorem iterate_parallel {T : Type*} {ValidT : T → Prop}
    (left : Process S Valid) (right : Process T ValidT)
    (n : Nat) (s : S) (t : T) :
    iterate (parallel left right) n (s, t) =
      (iterate left n s, iterate right n t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate_succ, ih]
      rfl

end Process

/-! ## Invariants and transported observables -/

/-- A conserved quantity for a proof-preserving process. -/
structure Invariant (P : Process S Valid) (Q : Type v) where
  quantity : S → Q
  preserved : ∀ s, Valid s → quantity (P s) = quantity s

namespace Invariant

variable {S : Type u} {Valid : S → Prop} {Q : Type v}

def parallel {T : Type*} {ValidT : T → Prop}
    {R : Type*} {left : Process S Valid} {right : Process T ValidT}
    (I : Invariant left Q) (J : Invariant right R) :
    Invariant (Process.parallel left right) (Q × R) where
  quantity := fun p => (I.quantity p.1, J.quantity p.2)
  preserved := by
    intro p hp
    exact congrArg₂ Prod.mk (I.preserved p.1 hp.1) (J.preserved p.2 hp.2)

theorem iterate (P : Process S Valid) (I : Invariant P Q) (n : Nat)
    {s : S} (hs : Valid s) :
    I.quantity (Process.iterate P n s) = I.quantity s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Process.iterate_succ, I.preserved]
      · exact ih
      · exact Process.iterate_valid P n hs


end Invariant

/-- A Schrödinger/Heisenberg-style transport law for any state map.  The
    observable pullback is supplied by the domain adapter (for example a
    Markov-kernel expectation or a Kraus adjoint); the compatibility equation
    is proof checked and can then be composed across several maps. -/
structure ObservableTransport
    {S : Type u} {T : Type v} {ValidS : S → Prop} {ValidT : T → Prop}
    (M : StateMap S T ValidS ValidT)
    (ObsS : Type w) (ObsT : Type*) (R : Type*)
    (evaluateS : S → ObsS → R) (evaluateT : T → ObsT → R) where
  pullback : ObsT → ObsS
  compatible : ∀ s, ValidS s → ∀ o,
    evaluateT (M s) o = evaluateS s (pullback o)

namespace ObservableTransport

variable {S : Type u} {T : Type v} {U : Type w}
variable {ValidS : S → Prop} {ValidT : T → Prop} {ValidU : U → Prop}

def identity {Obs R : Type*} {Valid : S → Prop}
    (evaluate : S → Obs → R) :
    ObservableTransport (StateMap.identity S Valid) Obs Obs R evaluate evaluate where
  pullback := id
  compatible := by
    intro s _ o
    rfl

def compose
    {ObsS ObsT ObsU R : Type*}
    {evalS : S → ObsS → R} {evalT : T → ObsT → R} {evalU : U → ObsU → R}
    {M : StateMap S T ValidS ValidT}
    {N : StateMap T U ValidT ValidU}
    (after : ObservableTransport N ObsT ObsU R evalT evalU)
    (before : ObservableTransport M ObsS ObsT R evalS evalT) :
    ObservableTransport (StateMap.compose N M) ObsS ObsU R evalS evalU where
  pullback := fun o => before.pullback (after.pullback o)
  compatible := by
    intro s hs o
    change evalU (N (M s)) o = evalS s (before.pullback (after.pullback o))
    rw [after.compatible (M s) (M.preserves s hs)]
    exact before.compatible s hs (after.pullback o)

theorem compose_assoc
    {X : Type*} {ValidX : X → Prop}
    {ObsS ObsT ObsU ObsX R : Type*}
    {evalS : S → ObsS → R} {evalT : T → ObsT → R}
    {evalU : U → ObsU → R} {evalX : X → ObsX → R}
    {M : StateMap S T ValidS ValidT}
    {N : StateMap T U ValidT ValidU}
    {L : StateMap U X ValidU ValidX}
    (third : ObservableTransport L ObsU ObsX R evalU evalX)
    (second : ObservableTransport N ObsT ObsU R evalT evalU)
    (first : ObservableTransport M ObsS ObsT R evalS evalT) :
    compose third (compose second first) =
      compose (compose third second) first := by
  cases third
  cases second
  cases first
  rfl

end ObservableTransport

end LeanPhy.Mathematics
