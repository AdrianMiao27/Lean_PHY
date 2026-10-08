import LeanPhy.FieldTheory.FermionWord

set_option autoImplicit false

/-!
# Symbolic interacting fermion expressions

Finite coefficient/word tables support multiplication, commutators and CAR
normalization before any occupation matrices are expanded. Coefficients live in
an arbitrary commutative ring: a ring homomorphism specializes them to complex
couplings only at interpretation. Collecting equal words is exact, and a zero
normalized difference certifies an identity in every supplied CAR representation.
-/

namespace LeanPhy.FieldTheory.FermionPolynomial

open FermionWord

abbrev Expression (R ι : Type) := List (R × Word ι)

variable {R ι : Type} [CommRing R]

def term (c : R) (w : Word ι) : Expression R ι := [(c, w)]
def scalar (c : R) : Expression R ι := term c []
def letter (a : Letter ι) : Expression R ι := term 1 [a]
def add (p q : Expression R ι) : Expression R ι := p ++ q
def neg (p : Expression R ι) : Expression R ι := p.map (fun t => (-t.1, t.2))
def sub (p q : Expression R ι) : Expression R ι := add p (neg q)
def mul (p q : Expression R ι) : Expression R ι :=
  p.flatMap (fun t => q.map (fun u => (t.1 * u.1, t.2 ++ u.2)))
def commutator (p q : Expression R ι) : Expression R ι := sub (mul p q) (mul q p)

def adjoint [StarRing R] (p : Expression R ι) : Expression R ι :=
  p.map (fun t => (star t.1, FermionWord.adjoint t.2))

def withAdjoint [StarRing R] (p : Expression R ι) : Expression R ι := add p (adjoint p)

def normalOrder [LinearOrder ι] (p : Expression R ι) : Expression R ι :=
  p.flatMap (fun t => (FermionWord.normalize t.2).map (fun u => (u.1 • t.1, u.2)))

/-- Merge a coefficient into the first matching word without expanding matrices. -/
def addTerm [DecidableEq ι] (c : R) (w : Word ι) : Expression R ι → Expression R ι
  | [] => [(c, w)]
  | t :: p => if w = t.2 then (c + t.1, w) :: p else t :: addTerm c w p

def collect [DecidableEq ι] : Expression R ι → Expression R ι
  | [] => []
  | t :: p => addTerm t.1 t.2 (collect p)

def compact [DecidableEq ι] [DecidableEq R] (p : Expression R ι) : Expression R ι :=
  (collect p).filter (fun t => t.1 != 0)

def compile [LinearOrder ι] [DecidableEq R] (p : Expression R ι) : Expression R ι :=
  compact (normalOrder p)

section OrderInvariant

variable [LinearOrder ι]

theorem normalOrder_ordered (p : Expression R ι) {t : R × Word ι}
    (ht : t ∈ normalOrder p) : t.2.Pairwise (· < ·) := by
  obtain ⟨v, _, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact FermionWord.normalize_ordered v.2 (t := u) hu

private theorem mem_addTerm_word (c : R) (w : Word ι) (p : Expression R ι)
    {t : R × Word ι} (ht : t ∈ addTerm c w p) :
    t.2 = w ∨ ∃ v ∈ p, t.2 = v.2 := by
  induction p with
  | nil =>
    simp only [addTerm, List.mem_singleton] at ht
    subst t
    exact Or.inl rfl
  | cons v p ih =>
    by_cases hw : w = v.2
    · simp only [addTerm, ite_eq_left hw, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact Or.inl rfl
      · exact Or.inr ⟨t, List.mem_cons_of_mem v ht, rfl⟩
    · simp only [addTerm, ite_eq_right hw, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact Or.inr ⟨t, by simp, rfl⟩
      · rcases ih ht with ht | ⟨u, hu, he⟩
        · exact Or.inl ht
        · exact Or.inr ⟨u, List.mem_cons_of_mem v hu, he⟩

private theorem mem_collect_word (p : Expression R ι)
    {t : R × Word ι} (ht : t ∈ collect p) : ∃ v ∈ p, t.2 = v.2 := by
  induction p generalizing t with
  | nil => simp [collect] at ht
  | cons v p ih =>
    rcases mem_addTerm_word v.1 v.2 (collect p) ht with he | ⟨u, hu, he⟩
    · exact ⟨v, by simp, he⟩
    · obtain ⟨z, hz, hez⟩ := ih hu
      exact ⟨z, List.mem_cons_of_mem v hz, he.trans hez⟩

theorem compile_ordered [DecidableEq R] (p : Expression R ι) {t : R × Word ι}
    (ht : t ∈ compile p) : t.2.Pairwise (· < ·) := by
  obtain ⟨v, hv, he⟩ := mem_collect_word (normalOrder p) (List.mem_filter.mp ht).1
  rw [he]
  exact normalOrder_ordered p hv

end OrderInvariant

section Semantics

variable {A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A]
variable (f : R →+* ℂ) (M : MultiModeCAR ι A)

def eval (p : Expression R ι) : A :=
  (p.map (fun t => f t.1 • FermionWord.eval M t.2)).sum

@[simp] theorem eval_nil : eval f M [] = 0 := rfl
@[simp] theorem eval_cons (c : R) (w : Word ι) (p : Expression R ι) :
    eval f M ((c, w) :: p) = f c • FermionWord.eval M w + eval f M p := rfl
@[simp] theorem eval_term (c : R) (w : Word ι) :
    eval f M (term c w) = f c • FermionWord.eval M w := by simp [term]
@[simp] theorem eval_scalar (c : R) : eval f M (scalar c) = f c • (1 : A) := by
  simp [scalar]
@[simp] theorem eval_letter (a : Letter ι) :
    eval f M (letter a) = FermionWord.generator M a := by simp [letter]
@[simp] theorem eval_append (p q : Expression R ι) :
    eval f M (p ++ q) = eval f M p + eval f M q := by simp [eval]
@[simp] theorem eval_add (p q : Expression R ι) :
    eval f M (add p q) = eval f M p + eval f M q := eval_append f M p q
@[simp] theorem eval_neg (p : Expression R ι) : eval f M (neg p) = -eval f M p := by
  induction p with
  | nil => simp [neg]
  | cons t p ih =>
    rcases t with ⟨c, w⟩
    simpa [neg, map_neg, neg_smul, add_comm] using congrArg (fun x => -(f c • FermionWord.eval M w) + x) ih
@[simp] theorem eval_sub (p q : Expression R ι) :
    eval f M (sub p q) = eval f M p - eval f M q := by simp [sub, sub_eq_add_neg]

theorem eval_mul (p q : Expression R ι) :
    eval f M (mul p q) = eval f M p * eval f M q := by
  have h (c : R) (w : Word ι) :
      eval f M (q.map (fun t => (c * t.1, w ++ t.2))) =
        (f c • FermionWord.eval M w) * eval f M q := by
    induction q with
    | nil => simp
    | cons t q ih =>
      rcases t with ⟨d, v⟩
      simp [ih, FermionWord.eval_append, map_mul, mul_add, smul_smul, mul_comm]
  induction p with
  | nil => simp [mul]
  | cons t p ih =>
    rcases t with ⟨c, w⟩
    simpa only [mul, List.flatMap_cons, eval_append, h, eval_cons, add_mul] using
      congrArg (fun x => (f c • FermionWord.eval M w) * eval f M q + x) ih

theorem eval_commutator (p q : Expression R ι) :
    eval f M (commutator p q) =
      LeanPhy.Quantum.commutator (eval f M p) (eval f M q) := by
  simp [commutator, eval_mul, LeanPhy.Quantum.commutator]

theorem eval_adjoint [StarRing R] [StarRing A] [StarModule ℂ A]
    (hf : ∀ c, f (star c) = star (f c)) (hstar : ∀ i, M.cre i = star (M.ann i))
    (p : Expression R ι) : eval f M (adjoint p) = star (eval f M p) := by
  induction p with
  | nil => simp [adjoint]
  | cons t p ih =>
    rcases t with ⟨c, w⟩
    simpa only [adjoint, List.map_cons, eval_cons, hf, FermionWord.eval_adjoint M hstar,
      star_add, star_smul] using
      congrArg (fun x => star (f c) • star (FermionWord.eval M w) + x) ih

theorem withAdjoint_selfAdjoint [StarRing R] [StarRing A] [StarModule ℂ A]
    (hf : ∀ c, f (star c) = star (f c)) (hstar : ∀ i, M.cre i = star (M.ann i))
    (p : Expression R ι) : star (eval f M (withAdjoint p)) = eval f M (withAdjoint p) := by
  simp [withAdjoint, eval_adjoint f M hf hstar, add_comm]

theorem eval_addTerm (c : R) (w : Word ι) (p : Expression R ι) :
    eval f M (addTerm c w p) = f c • FermionWord.eval M w + eval f M p := by
  induction p with
  | nil => simp [addTerm]
  | cons t p ih =>
    rcases t with ⟨d, v⟩
    by_cases hw : w = v
    · subst v
      simp [addTerm, map_add, add_smul, add_assoc]
    · simp [addTerm, hw, ih, add_left_comm]

theorem eval_collect (p : Expression R ι) : eval f M (collect p) = eval f M p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨c, w⟩
    simp [collect, eval_addTerm, ih]

theorem eval_compact [DecidableEq R] (p : Expression R ι) :
    eval f M (compact p) = eval f M p := by
  have h (q : Expression R ι) : eval f M (q.filter (fun t => t.1 != 0)) = eval f M q := by
    induction q with
    | nil => rfl
    | cons t q ih =>
      rcases t with ⟨c, w⟩
      by_cases hc : c = 0 <;> simp [hc, ih]
  exact (h (collect p)).trans (eval_collect f M p)

end Semantics

section Normalization

variable {A : Type} [LinearOrder ι] [Fintype ι] [Ring A] [Algebra ℂ A]
variable (f : R →+* ℂ) (M : MultiModeCAR ι A)

theorem eval_normalOrder (p : Expression R ι) : eval f M (normalOrder p) = eval f M p := by
  have h (c : R) (q : Expansion ι) :
      eval f M (q.map (fun t => (t.1 • c, t.2))) =
        f c • evalExpansion M q := by
    induction q with
    | nil => simp
    | cons t q ih =>
      rcases t with ⟨k, w⟩
      simp only [List.map_cons, eval_cons, evalExpansion_cons, ih, map_zsmul, smul_add]
      congr 1
      exact (smul_assoc k (f c) (FermionWord.eval M w)).trans
        (smul_comm k (f c) (FermionWord.eval M w))
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨c, w⟩
    simpa only [normalOrder, List.flatMap_cons, eval_append, h,
      eval_normalize, eval_cons] using congrArg (fun x => f c • FermionWord.eval M w + x) ih

theorem eval_compile [DecidableEq R] (p : Expression R ι) :
    eval f M (compile p) = eval f M p :=
  (eval_compact f M (normalOrder p)).trans (eval_normalOrder f M p)

/-- Kernel-checking a zero normalized difference proves an operator identity.
The coefficient specialization and the CAR model remain explicit arguments. -/
theorem eq_of_compile_sub_eq_nil [DecidableEq R] (p q : Expression R ι)
    (h : compile (sub p q) = []) : eval f M p = eval f M q := by
  have he := eval_compile f M (sub p q)
  rw [h, eval_nil, eval_sub] at he
  exact sub_eq_zero.mp he.symm

end Normalization
end LeanPhy.FieldTheory.FermionPolynomial
