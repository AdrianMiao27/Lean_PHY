import LeanPhy.FieldTheory.FermionBilinear
import Mathlib.Data.Sum.Order

set_option autoImplicit false

/-!
# Finite fermion words and exact CAR insertion

Creation letters precede annihilation letters; each block uses the supplied mode
order. Integer coefficients retain all contraction terms. The recursive insertion
terminates on the tail of the word and eliminates repeated equal generators.
No occupation matrix, state, Gaussian assumption or dimension is used by the
algorithm. Its semantics is proved for every complex CAR representation.
-/

namespace LeanPhy.FieldTheory.FermionWord

abbrev Letter (ι : Type) := ι ⊕ₗ ι
abbrev Word (ι : Type) := List (Letter ι)
abbrev Expansion (ι : Type) := List (ℤ × Word ι)

def cre {ι : Type} (i : ι) : Letter ι := Sum.inlₗ i
def ann {ι : Type} (i : ι) : Letter ι := Sum.inrₗ i

def dagger {ι : Type} : Letter ι → Letter ι
  | Sum.inl i => ann i
  | Sum.inr i => cre i

def adjoint {ι : Type} (w : Word ι) : Word ι := w.reverse.map dagger

@[simp] theorem dagger_cre {ι : Type} (i : ι) : dagger (cre i) = ann i := rfl
@[simp] theorem dagger_ann {ι : Type} (i : ι) : dagger (ann i) = cre i := rfl

def contraction {ι : Type} [DecidableEq ι] : Letter ι → Letter ι → Bool
  | Sum.inl i, Sum.inr j => decide (i = j)
  | Sum.inr i, Sum.inl j => decide (i = j)
  | _, _ => false

def insert {ι : Type} [LinearOrder ι] (a : Letter ι) : Word ι → Expansion ι
  | [] => [(1, [a])]
  | b :: w =>
    if a = b then []
    else if a < b then [(1, a :: b :: w)]
    else (if contraction a b then [(1, w)] else []) ++
      (insert a w).map (fun t => (-t.1, b :: t.2))

def normalize {ι : Type} [LinearOrder ι] : Word ι → Expansion ι
  | [] => [(1, [])]
  | a :: w => (normalize w).flatMap (fun t =>
      (insert a t.2).map (fun u => (t.1 * u.1, u.2)))

section OrderInvariant

variable {ι : Type} [LinearOrder ι]

/-- Every output letter came from the inserted generator or the original word. -/
theorem mem_insert {a x : Letter ι} {w : Word ι} {t : ℤ × Word ι}
    (ht : t ∈ insert a w) (hx : x ∈ t.2) : x = a ∨ x ∈ w := by
  induction w generalizing t with
  | nil =>
    simp only [insert, List.mem_singleton] at ht
    subst t
    simpa using hx
  | cons b w ih =>
    by_cases hab : a = b
    · simp [insert, hab] at ht
    · by_cases hlt : a < b
      · simp only [insert, ite_eq_right hab, ite_eq_left hlt, List.mem_singleton] at ht
        subst t
        simpa using hx
      · simp only [insert, ite_eq_right hab, ite_eq_right hlt, List.mem_append] at ht
        rcases ht with ht | ht
        · cases hc : contraction a b <;> simp [hc] at ht
          subst t
          exact Or.inr (List.mem_cons_of_mem b hx)
        · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
          rcases List.mem_cons.mp hx with h | h
          · exact Or.inr (by simp [h])
          · rcases ih hv h with h | h
            · exact Or.inl h
            · exact Or.inr (List.mem_cons_of_mem b h)

/-- Strict ordering gives creation-first blocks and removes equal generators
inside each block. This property is proved for every emitted term. -/
theorem insert_ordered {a : Letter ι} {w : Word ι}
    (hw : w.Pairwise (· < ·)) {t : ℤ × Word ι} (ht : t ∈ insert a w) :
    t.2.Pairwise (· < ·) := by
  induction w generalizing t with
  | nil =>
    simp only [insert, List.mem_singleton] at ht
    subst t
    exact List.pairwise_singleton (R := (· < ·)) a
  | cons b w ih =>
    obtain ⟨hb, hw⟩ := List.pairwise_cons.mp hw
    by_cases hab : a = b
    · simp [insert, hab] at ht
    · by_cases hlt : a < b
      · simp only [insert, ite_eq_right hab, ite_eq_left hlt, List.mem_singleton] at ht
        subst t
        apply List.pairwise_cons.mpr
        refine ⟨?_, List.pairwise_cons.mpr ⟨hb, hw⟩⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hlt
        · exact lt_trans hlt (hb x hx)
      · simp only [insert, ite_eq_right hab, ite_eq_right hlt, List.mem_append] at ht
        rcases ht with ht | ht
        · cases hc : contraction a b <;> simp [hc] at ht
          subst t
          exact hw
        · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih hw hv⟩
          intro x hx
          rcases mem_insert hv hx with rfl | hx
          · exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hab)
          · exact hb x hx

theorem normalize_ordered (w : Word ι) {t : ℤ × Word ι}
    (ht : t ∈ normalize w) : t.2.Pairwise (· < ·) := by
  induction w generalizing t with
  | nil =>
    simp only [normalize, List.mem_singleton] at ht
    subst t
    simp
  | cons a w ih =>
    obtain ⟨v, hv, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact insert_ordered (t := u) (ih hv) hu

end OrderInvariant

section Semantics

variable {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A]
variable (M : MultiModeCAR ι A)

def generator : Letter ι → A
  | Sum.inl i => M.cre i
  | Sum.inr i => M.ann i

@[simp] theorem generator_cre (i : ι) : generator M (cre i) = M.cre i := rfl
@[simp] theorem generator_ann (i : ι) : generator M (ann i) = M.ann i := rfl

def eval (M : MultiModeCAR ι A) : Word ι → A
  | [] => 1
  | a :: w => generator M a * eval M w

def evalExpansion (p : Expansion ι) : A :=
  (p.map (fun t => t.1 • eval M t.2)).sum

@[simp] theorem eval_nil : eval M [] = 1 := rfl
@[simp] theorem eval_cons (a : Letter ι) (w : Word ι) :
    eval M (a :: w) = generator M a * eval M w := rfl

theorem eval_append (u v : Word ι) : eval M (u ++ v) = eval M u * eval M v := by
  induction u with
  | nil => simp
  | cons a u ih => simp [ih, mul_assoc]

theorem generator_square [Algebra ℂ A] (a : Letter ι) :
    generator M a * generator M a = 0 := by
  have h : generator M a * generator M a + generator M a * generator M a = 0 := by
    cases a with
    | inl i => exact M.car_cre_cre i i
    | inr i => exact M.car_ann_ann i i
  have hs : (2 : ℂ) • (generator M a * generator M a) = 0 := by
    simpa only [two_smul] using h
  exact (smul_eq_zero.mp hs).resolve_left (by norm_num)

theorem generator_swap (a b : Letter ι) :
    generator M a * generator M b =
      (if contraction a b then (1 : A) else 0) - generator M b * generator M a := by
  cases a with
  | inl i =>
    cases b with
    | inl j => simpa [generator, contraction] using M.cre_cre_rewrite j i
    | inr j =>
      have h : M.cre i * M.ann j + M.ann j * M.cre i =
          (if i = j then 1 else 0) := by
        simpa only [LeanPhy.Quantum.anticommutator, add_comm, eq_comm] using M.car_ann_cre j i
      simpa [generator, contraction] using eq_sub_of_add_eq h
  | inr i =>
    cases b with
    | inl j => simpa [generator, contraction] using M.ann_cre_rewrite i j
    | inr j => simpa [generator, contraction] using M.ann_ann_rewrite i j

@[simp] theorem evalExpansion_nil : evalExpansion M [] = 0 := rfl
@[simp] theorem evalExpansion_cons (k : ℤ) (w : Word ι) (p : Expansion ι) :
    evalExpansion M ((k, w) :: p) = k • eval M w + evalExpansion M p := rfl

@[simp] theorem evalExpansion_append (p q : Expansion ι) :
    evalExpansion M (p ++ q) = evalExpansion M p + evalExpansion M q := by
  simp [evalExpansion]

theorem evalExpansion_prepend_neg (b : Letter ι) (p : Expansion ι) :
    evalExpansion M (p.map (fun t => (-t.1, b :: t.2))) =
      -(generator M b * evalExpansion M p) := by
  induction p with
  | nil => simp
  | cons t p ih =>
    rcases t with ⟨k, w⟩
    simp only [List.map_cons, evalExpansion_cons, eval_cons, neg_smul, ih,
      mul_add, neg_add_rev, mul_smul_comm]
    abel

section Adjoint

variable [StarRing A] (hstar : ∀ i, M.cre i = star (M.ann i))

include hstar

theorem generator_dagger (a : Letter ι) : generator M (dagger a) = star (generator M a) := by
  cases a with
  | inl i =>
    change M.ann i = star (M.cre i)
    rw [hstar, star_star]
  | inr i => exact hstar i

theorem eval_adjoint (w : Word ι) : eval M (adjoint w) = star (eval M w) := by
  induction w with
  | nil => simp [adjoint]
  | cons a w ih =>
    simpa only [adjoint, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      eval_append, eval_cons, eval_nil, mul_one, generator_dagger M hstar, star_mul] using
      congrArg (fun x => x * star (generator M a)) ih

end Adjoint
end Semantics

section Ordered

variable {ι A : Type} [LinearOrder ι] [Fintype ι] [Ring A] [Algebra ℂ A]
variable (M : MultiModeCAR ι A)

theorem eval_insert (a : Letter ι) (w : Word ι) :
    evalExpansion M (insert a w) = generator M a * eval M w := by
  induction w with
  | nil => simp [insert]
  | cons b w ih =>
    by_cases hab : a = b
    · subst b
      simp [insert, ← mul_assoc, generator_square]
    · by_cases hlt : a < b
      · simp [insert, hab, hlt]
      · rw [insert, ite_eq_right hab, ite_eq_right hlt, evalExpansion_append,
          evalExpansion_prepend_neg, ih, eval_cons]
        conv_rhs => rw [← mul_assoc, generator_swap M a b]
        cases contraction a b <;> simp [mul_assoc, sub_eq_add_neg, add_mul]

omit [Algebra ℂ A] in
theorem evalExpansion_scale (k : ℤ) (p : Expansion ι) :
    evalExpansion M (p.map (fun t => (k * t.1, t.2))) = k • evalExpansion M p := by
  induction p with
  | nil => simp
  | cons t p ih =>
    rcases t with ⟨n, w⟩
    simp [ih, smul_add, mul_smul]

theorem eval_normalize (w : Word ι) : evalExpansion M (normalize w) = eval M w := by
  induction w with
  | nil => simp [normalize]
  | cons a w ih =>
    have h (p : Expansion ι) :
        evalExpansion M (p.flatMap (fun t =>
          (insert a t.2).map (fun u => (t.1 * u.1, u.2)))) =
          generator M a * evalExpansion M p := by
      induction p with
      | nil => simp
      | cons t p hp =>
        rcases t with ⟨k, u⟩
        simp only [List.flatMap_cons, evalExpansion_append, evalExpansion_scale,
          eval_insert, hp, evalExpansion_cons, mul_add, mul_smul_comm]
    rw [normalize, h, ih, eval_cons]

end Ordered
end LeanPhy.FieldTheory.FermionWord
