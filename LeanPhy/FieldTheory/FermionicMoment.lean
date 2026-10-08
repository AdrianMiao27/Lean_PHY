import LeanPhy.FieldTheory.FermionicWick
import Mathlib.Data.List.Basic

set_option autoImplicit false

/-!
# Ordered fermionic contraction recursion

Remove one position at a time, retaining the order of all surviving slots and
alternating the sign. Equal physical probes may occur in different positions;
no equality test merges them. The kernel is algebraic. Its connection to actual
vacuum traces is proved in `FermionVacuumWick`.
-/

namespace LeanPhy.FieldTheory.FermionicWick

universe u v
variable {I : Type u} {A : Type v} [CommRing A]

/-- Sign, chosen slot, and the remaining ordered slots. -/
def removals : List I → List (ℤ × I × List I)
  | [] => []
  | x :: xs => (1, x, xs) :: (removals xs).map (fun t => (-t.1, t.2.1, x :: t.2.2))

theorem removal_length {xs : List I} {t : ℤ × I × List I} (h : t ∈ removals xs) :
    t.2.2.length + 1 = xs.length := by
  induction xs generalizing t with
  | nil => simp [removals] at h
  | cons x xs ih =>
    simp only [removals, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨u, hu, rfl⟩
    · simp
    · simpa using congrArg Nat.succ (ih hu)

/-- The ordered two-point kernel need not be antisymmetric on physical labels.
CAR contact terms are compatible with repeated probes. -/
def moment (C : I → I → A) : List I → A
  | [] => 1
  | p :: ps => ((removals ps).attach.map (fun t =>
      (t.val.1 : A) * C p t.val.2.1 * moment C t.val.2.2)).sum
  termination_by ps => ps.length
  decreasing_by
    have h := removal_length t.property
    simp only [List.length_cons]
    omega

@[simp] theorem moment_nil (C : I → I → A) : moment C [] = 1 := by
  rw [moment.eq_1]

theorem moment_cons (C : I → I → A) (p : I) (ps : List I) :
    moment C (p :: ps) =
      ((removals ps).map (fun t => (t.1 : A) * C p t.2.1 * moment C t.2.2)).sum := by
  rw [moment.eq_2]
  exact congrArg List.sum (List.attach_map_val (l := removals ps)
    (f := fun t : ℤ × I × List I => (t.1 : A) * C p t.2.1 * moment C t.2.2))

@[simp] theorem moment_one (C : I → I → A) (p : I) : moment C [p] = 0 := by
  simp [moment_cons, removals]

@[simp] theorem moment_two (C : I → I → A) (p q : I) : moment C [p,q] = C p q := by
  simp [moment_cons, removals]

theorem moment_four (C : I → I → A) (p q r s : I) :
    moment C [p,q,r,s] = fourPoint C p q r s := by
  simp [moment_cons, removals, fourPoint]
  ring

theorem removals_map {J : Type*} (f : I → J) (ps : List I) :
    removals (ps.map f) =
      (removals ps).map (fun t => (t.1, f t.2.1, t.2.2.map f)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [removals, ih, List.map_map, Function.comp_def]

/-- Relabeling probes commutes with the ordered recursion, including repeated labels. -/
theorem moment_map {J : Type*} (C : J → J → A) (f : I → J) (ps : List I) :
    moment C (ps.map f) = moment (fun p q => C (f p) (f q)) ps := by
  induction hn : ps.length using Nat.strong_induction_on generalizing ps with
  | h n ih =>
    cases ps with
    | nil => simp
    | cons p ps =>
      rw [List.map_cons, moment_cons, moment_cons, removals_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      simp only [Function.comp_apply]
      rw [ih t.2.2.length (by
        have hlen := removal_length ht
        simp only [List.length_cons] at hn
        omega) t.2.2 rfl]

/-- Exact coefficient specialization commutes with every contraction. -/
theorem map_moment {B : Type*} [CommRing B] (f : A →+* B)
    (C : I → I → A) (ps : List I) :
    f (moment C ps) = moment (fun p q => f (C p q)) ps := by
  induction hn : ps.length using Nat.strong_induction_on generalizing ps with
  | h n ih =>
    cases ps with
    | nil => simp
    | cons p ps =>
      rw [moment_cons, moment_cons, map_list_sum, List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      simp only [Function.comp_apply, map_mul, map_intCast]
      rw [ih t.2.2.length (by
        have hlen := removal_length ht
        simp only [List.length_cons] at hn
        omega) t.2.2 rfl]

/-- Odd ordered moments vanish for this pairing recursion. The actual-state
version requires and consumes the vacuum proof. -/
theorem moment_odd (C : I → I → A) (ps : List I) (hodd : ps.length % 2 = 1) :
    moment C ps = 0 := by
  induction hn : ps.length using Nat.strong_induction_on generalizing ps with
  | h n ih =>
    cases ps with
    | nil => simp at hodd
    | cons p ps =>
      rw [moment_cons]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      have htlen := removal_length ht
      have hlt : t.2.2.length < n := by simp only [List.length_cons] at hn; omega
      have hodd' : t.2.2.length % 2 = 1 := by
        simp only [List.length_cons] at hodd
        omega
      rw [ih _ hlt _ hodd' rfl, mul_zero]

end LeanPhy.FieldTheory.FermionicWick
