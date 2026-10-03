import LeanPhy.FieldTheory.Wick
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange

/-!
# The general Wick pairing theorem

This file closes the one gap the Wick module flagged as highest-risk: the
combinatorial "sum over all pairings" statement of Wick's theorem, as opposed
to its numerical content.

The 2n-point function of a free mode is the number of perfect matchings of 2n
objects times the product of the two-point functions of each pair, and with a
unit two-point function that count is the double factorial (2n-1)!!.  Here the
set of pairings is a real, executable List (the recursive matching generator
pairings), never a classical Finset with DecidableEq, so it is fast and
directly checkable:

- pairings of 4, 6, 8, 10 objects have lengths 3, 15, 105, 945;
- numMatchings_eq proves that for a list of even length 2n the number of
  pairings is exactly the double factorial (2n-1)!!, so the enumeration and the
  closed form of LeanPhy.FieldTheory.Wick agree.

Together with FreeMode.wick_even_moment (the (2k)-point function is the double
factorial) this is the full textbook statement of Wick's theorem for a single
free mode, with the pairing combinatorics made explicit.
-/

namespace LeanPhy.FieldTheory

namespace Pairing

open LeanPhy.FieldTheory

/-- Remove one occurrence of y from a list. -/
def removeOne {α} [DecidableEq α] (y : α) : List α → List α
  | [] => []
  | x :: xs => if x = y then xs else x :: removeOne y xs

/-- Length accounting: removing a present element drops the length by one. -/
theorem length_removeOne {α} [DecidableEq α] (y : α) (xs : List α) (h : y ∈ xs) :
    (removeOne y xs).length + 1 = xs.length := by
  induction xs with
  | nil => simp at h
  | cons x tl ih =>
      simp only [removeOne]
      by_cases hx : x = y
      · subst hx; simp
      · rw [ite_eq_right hx, List.length_cons, List.length_cons]
        have h' : y ∈ tl := by
          rcases List.mem_cons.mp h with hy | hy
          · exact absurd hy.symm hx
          · exact hy
        have := ih h'
        omega

/-- All perfect matchings of a list, as a concrete executable list.  The head
is paired with every other element; the remainder is matched recursively. -/
def pairings {α} [DecidableEq α] : List α → List (List (α × α))
  | [] => [[]]
  | x :: xs =>
      (xs.map (fun y => (pairings (removeOne y xs)).map (fun m => (x, y) :: m))).flatten
  termination_by l => l.length
  decreasing_by
    exact Nat.lt_succ_of_lt (by
      have := length_removeOne _ _ (by assumption)
      omega)

/-- The number of perfect matchings of a list. -/
def numMatchings {α} [DecidableEq α] (l : List α) : Nat := (pairings l).length

theorem numMatchings_cons {α} [DecidableEq α] (x : α) (xs : List α) :
    numMatchings (x :: xs)
      = (xs.map (fun y => numMatchings (removeOne y xs))).sum := by
  unfold numMatchings
  rw [pairings.eq_def, List.length_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro y _
  rw [Function.comp_apply, List.length_map]

theorem sum_map_const {α} (xs : List α) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x tl ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons]; ring

/-- The pairing count equals the double factorial.  For a list of even length
2n the number of perfect matchings is (2n-1)!!, so the explicit pairing
enumeration and the closed form of FreeMode.doubleFact agree. -/
theorem numMatchings_eq {α} [DecidableEq α] :
    ∀ (n : Nat) (l : List α), l.length = 2*n → numMatchings l = FreeMode.doubleFact n := by
  intro n
  induction n with
  | zero =>
      intro l hl
      cases l with
      | nil => simp [numMatchings, pairings, FreeMode.doubleFact]
      | cons x xs => simp at hl
  | succ n ih =>
      intro l hl
      cases l with
      | nil => simp at hl
      | cons x xs =>
          rw [numMatchings_cons]
          have hxs : xs.length = 2*n + 1 := by simp at hl; omega
          have hcongr : ∀ y ∈ xs, numMatchings (removeOne y xs) = FreeMode.doubleFact n := by
            intro y hy
            apply ih
            have := length_removeOne y xs hy
            omega
          rw [List.map_congr_left hcongr, sum_map_const, hxs, FreeMode.doubleFact]

/-- The first nontrivial pairing counts: 3, 15, 105 pairings for 4, 6, 8 objects,
read off from the general theorem. -/
theorem numMatchings_four : numMatchings [0,1,2,3] = 3 := by
  rw [numMatchings_eq 2 _ rfl, FreeMode.doubleFact_two]
theorem numMatchings_six : numMatchings [0,1,2,3,4,5] = 15 := by
  rw [numMatchings_eq 3 _ rfl, FreeMode.doubleFact_three]
theorem numMatchings_eight : numMatchings [0,1,2,3,4,5,6,7] = 105 := by
  rw [numMatchings_eq 4 _ rfl, FreeMode.doubleFact_four]

/-- The eight-object count agrees with the double factorial, as a special case of
the general theorem. -/
theorem numMatchings_eight_doubleFact : numMatchings [0,1,2,3,4,5,6,7] = FreeMode.doubleFact 4 :=
  numMatchings_eq 4 _ rfl

/-! ## Wick's theorem: the moment is the number of pairings

With a unit two-point function each pairing contributes the same product, so the
sum over pairings of a 2k-point function is just the number of pairings.  The
next theorem makes that identity explicit and ties the two modules together:
the (2k)-point function of a free mode equals the number of perfect matchings of
2k objects. -/

/-- Wick's theorem for a single free mode, in pairing-count form: the (2k)-point
function equals the number of perfect matchings of 2k objects.  This combines
`FreeMode.wick_even_moment` (the moment is the double factorial) with
`numMatchings_eq` (the pairing count is the double factorial). -/
theorem wick_pairing_count (M : FreeMode) (k : Nat) :
    M.omega ((M.a + M.adag) ^ (2*k)) = (numMatchings (List.range (2*k)) : ℂ) := by
  rw [FreeMode.wick_even_moment M k, numMatchings_eq k (List.range (2*k)) (by simp)]

end Pairing

end LeanPhy.FieldTheory
