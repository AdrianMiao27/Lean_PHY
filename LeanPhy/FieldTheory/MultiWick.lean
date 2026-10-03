import LeanPhy.FieldTheory.Pairing
import Mathlib.Tactic

/-!
# A finite multi-field bosonic Wick kernel

The single-mode Wick file proves the moment recursion for one oscillator.  This
module lifts the reusable combinatorial part to a finite family of fields.  A
covariance kernel `C i j` is supplied by the model and the finite Gaussian
moment is defined by contracting the first field with each remaining field.
The result is intentionally finite and algebraic: ordering, distributions,
time ordering, convergence and renormalisation are not inferred.

The recursive definition is useful as an executable normaliser for lattice,
finite-volume and truncated-QFT calculations.  Its four-point theorem is the
first nontrivial multi-field regression and exposes all three contractions.
-/

namespace LeanPhy.FieldTheory

open scoped BigOperators

universe u v

namespace MultiWick

variable {I : Type u} [DecidableEq I]
variable {A : Type v} [CommSemiring A]

/-- The finite bosonic Wick recursion for a covariance kernel. -/
def gaussianMoment (C : I → I → A) : List I → A
  | [] => 1
  | x :: xs =>
      (xs.map (fun y => C x y * gaussianMoment C (Pairing.removeOne y xs))).sum
  termination_by l => l.length
  decreasing_by
    exact Nat.lt_succ_of_lt (by
      have hlen := Pairing.length_removeOne _ _ (by assumption)
      omega)

@[simp] theorem gaussianMoment_nil (C : I → I → A) :
    gaussianMoment C [] = 1 := by
  rw [gaussianMoment.eq_1]

@[simp] theorem gaussianMoment_cons (C : I → I → A) (x : I) (xs : List I) :
    gaussianMoment C (x :: xs) =
      (xs.map (fun y => C x y * gaussianMoment C (Pairing.removeOne y xs))).sum := by
  rw [gaussianMoment.eq_2]

theorem gaussianMoment_two (C : I → I → A) (i j : I) :
    gaussianMoment C [i, j] = C i j := by
  simp [Pairing.removeOne]

@[simp] theorem gaussianMoment_one (C : I → I → A) (i : I) :
    gaussianMoment C [i] = 0 := by
  simp [Pairing.removeOne]

/-! A concrete four-slot statement avoids silently identifying distinct field
    labels.  `Fin 4` supplies four typed slots, while C may still encode any
    covariance convention. -/

theorem gaussianMoment_four (C : Fin 4 → Fin 4 → A) :
    gaussianMoment C [0, 1, 2, 3] =
      C 0 1 * C 2 3 + C 0 2 * C 1 3 + C 0 3 * C 1 2 := by
  simp [Pairing.removeOne]
  ring

theorem gaussianMoment_four_symmetric (C : Fin 4 → Fin 4 → A)
    (_hC : ∀ i j, C i j = C j i) :
    gaussianMoment C [0, 1, 2, 3] =
      C 0 1 * C 2 3 + C 0 2 * C 1 3 + C 0 3 * C 1 2 :=
  gaussianMoment_four C

end MultiWick

end LeanPhy.FieldTheory
