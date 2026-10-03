import LeanPhy.HighEnergy.Spinor
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

/-!
# Scattering kinematics: the Mandelstam invariants

The kinematic backbone of a 2 -> 2 amplitude is the three Mandelstam
invariants

    s = (p1 + p2)^2,   t = (p1 - p3)^2,   u = (p1 - p4)^2,

built from the Minkowski inner product `minkowskiDot` already used for the
Dirac algebra.  With four-momentum conservation `p1 + p2 = p3 + p4` they
satisfy the textbook identity

    s + t + u = m1^2 + m2^2 + m3^2 + m4^2.

This module proves that identity and the algebra it rests on: bilinearity,
symmetry and the sign law of `minkowskiDot`.  Everything is a kernel-checked
statement about `Fin 4 -> ℂ`; the physics input (which momenta, on shell
or off shell) is whatever the caller supplies, in keeping with the
conditional semantics of the library.  Continuum and analytic content
(crossing, dispersion relations, the optical theorem) is out of scope.
-/

namespace LeanPhy.HighEnergy

open scoped BigOperators Matrix

abbrev Vec := Fin 4 → ℂ

/-- The Minkowski product is symmetric. -/
theorem minkowskiDot_comm (a b : Vec) : minkowskiDot a b = minkowskiDot b a := by
  simp only [minkowskiDot, etaFin]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  fin_cases m <;> fin_cases n <;> simp [Fin.sum_univ_four] <;> ring

/-- The Minkowski product is linear in its second argument. -/
theorem minkowskiDot_add_right (a b c : Vec) :
    minkowskiDot a (b + c) = minkowskiDot a b + minkowskiDot a c := by
  simp only [minkowskiDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The Minkowski product is linear in its first argument. -/
theorem minkowskiDot_add_left (a b c : Vec) :
    minkowskiDot (a + b) c = minkowskiDot a c + minkowskiDot b c := by
  simp only [minkowskiDot, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

/-- Sign law under negation in the second slot. -/
theorem minkowskiDot_neg_right (a b : Vec) : minkowskiDot a (-b) = -minkowskiDot a b := by
  simp [minkowskiDot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-- Sign law under negation in the first slot. -/
theorem minkowskiDot_neg_left (a b : Vec) : minkowskiDot (-a) b = -minkowskiDot a b := by
  simp [minkowskiDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- Subtracting in the second slot. -/
theorem minkowskiDot_sub_right (a b c : Vec) :
    minkowskiDot a (b - c) = minkowskiDot a b - minkowskiDot a c := by
  rw [sub_eq_add_neg, minkowskiDot_add_right, minkowskiDot_neg_right]; ring

/-- Subtracting in the first slot. -/
theorem minkowskiDot_sub_left (a b c : Vec) :
    minkowskiDot (a - b) c = minkowskiDot a c - minkowskiDot b c := by
  rw [sub_eq_add_neg, minkowskiDot_add_left, minkowskiDot_neg_left]; ring

/-- The Minkowski product with the zero vector vanishes. -/
theorem minkowskiDot_zero_right (a : Vec) : minkowskiDot a 0 = 0 := by
  simp [minkowskiDot]

/-- **Mandelstam identity, off shell.**  For any four momenta the defect
`s + t + u - (m1^2 + m2^2 + m3^2 + m4^2)` equals
`2 p1.(p1 + p2 - p3 - p4)`, which vanishes under four-momentum conservation.
Stating it this way keeps the conservation law a visible hypothesis rather
than a hidden assumption. -/
theorem mandelstam_defect (p1 p2 p3 p4 : Vec) :
    minkowskiDot (p1 + p2) (p1 + p2) + minkowskiDot (p1 - p3) (p1 - p3)
        + minkowskiDot (p1 - p4) (p1 - p4)
      - (minkowskiDot p1 p1 + minkowskiDot p2 p2 + minkowskiDot p3 p3 + minkowskiDot p4 p4)
      = 2 * minkowskiDot p1 (p1 + p2 - p3 - p4) := by
  have hR : minkowskiDot p1 (p1 + p2 - p3 - p4)
      = minkowskiDot p1 p1 + minkowskiDot p1 p2 - minkowskiDot p1 p3 - minkowskiDot p1 p4 := by
    rw [minkowskiDot_sub_right, minkowskiDot_sub_right, minkowskiDot_add_right]
  rw [hR, minkowskiDot_add_left, minkowskiDot_add_right, minkowskiDot_add_right,
      minkowskiDot_sub_left, minkowskiDot_sub_right, minkowskiDot_sub_right,
      minkowskiDot_sub_left, minkowskiDot_sub_right, minkowskiDot_sub_right]
  rw [minkowskiDot_comm p2 p1, minkowskiDot_comm p3 p1, minkowskiDot_comm p4 p1]
  ring

/-- **Mandelstam identity on shell.**  With four-momentum conservation
`p1 + p2 = p3 + p4`, the three invariants obey
`s + t + u = m1^2 + m2^2 + m3^2 + m4^2`. -/
theorem mandelstam (p1 p2 p3 p4 : Vec) (h : p1 + p2 - p3 - p4 = 0) :
    minkowskiDot (p1 + p2) (p1 + p2) + minkowskiDot (p1 - p3) (p1 - p3)
        + minkowskiDot (p1 - p4) (p1 - p4)
      = minkowskiDot p1 p1 + minkowskiDot p2 p2 + minkowskiDot p3 p3 + minkowskiDot p4 p4 := by
  have hm := mandelstam_defect p1 p2 p3 p4
  rw [h, minkowskiDot_zero_right, mul_zero] at hm
  exact sub_eq_zero.mp hm

/-- A concrete on-shell massless configuration: all four momenta are
lightlike, so conservation holds and the identity reads `s + t + u = 0`.
The kernel evaluates the arithmetic. -/
theorem mandelstam_massless_witness :
    minkowskiDot ((![1,0,0,1] : Vec) + (![1,0,0,-1] : Vec)) ((![1,0,0,1] : Vec) + (![1,0,0,-1] : Vec))
        + minkowskiDot (((![1,0,0,1] : Vec) - (![1,0,0,1] : Vec))) (((![1,0,0,1] : Vec) - (![1,0,0,1] : Vec)))
        + minkowskiDot (((![1,0,0,1] : Vec) - (![1,0,0,-1] : Vec))) (((![1,0,0,1] : Vec) - (![1,0,0,-1] : Vec)))
      = minkowskiDot (![1,0,0,1] : Vec) (![1,0,0,1] : Vec)
        + minkowskiDot (![1,0,0,-1] : Vec) (![1,0,0,-1] : Vec)
        + minkowskiDot (![1,0,0,1] : Vec) (![1,0,0,1] : Vec)
        + minkowskiDot (![1,0,0,-1] : Vec) (![1,0,0,-1] : Vec) :=
  mandelstam _ _ _ _ (by ext i; fin_cases i <;> simp)

end LeanPhy.HighEnergy
