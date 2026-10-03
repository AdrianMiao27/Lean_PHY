import LeanPhy.Quantum.Basic
import Mathlib.Tactic

/-!
# Lorentz boosts: rapidity addition and the invariance of the interval

A boost along one spatial axis is the `2 x 2` matrix
`B(c, s) = [[c, -s], [-s, c]]` in the `(t, x)` plane, where the rapidity` phi` sets
`c = cosh phi`, `s = sinh phi`.  The defining identity of the boost is
`c^2 - s^2 = 1` (the hyperbolic Pythagorean identity), and from it everything about
the kinematics follows algebraically:

* **boosts compose by adding rapidities**: the product of two boost matrices is
  again a boost whose parameters add, `B(c1,s1) B(c2,s2) = B(c1 c2 + s1 s2, c1 s2 + s1 c2)`.
  This is the relativistic velocity-addition law in disguise, and the reason the
  set of rapidity boosts is a one-parameter group;
* **boosts preserve the Minkowski metric**: with `eta = diag (1, -1)`,
  `B^T eta B = eta` exactly when `c^2 - s^2 = 1`, so the invariant interval
  `t^2 - x^2` is preserved.  This is the Lorentz condition, checked on the explicit
  matrix rather than assumed.

The parameters are abstract complex numbers satisfying `c^2 - s^2 = 1`; no
hyperbolic functions enter, so the algebra is exact and kernel-checked.  The
hypothesis `c^2 - s^2 = 1` is what a real rapidity supplies, so this is conditional
correctness.
-/

namespace LeanPhy.Relativity

open scoped BigOperators Matrix

/-- Two-dimensional complex matrices for the `(t, x)` plane. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) Complex

/-- A boost with parameters `c`, `s` (`c = cosh phi`, `s = sinh phi`). -/
noncomputable def boost (c s : Complex) : M2 := !![c, -s; -s, c]

/-- The `(1+1)`-dimensional Minkowski metric `diag (1, -1)`. -/
noncomputable def etaM : M2 := !![1, 0; 0, -1]

/-- **Rapidity addition**: the product of two boosts is a boost with added
parameters, the relativistic velocity-addition law. -/
theorem boost_mul (c1 s1 c2 s2 : Complex) :
    boost c1 s1 * boost c2 s2 = boost (c1 * c2 + s1 * s2) (c1 * s2 + s1 * c2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boost, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Boosts form a one-parameter group: the identity is the boost `(1, 0)`. -/
theorem boost_one_mul (c s : Complex) :
    boost 1 0 * boost c s = boost c s := by
  rw [boost_mul]
  norm_num

/-- **The Lorentz condition**: a boost preserves the Minkowski metric exactly when
`c^2 - s^2 = 1`.  This is the invariance of the interval `t^2 - x^2`. -/
theorem boost_lorentz (c s : Complex) (h : c^2 - s^2 = 1) :
    (boost c s)ᵀ * etaM * boost c s = etaM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boost, etaM, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] <;>
    first
    | linear_combination h
    | linear_combination -h
    | ring

/-- The determinant of a boost is `c^2 - s^2`: a proper orthochronous boost has
determinant one. -/
theorem boost_det (c s : Complex) : (boost c s).det = c^2 - s^2 := by
  simp [boost, Matrix.det_fin_two]
  ring

/-- The inverse of a boost is the boost with `s` negated (the inverse rapidity). -/
theorem boost_inv (c s : Complex) (h : c^2 - s^2 = 1) :
    boost c s * boost c (-s) = 1 := by
  rw [boost_mul]
  have hs : s * -s = -(s^2) := by ring
  rw [hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boost] <;>
    first
    | linear_combination h
    | ring

end LeanPhy.Relativity
