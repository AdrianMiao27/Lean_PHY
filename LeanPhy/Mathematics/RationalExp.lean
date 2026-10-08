import LeanPhy.Mathematics.Approximation
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Exact rational enclosures of the real exponential

Taylor remainders on `[-1,1]` and repeated squaring give executable rational
centers and radii. The range-reduction condition is checked, not assumed from a
floating-point evaluation. A proposed rounded value is certified against the
whole enclosure; no property of an external rounding implementation is trusted.
-/

namespace LeanPhy.Mathematics.RationalExp

open scoped BigOperators

structure Ball where
  center : ℚ
  radius : ℚ
  deriving DecidableEq, Repr

namespace Ball

def Contains (b : Ball) (x : ℝ) : Prop := |x - b.center| ≤ b.radius

def square (b : Ball) : Ball :=
  ⟨b.center ^ 2, b.radius * (2 * |b.center| + b.radius)⟩

theorem square_contains (b : Ball) (x : ℝ) (h : b.Contains x) :
    b.square.Contains (x ^ 2) := by
  change |x - (b.center : ℝ)| ≤ b.radius at h
  have hr : (0 : ℝ) ≤ b.radius := (abs_nonneg _).trans h
  have hx : |x| ≤ |(b.center : ℝ)| + b.radius := by
    have := abs_add_le (x - b.center) (b.center : ℝ)
    rw [sub_add_cancel] at this
    linarith
  have hs : |x + b.center| ≤ 2 * |(b.center : ℝ)| + b.radius :=
    (abs_add_le _ _).trans (by linarith)
  change |x ^ 2 - ((b.center ^ 2 : ℚ) : ℝ)| ≤
    ((b.radius * (2 * |b.center| + b.radius) : ℚ) : ℝ)
  push_cast
  calc
    |x ^ 2 - (b.center : ℝ) ^ 2| = |x - b.center| * |x + b.center| := by
      rw [← abs_mul]; congr 1; ring
    _ ≤ (b.radius : ℝ) * (2 * |(b.center : ℝ)| + b.radius) :=
      mul_le_mul h hs (abs_nonneg _) hr

/-- Decidable acceptance of a proposed rounded value and its total error. -/
def Accepts (b : Ball) (value error : ℚ) : Prop :=
  0 ≤ error ∧ |b.center - value| + b.radius ≤ error

instance (b : Ball) (value error : ℚ) : Decidable (b.Accepts value error) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem error (b : Ball) (x : ℝ) (h : b.Contains x) (value error : ℚ)
    (hc : b.Accepts value error) : ErrorCertificate (value : ℝ) x (error : ℝ) := by
  change |x - (b.center : ℝ)| ≤ b.radius at h
  refine ⟨by exact_mod_cast hc.1, ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  have htriangle := abs_add_le (x - b.center) ((b.center : ℝ) - value)
  have hcast : |(b.center : ℝ) - value| + b.radius ≤ error := by exact_mod_cast hc.2
  have heq : x - (b.center : ℝ) + ((b.center : ℝ) - value) = x - value := by ring
  rw [heq] at htriangle
  linarith

end Ball

/-- `order + 1` terms, so even order zero has a valid nonempty remainder bound. -/
def taylor (q : ℚ) (order : ℕ) : Ball :=
  ⟨∑ k ∈ Finset.range (order + 1), q ^ k / (k.factorial : ℚ),
    |q| ^ (order + 1) * ((order + 2 : ℕ) : ℚ) /
      (((order + 1).factorial : ℚ) * ((order + 1 : ℕ) : ℚ))⟩

theorem taylor_contains (q : ℚ) (order : ℕ) (hq : |q| ≤ 1) :
    (taylor q order).Contains (Real.exp (q : ℝ)) := by
  have h := Real.exp_bound (x := (q : ℝ)) (by exact_mod_cast hq)
    (n := order + 1) (Nat.succ_pos order)
  simpa only [Ball.Contains, taylor, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_mul, Rat.cast_abs, mul_div_assoc] using h

/-- Repeated halving followed by squaring; the output is exact rational data. -/
def enclose (q : ℚ) : ℕ → ℕ → Ball
  | 0, order => taylor q order
  | depth + 1, order => (enclose (q / 2) depth order).square

theorem enclose_contains (q : ℚ) (depth order : ℕ) (hq : |q| ≤ (2 : ℚ) ^ depth) :
    (enclose q depth order).Contains (Real.exp (q : ℝ)) := by
  induction depth generalizing q with
  | zero => exact taylor_contains q order (by simpa using hq)
  | succ depth ih =>
    have hh : |q / 2| ≤ (2 : ℚ) ^ depth := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 2)]
      apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 2)).mpr
      simpa only [pow_succ] using hq
    have h := (enclose (q / 2) depth order).square_contains _ (ih (q / 2) hh)
    have he : Real.exp ((q / 2 : ℚ) : ℝ) ^ 2 = Real.exp (q : ℝ) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      push_cast
      ring
    simpa only [enclose, he] using h

/-- Arbitrarily supplied decimal/rational output gains a theorem only after
range reduction and its error budget have both passed exact checks. -/
def Accepted (q : ℚ) (depth order : ℕ) (value error : ℚ) : Prop :=
  |q| ≤ (2 : ℚ) ^ depth ∧ (enclose q depth order).Accepts value error

instance (q : ℚ) (depth order : ℕ) (value error : ℚ) :
    Decidable (Accepted q depth order value error) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem sound (q : ℚ) (depth order : ℕ) (value error : ℚ)
    (h : Accepted q depth order value error) :
    ErrorCertificate (value : ℝ) (Real.exp (q : ℝ)) (error : ℝ) :=
  (enclose q depth order).error _ (enclose_contains q depth order h.1) value error h.2

end LeanPhy.Mathematics.RationalExp
