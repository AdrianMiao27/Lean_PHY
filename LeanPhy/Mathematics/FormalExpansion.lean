import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Noncommuting expansions with an explicit retained order

The coefficient ring may be a matrix/operator ring. `Below N f g` means that
the coefficients of orders `0, ..., N-1` agree; it is a formal statement, not
a norm estimate after substituting a real expansion parameter. Operations
preserve order without permuting coefficients. Inversion requires an actual
unit constant coefficient, so a singular heavy block cannot be inverted by
total division. These tools support effective operators, source insertions,
and changes of variables in a common formal parameter.
-/

namespace LeanPhy.Mathematics.FormalExpansion

open PowerSeries

variable {R : Type*} [Ring R]

/-- Equality of all retained coefficients, with an exclusive cutoff. -/
def Below (N : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ k, k < N → coeff k f = coeff k g

namespace Below

theorem refl (N : ℕ) (f : PowerSeries R) : Below N f f := fun _ _ => rfl

theorem symm {N : ℕ} {f g : PowerSeries R} (h : Below N f g) : Below N g f :=
  fun k hk => (h k hk).symm

theorem trans {N : ℕ} {f g h : PowerSeries R} (hfg : Below N f g) (hgh : Below N g h) :
    Below N f h := fun k hk => (hfg k hk).trans (hgh k hk)

theorem weaken {M N : ℕ} {f g : PowerSeries R} (h : Below N f g) (hMN : M ≤ N) :
    Below M f g := fun k hk => h k (lt_of_lt_of_le hk hMN)

theorem add {N : ℕ} {f g a b : PowerSeries R} (h : Below N f g) (hab : Below N a b) :
    Below N (f + a) (g + b) := by
  intro k hk
  simp only [map_add, h k hk, hab k hk]

theorem sub {N : ℕ} {f g a b : PowerSeries R} (h : Below N f g) (hab : Below N a b) :
    Below N (f - a) (g - b) := by
  intro k hk
  simp only [map_sub, h k hk, hab k hk]

/-- Ordered Cauchy multiplication; no commutativity of `R` is used. -/
theorem mul {N : ℕ} {f g a b : PowerSeries R} (h : Below N f g) (hab : Below N a b) :
    Below N (f * a) (g * b) := by
  intro k hk
  simp only [coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hp := Finset.mem_antidiagonal.mp hij
  rw [h ij.1 (by omega), hab ij.2 (by omega)]

theorem mul_left {N : ℕ} {f g : PowerSeries R} (h : Below N f g) (a : PowerSeries R) :
    Below N (a * f) (a * g) := (refl N a).mul h

theorem mul_right {N : ℕ} {f g : PowerSeries R} (h : Below N f g) (a : PowerSeries R) :
    Below N (f * a) (g * a) := h.mul (refl N a)

theorem pow {N : ℕ} {f g : PowerSeries R} (h : Below N f g) (k : ℕ) :
    Below N (f ^ k) (g ^ k) := by
  induction k with
  | zero => simpa using refl N (1 : PowerSeries R)
  | succ k ih => simpa only [pow_succ] using ih.mul h

/-- Matching retained inputs gives matching inverse coefficients when both
constant coefficients are certified units. -/
theorem inverse {N : ℕ} {f g : PowerSeries R} (h : Below N f g)
    (u v : Rˣ) (hf : constantCoeff f = u) (hg : constantCoeff g = v) :
    Below N (invOfUnit f u) (invOfUnit g v) := by
  have hmul := (h.mul_left (invOfUnit f u)).mul_right (invOfUnit g v)
  have hl : invOfUnit f u * f * invOfUnit g v = invOfUnit g v := by
    rw [invOfUnit_mul f u hf, one_mul]
  have hr : invOfUnit f u * g * invOfUnit g v = invOfUnit f u := by
    rw [mul_assoc, mul_invOfUnit g v hg, mul_one]
  rw [hl, hr] at hmul
  exact hmul.symm

end Below

/-- First inverse coefficient with its noncommuting left and right factors. -/
theorem inverse_coeff_one (f : PowerSeries R) (u : Rˣ) :
    coeff 1 (invOfUnit f u) = -(↑(u⁻¹) : R) * coeff 1 f * (↑(u⁻¹) : R) := by
  rw [coeff_invOfUnit]
  have h : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
  simp [h, coeff_zero_eq_constantCoeff_apply, mul_assoc]

/-- Second-order inversion keeps operator ordering; matrices need not commute. -/
theorem inverse_coeff_two (f : PowerSeries R) (u : Rˣ) :
    coeff 2 (invOfUnit f u) =
      (↑(u⁻¹) : R) * coeff 1 f * (↑(u⁻¹) : R) * coeff 1 f * (↑(u⁻¹) : R) -
        (↑(u⁻¹) : R) * coeff 2 f * (↑(u⁻¹) : R) := by
  rw [coeff_invOfUnit]
  have h : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
  simp [h, inverse_coeff_one, coeff_zero_eq_constantCoeff_apply]
  noncomm_ring

/-- Retain exactly the coefficients below `N`, setting higher terms to zero. -/
noncomputable def truncate (N : ℕ) (f : PowerSeries R) : PowerSeries R :=
  mk (fun k => if k < N then coeff k f else 0)

@[simp] theorem coeff_truncate (N k : ℕ) (f : PowerSeries R) :
    coeff k (truncate N f) = if k < N then coeff k f else 0 := coeff_mk _ _

theorem truncate_below (N : ℕ) (f : PowerSeries R) : Below N (truncate N f) f := by
  intro k hk
  simp [hk]

theorem truncate_eq_iff (N : ℕ) (f g : PowerSeries R) :
    truncate N f = truncate N g ↔ Below N f g := by
  constructor
  · intro h k hk
    simpa [hk] using congrArg (coeff k) h
  · intro h
    ext k
    by_cases hk : k < N
    · simp [hk, h k hk]
    · simp [hk]

theorem truncate_mul (N : ℕ) (f g : PowerSeries R) :
    truncate N (truncate N f * truncate N g) = truncate N (f * g) :=
  (truncate_eq_iff _ _ _).mpr ((truncate_below N f).mul (truncate_below N g))

theorem truncate_inverse (N : ℕ) (f : PowerSeries R) (u : Rˣ)
    (hf : constantCoeff f = u) (hN : 0 < N) :
    truncate N (invOfUnit (truncate N f) u) = truncate N (invOfUnit f u) := by
  apply (truncate_eq_iff _ _ _).mpr
  apply (truncate_below N f).inverse u u _ hf
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_truncate, ite_eq_left hN,
    coeff_zero_eq_constantCoeff_apply, hf]

/-- Conjugating an operator by an invertible formal change of variables.
This is a similarity transform; unitarity requires a separate star condition. -/
noncomputable def conjugate (U A : PowerSeries R) (u : Rˣ) : PowerSeries R :=
  U * A * invOfUnit U u

theorem conjugate_mul (U A B : PowerSeries R) (u : Rˣ) (hU : constantCoeff U = u) :
    conjugate U (A * B) u = conjugate U A u * conjugate U B u := by
  unfold conjugate
  symm
  calc
    _ = U * A * (invOfUnit U u * U) * B * invOfUnit U u := by noncomm_ring
    _ = _ := by rw [invOfUnit_mul U u hU]; simp [mul_assoc]

/-- All inputs, including the change of variables, may be replaced to the
same retained order. In particular probes must be transformed along with H. -/
theorem conjugate_below {N : ℕ} {U V A B : PowerSeries R}
    (hUV : Below N U V) (hAB : Below N A B) (u v : Rˣ)
    (hU : constantCoeff U = u) (hV : constantCoeff V = v) :
    Below N (conjugate U A u) (conjugate V B v) :=
  (hUV.mul hAB).mul (hUV.inverse u v hU hV)

end LeanPhy.Mathematics.FormalExpansion
