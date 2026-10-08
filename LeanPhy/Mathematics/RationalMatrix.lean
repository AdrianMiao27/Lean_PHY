import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Exact rational data for complex matrix certificates

The two rational matrices are real and imaginary parts, not a product-ring
matrix. Data multiplication implements complex multiplication explicitly.
Row sums of `abs re + abs im` give conservative, rationally decidable bounds
for the L-infinity operator norm. Rectangular matrices and empty dimensions
are supported. No floating-point rounding or spectral norm is implicit.
-/

namespace LeanPhy.Mathematics

structure RationalMatrix (m n : ℕ) where
  re : Matrix (Fin m) (Fin n) ℚ
  im : Matrix (Fin m) (Fin n) ℚ

namespace RationalMatrix

open scoped NNReal Matrix.Norms.Operator

variable {l m n : ℕ}

noncomputable def realize (A : RationalMatrix m n) : Matrix (Fin m) (Fin n) ℂ :=
  fun i j => ⟨A.re i j, A.im i j⟩

def ofReal (A : Matrix (Fin m) (Fin n) ℚ) : RationalMatrix m n := ⟨A, 0⟩

def zero (m n : ℕ) : RationalMatrix m n := ⟨0, 0⟩

def one (n : ℕ) : RationalMatrix n n := ⟨1, 0⟩

def add (A B : RationalMatrix m n) : RationalMatrix m n := ⟨A.re + B.re, A.im + B.im⟩

def sub (A B : RationalMatrix m n) : RationalMatrix m n := ⟨A.re - B.re, A.im - B.im⟩

def mul (A : RationalMatrix l m) (B : RationalMatrix m n) : RationalMatrix l n :=
  ⟨A.re * B.re - A.im * B.im, A.re * B.im + A.im * B.re⟩

@[simp] theorem realize_zero (m n : ℕ) : (zero m n).realize = 0 := by
  ext i j
  apply Complex.ext <;> simp [realize, zero]

@[simp] theorem realize_one (n : ℕ) : (one n).realize = 1 := by
  ext i j
  apply Complex.ext <;> by_cases h : i = j <;> simp [realize, one, Matrix.one_apply, h]

@[simp] theorem realize_add (A B : RationalMatrix m n) :
    (A.add B).realize = A.realize + B.realize := by
  ext i j
  apply Complex.ext <;> simp [realize, add]

@[simp] theorem realize_sub (A B : RationalMatrix m n) :
    (A.sub B).realize = A.realize - B.realize := by
  ext i j
  apply Complex.ext <;> simp [realize, sub]

@[simp] theorem realize_mul (A : RationalMatrix l m) (B : RationalMatrix m n) :
    (A.mul B).realize = A.realize * B.realize := by
  ext i j
  apply Complex.ext <;> simp [realize, mul, Matrix.mul_apply, Complex.mul_re, Complex.mul_im,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Rational upper bound for the modulus of an entry. -/
def entryBound (A : RationalMatrix m n) (i : Fin m) (j : Fin n) : ℚ :=
  |A.re i j| + |A.im i j|

def rowBound (A : RationalMatrix m n) (i : Fin m) : ℚ := ∑ j, A.entryBound i j

/-- The nonnegative bound also handles an empty set of rows. -/
def Bounded (A : RationalMatrix m n) (b : ℚ) : Prop := 0 ≤ b ∧ ∀ i, A.rowBound i ≤ b

instance (A : RationalMatrix m n) (b : ℚ) : Decidable (A.Bounded b) :=
  inferInstanceAs (Decidable (0 ≤ b ∧ ∀ i, A.rowBound i ≤ b))

theorem entry_norm_le (A : RationalMatrix m n) (i : Fin m) (j : Fin n) :
    ‖A.realize i j‖ ≤ (A.entryBound i j : ℝ) := by
  simpa [realize, entryBound] using Complex.norm_le_abs_re_add_abs_im (A.realize i j)

/-- The row criterion uses a submultiplicative matrix norm, not an entrywise norm. -/
theorem norm_le_of_rows (A : Matrix (Fin m) (Fin n) ℂ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ i, ∑ j, ‖A i j‖ ≤ b) : ‖A‖ ≤ b := by
  rw [Matrix.linfty_opNorm_def]
  have hs : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ (⟨b, hb⟩ : ℝ≥0) := by
    apply Finset.sup_le
    intro i _
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_sum, NNReal.coe_mk, coe_nnnorm] using! h i
  exact_mod_cast hs

theorem norm_le (A : RationalMatrix m n) (b : ℚ) (h : A.Bounded b) :
    ‖A.realize‖ ≤ (b : ℝ) := by
  apply norm_le_of_rows _ _ (by exact_mod_cast h.1)
  intro i
  calc
    _ ≤ ∑ j, (A.entryBound i j : ℝ) := Finset.sum_le_sum fun j _ => A.entry_norm_le i j
    _ = (A.rowBound i : ℝ) := by simp [rowBound]
    _ ≤ _ := by exact_mod_cast h.2 i

/-- A row-wise complex enclosure supplies the norm-ball premise used by a
robust certificate. The enclosure's relation to the physical model is proved. -/
theorem enclosure_norm_le (A : RationalMatrix m n) (D : Matrix (Fin m) (Fin n) ℂ)
    (E : Matrix (Fin m) (Fin n) ℚ) (ε : ℚ) (hε : 0 ≤ ε)
    (hrows : ∀ i, ∑ j, E i j ≤ ε)
    (hmodel : ∀ i j, ‖D i j - A.realize i j‖ ≤ (E i j : ℝ)) :
    ‖D - A.realize‖ ≤ (ε : ℝ) := by
  apply norm_le_of_rows _ _ (by exact_mod_cast hε)
  intro i
  calc
    _ ≤ ∑ j, (E i j : ℝ) := Finset.sum_le_sum fun j _ => hmodel i j
    _ ≤ _ := by exact_mod_cast hrows i

end RationalMatrix
end LeanPhy.Mathematics
