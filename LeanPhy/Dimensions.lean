import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
# Physical dimensions and quantities

A dimension is a vector of integer exponents for the seven SI base dimensions.
The type `Quantity d α` carries the dimension `d` at the *type* level, so the
operations that physics allows are exactly the ones the elaborator accepts:

- adding or subtracting two quantities requires the *same* dimension, so adding
  a length to a time is a **type error caught before any proof is attempted**;
- multiplying quantities *adds* their dimensions, dividing subtracts them;
- a dimensionless quantity is `Quantity 0 α`.

This module is deliberately about bookkeeping, not analysis: no claim about
real numbers, limits, or units systems beyond the exponent vector is made.
-/

namespace LeanPhy

/-- A physical dimension: integer exponents of the seven SI base dimensions. -/
structure Dimension where
  length : Int := 0
  mass : Int := 0
  time : Int := 0
  current : Int := 0
  temperature : Int := 0
  amount : Int := 0
  luminousIntensity : Int := 0
  deriving DecidableEq, Repr

namespace Dimension

instance : Add Dimension where
  add x y :=
    { length := x.length + y.length
      mass := x.mass + y.mass
      time := x.time + y.time
      current := x.current + y.current
      temperature := x.temperature + y.temperature
      amount := x.amount + y.amount
      luminousIntensity := x.luminousIntensity + y.luminousIntensity }

instance : Neg Dimension where
  neg x :=
    { length := -x.length
      mass := -x.mass
      time := -x.time
      current := -x.current
      temperature := -x.temperature
      amount := -x.amount
      luminousIntensity := -x.luminousIntensity }

instance : Sub Dimension where
  sub x y := x + (-y)

instance : Zero Dimension := ⟨{}⟩

/-- The dimensionless exponent vector. -/
abbrev dimensionless : Dimension := {}

/-! The exponent vector is an additive commutative group.  Keeping these laws
   in the public API matters because derived dimensions (powers, quotients and
   action functionals) should simplify by the same algebraic normalisation as
   their numerical values. -/

@[simp] theorem zero_add (x : Dimension) : 0 + x = x := by
  cases x with
  | mk l m t c temp a li =>
    change (⟨(0 : Int) + l, 0 + m, 0 + t, 0 + c, 0 + temp, 0 + a, 0 + li⟩ : Dimension) =
      ⟨l, m, t, c, temp, a, li⟩
    congr <;> omega

@[simp] theorem add_zero (x : Dimension) : x + 0 = x := by
  cases x with
  | mk l m t c temp a li =>
    change (⟨l + (0 : Int), m + 0, t + 0, c + 0, temp + 0, a + 0, li + 0⟩ : Dimension) =
      ⟨l, m, t, c, temp, a, li⟩
    congr <;> omega

@[simp] theorem neg_neg (x : Dimension) : -(-x) = x := by
  cases x with
  | mk l m t c temp a li =>
    change (⟨-(-l), -(-m), -(-t), -(-c), -(-temp), -(-a), -(-li)⟩ : Dimension) =
      ⟨l, m, t, c, temp, a, li⟩
    congr <;> omega

@[simp] theorem sub_self (x : Dimension) : x - x = 0 := by
  cases x with
  | mk l m t c temp a li =>
    change (⟨l + -l, m + -m, t + -t, c + -c, temp + -temp, a + -a, li + -li⟩ : Dimension) =
      (0 : Dimension)
    congr <;> omega

@[simp] theorem sub_zero (x : Dimension) : x - 0 = x := by
  cases x with
  | mk l m t c temp a li =>
    change (⟨l + -(0 : Int), m + -0, t + -0, c + -0, temp + -0, a + -0, li + -0⟩ : Dimension) =
      ⟨l, m, t, c, temp, a, li⟩
    congr <;> omega

@[simp] theorem zero_sub (x : Dimension) : 0 - x = -x := by
  cases x with
  | mk l m t c temp a li =>
    change (⟨(0 : Int) + -l, 0 + -m, 0 + -t, 0 + -c, 0 + -temp, 0 + -a, 0 + -li⟩ : Dimension) =
      ⟨-l, -m, -t, -c, -temp, -a, -li⟩
    congr <;> omega

theorem add_neg_cancel (x y : Dimension) : x + (-x + y) = y := by
  cases x with
  | mk l₁ m₁ t₁ c₁ temp₁ a₁ li₁ =>
    cases y with
    | mk l₂ m₂ t₂ c₂ temp₂ a₂ li₂ =>
      change (⟨l₁ + (-l₁ + l₂), m₁ + (-m₁ + m₂),
        t₁ + (-t₁ + t₂), c₁ + (-c₁ + c₂),
        temp₁ + (-temp₁ + temp₂), a₁ + (-a₁ + a₂),
        li₁ + (-li₁ + li₂)⟩ : Dimension) =
        ⟨l₂, m₂, t₂, c₂, temp₂, a₂, li₂⟩
      congr <;> omega

/- The natural-number scaling of exponents is named explicitly rather than
  relying on a hidden type-class instance.  This keeps generated quantity
  types readable in diagnostics (`dimensionScale 2 Energy`). -/
def dimensionScale : Nat → Dimension → Dimension
  | 0, _ => 0
  | n + 1, d => dimensionScale n d + d

@[simp] theorem dimensionScale_zero (d : Dimension) : dimensionScale 0 d = 0 := rfl

@[simp] theorem dimensionScale_succ (n : Nat) (d : Dimension) :
    dimensionScale (n + 1) d = dimensionScale n d + d := rfl

theorem dimensionScale_one (d : Dimension) : dimensionScale 1 d = d := by
  exact Dimension.zero_add d

@[simp] theorem add_length (x y : Dimension) : (x + y).length = x.length + y.length := rfl
@[simp] theorem add_mass (x y : Dimension) : (x + y).mass = x.mass + y.mass := rfl
@[simp] theorem add_time (x y : Dimension) : (x + y).time = x.time + y.time := rfl

theorem add_comm (x y : Dimension) : x + y = y + x := by
  obtain ⟨a, b, c, d, e, f, g⟩ := x
  obtain ⟨a', b', c', d', e', f', g'⟩ := y
  simp only [HAdd.hAdd, Add.add, Dimension.mk.injEq]
  exact ⟨Int.add_comm a a', Int.add_comm b b', Int.add_comm c c', Int.add_comm d d',
    Int.add_comm e e', Int.add_comm f f', Int.add_comm g g'⟩

theorem add_assoc (x y z : Dimension) : x + y + z = x + (y + z) := by
  obtain ⟨a, b, c, d, e, f, g⟩ := x
  obtain ⟨a', b', c', d', e', f', g'⟩ := y
  obtain ⟨a'', b'', c'', d'', e'', f'', g''⟩ := z
  simp only [HAdd.hAdd, Add.add, Dimension.mk.injEq]
  exact ⟨Int.add_assoc a a' a'', Int.add_assoc b b' b'', Int.add_assoc c c' c'',
    Int.add_assoc d d' d'', Int.add_assoc e e' e'', Int.add_assoc f f' f'',
    Int.add_assoc g g' g''⟩

theorem dimensionScale_add (m n : Nat) (d : Dimension) :
    dimensionScale (m + n) d = dimensionScale m d + dimensionScale n d := by
  induction m with
  | zero =>
      simpa only [Nat.zero_add, dimensionScale_zero] using
        (Dimension.zero_add (dimensionScale n d)).symm
  | succ m ih =>
      simp only [Nat.succ_add, dimensionScale_succ, ih]
      calc
        dimensionScale m d + dimensionScale n d + d =
            dimensionScale m d + (dimensionScale n d + d) :=
          Dimension.add_assoc _ _ _
        _ = dimensionScale m d + (d + dimensionScale n d) := by
          congr 1
          exact Dimension.add_comm _ _
        _ = (dimensionScale m d + d) + dimensionScale n d :=
          (Dimension.add_assoc _ _ _).symm

end Dimension

/-- A physical quantity with dimension `d`, whose value lives in `α`. -/
structure Quantity (d : Dimension) (α : Type) where
  /-- The numerical value, in whatever unit system the user has chosen. -/
  val : α

namespace Quantity

variable {d e : Dimension} {α β : Type}

/-- Dimension-respecting addition: only quantities of the *same* dimension can
be added. -/
instance [Add α] : Add (Quantity d α) where
  add x y := ⟨x.val + y.val⟩

instance [Neg α] : Neg (Quantity d α) where
  neg x := ⟨-x.val⟩

instance [Sub α] : Sub (Quantity d α) where
  sub x y := ⟨x.val - y.val⟩

instance [Zero α] : Zero (Quantity d α) where
  zero := ⟨0⟩

/- Multiplication by an ordinary coefficient leaves the physical dimension
   unchanged.  This is the operation used for amplitudes, coupling constants
   and numerical prefactors in essentially every domain adapter. -/
instance [SMul α α] : SMul α (Quantity d α) where
  smul c x := ⟨c • x.val⟩

/-! Quotients and powers are dimension checked at elaboration time.  Their
   result dimensions are part of the result type, so a missing inverse power
   cannot be repaired later by an unsound rewrite. -/

instance [Div α] : HDiv (Quantity d α) (Quantity e α) (Quantity (d - e) α) where
  hDiv x y := ⟨x.val / y.val⟩

/-- Change the coefficient type without changing the physical dimension. -/
def map (f : α → β) (x : Quantity d α) : Quantity d β := ⟨f x.val⟩

/-- Dimension-aware inverse.  It is a function rather than an `Inv` instance:
   Lean's `Inv` class has the same input and output type, while a physical
   inverse must change `d` to `-d`. -/
def inverse [Inv α] (x : Quantity d α) : Quantity (-d) α := ⟨x.val⁻¹⟩

/-- Dimension-aware natural power.  The exponent is explicit in the result
   type, so `Quantity.pow q n` cannot be confused with an untyped scalar
   power. -/
def pow [Pow α Nat] (x : Quantity d α) (n : Nat) :
    Quantity (Dimension.dimensionScale n d) α := ⟨x.val ^ n⟩

@[simp] theorem val_div [Div α] (x : Quantity d α) (y : Quantity e α) :
    (x / y).val = x.val / y.val := rfl

@[simp] theorem val_inverse [Inv α] (x : Quantity d α) :
    (inverse x).val = x.val⁻¹ := rfl

@[simp] theorem val_pow [Pow α Nat] (x : Quantity d α) (n : Nat) :
    (pow x n).val = x.val ^ n := rfl

@[simp] theorem map_val (f : α → β) (x : Quantity d α) : (map f x).val = f x.val := rfl

/-- Multiplication combines dimensions additively: `[L] * [T] = [L T]`. -/
instance [Mul α] : HMul (Quantity d α) (Quantity e α) (Quantity (d + e) α) where
  hMul x y := ⟨x.val * y.val⟩

@[simp] theorem val_add [Add α] (x y : Quantity d α) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_neg [Neg α] (x : Quantity d α) : (-x).val = -x.val := rfl
@[simp] theorem val_sub [Sub α] (x y : Quantity d α) : (x - y).val = x.val - y.val := rfl
@[simp] theorem val_zero [Zero α] : (0 : Quantity d α).val = 0 := rfl

@[simp] theorem val_smul [SMul α α] (c : α) (x : Quantity d α) :
    (c • x).val = c • x.val := rfl

/-- Multiplying two quantities multiplies their values and adds their
dimensions. -/
@[simp] theorem val_mul [Mul α] (x : Quantity d α) (y : Quantity e α) :
    (x * y).val = x.val * y.val := rfl

end Quantity

/-- A dimensionless scalar quantity. -/
abbrev Scalar (α : Type := ℂ) := Quantity Dimension.dimensionless α

/-- Length, as a type-level dimension tag. -/
abbrev Length := Quantity { length := 1 } ℂ

/-- Time, as a type-level dimension tag. -/
abbrev TimeQ := Quantity { time := 1 } ℂ

/-- Velocity, as a type-level dimension tag. -/
abbrev Velocity := Quantity { length := 1, time := -1 } ℂ

/-- Frequency, momentum and energy tags used by mechanics, field theory and
   condensed-matter interfaces.  They are aliases only: no numerical unit
   conversion or physical calibration is hidden in the type. -/
abbrev Frequency := Quantity { time := -1 } ℂ
abbrev Momentum := Quantity { length := 1, mass := 1, time := -1 } ℂ
abbrev Energy := Quantity { length := 2, mass := 1, time := -2 } ℂ
abbrev Action := Quantity { length := 2, mass := 1, time := -1 } ℂ
abbrev Charge := Quantity { current := 1, time := 1 } ℂ

/- Coefficient-polymorphic aliases for classical or numerical developments
   that use `ℝ`, `ℚ` or an abstract scalar type instead of the complex default
   used by the short physics names above. -/
abbrev LengthOf (α : Type) := Quantity { length := 1 } α
abbrev TimeOf (α : Type) := Quantity { time := 1 } α
abbrev FrequencyOf (α : Type) := Quantity { time := -1 } α
abbrev MomentumOf (α : Type) := Quantity { length := 1, mass := 1, time := -1 } α
abbrev EnergyOf (α : Type) := Quantity { length := 2, mass := 1, time := -2 } α
abbrev ActionOf (α : Type) := Quantity { length := 2, mass := 1, time := -1 } α
abbrev ChargeOf (α : Type) := Quantity { current := 1, time := 1 } α

/-! A few dimension-only identities are useful in proofs that mix the aliases
   above.  They are deliberately value-independent and therefore remain valid
   over any coefficient field once the aliases are specialised. -/

theorem energy_eq_momentum_mul_velocity (p : Momentum) (v : Velocity) :
    (p * v : Quantity ({ length := 2, mass := 1, time := -2 } : Dimension) ℂ).val =
      p.val * v.val := rfl

theorem action_eq_energy_mul_time (e : Energy) (t : TimeQ) :
    (e * t : Quantity ({ length := 2, mass := 1, time := -1 } : Dimension) ℂ).val =
      e.val * t.val := rfl

/-! The elaborator rejects adding unlike physical dimensions before proof search. -/
/-- error: failed to synthesize instance of type class
  HAdd Length TimeQ ?m.3

Hint: Type class instance resolution failures can be inspected with the
`set_option trace.Meta.synthInstance true` command. -/
#guard_msgs (error) in
example (x : Length) (y : TimeQ) : Length := x + y

end LeanPhy
