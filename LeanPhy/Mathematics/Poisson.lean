import LeanPhy.Mathematics.Derivation
import Mathlib.Tactic

/-!
# A reusable Poisson-algebra interface

Classical mechanics, kinetic theory, statistical mechanics and the classical
limit of quantum models all use the same algebraic pattern: observables form a
commutative algebra and the Poisson bracket is bilinear, antisymmetric,
Jacobi, and a derivation in each argument.  This file records that pattern as
an explicit interface.  It is intentionally independent of coordinates,
smoothness, integration and Hamiltonian ODE existence.

The existing finite-dimensional `AffineObservable` example remains a concrete
coordinate model.  This interface is its future adapter target, as well as the
target for polynomial, lattice and field-observable models whose extra
regularity assumptions can be stated separately.
-/

namespace LeanPhy.Mathematics

universe u v

/-- A Poisson algebra over a commutative scalar ring.

All laws that a downstream physics model relies on are fields.  Consequently
an implementation can use a kernel-checked concrete bracket or expose a
named physical assumption without changing the generic conservation rules.
-/
structure PoissonAlgebra (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A] where
  bracket : A → A → A
  add_left : ∀ x y z, bracket (x + y) z = bracket x z + bracket y z
  add_right : ∀ x y z, bracket x (y + z) = bracket x y + bracket x z
  smul_left : ∀ (r : R) x y, bracket (r • x) y = r • bracket x y
  smul_right : ∀ (r : R) x y, bracket x (r • y) = r • bracket x y
  zero_left : ∀ x, bracket 0 x = 0
  alternating : ∀ x, bracket x x = 0
  antisymm : ∀ x y, bracket x y = -bracket y x
  jacobi : ∀ x y z,
    bracket x (bracket y z) + bracket y (bracket z x) + bracket z (bracket x y) = 0
  leibniz : ∀ x y z,
    bracket x (y * z) = bracket x y * z + y * bracket x z

namespace PoissonAlgebra

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]
variable (P : PoissonAlgebra R A)

instance : CoeFun (PoissonAlgebra R A) (fun _ => A → A → A) :=
  ⟨PoissonAlgebra.bracket⟩

@[simp] theorem bracket_zero_left (x : A) : P 0 x = 0 := P.zero_left x

@[simp] theorem bracket_zero_right (x : A) : P x 0 = 0 := by
  rw [P.antisymm, P.zero_left]
  simp

@[simp] theorem bracket_self (x : A) : P x x = 0 := P.alternating x

theorem bracket_neg_left (x y : A) : P (-x) y = -P x y := by
  have h := P.add_left (-x) x y
  have hz : P (-x) y + P x y = 0 := by simpa using h.symm
  exact eq_neg_of_add_eq_zero_left hz

theorem bracket_neg_right (x y : A) : P x (-y) = -P x y := by
  have h := P.add_right x (-y) y
  have hz : P x (-y) + P x y = 0 := by simpa using h.symm
  exact eq_neg_of_add_eq_zero_left hz

theorem bracket_mul_right (x y z : A) :
    P x (y * z) = P x y * z + y * P x z := P.leibniz x y z

theorem bracket_mul_left (x y z : A) :
    P (x * y) z = x * P y z + P x z * y := by
  calc
    P (x * y) z = -P z (x * y) := P.antisymm (x * y) z
    _ = -(P z x * y + x * P z y) := by rw [P.leibniz]
    _ = x * P y z + P x z * y := by
      rw [P.antisymm z x, P.antisymm z y]
      ring

/-- A Hamiltonian observable is conserved when its Poisson bracket with the
Hamiltonian vanishes.  This is the algebraic part of a Heisenberg/Hamilton
equation; no time parameter is introduced here. -/
def Conserved (H O : A) : Prop := P H O = 0

@[simp] theorem conserved_zero (H : A) : Conserved P H 0 := by
  simp [Conserved]

@[simp] theorem conserved_one (H : A) : Conserved P H 1 := by
  unfold Conserved
  have h := P.leibniz H 1 1
  have hx : P H 1 + P H 1 = P H 1 + 0 := by
    simpa using h.symm
  exact add_left_cancel hx

theorem conserved_add (H O Q : A)
    (hO : Conserved P H O) (hQ : Conserved P H Q) :
    Conserved P H (O + Q) := by
  unfold Conserved at hO hQ ⊢
  rw [P.add_right, hO, hQ, add_zero]

theorem conserved_smul (H O : A) (r : R) (hO : Conserved P H O) :
    Conserved P H (r • O) := by
  unfold Conserved at hO ⊢
  rw [P.smul_right, hO, smul_zero]

theorem conserved_mul (H O Q : A)
    (hO : Conserved P H O) (hQ : Conserved P H Q) :
    Conserved P H (O * Q) := by
  unfold Conserved at hO hQ ⊢
  rw [P.leibniz, hO, hQ, zero_mul, mul_zero, add_zero]

theorem conserved_pow (H O : A) (n : Nat) (hO : Conserved P H O) :
    Conserved P H (O ^ n) := by
  induction n with
  | zero =>
      rw [pow_zero]
      exact conserved_one P H
  | succ n ih =>
      rw [pow_succ]
      exact conserved_mul P H (O ^ n) O ih hO

theorem conserved_linear_combination (H a b O Q : A)
    (ha : Conserved P H a) (hb : Conserved P H b)
    (hO : Conserved P H O) (hQ : Conserved P H Q) :
    Conserved P H (a * O + b * Q) := by
  exact conserved_add P H (a * O) (b * Q)
    (conserved_mul P H a O ha hO) (conserved_mul P H b Q hb hQ)

/-- Hamiltonian evolution is a derivation of the observable product. -/
theorem hamiltonian_leibniz (H O Q : A) :
    P H (O * Q) = P H O * Q + O * P H Q :=
  P.leibniz H O Q

/-- The Hamiltonian action `{H, ·}` is a genuine mathlib derivation.

This is the bridge from an algebraic Poisson model to the common differential
operator layer used by gauge theory and continuum mechanics.  It does not
claim that this derivation integrates to a time flow; that requires separate
analytic hypotheses.
-/
def hamiltonianLinearMap (H : A) : A →ₗ[R] A where
  toFun := P H
  map_add' := by intro x y; exact P.add_right H x y
  map_smul' := by intro r x; exact P.smul_right r H x

def hamiltonianDerivation (H : A) : PhysicsDerivation R A :=
  Derivation.mk' (hamiltonianLinearMap P H) (by
    intro x y
    change P H (x * y) = x * P H y + y * P H x
    simpa [mul_comm, add_comm] using P.leibniz H x y)

@[simp] theorem hamiltonianDerivation_apply (H x : A) :
    hamiltonianDerivation P H x = P H x := rfl

theorem hamiltonianDerivation_product (H x y : A) :
    hamiltonianDerivation P H (x * y) =
      x * hamiltonianDerivation P H y + y * hamiltonianDerivation P H x := by
  simpa [hamiltonianDerivation_apply, smul_eq_mul, mul_comm, add_comm] using
    P.leibniz H x y

/-! The Hamiltonian derivations themselves form a Lie representation of the
Poisson algebra. -/

theorem hamiltonianDerivation_commutator (H K : A) :
    derivationCommutator (hamiltonianDerivation P H)
        (hamiltonianDerivation P K) =
      hamiltonianDerivation P (P H K) := by
  ext f
  simp only [derivationCommutator_apply, hamiltonianDerivation_apply]
  have hJ := P.jacobi H K f
  rw [P.antisymm f H, P.antisymm f (P H K)] at hJ
  rw [bracket_neg_right P] at hJ
  linear_combination hJ

/-! ### Canonical brackets from commuting derivations -/

/-- The two-derivation bracket used by canonical coordinates:
`{f,g} = D_q f D_p g - D_p f D_q g`.
-/
def derivationBracket (Dq Dp : PhysicsDerivation R A) (f g : A) : A :=
  Dq f * Dp g - Dp f * Dq g

theorem derivationBracket_add_left (Dq Dp : PhysicsDerivation R A) (x y z : A) :
    derivationBracket Dq Dp (x + y) z =
      derivationBracket Dq Dp x z + derivationBracket Dq Dp y z := by
  simp [derivationBracket, map_add]
  ring

theorem derivationBracket_add_right (Dq Dp : PhysicsDerivation R A) (x y z : A) :
    derivationBracket Dq Dp x (y + z) =
      derivationBracket Dq Dp x y + derivationBracket Dq Dp x z := by
  simp [derivationBracket, map_add]
  ring

theorem derivationBracket_smul_left (Dq Dp : PhysicsDerivation R A)
    (r : R) (x y : A) :
    derivationBracket Dq Dp (r • x) y =
      r • derivationBracket Dq Dp x y := by
  simp [derivationBracket, Algebra.smul_def]
  ring

theorem derivationBracket_smul_right (Dq Dp : PhysicsDerivation R A)
    (r : R) (x y : A) :
    derivationBracket Dq Dp x (r • y) =
      r • derivationBracket Dq Dp x y := by
  simp [derivationBracket, Algebra.smul_def]
  ring

theorem derivationBracket_zero_left (Dq Dp : PhysicsDerivation R A) (x : A) :
    derivationBracket Dq Dp 0 x = 0 := by
  simp [derivationBracket]

theorem derivationBracket_alternating (Dq Dp : PhysicsDerivation R A) (x : A) :
    derivationBracket Dq Dp x x = 0 := by
  simp only [derivationBracket]
  ring

theorem derivationBracket_antisymm (Dq Dp : PhysicsDerivation R A) (x y : A) :
    derivationBracket Dq Dp x y = -derivationBracket Dq Dp y x := by
  simp [derivationBracket]
  ring

theorem derivationBracket_leibniz (Dq Dp : PhysicsDerivation R A) (x y z : A) :
    derivationBracket Dq Dp x (y * z) =
      derivationBracket Dq Dp x y * z + y * derivationBracket Dq Dp x z := by
  simp only [derivationBracket, Derivation.leibniz, smul_eq_mul, sub_mul, mul_sub]
  ring

theorem derivation_commute_apply (D E : PhysicsDerivation R A) (f : A)
    (h : ⁅D, E⁆ = 0) : D (E f) = E (D f) := by
  have h' := congrArg (fun X : PhysicsDerivation R A => X f) h
  exact sub_eq_zero.mp (by simpa [Derivation.commutator_apply] using h')

theorem derivationBracket_jacobi (Dq Dp : PhysicsDerivation R A)
    (hcomm : ⁅Dq, Dp⁆ = 0) (x y z : A) :
    derivationBracket Dq Dp x (derivationBracket Dq Dp y z) +
        derivationBracket Dq Dp y (derivationBracket Dq Dp z x) +
        derivationBracket Dq Dp z (derivationBracket Dq Dp x y) = 0 := by
  have hxy := derivation_commute_apply Dq Dp x hcomm
  have hyz := derivation_commute_apply Dq Dp y hcomm
  have hzx := derivation_commute_apply Dq Dp z hcomm
  unfold derivationBracket
  simp only [map_sub, Derivation.leibniz, smul_eq_mul, sub_mul, mul_sub]
  rw [hxy, hyz, hzx]
  ring

/-- Build a Poisson algebra from two commuting derivations of a commutative
algebra.  This is the reusable construction behind canonical phase-space
brackets and polynomial field observables.
-/
def derivationPoissonAlgebra (Dq Dp : PhysicsDerivation R A)
    (hcomm : ⁅Dq, Dp⁆ = 0) : PoissonAlgebra R A where
  bracket := derivationBracket Dq Dp
  add_left := derivationBracket_add_left Dq Dp
  add_right := derivationBracket_add_right Dq Dp
  smul_left := derivationBracket_smul_left Dq Dp
  smul_right := derivationBracket_smul_right Dq Dp
  zero_left := derivationBracket_zero_left Dq Dp
  alternating := derivationBracket_alternating Dq Dp
  antisymm := derivationBracket_antisymm Dq Dp
  jacobi := derivationBracket_jacobi Dq Dp hcomm
  leibniz := derivationBracket_leibniz Dq Dp

/-- The bracket of two conserved observables is conserved.  This is the
Jacobi-identity form of closure under symmetry generators. -/
theorem conserved_bracket (H O Q : A)
    (hO : Conserved P H O) (hQ : Conserved P H Q) :
    Conserved P H (P O Q) := by
  unfold Conserved at hO hQ ⊢
  have hJ := P.jacobi H O Q
  have hQH : P Q H = 0 := by
    rw [P.antisymm, hQ, neg_zero]
  rw [hQH, hO, P.bracket_zero_right, P.bracket_zero_right] at hJ
  simpa using hJ

end PoissonAlgebra

end LeanPhy.Mathematics
