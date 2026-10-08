import LeanPhy.GaugeTheory.QuadraticGhost

/-!
# Odd derivations determined by finite ghost data

An even polynomial `F i` assigned to each generator determines the odd
derivation `D = ∑ i, F i ∂ᵢ`. Its square is an ordinary derivation, so it
vanishes on the entire exterior algebra exactly when `D (F i) = 0` for every
generator. These are finite, necessary-and-sufficient certificate obligations;
nilpotency is not assumed for arbitrary polynomials.

The construction works over any commutative ring, without division by two.
It records parity; integer degree and a matter action are separate data.
-/

namespace LeanPhy.GaugeTheory.GhostPolynomial

open LeanPhy.Mathematics

variable {R : Type*} [CommRing R] {n : Nat}

/-- Every parity-even ghost polynomial is central, including in characteristic two. -/
theorem even_mul_comm {a : GhostPolynomial R n}
    (ha : parityInvolution a = a) (x : GhostPolynomial R n) : a * x = x * a := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => exact (Algebra.commutes r a).symm
  | ι v => simpa only [ha] using (ι_mul_eq_parity_mul v a).symm
  | mul x y hx hy => rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]
  | add x y hx hy => simp only [mul_add, add_mul, hx, hy]

/-- Coordinate decomposition, used to extend finite checks to the whole algebra. -/
theorem ι_eq_sum_generators (v : Fin n → R) :
    ExteriorAlgebra.ι R v = ∑ i, v i • generator i := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, generator]

theorem generator_swap (i j : Fin n) :
    generator (R := R) i * generator j = -(generator j * generator i) :=
  eq_neg_of_add_eq_zero_left (generator_anticommute i j)

theorem triple_swap_first (i j k : Fin n) :
    generator (R := R) i * (generator j * generator k) =
      -(generator j * (generator i * generator k)) := by
  rw [← mul_assoc, generator_swap i j, neg_mul, mul_assoc]

theorem triple_swap_last (i j k : Fin n) :
    generator (R := R) i * (generator j * generator k) =
      -(generator i * (generator k * generator j)) := by
  rw [generator_swap j k, mul_neg]

@[simp] theorem triple_repeat_first (i k : Fin n) :
    generator (R := R) i * (generator i * generator k) = 0 := by
  rw [← mul_assoc, generator_sq, zero_mul]

@[simp] theorem triple_repeat_outer (i j : Fin n) :
    generator (R := R) i * (generator j * generator i) = 0 := by
  rw [triple_swap_first, generator_sq, mul_zero, neg_zero]

@[simp] theorem triple_repeat_last (i j : Fin n) :
    generator (R := R) i * (generator j * generator j) = 0 := by
  rw [generator_sq, mul_zero]

/-- Polynomial vector field in Grassmann coordinates. -/
noncomputable def vectorField (F : Fin n → GhostPolynomial R n) :
    GhostPolynomial R n →ₗ[R] GhostPolynomial R n where
  toFun x := ∑ i, F i * derivative i x
  map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by intro r x; simp [Finset.smul_sum]

@[simp] theorem vectorField_generator (F : Fin n → GhostPolynomial R n) (i : Fin n) :
    vectorField F (generator i) = F i := by
  simp [vectorField]

@[simp] theorem vectorField_scalar (F : Fin n → GhostPolynomial R n) (r : R) :
    vectorField F (algebraMap R _ r) = 0 := by
  simp [vectorField, derivative]

@[simp] theorem vectorField_one (F : Fin n → GhostPolynomial R n) :
    vectorField F 1 = 0 := by
  simpa using vectorField_scalar F 1

theorem vectorField_mul (F : Fin n → GhostPolynomial R n)
    (hF : ∀ i, parityInvolution (F i) = F i) (x y : GhostPolynomial R n) :
    vectorField F (x * y) = vectorField F x * y +
      parityInvolution x * vectorField F y := by
  simp only [vectorField, LinearMap.coe_mk, AddHom.coe_mk, derivative, contract_mul,
    mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro i _; exact (mul_assoc _ _ _).symm
  · apply Finset.sum_congr rfl; intro i _
    rw [← mul_assoc, even_mul_comm (hF i), mul_assoc]

theorem parity_vectorField (F : Fin n → GhostPolynomial R n)
    (hF : ∀ i, parityInvolution (F i) = F i) (x : GhostPolynomial R n) :
    parityInvolution (vectorField F x) = -vectorField F (parityInvolution x) := by
  simp [vectorField, map_sum, hF, derivative, parity_contract, Finset.sum_neg_distrib]

/-- The mixed terms cancel without any invertibility assumption on two. -/
theorem vectorField_sq_mul (F : Fin n → GhostPolynomial R n)
    (hF : ∀ i, parityInvolution (F i) = F i) (x y : GhostPolynomial R n) :
    vectorField F (vectorField F (x * y)) =
      vectorField F (vectorField F x) * y + x * vectorField F (vectorField F y) := by
  have hσ : vectorField F (parityInvolution x) = -parityInvolution (vectorField F x) := by
    rw [parity_vectorField F hF, neg_neg]
  rw [vectorField_mul F hF, map_add, vectorField_mul F hF, vectorField_mul F hF,
    hσ, parityInvolution_involutive]
  noncomm_ring

/-- Finite checks on the generator images imply nilpotency on every polynomial. -/
theorem vectorField_sq_of_generators (F : Fin n → GhostPolynomial R n)
    (hF : ∀ i, parityInvolution (F i) = F i) (hclosed : ∀ i, vectorField F (F i) = 0)
    (x : GhostPolynomial R n) : vectorField F (vectorField F x) = 0 := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => simp
  | ι v => simp [ι_eq_sum_generators, map_sum, hclosed]
  | mul x y hx hy => rw [vectorField_sq_mul F hF, hx, hy, zero_mul, mul_zero, add_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem vectorField_sq_iff (F : Fin n → GhostPolynomial R n)
    (hF : ∀ i, parityInvolution (F i) = F i) :
    (∀ x, vectorField F (vectorField F x) = 0) ↔ ∀ i, vectorField F (F i) = 0 := by
  constructor
  · intro h i; simpa using h (generator i)
  · exact fun h => vectorField_sq_of_generators F hF h

/-- A BRST parity differential certified by finitely many polynomial identities. -/
noncomputable def vectorFieldBRST (F : Fin n → GhostPolynomial R n)
    (hF : ∀ i, parityInvolution (F i) = F i) (hclosed : ∀ i, vectorField F (F i) = 0) :
    GradedBRSTDifferential (grading (R := R) (n := n)) where
  differential := vectorField F
  map_zero' := map_zero _
  map_add' := map_add _
  map_neg' := map_neg _
  maps_grade' := by
    intro p x hx
    cases p
    · change parityInvolution (vectorField F x) = -vectorField F x
      rw [parity_vectorField F hF, show parityInvolution x = x from hx]
    · change parityInvolution (vectorField F x) = vectorField F x
      rw [parity_vectorField F hF, show parityInvolution x = -x from hx, map_neg, neg_neg]
  leibniz' := by
    intro p q x y hx _
    rw [vectorField_mul F hF]
    cases p
    · change _ = vectorField F x * y + x * vectorField F y
      rw [show parityInvolution x = x from hx]
    · change _ = vectorField F x * y + -(x * vectorField F y)
      rw [show parityInvolution x = -x from hx, neg_mul]
  nilpotent := vectorField_sq_of_generators F hF hclosed

end LeanPhy.GaugeTheory.GhostPolynomial
