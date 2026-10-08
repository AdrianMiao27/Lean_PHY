import LeanPhy.GaugeTheory.LieGhostComplex

/-!
# A parameter-dependent Lie ghost family over arbitrary rings

The bracket `[e₀,e₁]=a e₁`, `[e₀,e₂]=b e₂` is valid for all parameters.
Jacobi gives a canonical ghost differential without parameter-specific
nilpotency certificates. The ghost pair `c¹c²` is closed exactly on `a+b=0`.
This is a closedness criterion, not a nonzero cohomology-class assertion.
-/

namespace LeanPhy.GaugeTheory.LieGhostFamily

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology GhostPolynomial

variable {R : Type*} [CommRing R]

abbrev Space (R : Type*) := Fin 3 → R
abbrev Ghosts (R : Type*) [CommRing R] := GhostPolynomial R 3

def bracket (a b : R) (x y : Space R) : Space R :=
  ![0, a * (x 0 * y 1 - x 1 * y 0), b * (x 0 * y 2 - x 2 * y 0)]

def algebra (a b : R) : LieAlgebra R (Space R) where
  bracket := bracket a b
  add_left := by intros; ext i; fin_cases i <;> simp [bracket] <;> ring
  add_right := by intros; ext i; fin_cases i <;> simp [bracket] <;> ring
  smul_left := by intros; ext i; fin_cases i <;> simp [bracket] <;> ring
  smul_right := by intros; ext i; fin_cases i <;> simp [bracket] <;> ring
  zero_left := by intros; ext i; fin_cases i <;> simp [bracket]
  alternating := by intros; ext i; fin_cases i <;> dsimp [bracket] <;> ring
  antisymm := by intros; ext i; fin_cases i <;> simp [bracket] <;> ring
  jacobi := by intros; ext i; fin_cases i <;> simp [bracket] <;> ring

noncomputable def differential (a b : R) := canonicalLieBRST (algebra a b)

@[simp] theorem image_zero (a b : R) :
    differential a b (generator 0) = 0 := by
  change lieDifferential (algebra a b) (generator 0) = 0
  simp [lieImages_formula, algebra, bracket, Pi.single_apply]

@[simp] theorem image_one (a b : R) :
    differential a b (generator 1) = -a • (generator 0 * generator 1) := by
  change lieDifferential (algebra a b) (generator 1) = _
  simp [lieImages_formula, algebra, bracket, Fin.sum_univ_succ, Pi.single_apply]

@[simp] theorem image_two (a b : R) :
    differential a b (generator 2) = -b • (generator 0 * generator 2) := by
  change lieDifferential (algebra a b) (generator 2) = _
  simp [lieImages_formula, algebra, bracket, Fin.sum_univ_succ, Pi.single_apply]

theorem nilpotent (a b : R) (x : Ghosts R) :
    differential a b (differential a b x) = 0 := (differential a b).nilpotent_apply x

theorem pair_differential (a b : R) :
    differential a b (generator 1 * generator 2) =
      -(a + b) • (generator 0 * (generator 1 * generator 2)) := by
  change lieDifferential (algebra a b) (generator 1 * generator 2) = _
  rw [lieDifferential_mul]
  change differential a b (generator 1) * generator 2 +
    parityInvolution (generator 1) * differential a b (generator 2) = _
  rw [image_one, image_two,
    show parityInvolution (generator (R := R) (1 : Fin 3)) = -generator 1 from generator_isOdd 1]
  simp only [smul_mul_assoc, mul_smul_comm, mul_assoc, neg_mul, mul_neg,
    triple_swap_first (R := R) (1 : Fin 3) 0 2, neg_neg, neg_smul,
    add_smul, neg_add]

/-- Ordered triple contraction detects coefficients even over rings with zero divisors. -/
theorem triple_coefficient (r : R) :
    ExteriorAlgebra.algebraMapInv
      (derivative 2 (derivative 1 (derivative 0
        (r • (generator (R := R) (0 : Fin 3) * (generator 1 * generator 2)))))) = r := by
  simp [derivative, contract_mul, generator]

/-- The complete closedness locus retains all parameter degenerations. -/
theorem pair_closed_iff (a b : R) :
    differential a b (generator 1 * generator 2) = 0 ↔ a + b = 0 := by
  rw [pair_differential]
  constructor
  · intro h
    have hc := congrArg (fun x : Ghosts R => ExteriorAlgebra.algebraMapInv
      (derivative 2 (derivative 1 (derivative 0 x)))) h
    simpa only [triple_coefficient, map_zero, neg_eq_zero] using hc
  · intro h; simp [h]

end LeanPhy.GaugeTheory.LieGhostFamily
