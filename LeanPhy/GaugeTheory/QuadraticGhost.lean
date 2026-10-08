import LeanPhy.GaugeTheory.GhostKoszul

/-!
# A nontrivial quadratic ghost differential

For distinct generators `i,j`, `quadratic i j` acts by `cᵢ cⱼ ∂ⱼ`.
It sends `cⱼ` to `cᵢ cⱼ`, kills the other generators, obeys the odd Leibniz
rule and squares to zero on every polynomial. In two generators this is the
ghost-sector formula for the affine Lie algebra with `[eᵢ,eⱼ] = -eⱼ` and
the CE convention `d c(x,y) = -c([x,y])`.

The polynomial identities are proved here. `LieGhost` supplies general finite
Lie generator images and a degree-one CE bridge; `LieGhostComplex` adds the
degree-two bridge and canonical nilpotency from Jacobi. A full chain equivalence,
a matter representation, a full BRST/BV complex, gauge fixing and a physical
interpretation of cohomology are separate obligations.
-/

namespace LeanPhy.GaugeTheory.GhostPolynomial

open LeanPhy.Mathematics

variable {R : Type*} [CommRing R] {n : Nat}

theorem generator_mul_eq_parity_mul (i : Fin n) (x : GhostPolynomial R n) :
    generator i * x = parityInvolution x * generator i :=
  ι_mul_eq_parity_mul _ _

/-- A product of two ghosts commutes with every polynomial. -/
theorem pair_mul_comm (i j : Fin n) (x : GhostPolynomial R n) :
    (generator i * generator j) * x = x * (generator (R := R) i * generator j) := by
  rw [mul_assoc, generator_mul_eq_parity_mul j x, ← mul_assoc,
    generator_mul_eq_parity_mul i (parityInvolution x), parityInvolution_involutive,
    mul_assoc]

theorem pair_mul_left_generator (i j : Fin n) :
    (generator i * generator j) * generator (R := R) i = 0 := by
  rw [pair_mul_comm, ← mul_assoc, generator_sq, zero_mul]

/-- A quadratic ghost differential with a specified differentiated generator. -/
noncomputable def quadratic (i j : Fin n) (x : GhostPolynomial R n) :
    GhostPolynomial R n := (generator i * generator j) * derivative j x

@[simp] theorem quadratic_generator (i j k : Fin n) :
    quadratic (R := R) i j (generator k) =
      if j = k then generator i * generator j else 0 := by
  simp [quadratic]

theorem quadratic_mul (i j : Fin n) (x y : GhostPolynomial R n) :
    quadratic i j (x * y) = quadratic i j x * y +
      parityInvolution x * quadratic i j y := by
  unfold quadratic derivative
  rw [contract_mul, mul_add]
  congr 1
  · exact (mul_assoc _ _ _).symm
  · rw [← mul_assoc, pair_mul_comm, mul_assoc]

@[simp] theorem derivative_pair (i j : Fin n) (hij : i ≠ j) :
    derivative j (generator (R := R) i * generator j) = -generator i := by
  rw [derivative, contract_mul]
  change derivative j (generator (R := R) i) * generator j +
    parityInvolution (generator i) * derivative j (generator j) = _
  simp [derivative_generator, Ne.symm hij, show parityInvolution (generator (R := R) i) =
    -generator i from generator_isOdd i]

theorem quadratic_sq (i j : Fin n) (hij : i ≠ j) (x : GhostPolynomial R n) :
    quadratic i j (quadratic (R := R) i j x) = 0 := by
  unfold quadratic
  rw [show derivative j ((generator i * generator j) * derivative j x) =
    derivative j (generator i * generator j) * derivative j x +
      parityInvolution (generator i * generator j) * derivative j (derivative j x) from
        contract_mul _ _ _]
  rw [derivative_pair i j hij, derivative_sq, mul_zero, add_zero, ← mul_assoc,
    mul_neg, pair_mul_left_generator, neg_zero, zero_mul]

/-- A nontrivial, square-zero odd derivation on any finite ghost algebra. -/
noncomputable def quadraticBRST (i j : Fin n) (hij : i ≠ j) :
    GradedBRSTDifferential (grading (R := R) (n := n)) where
  differential := quadratic i j
  map_zero' := by simp [quadratic]
  map_add' := by intro x y; simp [quadratic, mul_add]
  map_neg' := by intro x; simp [quadratic]
  maps_grade' := by
    intro p x hx
    have hp : parityInvolution (generator (R := R) i * generator j) =
        generator i * generator j := by
      rw [map_mul, show parityInvolution (generator (R := R) i) = -generator i from
        generator_isOdd i, show parityInvolution (generator (R := R) j) =
        -generator j from generator_isOdd j, neg_mul_neg]
    cases p
    · change parityInvolution (quadratic i j x) = -quadratic i j x
      simp only [quadratic, map_mul, hp, derivative, parity_contract,
        show parityInvolution x = x from hx, mul_neg]
    · change parityInvolution (quadratic i j x) = quadratic i j x
      simp only [quadratic, map_mul, hp, derivative, parity_contract,
        show parityInvolution x = -x from hx, map_neg, neg_neg]
  leibniz' := by
    intro p q x y hx _
    rw [quadratic_mul]
    cases p
    · change _ = quadratic i j x * y + x * quadratic i j y
      rw [show parityInvolution x = x from hx]
    · change _ = quadratic i j x * y + -(x * quadratic i j y)
      rw [show parityInvolution x = -x from hx, neg_mul]
  nilpotent := quadratic_sq i j hij

/-- Distinct ghost generators have a nonzero wedge product over a nonzero ring. -/
theorem pair_ne_zero [Nontrivial R] (i j : Fin n) (hij : i ≠ j) :
    generator (R := R) i * generator j ≠ 0 := by
  intro h
  have hd := congrArg (fun x => derivative i (derivative j x)) h
  rw [derivative_pair i j hij, map_neg, derivative_generator, ite_eq_left rfl,
    map_zero, map_zero] at hd
  exact one_ne_zero (neg_eq_zero.mp hd)

/-- Nontriviality is checked independently of the nilpotency proof. -/
theorem quadratic_nonzero [Nontrivial R] (i j : Fin n) (hij : i ≠ j) :
    quadratic (R := R) i j (generator j) ≠ 0 := by
  simpa using pair_ne_zero (R := R) i j hij

end LeanPhy.GaugeTheory.GhostPolynomial
