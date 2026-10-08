import LeanPhy.Mathematics.GradedBRST
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-!
# Finite Grassmann ghost polynomials

`GhostPolynomial R n` is mathlib's exterior algebra on `n` generators, with
square-zero generators and their anticommutation relations. Parity is expressed
by the eigenspaces of the sign involution; these need not be disjoint over a
ring with 2-torsion. The separate `GhostDegree` module supplies actual integer
ghost degrees and a finite homogeneous decomposition from exterior powers.

The inner graded commutator is retained as an algebraic constructor, but
`innerDifferential_eq_zero` proves that it vanishes on this pure exterior
algebra. Nontrivial differentiation is supplied separately by `GhostKoszul`;
nilpotency of an inner commutator alone is not evidence of a gauge BRST model.
-/

namespace LeanPhy.GaugeTheory

open LeanPhy.Mathematics

universe u v

abbrev GhostPolynomial (R : Type u) (n : Nat) [CommRing R] :=
  ExteriorAlgebra R (Fin n → R)

namespace GhostPolynomial

variable {R : Type u} [CommRing R] {n : Nat}

/-- The parity involution sends every ghost generator to its negative. -/
noncomputable def parityInvolution : GhostPolynomial R n →ₐ[R] GhostPolynomial R n :=
  ExteriorAlgebra.lift R ⟨-(ExteriorAlgebra.ι R), by
    intro m
    simp [neg_mul_neg, ExteriorAlgebra.ι_sq_zero]
  ⟩

@[simp] theorem parityInvolution_ι (m : Fin n → R) :
    parityInvolution (ExteriorAlgebra.ι R m) = -ExteriorAlgebra.ι R m := by
  simp [parityInvolution]

@[simp] theorem parityInvolution_zero :
    parityInvolution (0 : GhostPolynomial R n) = 0 := by simp [parityInvolution]

@[simp] theorem parityInvolution_one :
    parityInvolution (1 : GhostPolynomial R n) = 1 := by simp [parityInvolution]

@[simp] theorem parityInvolution_involutive (x : GhostPolynomial R n) :
    parityInvolution (parityInvolution x) = x := by
  refine ExteriorAlgebra.induction (C := fun x => parityInvolution (parityInvolution x) = x)
    ?_ ?_ ?_ ?_ x
  · intro r
    simp
  · intro m
    simp
  · intro a b ha hb
    simp only [map_mul, ha, hb]
  · intro a b ha hb
    simp only [map_add, ha, hb]

/-- Even and odd polynomial subspaces, defined by the parity involution. -/
def homogeneous (p : Parity) : Set (GhostPolynomial R n) :=
  match p with
  | .even => {x | parityInvolution x = x}
  | .odd => {x | parityInvolution x = -x}

@[simp] theorem even_mem (x : GhostPolynomial R n)
    (hx : x ∈ homogeneous (R := R) (n := n) .even) :
    parityInvolution x = x := hx

@[simp] theorem odd_mem (x : GhostPolynomial R n)
    (hx : x ∈ homogeneous (R := R) (n := n) .odd) :
    parityInvolution x = -x := hx

noncomputable def grading : GradedRing Parity (GhostPolynomial R n) where
  homogeneous := homogeneous
  zero_mem := by
    intro p
    cases p <;> simp [homogeneous]
  add_mem := by
    intro p x y hx hy
    cases p
    · change parityInvolution (x + y) = x + y
      rw [map_add, hx, hy]
    · change parityInvolution (x + y) = -(x + y)
      rw [map_add, hx, hy, neg_add]
  neg_mem := by
    intro p x hx
    cases p
    · change parityInvolution (-x) = -x
      rw [map_neg, hx]
    · change parityInvolution (-x) = -(-x)
      rw [map_neg, hx, neg_neg]
  one_mem := by
    change parityInvolution (1 : GhostPolynomial R n) = 1
    simp
  mul_mem := by
    intro p q x y hx hy
    cases p <;> cases q
    · change parityInvolution x = x at hx
      change parityInvolution y = y at hy
      change parityInvolution (x * y) = x * y
      rw [map_mul, hx, hy]
    · change parityInvolution x = x at hx
      change parityInvolution y = -y at hy
      change parityInvolution (x * y) = -(x * y)
      rw [map_mul, hx, hy]
      simp
    · change parityInvolution x = -x at hx
      change parityInvolution y = y at hy
      change parityInvolution (x * y) = -(x * y)
      rw [map_mul, hx, hy]
      simp
    · change parityInvolution x = -x at hx
      change parityInvolution y = -y at hy
      change parityInvolution (x * y) = x * y
      rw [map_mul, hx, hy]
      simp
  parity := id
  parity_add := by intro p q; rfl
  differential_degree := .odd
  differential_is_odd := rfl

/-- The `i`th Grassmann generator. -/
noncomputable def generator (i : Fin n) : GhostPolynomial R n :=
  ExteriorAlgebra.ι R (Pi.single i 1)

@[simp] theorem generator_sq (i : Fin n) :
    generator (R := R) i * generator i = 0 := by
  exact ExteriorAlgebra.ι_sq_zero _

theorem generator_anticommute (i j : Fin n) :
    generator (R := R) i * generator j + generator j * generator i = 0 := by
  exact ExteriorAlgebra.ι_add_mul_swap _ _

@[simp] theorem generator_isOdd (i : Fin n) :
    generator (R := R) i ∈ homogeneous (R := R) (n := n) .odd := by
  change parityInvolution (generator (R := R) i) = -generator i
  simp [generator]

/-- Moving a generator through any polynomial applies the parity involution. -/
theorem ι_mul_eq_parity_mul (v : Fin n → R) (x : GhostPolynomial R n) :
    ExteriorAlgebra.ι R v * x = parityInvolution x * ExteriorAlgebra.ι R v := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, Algebra.commutes]
  | ι w =>
      rw [parityInvolution_ι, neg_mul]
      exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v w)
  | mul x y hx hy => rw [map_mul, ← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]
  | add x y hx hy => simp only [map_add, mul_add, add_mul, hx, hy]

/-- An odd element supercommutes with every element of the pure ghost algebra. -/
theorem odd_mul_eq_parity_mul {Q : GhostPolynomial R n}
    (hQ : Q ∈ homogeneous (R := R) (n := n) .odd) (x : GhostPolynomial R n) :
    Q * x = parityInvolution x * Q := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, Algebra.commutes]
  | ι v =>
      have h := ι_mul_eq_parity_mul v Q
      rw [show parityInvolution Q = -Q from hQ, neg_mul] at h
      rw [parityInvolution_ι, neg_mul, h, neg_neg]
  | mul x y hx hy => rw [map_mul, ← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]
  | add x y hx hy => simp only [map_add, mul_add, add_mul, hx, hy]

/-- An inner odd differential generated by a nilpotent odd charge `Q`.

The differential is the graded commutator `Q x - σ(x) Q`, where `σ` is the
parity involution. On this pure exterior algebra it is identically zero;
see `innerDifferential_eq_zero`. It does not define a nontrivial gauge action.
-/
noncomputable def innerDifferential (Q : GhostPolynomial R n)
    (hQ : Q ∈ homogeneous (R := R) (n := n) .odd)
    (hQsq : Q * Q = 0) : GradedBRSTDifferential (grading (R := R) (n := n)) := by
  let σ := parityInvolution (R := R) (n := n)
  let d : GhostPolynomial R n → GhostPolynomial R n := fun x => Q * x - σ x * Q
  refine {
    differential := d
    map_zero' := by simp [d, σ]
    map_add' := by
      intro x y
      simp [d, σ, sub_eq_add_neg, mul_add, map_add, add_mul, add_assoc, add_left_comm,
        add_comm]
    map_neg' := by
      intro x
      simp [d, σ, sub_eq_add_neg, map_neg, neg_mul, mul_neg, add_comm]
    maps_grade' := ?_
    leibniz' := ?_
    nilpotent := by
      intro x
      have hσQ : σ Q = -Q := hQ
      have hσσ : σ (σ x) = x := parityInvolution_involutive x
      calc
        d (d x) = (Q * Q) * x - x * (Q * Q) := by
          simp only [d, map_sub, map_add, map_neg, map_mul, map_smul, hσQ, hσσ,
            add_mul, mul_add, neg_mul, mul_neg, neg_neg]
          noncomm_ring
        _ = 0 := by rw [hQsq]; simp
  }
  · intro p x hx
    cases p with
    | even =>
        have hσQ : σ Q = -Q := hQ
        have hσx : σ x = x := hx
        change σ (d x) = -d x
        simp [d, σ, map_sub, map_mul, map_smul, hσQ, hσx, neg_mul, mul_neg,
          neg_neg, smul_eq_mul]
        noncomm_ring
    | odd =>
        have hσQ : σ Q = -Q := hQ
        have hσx : σ x = -x := hx
        change σ (d x) = d x
        simp [d, σ, map_sub, map_mul, map_smul, hσQ, hσx, neg_mul, mul_neg,
          neg_neg, smul_eq_mul]
  · intro p q x y hx hy
    have hσQ : σ Q = -Q := hQ
    cases p with
    | even =>
        have hσx : σ x = x := hx
        cases q with
        | even =>
            have hσy : σ y = y := hy
            simp [d, σ, map_sub, map_mul, map_smul, hσQ, hσx, hσy,
              sub_eq_add_neg, add_mul, mul_add, one_mul, neg_mul, mul_neg,
              neg_neg, grading, Parity.sign, smul_eq_mul]
            noncomm_ring
        | odd =>
            have hσy : σ y = -y := hy
            simp [d, σ, map_sub, map_mul, map_smul, hσQ, hσx, hσy,
              sub_eq_add_neg, add_mul, mul_add, one_mul, neg_mul, mul_neg,
              neg_neg, grading, Parity.sign, smul_eq_mul]
            noncomm_ring
    | odd =>
        have hσx : σ x = -x := hx
        cases q with
        | even =>
            have hσy : σ y = y := hy
            simp [d, σ, map_sub, map_mul, map_smul, hσQ, hσx, hσy,
              sub_eq_add_neg, add_mul, mul_add, one_mul, neg_mul, mul_neg,
              neg_neg, grading, Parity.sign, smul_eq_mul]
            noncomm_ring
        | odd =>
            have hσy : σ y = -y := hy
            simp [d, σ, map_sub, map_mul, map_smul, hσQ, hσx, hσy,
              sub_eq_add_neg, add_mul, mul_add, one_mul, neg_mul, mul_neg,
              neg_neg, grading, Parity.sign, smul_eq_mul]
            noncomm_ring

/-- Inner graded commutators on the pure Grassmann algebra are degenerate. -/
theorem innerDifferential_eq_zero (Q : GhostPolynomial R n)
    (hQ : Q ∈ homogeneous (R := R) (n := n) .odd) (hQsq : Q * Q = 0)
    (x : GhostPolynomial R n) : innerDifferential Q hQ hQsq x = 0 := by
  change Q * x - parityInvolution x * Q = 0
  exact sub_eq_zero.mpr (odd_mul_eq_parity_mul hQ x)

end GhostPolynomial

end LeanPhy.GaugeTheory
