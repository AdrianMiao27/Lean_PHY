import LeanPhy.GaugeTheory.FiniteGhostPolynomial
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Grassmann differentiation and finite Koszul complexes

Left contraction on the exterior algebra gives a nontrivial odd differential.
For a supplied linear functional `f`, it sends a generator `ι v` to the scalar
`f v`. The signed product rule, nilpotency, and contraction homotopy are proved
for arbitrary ghost polynomials. Coordinate contractions implement Grassmann
left derivatives and satisfy the CAR identities with generator multiplication.

This is the algebraic Koszul differential (integer degree -1), recorded through
the parity-only `GradedBRSTDifferential` interface. It is not the degree +1
Chevalley--Eilenberg differential of a gauge Lie algebra. Exactness requires the
explicit unit-pairing witness; no physical cohomology interpretation is inferred.
-/

namespace LeanPhy.GaugeTheory.GhostPolynomial

open LeanPhy.Mathematics

variable {R : Type*} [CommRing R] {n : Nat}

/-- Contraction with a supplied covector, extended to all ghost polynomials. -/
noncomputable def contract (f : Module.Dual R (Fin n → R)) :
    GhostPolynomial R n →ₗ[R] GhostPolynomial R n :=
  CliffordAlgebra.contractLeft (Q := 0) f

@[simp] theorem contract_zero_covector (x : GhostPolynomial R n) :
    contract (0 : Module.Dual R (Fin n → R)) x = 0 := by
  simp [contract]

@[simp] theorem contract_scalar (f : Module.Dual R (Fin n → R)) (r : R) :
    contract f (algebraMap R (GhostPolynomial R n) r) = 0 :=
  CliffordAlgebra.contractLeft_algebraMap _ _ _

@[simp] theorem contract_one (f : Module.Dual R (Fin n → R)) : contract f 1 = 0 :=
  CliffordAlgebra.contractLeft_one _ _

@[simp] theorem contract_ι (f : Module.Dual R (Fin n → R)) (v : Fin n → R) :
    contract f (ExteriorAlgebra.ι R v) = algebraMap R _ (f v) :=
  CliffordAlgebra.contractLeft_ι _ _ _

theorem contract_ι_mul (f : Module.Dual R (Fin n → R))
    (v : Fin n → R) (x : GhostPolynomial R n) :
    contract f (ExteriorAlgebra.ι R v * x) =
      f v • x - ExteriorAlgebra.ι R v * contract f x :=
  CliffordAlgebra.contractLeft_ι_mul _ _ _

/-- The product rule works on inhomogeneous polynomials via parity involution. -/
theorem contract_mul (f : Module.Dual R (Fin n → R)) (x y : GhostPolynomial R n) :
    contract f (x * y) = contract f x * y + parityInvolution x * contract f y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [contract_scalar, zero_mul, zero_add, AlgHom.commutes]
      exact CliffordAlgebra.contractLeft_algebraMap_mul _ _ _
  | add x z hx hz =>
      simp only [add_mul, map_add, hx, hz]
      abel
  | ι_mul x v hx =>
      change contract f ((ExteriorAlgebra.ι R v * x) * y) = _
      rw [mul_assoc, contract_ι_mul, hx, contract_ι_mul]
      simp only [map_mul, parityInvolution_ι, sub_mul, smul_mul_assoc]
      noncomm_ring

/-- Contraction reverses parity. -/
theorem parity_contract (f : Module.Dual R (Fin n → R)) (x : GhostPolynomial R n) :
    parityInvolution (contract f x) = -contract f (parityInvolution x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | ι_mul x v hx =>
      change parityInvolution (contract f (ExteriorAlgebra.ι R v * x)) = _
      rw [contract_ι_mul]
      simp only [map_sub, map_smul, map_mul, parityInvolution_ι, hx, neg_mul,
        map_neg, contract_ι_mul, neg_neg, mul_neg]

@[simp] theorem contract_sq (f : Module.Dual R (Fin n → R)) (x : GhostPolynomial R n) :
    contract f (contract f x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft _ _

theorem contract_anticommute (f g : Module.Dual R (Fin n → R))
    (x : GhostPolynomial R n) : contract f (contract g x) = -contract g (contract f x) :=
  CliffordAlgebra.contractLeft_comm _ _ _

/-- A finite Koszul differential from explicitly supplied constraint coefficients. -/
noncomputable def koszul (f : Module.Dual R (Fin n → R)) :
    GradedBRSTDifferential (grading (R := R) (n := n)) where
  differential := contract f
  map_zero' := map_zero _
  map_add' := map_add _
  map_neg' := map_neg _
  maps_grade' := by
    intro p x hx
    cases p
    · change parityInvolution (contract f x) = -contract f x
      rw [parity_contract, show parityInvolution x = x from hx]
    · change parityInvolution (contract f x) = contract f x
      rw [parity_contract, show parityInvolution x = -x from hx, map_neg, neg_neg]
  leibniz' := by
    intro p q x y hx _
    rw [contract_mul]
    cases p
    · change _ = contract f x * y + x * contract f y
      rw [show parityInvolution x = x from hx]
    · change _ = contract f x * y + -(x * contract f y)
      rw [show parityInvolution x = -x from hx, neg_mul]
  nilpotent := contract_sq f

/-- A finite constraint sequence, interpreted as a covector over the coefficient ring.
The ring may itself be a polynomial ring of classical observables. -/
def constraintCovector (constraints : Fin n → R) : Module.Dual R (Fin n → R) where
  toFun v := ∑ i, constraints i * v i
  map_add' := by intro v w; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro r v
    simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem constraintCovector_single (constraints : Fin n → R) (i : Fin n) :
    constraintCovector constraints (Pi.single i 1) = constraints i := by
  simp [constraintCovector, Pi.single_apply]

/-- The Koszul differential for a user-supplied finite sequence of constraints. -/
noncomputable def koszulOfConstraints (constraints : Fin n → R) :
    GradedBRSTDifferential (grading (R := R) (n := n)) :=
  koszul (constraintCovector constraints)

@[simp] theorem koszulOfConstraints_generator (constraints : Fin n → R) (i : Fin n) :
    koszulOfConstraints constraints (generator i) = algebraMap R _ (constraints i) := by
  change contract (constraintCovector constraints) (ExteriorAlgebra.ι R (Pi.single i 1)) = _
  simp

/-- The boundary of a ghost pair is the elementary constraint syzygy. -/
theorem koszulOfConstraints_pair (constraints : Fin n → R) (i j : Fin n) :
    koszulOfConstraints constraints (generator i * generator j) =
      constraints i • generator j - constraints j • generator i := by
  change contract (constraintCovector constraints)
    (ExteriorAlgebra.ι R (Pi.single i 1) * generator j) = _
  rw [contract_ι_mul, constraintCovector_single]
  change constraints i • generator j - generator i *
    koszulOfConstraints constraints (generator j) = _
  rw [koszulOfConstraints_generator, ← Algebra.commutes, ← Algebra.smul_def]

/-- The homotopy identity keeps the constraint pairing visible. -/
theorem contraction_homotopy (f : Module.Dual R (Fin n → R))
    (v : Fin n → R) (x : GhostPolynomial R n) :
    contract f (ExteriorAlgebra.ι R v * x) + ExteriorAlgebra.ι R v * contract f x =
      f v • x := by
  rw [contract_ι_mul, sub_add_cancel]

/-- A unit pairing contracts this Koszul complex; nilpotency alone does not. -/
theorem exact_of_closed_of_pairing_one (f : Module.Dual R (Fin n → R))
    (v : Fin n → R) (hv : f v = 1) {x : GhostPolynomial R n}
    (hx : (koszul f).IsClosed x) : (koszul f).IsExact x := by
  refine ⟨ExteriorAlgebra.ι R v * x, ?_⟩
  change contract f (ExteriorAlgebra.ι R v * x) = x
  change contract f x = 0 at hx
  rw [contract_ι_mul, hv, hx, one_smul, mul_zero, sub_zero]

/-- With zero constraints only zero is exact, despite every element being closed. -/
theorem koszul_zero_exact_iff (x : GhostPolynomial R n) :
    (koszul (0 : Module.Dual R (Fin n → R))).IsExact x ↔ x = 0 := by
  change (∃ y, contract (0 : Module.Dual R (Fin n → R)) y = x) ↔ x = 0
  simp [eq_comm]

/-- Grassmann left differentiation with respect to the indexed generator. -/
noncomputable def derivative (i : Fin n) :
    GhostPolynomial R n →ₗ[R] GhostPolynomial R n := contract (LinearMap.proj i)

@[simp] theorem derivative_generator (i j : Fin n) :
    derivative (R := R) i (generator j) = if i = j then 1 else 0 := by
  simp [derivative, generator, Pi.single_apply]

theorem derivative_generator_mul (i j : Fin n) (x : GhostPolynomial R n) :
    derivative i (generator j * x) + generator j * derivative (R := R) i x =
      if i = j then x else 0 := by
  simpa [derivative, generator, Pi.single_apply, eq_comm] using
    contraction_homotopy (R := R) (LinearMap.proj i) (Pi.single j 1) x

@[simp] theorem derivative_sq (i : Fin n) (x : GhostPolynomial R n) :
    derivative i (derivative (R := R) i x) = 0 := contract_sq _ _

theorem derivative_anticommute (i j : Fin n) (x : GhostPolynomial R n) :
    derivative i (derivative (R := R) j x) = -derivative j (derivative i x) :=
  contract_anticommute _ _ _

end LeanPhy.GaugeTheory.GhostPolynomial
