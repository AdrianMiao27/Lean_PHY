import Mathlib.RingTheory.Derivation.Lie

/-!
# Differential operators for continuum physics

Mathlib already contains the algebraic theory of derivations.  This file gives
it a physics-facing wrapper for directional derivatives and gauge-covariant
derivatives.  A derivation is an explicitly `R`-linear map satisfying the
Leibniz rule; smoothness, coordinates and boundary conditions are deliberately
not inferred.  The commutator of derivations is again a derivation, and its
Jacobi identity is the algebraic Bianchi identity used by gauge theory,
electromagnetism, differential geometry and lattice-to-continuum bridges.
-/

namespace LeanPhy.Mathematics

universe u v

/-- An `R`-derivation of a commutative algebra `A` into itself, named in the
physics layer so the underlying mathlib object remains explicit. -/
abbrev PhysicsDerivation (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A] := Derivation R A A

/-- The commutator of two derivations.  Mathlib proves that it again satisfies
the Leibniz rule; no differentiability axiom is added here. -/
def derivationCommutator {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D E : PhysicsDerivation R A) : PhysicsDerivation R A := ⁅D, E⁆

@[simp] theorem derivationCommutator_apply {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D E : PhysicsDerivation R A) (f : A) :
    derivationCommutator D E f = D (E f) - E (D f) :=
  Derivation.commutator_apply f

/-- A finite family of covariant derivatives and its curvature/field strength.
The index set is finite only to match the finite tensor and Einstein layers;
the derivations themselves can be abstract model objects. -/
def derivationCurvature {n : Nat} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → PhysicsDerivation R A) (i j : Fin n) : PhysicsDerivation R A :=
  derivationCommutator (D i) (D j)

theorem derivationCurvature_antisymm {n : Nat} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → PhysicsDerivation R A) (i j : Fin n) :
    derivationCurvature D i j = -derivationCurvature D j i := by
  unfold derivationCurvature derivationCommutator
  exact (lie_skew (D i) (D j)).symm

theorem derivationCurvature_self {n : Nat} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → PhysicsDerivation R A) (i : Fin n) :
    derivationCurvature D i i = 0 := by
  unfold derivationCurvature derivationCommutator
  exact lie_self (D i)

/-- The covariant-derivative Bianchi identity as a Lie-algebra identity. -/
theorem derivation_bianchi {n : Nat} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → PhysicsDerivation R A) (i j k : Fin n) :
    ⁅derivationCurvature D i j, D k⁆ +
        ⁅derivationCurvature D j k, D i⁆ +
        ⁅derivationCurvature D k i, D j⁆ = 0 := by
  have h1 : ⁅⁅D i, D j⁆, D k⁆ = -⁅D k, ⁅D i, D j⁆⁆ := by
    simpa only [neg_neg] using congrArg Neg.neg (lie_skew (D k) ⁅D i, D j⁆)
  have h2 : ⁅⁅D j, D k⁆, D i⁆ = -⁅D i, ⁅D j, D k⁆⁆ := by
    simpa only [neg_neg] using congrArg Neg.neg (lie_skew (D i) ⁅D j, D k⁆)
  have h3 : ⁅⁅D k, D i⁆, D j⁆ = -⁅D j, ⁅D k, D i⁆⁆ := by
    simpa only [neg_neg] using congrArg Neg.neg (lie_skew (D j) ⁅D k, D i⁆)
  unfold derivationCurvature derivationCommutator
  rw [h1, h2, h3]
  simpa [add_comm, add_left_comm, add_assoc] using
    congrArg Neg.neg (lie_jacobi (D i) (D j) (D k))

/-- Pointwise form of Bianchi, useful when the derivations act on fields. -/
theorem derivation_bianchi_apply {n : Nat} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → PhysicsDerivation R A) (i j k : Fin n) (f : A) :
    (derivationCurvature D i j) (D k f) - D k (derivationCurvature D i j f) +
        (derivationCurvature D j k) (D i f) - D i (derivationCurvature D j k f) +
        (derivationCurvature D k i) (D j f) - D j (derivationCurvature D k i f) = 0 := by
  have h := congrArg (fun X : PhysicsDerivation R A => X f)
    (derivation_bianchi D i j k)
  simp only [add_apply, zero_apply] at h
  have h1 : ⁅derivationCurvature D i j, D k⁆ f =
      (derivationCurvature D i j) (D k f) - D k (derivationCurvature D i j f) :=
    Derivation.commutator_apply f
  have h2 : ⁅derivationCurvature D j k, D i⁆ f =
      (derivationCurvature D j k) (D i f) - D i (derivationCurvature D j k f) :=
    Derivation.commutator_apply f
  have h3 : ⁅derivationCurvature D k i, D j⁆ f =
      (derivationCurvature D k i) (D j f) - D j (derivationCurvature D k i f) :=
    Derivation.commutator_apply f
  rw [h1, h2, h3] at h
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

end LeanPhy.Mathematics
