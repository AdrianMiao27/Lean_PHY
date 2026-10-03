import LeanPhy.Mathematics.AlgebraicDerivation
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-!
# Finite noncommutative exterior calculus

This is the algebraic core shared by matrix-valued Yang--Mills fields,
noncommutative geometry and finite/discrete gauge models.  The coefficient
ring may be noncommutative.  A connection consists of commuting background
derivations and a potential; its curvature is `dA + [A,A]` and its covariant
derivative satisfies the Bianchi identity.  Smoothness, a gauge group,
holonomy and continuum limits are deliberately not inferred.
-/

namespace LeanPhy.Mathematics

universe u

/-! The following definitions are parametrized by an arbitrary finite index
set, rather than fixing four space-time directions. -/

structure NoncommConnection (n : Nat) (A : Type u) [Ring A] where
  deriv : Fin n → AlgebraicDerivation A
  potential : Fin n → A
  deriv_commute : ∀ i j x, deriv i (deriv j x) = deriv j (deriv i x)

/-- A concrete connection whose background derivations are inner derivations.
The pairwise commutation hypothesis is explicit because arbitrary inner
derivations need not commute. -/
def innerConnection {n : Nat} {A : Type u} [Ring A]
    (generators potential : Fin n → A)
    (hcomm : ∀ i j, generators i * generators j = generators j * generators i) :
    NoncommConnection n A where
  deriv := fun i => innerDerivation (generators i)
  potential := potential
  deriv_commute := by
    intro i j x
    exact innerDerivation_commute_of_commute (hcomm i j)

namespace NoncommConnection

variable {n : Nat} {A : Type u} [Ring A] (C : NoncommConnection n A)

/-- The curvature `F_ij = D_i A_j - D_j A_i + [A_i,A_j]`. -/
def curvature (i j : Fin n) : A :=
  C.deriv i (C.potential j) - C.deriv j (C.potential i) +
    C.potential i * C.potential j - C.potential j * C.potential i

/-- The adjoint covariant derivative `∇_i X = D_i X + [A_i,X]`. -/
def covariantDerivative (i : Fin n) (X : A) : A :=
  C.deriv i X + C.potential i * X - X * C.potential i

theorem curvature_antisym (i j : Fin n) :
    C.curvature i j = -C.curvature j i := by
  simp only [curvature]
  noncomm_ring

/-- The finite noncommutative Bianchi identity. -/
theorem bianchi (i j k : Fin n) :
    C.covariantDerivative i (C.curvature j k) +
        C.covariantDerivative j (C.curvature k i) +
        C.covariantDerivative k (C.curvature i j) = 0 := by
  simp only [covariantDerivative, curvature]
  simp only [AlgebraicDerivation.map_add, AlgebraicDerivation.map_sub,
    AlgebraicDerivation.leibniz]
  have h1 := C.deriv_commute i j (C.potential k)
  have h2 := C.deriv_commute i k (C.potential j)
  have h3 := C.deriv_commute j k (C.potential i)
  rw [h1, h2, h3]
  noncomm_ring

end NoncommConnection

end LeanPhy.Mathematics
