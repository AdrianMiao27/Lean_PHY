import LeanPhy.Mathematics.AlgebraicDerivation
import LeanPhy.Mathematics.NoncommExterior
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LeanPhy.GaugeTheory

/-! Backward-compatible name for the generic mathematical interface. -/
abbrev AlgebraicDerivation (A : Type) [Ring A] :=
  LeanPhy.Mathematics.AlgebraicDerivation A

namespace AlgebraicDerivation

@[simp] theorem map_zero {A : Type} [Ring A]
    (D : AlgebraicDerivation A) : D 0 = 0 :=
  LeanPhy.Mathematics.AlgebraicDerivation.map_zero D

@[simp] theorem map_add {A : Type} [Ring A]
    (D : AlgebraicDerivation A) (x y : A) : D (x + y) = D x + D y :=
  LeanPhy.Mathematics.AlgebraicDerivation.map_add D x y

theorem leibniz {A : Type} [Ring A]
    (D : AlgebraicDerivation A) (x y : A) : D (x * y) = D x * y + x * D y :=
  LeanPhy.Mathematics.AlgebraicDerivation.leibniz D x y

theorem map_neg {A : Type} [Ring A]
    (D : AlgebraicDerivation A) (x : A) : D (-x) = -D x :=
  LeanPhy.Mathematics.AlgebraicDerivation.map_neg D x

theorem map_sub {A : Type} [Ring A]
    (D : AlgebraicDerivation A) (x y : A) : D (x - y) = D x - D y :=
  LeanPhy.Mathematics.AlgebraicDerivation.map_sub D x y

end AlgebraicDerivation

/-- A finite matrix-valued connection with commuting background deriv
  derivatives.  `potential` is the gauge potential `A_mu`. -/
structure YangMillsConnection (A : Type) [Ring A] where
  deriv : Fin 4 → AlgebraicDerivation A
  potential : Fin 4 → A
  deriv_commute : ∀ mu nu x, deriv mu (deriv nu x) = deriv nu (deriv mu x)

namespace YangMillsConnection

variable {A : Type} [Ring A] (C : YangMillsConnection A)

/-- View a fixed four-direction Yang--Mills connection through the generic
finite noncommutative exterior-calculus interface. -/
def toNoncommConnection : LeanPhy.Mathematics.NoncommConnection 4 A where
  deriv := C.deriv
  potential := C.potential
  deriv_commute := C.deriv_commute

/-- The non-Abelian curvature `F_mu nu = d_mu A_nu - d_nu A_mu + [A_mu,A_nu]`. -/
def curvature (mu nu : Fin 4) : A :=
  C.deriv mu (C.potential nu) - C.deriv nu (C.potential mu) +
    C.potential mu * C.potential nu - C.potential nu * C.potential mu

/-- The adjoint covariant derivative `nabla_mu X = d_mu X + [A_mu,X]`. -/
def covariantDerivative (mu : Fin 4) (X : A) : A :=
  C.deriv mu X + C.potential mu * X - X * C.potential mu

theorem curvature_eq_noncommExterior (mu nu : Fin 4) :
    C.curvature mu nu =
      (C.toNoncommConnection).curvature mu nu := rfl

theorem covariantDerivative_eq_noncommExterior (mu : Fin 4) (X : A) :
    C.covariantDerivative mu X =
      (C.toNoncommConnection).covariantDerivative mu X := rfl

theorem bianchi_via_noncommExterior (mu nu rho : Fin 4) :
    C.covariantDerivative mu (C.curvature nu rho) +
        C.covariantDerivative nu (C.curvature rho mu) +
        C.covariantDerivative rho (C.curvature mu nu) = 0 := by
  exact LeanPhy.Mathematics.NoncommConnection.bianchi
    C.toNoncommConnection mu nu rho

theorem curvature_antisym (mu nu : Fin 4) :
    C.curvature mu nu = -C.curvature nu mu := by
  simp only [curvature]
  noncomm_ring

/-- Covariant Bianchi identity for a matrix-valued connection. -/
theorem bianchi (mu nu rho : Fin 4) :
    C.covariantDerivative mu (C.curvature nu rho) +
        C.covariantDerivative nu (C.curvature rho mu) +
        C.covariantDerivative rho (C.curvature mu nu) = 0 := by
  simp only [covariantDerivative, curvature]
  simp only [AlgebraicDerivation.map_add, AlgebraicDerivation.map_sub,
    AlgebraicDerivation.leibniz]
  have h1 := C.deriv_commute mu nu (C.potential rho)
  have h2 := C.deriv_commute mu rho (C.potential nu)
  have h3 := C.deriv_commute nu rho (C.potential mu)
  rw [h1, h2, h3]
  noncomm_ring

end YangMillsConnection

end LeanPhy.GaugeTheory
