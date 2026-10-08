import LeanPhy.Mathematics.Derivation
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finsupp.Single
import Mathlib.Tactic

/-!
# Polynomial jets of commuting fields in flat coordinates

A variable `jet a α` represents the derivative `∂^α φ_a`. Multi-indices record
all derivative orders, so applying a total derivative never silently drops a
higher jet. Every polynomial still has finite support. Field components and
coordinate directions are distinct types; no metric or Fourier convention is
implicit. The total derivatives commute, as appropriate to ordinary flat
coordinate derivatives, not covariant derivatives with curvature.

This is a formal differential algebra, not a space of smooth field solutions.
Its real/complex coefficient rings describe commuting bosonic fields; Grassmann
fields and gauge-covariant jets require additional structures.
-/

namespace LeanPhy.FieldTheory

open LeanPhy.Mathematics

abbrev JetPolynomial (R : Type*) [CommRing R] (Field : Type*) (Direction : Type*) :=
  MvPolynomial (Field × (Direction →₀ ℕ)) R

namespace JetPolynomial

variable {R Field Direction : Type*} [CommRing R]

noncomputable def jet (a : Field) (α : Direction →₀ ℕ) :
    JetPolynomial R Field Direction := MvPolynomial.X (a, α)

/-- `D_μ(∂^α φ_a) = ∂^(α+e_μ) φ_a`, for every field component. -/
noncomputable def totalDerivative (μ : Direction) :
    PhysicsDerivation R (JetPolynomial R Field Direction) :=
  MvPolynomial.mkDerivation R (fun p => jet p.1 (p.2 + Finsupp.single μ 1))

@[simp] theorem totalDerivative_jet (μ : Direction) (a : Field)
    (α : Direction →₀ ℕ) :
    totalDerivative μ (jet a α : JetPolynomial R Field Direction) =
      jet a (α + Finsupp.single μ 1) := by
  simp [totalDerivative, jet]

/-- Ordinary spacetime derivatives commute on the entire polynomial algebra,
not just on a preselected list of fields. -/
theorem totalDerivative_commutator (μ ν : Direction) :
    ⁅(totalDerivative μ : PhysicsDerivation R (JetPolynomial R Field Direction)),
      (totalDerivative ν : PhysicsDerivation R (JetPolynomial R Field Direction))⁆ = 0 := by
  apply MvPolynomial.derivation_ext
  rintro ⟨a, α⟩
  simp [Derivation.commutator_apply, totalDerivative, jet,
    add_left_comm, add_comm]

theorem totalDerivative_commute (μ ν : Direction) (P : JetPolynomial R Field Direction) :
    totalDerivative μ (totalDerivative ν P) = totalDerivative ν (totalDerivative μ P) := by
  have h := congrArg (fun D : PhysicsDerivation R (JetPolynomial R Field Direction) => D P)
    (totalDerivative_commutator (R := R) (Field := Field) μ ν)
  simpa only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] using h

/-- Relabel field components without changing their derivative multi-indices. -/
noncomputable def renameFields {OtherField : Type*} (f : Field → OtherField) :
    JetPolynomial R Field Direction →ₐ[R] JetPolynomial R OtherField Direction :=
  MvPolynomial.rename (fun p => (f p.1, p.2))

@[simp] theorem renameFields_jet {OtherField : Type*} (f : Field → OtherField)
    (a : Field) (α : Direction →₀ ℕ) :
    renameFields f (jet a α : JetPolynomial R Field Direction) = jet (f a) α := by
  simp [renameFields, jet]

/-- Field naming and mode ordering do not change total differentiation. -/
theorem renameFields_totalDerivative {OtherField : Type*} (f : Field → OtherField)
    (μ : Direction) (P : JetPolynomial R Field Direction) :
    renameFields f (totalDerivative μ P) = totalDerivative μ (renameFields f P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [renameFields]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      rcases j with ⟨a, α⟩
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp]
      simp [renameFields, totalDerivative, jet]

end JetPolynomial
end LeanPhy.FieldTheory
