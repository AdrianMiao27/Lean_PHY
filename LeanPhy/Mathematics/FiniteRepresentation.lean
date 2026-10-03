import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Finite matrix representations and characters

Finite-dimensional symmetry calculations in particle physics, condensed matter
and quantum information share the same algebraic core: a monoid or group acts
by square matrices, and intertwiners transport that action between spaces.
This module packages that core without choosing a particular gauge group,
point group or basis.

The theorems are finite matrix identities.  They do not construct Lie groups,
compact-group Haar measure, irreducibility decompositions, Schur orthogonality
or a physical symmetry.  A model must supply those structures explicitly.
-/

namespace LeanPhy.Mathematics

open scoped Matrix

universe u v w

/-- A finite matrix representation of a monoid.  The finite index and its
decidable equality are required by matrix multiplication. -/
structure FiniteMatrixRepresentation (G : Type u) (ι : Type v)
    [Monoid G] [Fintype ι] [DecidableEq ι] where
  rep : G →* Matrix ι ι ℂ

namespace FiniteMatrixRepresentation

variable {G : Type u} {ι : Type v} [Monoid G] [Fintype ι] [DecidableEq ι]
  (R : FiniteMatrixRepresentation G ι)

@[simp] theorem rep_one : R.rep 1 = (1 : Matrix ι ι ℂ) := R.rep.map_one

@[simp] theorem rep_mul (g h : G) : R.rep (g * h) = R.rep g * R.rep h :=
  R.rep.map_mul g h

/-- Pull a representation back along a monoid homomorphism.  This is the
standard finite algebraic bridge for subgroups, quotient maps and parameter
relabelings. -/
def pullback {H : Type w} [Monoid H] (f : H →* G) :
    FiniteMatrixRepresentation H ι where
  rep := R.rep.comp f

@[simp] theorem pullback_rep {H : Type w} [Monoid H] (f : H →* G) (h : H) :
    (R.pullback f).rep h = R.rep (f h) := rfl

/-- The character is the finite matrix trace. -/
def character (g : G) : ℂ := Matrix.trace (R.rep g)

@[simp] theorem pullback_character {H : Type w} [Monoid H] (f : H →* G) (h : H) :
    (R.pullback f).character h = R.character (f h) := rfl

@[simp] theorem character_one : R.character 1 = (Fintype.card ι : ℂ) := by
  simp [character, Matrix.trace]

@[simp] theorem character_mul_trace (g h : G) :
    R.character (g * h) = Matrix.trace (R.rep g * R.rep h) := by
  change Matrix.trace (R.rep (g * h)) = Matrix.trace (R.rep g * R.rep h)
  rw [R.rep_mul]

end FiniteMatrixRepresentation

section Group

variable {G : Type u} {ι : Type v} [Group G] [Fintype ι] [DecidableEq ι]
  (R : FiniteMatrixRepresentation G ι)

theorem rep_mul_inv (g : G) : R.rep g * R.rep g⁻¹ = (1 : Matrix ι ι ℂ) := by
  rw [← R.rep.map_mul]
  simp

theorem rep_inv_mul (g : G) : R.rep g⁻¹ * R.rep g = (1 : Matrix ι ι ℂ) := by
  rw [← R.rep.map_mul]
  simp

/-- The character is constant on group conjugacy classes. -/
theorem character_conjugate (a g : G) :
    R.character (a * g * a⁻¹) = R.character g := by
  simp only [FiniteMatrixRepresentation.character, map_mul]
  rw [Matrix.trace_mul_cycle]
  rw [← R.rep.map_mul]
  simp

end Group

/-! Intertwiners are kept separate from representations so a proof can state
exactly which change-of-basis or symmetry map is available. -/

def Intertwiner {G : Type u} {ι : Type v} {κ : Type w}
    [Monoid G] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (R : FiniteMatrixRepresentation G ι)
    (S : FiniteMatrixRepresentation G κ)
    (T : Matrix κ ι ℂ) : Prop :=
  ∀ g, T * R.rep g = S.rep g * T

namespace Intertwiner

variable {G : Type u} {ι : Type v} {κ : Type w}
  [Monoid G] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {R : FiniteMatrixRepresentation G ι}
  {S : FiniteMatrixRepresentation G κ}

theorem identity (R : FiniteMatrixRepresentation G ι) :
    Intertwiner R R (1 : Matrix ι ι ℂ) := by
  intro g
  simp

theorem zero : Intertwiner R S (0 : Matrix κ ι ℂ) := by
  intro g
  simp

theorem add {T U : Matrix κ ι ℂ}
    (hT : Intertwiner R S T) (hU : Intertwiner R S U) :
    Intertwiner R S (T + U) := by
  intro g
  rw [Matrix.add_mul, Matrix.mul_add, hT g, hU g]

theorem smul (c : ℂ) {T : Matrix κ ι ℂ}
    (hT : Intertwiner R S T) : Intertwiner R S (c • T) := by
  intro g
  simp only [Matrix.smul_mul, Matrix.mul_smul, hT g]

theorem compose {μ : Type w} [Fintype μ] [DecidableEq μ]
    {T : Matrix κ ι ℂ} {U : Matrix μ κ ℂ}
    {Q : FiniteMatrixRepresentation G μ}
    (hT : Intertwiner R S T) (hU : Intertwiner S Q U) :
    Intertwiner R Q (U * T) := by
  intro g
  rw [Matrix.mul_assoc, hT g, ← Matrix.mul_assoc, hU g, Matrix.mul_assoc]

end Intertwiner

/-! A unitary representation records the physical inner-product condition as
a field.  The inverse-to-adjoint theorem is useful when translating group
actions into finite quantum or band Hamiltonian calculations. -/

structure UnitaryMatrixRepresentation (G : Type u) (ι : Type v)
    [Group G] [Fintype ι] [DecidableEq ι]
    extends FiniteMatrixRepresentation G ι where
  unitary : ∀ g, Matrix.conjTranspose (rep g) * rep g = 1

namespace UnitaryMatrixRepresentation

variable {G : Type u} {ι : Type v} [Group G] [Fintype ι] [DecidableEq ι]
  (R : UnitaryMatrixRepresentation G ι)

theorem rep_mul_inv (g : G) : R.toFiniteMatrixRepresentation.rep g *
    R.toFiniteMatrixRepresentation.rep g⁻¹ = (1 : Matrix ι ι ℂ) := by
  rw [← R.toFiniteMatrixRepresentation.rep.map_mul]
  simp

theorem rep_inv_eq_adjoint (g : G) :
    R.toFiniteMatrixRepresentation.rep g⁻¹ =
      Matrix.conjTranspose (R.toFiniteMatrixRepresentation.rep g) := by
  symm
  calc
    Matrix.conjTranspose (R.toFiniteMatrixRepresentation.rep g) =
        Matrix.conjTranspose (R.toFiniteMatrixRepresentation.rep g) * 1 := by simp
    _ = Matrix.conjTranspose (R.toFiniteMatrixRepresentation.rep g) *
        (R.toFiniteMatrixRepresentation.rep g *
          R.toFiniteMatrixRepresentation.rep g⁻¹) := by
          rw [R.rep_mul_inv]
    _ = (Matrix.conjTranspose (R.toFiniteMatrixRepresentation.rep g) *
          R.toFiniteMatrixRepresentation.rep g) *
          R.toFiniteMatrixRepresentation.rep g⁻¹ := by
          rw [Matrix.mul_assoc]
    _ = R.toFiniteMatrixRepresentation.rep g⁻¹ := by
          rw [R.unitary g, Matrix.one_mul]

theorem character_conjugate (a g : G) :
    Matrix.trace (R.toFiniteMatrixRepresentation.rep (a * g * a⁻¹)) =
      Matrix.trace (R.toFiniteMatrixRepresentation.rep g) := by
  simp only [map_mul]
  rw [Matrix.trace_mul_cycle]
  rw [← R.toFiniteMatrixRepresentation.rep.map_mul]
  simp

end UnitaryMatrixRepresentation

end LeanPhy.Mathematics

/-! Domain vocabulary.  These aliases expose one checked representation
contract under the names used by different physics communities. -/

namespace LeanPhy

namespace GaugeTheory
abbrev FiniteGaugeRepresentation (G : Type u) (ι : Type v)
    [Group G] [Fintype ι] [DecidableEq ι] :=
  Mathematics.FiniteMatrixRepresentation G ι
abbrev FiniteUnitaryGaugeRepresentation (G : Type u) (ι : Type v)
    [Group G] [Fintype ι] [DecidableEq ι] :=
  Mathematics.UnitaryMatrixRepresentation G ι
end GaugeTheory

namespace HighEnergy
abbrev FiniteParticleRepresentation (G : Type u) (ι : Type v)
    [Group G] [Fintype ι] [DecidableEq ι] :=
  Mathematics.FiniteMatrixRepresentation G ι
end HighEnergy

namespace Condensed
abbrev FinitePointGroupRepresentation (G : Type u) (ι : Type v)
    [Group G] [Fintype ι] [DecidableEq ι] :=
  Mathematics.FiniteMatrixRepresentation G ι
end Condensed

namespace Quantum
abbrev FiniteSymmetryRepresentation (G : Type u) (ι : Type v)
    [Group G] [Fintype ι] [DecidableEq ι] :=
  Mathematics.UnitaryMatrixRepresentation G ι
end Quantum

end LeanPhy
