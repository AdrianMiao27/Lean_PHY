import LeanPhy.Mathematics.FiniteRepresentation
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic

/-!
# Finite group averages and twirling

Finite symmetry averages occur under several names in physics: a quantum
twirl, a gauge-group average on a finite model, a point-group projection in a
band calculation, or a lattice orbit sum.  They all use the same finite
reindexing fact.  This module packages that fact once and keeps the physical
interpretation outside the kernel theorem.

Only a finite group and an additive target are required for orbit sums.  The
matrix twirl additionally consumes an explicit finite matrix representation;
the representation homomorphism is what lets the kernel prove conjugation
invariance.  No Haar measure, compactness, irreducibility, or continuum group
limit is inferred here.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators Matrix

universe u v

section FiniteSum

variable {G : Type u} {A : Type v} [Group G] [Fintype G]
  [AddCommMonoid A]

/-- The unnormalised finite orbit sum of a function on a finite group. -/
def groupSum (f : G → A) : A := ∑ g, f g

@[simp] theorem groupSum_apply (f : G → A) : groupSum f = ∑ g, f g := rfl

/-- Left multiplication is a permutation of a finite group, so orbit sums are
invariant under relabelling. -/
theorem groupSum_mulLeft (h : G) (f : G → A) :
    groupSum (fun g => f (h * g)) = groupSum f := by
  exact Equiv.sum_comp (Equiv.mulLeft h) f

/-- Right multiplication gives the corresponding reindexing law. -/
theorem groupSum_mulRight (h : G) (f : G → A) :
    groupSum (fun g => f (g * h)) = groupSum f := by
  exact Equiv.sum_comp (Equiv.mulRight h) f

@[simp] theorem groupSum_add (f g : G → A) :
    groupSum (fun x => f x + g x) = groupSum f + groupSum g := by
  simp [groupSum, Finset.sum_add_distrib]

end FiniteSum

section MatrixTwirl

variable {G : Type u} {ι : Type v} [Group G] [Fintype G]
  [Fintype ι] [DecidableEq ι]

/-- Conjugation average of a finite matrix representation. -/
def groupTwirl (R : FiniteMatrixRepresentation G ι)
    (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ g, R.rep g * X * R.rep g⁻¹

@[simp] theorem groupTwirl_apply (R : FiniteMatrixRepresentation G ι)
    (X : Matrix ι ι ℂ) :
    groupTwirl R X = ∑ g, R.rep g * X * R.rep g⁻¹ := rfl

/-- The finite twirl is invariant under conjugating its output by any group
element.  This is the algebraic core reused by finite quantum, gauge and
point-group calculations. -/
theorem groupTwirl_conjugate (R : FiniteMatrixRepresentation G ι)
    (h : G) (X : Matrix ι ι ℂ) :
    R.rep h * groupTwirl R X * R.rep h⁻¹ = groupTwirl R X := by
  unfold groupTwirl
  rw [Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ g, R.rep h * (R.rep g * X * R.rep g⁻¹) * R.rep h⁻¹) =
        ∑ g, R.rep (h * g) * X * R.rep (h * g)⁻¹ := by
      apply Finset.sum_congr rfl
      intro g hg
      calc
        R.rep h * (R.rep g * X * R.rep g⁻¹) * R.rep h⁻¹ =
            (R.rep h * R.rep g) * X * (R.rep g⁻¹ * R.rep h⁻¹) := by
              simp only [mul_assoc]
        _ = R.rep (h * g) * X * R.rep (h * g)⁻¹ := by
              rw [← R.rep.map_mul, ← R.rep.map_mul]
              simp
    _ = groupTwirl R X := groupSum_mulLeft h (fun g => R.rep g * X * R.rep g⁻¹)

/-- Equivalently, a finite twirl commutes with every represented group
element.  This form is convenient for conserved-subspace and symmetry-sector
arguments. -/
theorem groupTwirl_commute (R : FiniteMatrixRepresentation G ι)
    (h : G) (X : Matrix ι ι ℂ) :
    R.rep h * groupTwirl R X = groupTwirl R X * R.rep h := by
  have hc := groupTwirl_conjugate R h X
  calc
    R.rep h * groupTwirl R X =
        (R.rep h * groupTwirl R X) * (1 : Matrix ι ι ℂ) := by simp
    _ = (R.rep h * groupTwirl R X) *
        (R.rep h⁻¹ * R.rep h) := by rw [rep_inv_mul R h]
    _ = (R.rep h * groupTwirl R X * R.rep h⁻¹) * R.rep h := by
      simp only [mul_assoc]
    _ = groupTwirl R X * R.rep h := by rw [hc]

@[simp] theorem groupTwirl_zero (R : FiniteMatrixRepresentation G ι) :
    groupTwirl R 0 = 0 := by
  simp [groupTwirl]

theorem groupTwirl_add (R : FiniteMatrixRepresentation G ι)
    (X Y : Matrix ι ι ℂ) :
    groupTwirl R (X + Y) = groupTwirl R X + groupTwirl R Y := by
  simp [groupTwirl, Finset.sum_add_distrib, Matrix.mul_add, Matrix.add_mul]

theorem groupTwirl_smul (R : FiniteMatrixRepresentation G ι)
    (c : ℂ) (X : Matrix ι ι ℂ) :
    groupTwirl R (c • X) = c • groupTwirl R X := by
  simp [groupTwirl, Finset.smul_sum]

end MatrixTwirl

end LeanPhy.Mathematics

/-! Domain vocabulary for the same finite theorem. -/

namespace LeanPhy

namespace Quantum
abbrev FiniteQuantumTwirl {G ι : Type} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι] :=
  Mathematics.groupTwirl (G := G) (ι := ι)
end Quantum

namespace GaugeTheory
abbrev FiniteGaugeTwirl {G ι : Type} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι] :=
  Mathematics.groupTwirl (G := G) (ι := ι)
end GaugeTheory

namespace Condensed
abbrev FinitePointGroupTwirl {G ι : Type} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι] :=
  Mathematics.groupTwirl (G := G) (ι := ι)
end Condensed

end LeanPhy
