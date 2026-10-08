import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Eliminate an invertible block, preserving sources and readouts

The light and heavy labels can have different finite cardinalities. The
coefficient ring may be noncommutative, including formal-series rings. A unit
heavy block supplies a checked two-sided inverse; singular blocks are not
handled by silently evaluating a total inverse.

The effective operator is `A - B D⁻¹ C`, its source is `jL - B D⁻¹ jH`, and
the eliminated component is `D⁻¹(jH - C x)`. Theorems prove equivalence of the
actual equations and transport arbitrary linear readouts. This is exact block
elimination, not an energy-independent low-energy approximation, a unitary
Schrieffer--Wolff transformation, or a continuum functional integral.
-/

namespace LeanPhy.Mathematics.BlockElimination

open scoped Matrix

variable {R L H O : Type*} [Ring R] [Fintype L] [Fintype H] [DecidableEq H]

/-- A finite two-sector linear problem, with an invertible heavy block. -/
structure System (R L H : Type*) [Ring R] [Fintype H] [DecidableEq H] where
  light : Matrix L L R
  toLight : Matrix L H R
  toHeavy : Matrix H L R
  heavy : (Matrix H H R)ˣ

namespace System

variable (S : System R L H)

def effective : Matrix L L R := S.light - S.toLight * (↑(S.heavy⁻¹) : Matrix H H R) * S.toHeavy

def effectiveSource (jL : L → R) (jH : H → R) : L → R :=
  jL - (S.toLight * (↑(S.heavy⁻¹) : Matrix H H R)).mulVec jH

def reconstruct (x : L → R) (jH : H → R) : H → R :=
  ((↑(S.heavy⁻¹) : Matrix H H R) : Matrix H H R).mulVec (jH - S.toHeavy.mulVec x)

def Satisfies (x : L → R) (y : H → R) (jL : L → R) (jH : H → R) : Prop :=
  S.light.mulVec x + S.toLight.mulVec y = jL ∧
    S.toHeavy.mulVec x + (↑S.heavy : Matrix H H R).mulVec y = jH

theorem reconstruct_heavy_equation (x : L → R) (jH : H → R) :
    S.toHeavy.mulVec x + (↑S.heavy : Matrix H H R).mulVec (S.reconstruct x jH) = jH := by
  simp [reconstruct, Matrix.mulVec_mulVec]

theorem heavy_equation_iff (x : L → R) (y jH : H → R) :
    S.toHeavy.mulVec x + (↑S.heavy : Matrix H H R).mulVec y = jH ↔
      y = S.reconstruct x jH := by
  constructor
  · intro h
    have hy : (↑S.heavy : Matrix H H R).mulVec y = jH - S.toHeavy.mulVec x := by
      exact eq_sub_of_add_eq' h
    have hi := congrArg (fun v => ((↑(S.heavy⁻¹) : Matrix H H R) : Matrix H H R).mulVec v) hy
    simpa [Matrix.mulVec_mulVec, reconstruct] using hi
  · rintro rfl
    exact S.reconstruct_heavy_equation x jH

theorem reconstructed_light_equation (x : L → R) (jH : H → R) :
    S.light.mulVec x + S.toLight.mulVec (S.reconstruct x jH) =
      S.effective.mulVec x + (S.toLight * (↑(S.heavy⁻¹) : Matrix H H R)).mulVec jH := by
  simp only [reconstruct, effective, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.mul_assoc]
  abel

/-- Full solutions are exactly effective solutions with the reconstructed heavy part. -/
theorem satisfies_iff (x : L → R) (y : H → R) (jL : L → R) (jH : H → R) :
    S.Satisfies x y jL jH ↔
      S.effective.mulVec x = S.effectiveSource jL jH ∧ y = S.reconstruct x jH := by
  unfold Satisfies
  rw [S.heavy_equation_iff]
  constructor
  · rintro ⟨hL, rfl⟩
    rw [S.reconstructed_light_equation] at hL
    exact ⟨eq_sub_of_add_eq hL, rfl⟩
  · rintro ⟨hL, rfl⟩
    refine ⟨?_, rfl⟩
    rw [S.reconstructed_light_equation, hL]
    simp [effectiveSource]

/-- The reduced equation retains the exact full light-equation residual. -/
theorem residual_identity (x : L → R) (jL : L → R) (jH : H → R) :
    S.light.mulVec x + S.toLight.mulVec (S.reconstruct x jH) - jL =
      S.effective.mulVec x - S.effectiveSource jL jH := by
  rw [S.reconstructed_light_equation]
  unfold effectiveSource
  abel

/-- Effective linear probes may have any output label type. -/
def effectiveReadout (OL : Matrix O L R) (OH : Matrix O H R) : Matrix O L R :=
  OL - OH * (↑(S.heavy⁻¹) : Matrix H H R) * S.toHeavy

/-- A nonzero heavy source produces an affine offset in the readout. -/
def readoutOffset (OH : Matrix O H R) (jH : H → R) : O → R :=
  (OH * (↑(S.heavy⁻¹) : Matrix H H R)).mulVec jH

theorem readout_reconstruct (OL : Matrix O L R) (OH : Matrix O H R)
    (x : L → R) (jH : H → R) :
    OL.mulVec x + OH.mulVec (S.reconstruct x jH) =
      (S.effectiveReadout OL OH).mulVec x + S.readoutOffset OH jH := by
  simp only [reconstruct, effectiveReadout, readoutOffset, Matrix.mulVec_sub,
    Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.mul_assoc]
  abel

theorem readout_of_solution (OL : Matrix O L R) (OH : Matrix O H R)
    (x : L → R) (y : H → R) (jL : L → R) (jH : H → R)
    (h : S.Satisfies x y jL jH) :
    OL.mulVec x + OH.mulVec y =
      (S.effectiveReadout OL OH).mulVec x + S.readoutOffset OH jH := by
  rw [(S.satisfies_iff x y jL jH).mp h |>.2]
  exact S.readout_reconstruct OL OH x jH

/-- Connect the two-sector interface to the actual block matrix on `L ⊕ H`. -/
def fullMatrix : Matrix (L ⊕ H) (L ⊕ H) R :=
  Matrix.fromBlocks S.light S.toLight S.toHeavy ↑S.heavy

theorem fullMatrix_equation_iff (x : L → R) (y : H → R) (jL : L → R) (jH : H → R) :
    S.fullMatrix.mulVec (Sum.elim x y) = Sum.elim jL jH ↔ S.Satisfies x y jL jH := by
  rw [fullMatrix, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h
    exact ⟨congrArg (fun f i => f (Sum.inl i)) h,
      congrArg (fun f i => f (Sum.inr i)) h⟩
  · rintro ⟨hL, hH⟩
    rw [hL, hH]

end System

end LeanPhy.Mathematics.BlockElimination
