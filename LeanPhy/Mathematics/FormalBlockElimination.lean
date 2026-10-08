import LeanPhy.Mathematics.FormalMatrix
import LeanPhy.Mathematics.BlockElimination

set_option autoImplicit false

/-!
# Retained-order block elimination

Formal matrix series and block equations share an actual representation map.
Truncating input blocks and the certified heavy inverse preserves every
retained coefficient of the effective operator, effective sources and linear
readouts. Rectangular light/heavy blocks are allowed. The cutoff is exclusive;
these conclusions do not assert convergence or a numerical remainder bound.
-/

namespace LeanPhy.Mathematics.FormalExpansion

open PowerSeries BlockElimination
open scoped Matrix

variable {R L H O : Type*} [Ring R]

def MatrixBelow (N : ℕ) {I J : Type*} (A B : Matrix I J (PowerSeries R)) : Prop :=
  ∀ i j, Below N (A i j) (B i j)

namespace MatrixBelow

theorem refl (N : ℕ) {I J : Type*} (A : Matrix I J (PowerSeries R)) : MatrixBelow N A A :=
  fun _ _ => Below.refl N _

theorem sub {N : ℕ} {I J : Type*} {A B C D : Matrix I J (PowerSeries R)}
    (hAB : MatrixBelow N A B) (hCD : MatrixBelow N C D) :
    MatrixBelow N (A - C) (B - D) := fun i j => (hAB i j).sub (hCD i j)

theorem mul {N : ℕ} {I J K : Type*} [Fintype J]
    {A B : Matrix I J (PowerSeries R)} {C D : Matrix J K (PowerSeries R)}
    (hAB : MatrixBelow N A B) (hCD : MatrixBelow N C D) :
    MatrixBelow N (A * C) (B * D) := by
  intro i k n hn
  simp only [Matrix.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact ((hAB i j).mul (hCD j k)) n hn

theorem mulVec {N : ℕ} {I J : Type*} [Fintype J]
    {A B : Matrix I J (PowerSeries R)} {x y : J → PowerSeries R}
    (hAB : MatrixBelow N A B) (hxy : ∀ j, Below N (x j) (y j)) :
    ∀ i, Below N (A.mulVec x i) (B.mulVec y i) := by
  intro i n hn
  simp only [Matrix.mulVec, dotProduct, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact ((hAB i j).mul (hxy j)) n hn

end MatrixBelow

theorem matrix_below {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    {f g : PowerSeries (Matrix ι ι R)} (h : Below N f g) :
    MatrixBelow N (matrix f) (matrix g) := by
  intro i j n hn
  simpa using congrArg (fun A : Matrix ι ι R => A i j) (h n hn)

variable [Fintype H] [DecidableEq H]

/-- Model builder: the heavy inverse is computed from its constant matrix unit. -/
noncomputable def blockSystem (A : Matrix L L (PowerSeries R))
    (B : Matrix L H (PowerSeries R)) (C : Matrix H L (PowerSeries R))
    (D : PowerSeries (Matrix H H R)) (u : (Matrix H H R)ˣ)
    (hD : constantCoeff D = u) : System (PowerSeries R) L H :=
  ⟨A, B, C, matrixUnit D u hD⟩

theorem blockSystem_effective (A : Matrix L L (PowerSeries R))
    (B : Matrix L H (PowerSeries R)) (C : Matrix H L (PowerSeries R))
    (D : PowerSeries (Matrix H H R)) (u : (Matrix H H R)ˣ)
    (hD : constantCoeff D = u) :
    (blockSystem A B C D u hD).effective = A - B * matrix (invOfUnit D u) * C := rfl

/-- All block inputs and the heavy inverse may be replaced to retained order. -/
theorem effective_below {N : ℕ}
    {A A' : Matrix L L (PowerSeries R)} {B B' : Matrix L H (PowerSeries R)}
    {C C' : Matrix H L (PowerSeries R)} {D D' : PowerSeries (Matrix H H R)}
    (hA : MatrixBelow N A A') (hB : MatrixBelow N B B') (hC : MatrixBelow N C C')
    (hD : Below N D D') (u v : (Matrix H H R)ˣ)
    (hu : constantCoeff D = u) (hv : constantCoeff D' = v) :
    MatrixBelow N (blockSystem A B C D u hu).effective
      (blockSystem A' B' C' D' v hv).effective :=
  hA.sub ((hB.mul (matrix_below (hD.inverse u v hu hv))).mul hC)

/-- Truncation of a source uses the same inverse and preserves its retained coefficients. -/
theorem effectiveSource_below {N : ℕ} (S T : System (PowerSeries R) L H)
    (hB : MatrixBelow N S.toLight T.toLight)
    (hInv : MatrixBelow N (↑(S.heavy⁻¹) : Matrix H H (PowerSeries R)) ↑(T.heavy⁻¹))
    {jL kL : L → PowerSeries R} {jH kH : H → PowerSeries R}
    (hL : ∀ i, Below N (jL i) (kL i)) (hH : ∀ i, Below N (jH i) (kH i)) :
    ∀ i, Below N (S.effectiveSource jL jH i) (T.effectiveSource kL kH i) :=
  fun i => (hL i).sub (((hB.mul hInv).mulVec hH) i)

theorem effectiveReadout_below {N : ℕ} (S T : System (PowerSeries R) L H)
    (hC : MatrixBelow N S.toHeavy T.toHeavy)
    (hInv : MatrixBelow N (↑(S.heavy⁻¹) : Matrix H H (PowerSeries R)) ↑(T.heavy⁻¹))
    {OL PL : Matrix O L (PowerSeries R)} {OH PH : Matrix O H (PowerSeries R)}
    (hL : MatrixBelow N OL PL) (hH : MatrixBelow N OH PH) :
    MatrixBelow N (S.effectiveReadout OL OH) (T.effectiveReadout PL PH) :=
  hL.sub ((hH.mul hInv).mul hC)

end LeanPhy.Mathematics.FormalExpansion
