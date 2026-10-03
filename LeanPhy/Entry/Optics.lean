import LeanPhy.Entry.Classical
import LeanPhy.Quantum.Unitary

/-!
# Optics and AMO entry point

The first optics layer deliberately reuses two generic finite contracts:
paraxial ABCD matrices are two-dimensional symplectic maps, while lossless
polarisation elements are finite unitaries.  This keeps the optical API
compatible with classical mechanics and finite quantum mechanics instead of
creating a third matrix language.  Dispersion, Maxwell boundary problems and
continuous Fourier optics remain explicit analytic obligations.
-/

namespace LeanPhy.Optics

open scoped Matrix

abbrev ABCD := LeanPhy.Classical.M2R

abbrev JonesElement (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  LeanPhy.Quantum.FiniteUnitary ι

def isCanonical (A : ABCD) : Prop :=
  Aᵀ * LeanPhy.Classical.symplecticJ * A = LeanPhy.Classical.symplecticJ

theorem compose_isCanonical (A B : ABCD)
    (hA : isCanonical A) (hB : isCanonical B) :
    isCanonical (A * B) := by
  unfold isCanonical at hA hB ⊢
  exact LeanPhy.Classical.symplectic_mul A B hA hB

theorem freeSpace_isCanonical (d : ℝ) :
    isCanonical (!![1, d; 0, 1] : ABCD) :=
  by simpa [isCanonical] using LeanPhy.Classical.shear_symplectic d

theorem lens_isCanonical (f : ℝ) (_hf : f ≠ 0) :
    isCanonical (!![1, 0; -(1 / f), 1] : ABCD) := by
  unfold isCanonical
  apply (LeanPhy.Classical.symplectic_iff_det _).mpr
  simp [Matrix.det_fin_two]

theorem jones_preserves_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : JonesElement ι) (v w : ι → ℂ) :
    dotProduct (star (U.evolve v)) (U.evolve w) =
      dotProduct (star v) w :=
  U.evolve_inner v w

end LeanPhy.Optics
