import LeanPhy.Mathematics.Hilbert
import LeanPhy.Mathematics.ContinuousAnalysis
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Infinite-dimensional Hilbert-space time averages

This module exposes a theorem that is useful for equilibrium limits, Floquet
averages and linear-response reductions.  The operator is allowed to act on an
arbitrary complete inner-product space; no finite basis or matrix
representation is used.  The only dynamical hypothesis consumed by the
theorem is the explicit contraction bound `‖T‖ ≤ 1`.

The limit is the orthogonal projection onto the fixed-point subspace.  This is
the von Neumann mean ergodic theorem already proved in mathlib.  Keeping the
result behind a LeanPhy certificate makes the assumption and the exact target
visible in a physics workflow, while leaving stronger claims (generator
domains, differentiability in time, mixing rates and thermodynamic limits) as
separate obligations.
-/

namespace LeanPhy.Mathematics

open Filter
open scoped Topology

universe u v w

section Hilbert

variable {𝕜 : Type u} {E : Type v}
  [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The explicit dynamical assumption needed by the Hilbert-space mean
ergodic theorem.  The proposition contains no executable approximation data:
the bound is a proof obligation checked by the kernel. -/
structure MeanErgodicCertificate (T : E →L[𝕜] E) : Prop where
  contractive : ‖T‖ ≤ 1

namespace MeanErgodicCertificate

variable {T : E →L[𝕜] E}

/-- The Birkhoff average of a vector under a bounded operator. -/
def average (T : E →L[𝕜] E) (n : ℕ) (x : E) : E :=
  birkhoffAverage 𝕜 (T : E → E) id n x

@[simp] theorem average_zero (T : E →L[𝕜] E) (x : E) :
    average T 0 x = 0 := by
  simp [average]

@[simp] theorem average_one (T : E →L[𝕜] E) (x : E) :
    average T 1 x = x := by
  simp [average]

/-- Mean ergodic convergence in an arbitrary (possibly infinite-dimensional)
Hilbert space.  The target is the orthogonal projection onto the fixed-point
subspace of `T`, coerced back to the ambient space. -/
theorem average_tendsto_projection
    (h : MeanErgodicCertificate T) (x : E) :
    Tendsto (fun n => average T n x) atTop
      (𝓝 (((T.eqLocus (1 : E →L[𝕜] E)).orthogonalProjectionOnto x :
        (T.eqLocus (1 : E →L[𝕜] E))) : E)) := by
  simpa [average] using
    (ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection
      T h.contractive x)

/-- A bounded linear observable can be applied after the Hilbert-space mean
ergodic limit.  This is the common form used for expectation values and
linear-response observables. -/
theorem observable_tendsto_projection
    {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (h : MeanErgodicCertificate T) (O : E →L[𝕜] F) (x : E) :
    Tendsto (fun n => O (average T n x)) atTop
      (𝓝 (O (((T.eqLocus (1 : E →L[𝕜] E)).orthogonalProjectionOnto x :
        (T.eqLocus (1 : E →L[𝕜] E))) : E))) := by
  exact (O.continuous.tendsto _).comp (h.average_tendsto_projection x)

/-- A fixed vector is already its own time average.  This is useful for
checking conserved states before invoking the general projection theorem. -/
theorem average_eq_of_fixed
    {n : ℕ} (hn : (n : 𝕜) ≠ 0) (hfixed : T x = x) :
    average T n x = x := by
  simpa [average] using
    (Function.IsFixedPt.birkhoffAverage_eq
      (R := 𝕜) (f := (T : E → E)) (x := x) (g := id)
      hfixed hn)

end MeanErgodicCertificate

end Hilbert

/-! Spectral-radius limits used in stability and long-time growth arguments. -/

section SpectralRadius

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Gelfand's formula as a reusable convergence certificate.  It records the
actual sequence of operator powers rather than a numerical estimate. -/
theorem spectral_radius_power_limit (a : A) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (‖a ^ n‖ ^ (1 / (n : ℝ)))) atTop
      (𝓝 (spectralRadius ℂ a)) := by
  exact spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a

end SpectralRadius

end LeanPhy.Mathematics
