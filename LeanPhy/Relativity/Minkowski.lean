import Mathlib.LinearAlgebra.Matrix.Notation

/-! Elementary Minkowski metric identities, with signature (+---). -/

namespace LeanPhy.Relativity

def minkowskiMetric : Matrix (Fin 4) (Fin 4) ℤ := !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

def minkowskiNorm (x : Fin 4 → ℤ) : ℤ :=
  x 0 * x 0 - x 1 * x 1 - x 2 * x 2 - x 3 * x 3

theorem metric_diagonal : minkowskiMetric 0 0 = 1 ∧ minkowskiMetric 1 1 = -1 ∧
    minkowskiMetric 2 2 = -1 ∧ minkowskiMetric 3 3 = -1 := by
  simp [minkowskiMetric]

theorem lightlike_zero (x : Fin 4 → ℤ) (h : minkowskiNorm x = 0) :
    x 0 * x 0 = x 1 * x 1 + x 2 * x 2 + x 3 * x 3 := by
  dsimp [minkowskiNorm] at h
  omega

end LeanPhy.Relativity
