import LeanPhy.Quantum.Projector
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LeanPhy.Quantum
open scoped BigOperators Matrix

/-- A finite complete family of pairwise orthogonal projectors.  This is the
algebraic input to a finite spectral decomposition; existence of such a family
for an arbitrary operator is deliberately not asserted. -/
structure SpectralProjectors (n m : Nat) where
  proj : Fin m → Operator n
  idempotent : ∀ i, proj i * proj i = proj i
  orthogonal : ∀ i j, i ≠ j → proj i * proj j = 0
  complete : ∑ i, proj i = 1

/-- The operator with eigenvalue `e i` on the range of projector `P_i`. -/
def spectralOperator {n m : Nat} (S : SpectralProjectors n m)
    (e : Fin m → ℂ) : Operator n :=
  ∑ i, e i • S.proj i

theorem spectralOperator_mul_projector {n m : Nat}
    (S : SpectralProjectors n m) (e : Fin m → ℂ) (j : Fin m) :
    spectralOperator S e * S.proj j = e j • S.proj j := by
  unfold spectralOperator
  rw [Finset.sum_mul]
  rw [Finset.sum_eq_single j]
  · simp only [Matrix.smul_mul, S.idempotent]
  · intro i hi hij
    rw [Matrix.smul_mul, S.orthogonal i j hij, smul_zero]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

theorem projector_mul_spectralOperator {n m : Nat}
    (S : SpectralProjectors n m) (e : Fin m → ℂ) (j : Fin m) :
    S.proj j * spectralOperator S e = e j • S.proj j := by
  unfold spectralOperator
  rw [Matrix.mul_sum]
  rw [Finset.sum_eq_single j]
  · simp only [Matrix.mul_smul, S.idempotent]
  · intro i hi hij
    rw [Matrix.mul_smul, S.orthogonal j i (Ne.symm hij), smul_zero]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- Every projector range is an eigenspace of the reconstructed operator. -/
theorem spectralOperator_mulVec_of_projector
    {n m : Nat} (S : SpectralProjectors n m) (e : Fin m → ℂ)
    (j : Fin m) (v : Ket n) (hv : (S.proj j).mulVec v = v) :
    (spectralOperator S e).mulVec v = e j • v := by
  calc
    (spectralOperator S e).mulVec v =
        (spectralOperator S e).mulVec ((S.proj j).mulVec v) := by rw [hv]
    _ = (spectralOperator S e * S.proj j).mulVec v := by
      rw [Matrix.mulVec_mulVec]
    _ = (e j • S.proj j).mulVec v := by rw [spectralOperator_mul_projector]
    _ = e j • v := by rw [Matrix.smul_mulVec, hv]

/-- The reconstructed operator acts as the eigenvalue on any vector in a
projector range, which is the useful finite-dimensional spectral rule. -/
theorem spectralOperator_mulVec_of_projector'
    {n m : Nat} (S : SpectralProjectors n m) (e : Fin m → ℂ)
    (j : Fin m) (v : Ket n) (hv : (S.proj j).mulVec v = v) :
    (spectralOperator S e).mulVec v = (e j) • v :=
  spectralOperator_mulVec_of_projector S e j v hv

end LeanPhy.Quantum
