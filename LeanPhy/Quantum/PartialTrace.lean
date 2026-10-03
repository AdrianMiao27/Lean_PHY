import LeanPhy.Quantum.Basic
import LeanPhy.Quantum.Composite

/-!
# Partial trace

For a state on a bipartite space `Fin m × Fin n`, the partial trace over the
second factor is defined entrywise.  This is the operation that produces
reduced density matrices, so it is the piece of quantum-information calculus
that proofs about entanglement depend on.
-/

namespace LeanPhy.Quantum

open scoped BigOperators

/-- Trace over the second tensor factor. -/
noncomputable def partialTraceRight {m n : Nat}
    (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : Operator m :=
  fun i j => ∑ k, ρ (i, k) (j, k)

/-- Trace over the first tensor factor. -/
noncomputable def partialTraceLeft {m n : Nat}
    (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : Operator n :=
  fun k l => ∑ i, ρ (i, k) (i, l)

theorem partialTraceRight_add {m n : Nat}
    (ρ σ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    partialTraceRight (ρ + σ) = partialTraceRight ρ + partialTraceRight σ := by
  ext i j
  simp [partialTraceRight, Matrix.add_apply, Finset.sum_add_distrib]

/-- The partial trace preserves the total trace: it is trace-preserving as a
map on bipartite operators. -/
theorem trace_partialTraceRight {m n : Nat}
    (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    Matrix.trace (partialTraceRight ρ) = Matrix.trace ρ := by
  simp [partialTraceRight, Matrix.trace, Fintype.sum_prod_type]

end LeanPhy.Quantum
