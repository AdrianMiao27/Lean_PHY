import LeanPhy.Quantum.Basic
import LeanPhy.Quantum.Pauli
import LeanPhy.Quantum.Composite
import LeanPhy.Quantum.PartialTrace

/-!
# Bell state and EPR correlations

The Bell state is written unnormalised (`|00⟩ + |11⟩`), so every correlation
below is an exact integer multiple of the normalised value and no square roots
enter the arithmetic.  This keeps the whole module kernel-checked over `ℂ`
while still capturing the physics: perfect `σᵢ ⊗ σᵢ` correlations and
maximally mixed marginals.
-/

namespace LeanPhy.QuantumInfo

open LeanPhy.Quantum
open scoped BigOperators

/-- The unnormalised Bell pair `|00⟩ + |11⟩`. -/
def bell : Fin 2 × Fin 2 → ℂ :=
  fun p => if p.1 = p.2 then 1 else 0

/-- The rank-one operator `|Φ⁺⟩⟨Φ⁺|` for the unnormalised Bell pair. -/
def bellState : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j => bell i * star (bell j)

/-- Joint expectation value `⟨Φ⁺| A ⊗ B |Φ⁺⟩`. -/
noncomputable def bellCorr (A B : Operator 2) : ℂ :=
  ∑ i, ∑ j, star (bell i) * tensorOp A B i j * bell j

theorem bellCorr_xx : bellCorr pauliX pauliX = 2 := by
  simp [bellCorr, bell, tensorOp, Matrix.kroneckerMap_apply, pauliX,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

theorem bellCorr_zz : bellCorr pauliZ pauliZ = 2 := by
  simp [bellCorr, bell, tensorOp, Matrix.kroneckerMap_apply, pauliZ,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

theorem bellCorr_xz : bellCorr pauliX pauliZ = 0 := by
  simp [bellCorr, bell, tensorOp, Matrix.kroneckerMap_apply, pauliX, pauliZ,
    Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Marginal of the Bell pair: tracing out one qubit leaves the maximally mixed
state `I` (up to the normalisation convention used here). -/
theorem partialTrace_bell_marginal :
    partialTraceRight bellState = (1 : Operator 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialTraceRight, bellState, bell]

end LeanPhy.QuantumInfo
