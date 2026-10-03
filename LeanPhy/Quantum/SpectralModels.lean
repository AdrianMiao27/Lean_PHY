import LeanPhy.Quantum.SpectralDecomposition
import LeanPhy.Quantum.Pauli
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-!
# Concrete finite spectral models

This module supplies a small but reusable spectral witness: the computational
projectors of a qubit.  The same shape is used by spin measurements, two-band
Bloch Hamiltonians and a truncated BdG model.  The projectors and their
completeness are proved entrywise; no spectral theorem or eigenbasis existence
is smuggled into the definition.
-/

namespace LeanPhy.Quantum

open scoped BigOperators Matrix

/-- Projector onto the computational `|0>` mode. -/
def computationalProjector0 : Operator 2 := !![1, 0; 0, 0]

/-- Projector onto the computational `|1>` mode. -/
def computationalProjector1 : Operator 2 := !![0, 0; 0, 1]

/-- The two computational projectors form a complete orthogonal family. -/
noncomputable def computationalSpectralProjectors : SpectralProjectors 2 2 where
  proj := ![computationalProjector0, computationalProjector1]
  idempotent := by
    intro i
    fin_cases i <;>
      ext r c <;> fin_cases r <;> fin_cases c <;>
      simp [computationalProjector0, computationalProjector1, Matrix.mul_apply]
  orthogonal := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      ext r c <;> fin_cases r <;> fin_cases c <;>
      simp_all [computationalProjector0, computationalProjector1, Matrix.mul_apply]
  complete := by
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [computationalProjector0, computationalProjector1, Matrix.add_apply]

theorem pauliZ_spectral_reconstruction :
    spectralOperator computationalSpectralProjectors ![1, -1] = pauliZ := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [spectralOperator, computationalSpectralProjectors,
      computationalProjector0, computationalProjector1, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.add_apply, pauliZ]

theorem pauliZ_plus_projector_eigenvalue :
    (spectralOperator computationalSpectralProjectors ![1, -1]).mulVec
        (fun i : Fin 2 => if i = (0 : Fin 2) then (1 : ℂ) else 0) =
      (1 : ℂ) • (fun i : Fin 2 => if i = (0 : Fin 2) then (1 : ℂ) else 0) := by
  apply spectralOperator_mulVec_of_projector computationalSpectralProjectors
      ![1, -1] 0
  ext i
  fin_cases i <;>
    simp [computationalSpectralProjectors, computationalProjector0,
      Matrix.mulVec, dotProduct]

theorem pauliZ_minus_projector_eigenvalue :
    (spectralOperator computationalSpectralProjectors ![1, -1]).mulVec
        (fun i : Fin 2 => if i = (1 : Fin 2) then (1 : ℂ) else 0) =
      (-1 : ℂ) • (fun i : Fin 2 => if i = (1 : Fin 2) then (1 : ℂ) else 0) := by
  apply spectralOperator_mulVec_of_projector computationalSpectralProjectors
      ![1, -1] 1
  ext i
  fin_cases i <;>
    simp [computationalSpectralProjectors, computationalProjector1,
      Matrix.mulVec, dotProduct]

end LeanPhy.Quantum
