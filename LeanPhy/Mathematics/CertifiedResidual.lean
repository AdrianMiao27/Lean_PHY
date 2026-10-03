import LeanPhy.Mathematics.Approximation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Residual certificates for finite models

Researchers routinely replace an exact equation by a finite or numerical one:
an approximate eigenvector, a truncated mode, a transfer-matrix eigenpair, or
a one-step discretisation of an ODE.  These objects should share one semantic
interface while retaining their physical vocabulary.  The definitions below
all reduce to `ErrorCertificate`, so a proof can compose independent errors
and transport them through a supplied Lipschitz estimate.

No spectral theorem, convergence rate or continuum limit is inferred.  A
residual radius is exactly the bound that the caller supplies.
-/

namespace LeanPhy.Mathematics

universe u v

open scoped Matrix

/-! A reusable equation residual for any map into a pseudometric additive
space. -/

def EquationResidual {X : Type u} {Y : Type v} [PseudoMetricSpace Y] [Zero Y]
    (F : X → Y) (x : X) (ε : ℝ) : Prop :=
  ErrorCertificate.ResidualCertificate (F x) ε

theorem equationResidual_zero {X : Type u} {Y : Type v}
    [PseudoMetricSpace Y] [Zero Y] (F : X → Y) (x : X)
    (h : F x = 0) : EquationResidual F x 0 := by
  exact ErrorCertificate.residual_zero (F x) h

theorem equationResidual_weaken {X : Type u} {Y : Type v}
    [PseudoMetricSpace Y] [Zero Y] {F : X → Y} {x : X} {ε δ : ℝ}
    (h : EquationResidual F x ε) (hεδ : ε ≤ δ) :
    EquationResidual F x δ := by
  exact ErrorCertificate.weaken h hεδ

/-! The standard residual of a finite matrix eigen-equation.  The vector
space carries the usual finite-function pseudometric from mathlib. -/

def MatrixEigenpairResidual {ι : Type u} [Fintype ι]
    (A : Matrix ι ι ℂ) (eigenvalue : ℂ) (v : ι → ℂ) (ε : ℝ) : Prop :=
  EquationResidual (fun x : ι → ℂ => A.mulVec x - eigenvalue • x) v ε

theorem matrixEigenpairResidual_of_eigenpair {ι : Type u} [Fintype ι]
    (A : Matrix ι ι ℂ) (eigenvalue : ℂ) (v : ι → ℂ)
    (h : A.mulVec v = eigenvalue • v) :
    MatrixEigenpairResidual A eigenvalue v 0 := by
  apply equationResidual_zero
  simp [h]

theorem MatrixEigenpairResidual.weaken {ι : Type u} [Fintype ι]
    {A : Matrix ι ι ℂ} {eigenvalue : ℂ} {v : ι → ℂ} {ε δ : ℝ}
    (h : MatrixEigenpairResidual A eigenvalue v ε) (hεδ : ε ≤ δ) :
    MatrixEigenpairResidual A eigenvalue v δ := by
  exact equationResidual_weaken h hεδ

/-! A residual for a one-step discretisation.  `nextState` is compared with
the right-hand side supplied by the model, so the same object covers ODE,
master-equation and iterative solver steps. -/

def StepResidual {X : Type u} [PseudoMetricSpace X] [AddGroup X]
    (nextState rhs : X) (ε : ℝ) : Prop :=
  ErrorCertificate.ResidualCertificate (nextState - rhs) ε

theorem stepResidual_of_eq {X : Type u} [PseudoMetricSpace X]
    [AddGroup X] (nextState rhs : X) (h : nextState = rhs) :
    StepResidual nextState rhs 0 := by
  change ErrorCertificate.ResidualCertificate (nextState - rhs) 0
  apply ErrorCertificate.residual_zero
  simp [h]

theorem stepResidual_weaken {X : Type u} [PseudoMetricSpace X]
    [AddGroup X] {nextState rhs : X} {ε δ : ℝ}
    (h : StepResidual nextState rhs ε) (hεδ : ε ≤ δ) :
    StepResidual nextState rhs δ := by
  change ErrorCertificate.ResidualCertificate (nextState - rhs) ε at h
  change ErrorCertificate.ResidualCertificate (nextState - rhs) δ
  exact ErrorCertificate.weaken h hεδ

end LeanPhy.Mathematics

/-! Physics-facing names for the same residual contracts. -/

namespace LeanPhy

namespace Quantum
abbrev ApproximateEigenpair {ι : Type*} [Fintype ι] :=
  LeanPhy.Mathematics.MatrixEigenpairResidual (ι := ι)
end Quantum

namespace FieldTheory
abbrev ModeEquationResidual {X Y : Type*} [PseudoMetricSpace Y] [Zero Y] :=
  LeanPhy.Mathematics.EquationResidual (X := X) (Y := Y)
end FieldTheory

namespace Condensed
abbrev BdGResidual {ι : Type*} [Fintype ι] :=
  LeanPhy.Mathematics.MatrixEigenpairResidual (ι := ι)
end Condensed

namespace StatMech
abbrev TransferEigenpairResidual {ι : Type*} [Fintype ι] :=
  LeanPhy.Mathematics.MatrixEigenpairResidual (ι := ι)
end StatMech

namespace Classical
abbrev ODEStepResidual {X : Type*} [PseudoMetricSpace X] [AddGroup X] :=
  LeanPhy.Mathematics.StepResidual (X := X)
end Classical

end LeanPhy
