import LeanPhy.Mathematics.LinearFlow
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Invariants of finite linear flows

Quantum Heisenberg conservation, a conserved quadratic mode of a BdG block,
an invariant of a transfer matrix, and a symmetry of a finite classical linear
system all share the same finite algebraic core: an observable commutes with
the propagator, and the propagator has a checked inverse.  This module exposes
that core independently of a physical interpretation.

The statements are deliberately conditional.  A `FiniteMatrixFlow` records
zero-time and composition only; the invariant theorem below additionally asks
for a two-sided inverse law and a commutation certificate.  No differentiability,
stability, positivity, spectral completeness or continuum limit is inferred.
-/

namespace LeanPhy.Mathematics

open NormedSpace
open scoped Matrix Matrix.Norms.Operator

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]

namespace FiniteMatrixFlow

variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-! A finite Heisenberg-style conjugation for an evolution family. -/

def conjugate (F : FiniteMatrixFlow (𝕜 := 𝕜) ι) (t : ℝ)
    (O : Matrix ι ι 𝕜) : Matrix ι ι 𝕜 :=
  F.flow t * O * F.flow (-t)

def IsInvariant (F : FiniteMatrixFlow (𝕜 := 𝕜) ι) (O : Matrix ι ι 𝕜) : Prop :=
  ∀ t : ℝ, F.conjugate t O = O

theorem conjugate_of_commute_of_inverse
    (F : FiniteMatrixFlow (𝕜 := 𝕜) ι) (O : Matrix ι ι 𝕜)
    (hcomm : ∀ t : ℝ, F.flow t * O = O * F.flow t)
    (hinv : ∀ t : ℝ, F.flow t * F.flow (-t) = 1) :
    F.IsInvariant O := by
  intro t
  unfold conjugate
  rw [hcomm t, Matrix.mul_assoc, hinv t, Matrix.mul_one]

/-! The matrix exponential gives the commutation certificate automatically when
its generator commutes with the observable. -/

theorem exponential_isInvariant_of_commute
    (A O : Matrix ι ι 𝕜) (hAO : Commute A O) :
    (FiniteMatrixFlow.exponential A).IsInvariant O := by
  apply conjugate_of_commute_of_inverse (FiniteMatrixFlow.exponential A) O
  · intro t
    rw [FiniteMatrixFlow.exponential_flow]
    have hscaled : Commute ((algebraMap ℝ 𝕜 t) • A) O :=
      hAO.smul_left (algebraMap ℝ 𝕜 t)
    exact hscaled.exp_left.eq
  · intro t
    exact FiniteMatrixFlow.exponential_mul_neg A t

@[simp] theorem exponential_conjugate_of_commute
    (A O : Matrix ι ι 𝕜) (hAO : Commute A O) (t : ℝ) :
    (FiniteMatrixFlow.exponential A).conjugate t O = O :=
  (exponential_isInvariant_of_commute A O hAO) t

end FiniteMatrixFlow

end LeanPhy.Mathematics

/-! Physics-facing names keep the shared theorem discoverable without making
the common layer depend on any one subject. -/

namespace LeanPhy
namespace Quantum
abbrev FlowInvariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Mathematics.FiniteMatrixFlow (𝕜 := ℂ) ι) (O : Matrix ι ι ℂ) : Prop :=
  F.IsInvariant O
end Quantum

namespace Classical
abbrev LinearFlowInvariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Mathematics.FiniteMatrixFlow (𝕜 := ℝ) ι) (O : Matrix ι ι ℝ) : Prop :=
  F.IsInvariant O
end Classical

namespace Condensed
abbrev BdGFlowInvariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Mathematics.FiniteMatrixFlow (𝕜 := ℂ) ι) (O : Matrix ι ι ℂ) : Prop :=
  F.IsInvariant O
end Condensed

namespace StatMech
abbrev TransferFlowInvariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Mathematics.FiniteMatrixFlow (𝕜 := ℝ) ι) (O : Matrix ι ι ℝ) : Prop :=
  F.IsInvariant O
end StatMech

namespace FieldTheory
abbrev FiniteModeFlowInvariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Mathematics.FiniteMatrixFlow (𝕜 := ℂ) ι) (O : Matrix ι ι ℂ) : Prop :=
  F.IsInvariant O
end FieldTheory

end LeanPhy
