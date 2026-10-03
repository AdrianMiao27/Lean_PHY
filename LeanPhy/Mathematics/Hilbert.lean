import LeanPhy.Mathematics.Approximation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Hilbert-space operator bridge

Most of the executable examples in LeanPhy use finite matrices.  Research
arguments also need a basis-free layer for wavefunctions, scattering states,
band subspaces and truncated field modes.  This file exposes the small part of
that interface already developed in mathlib: continuous linear operators on a
complete inner-product space, their adjoints, self-adjointness and unitarity.

The bridge deliberately does not define an unbounded operator, a spectral
measure, a domain, or a time-evolution theorem.  Those analytic obligations
remain visible to the caller.  Finite matrices can still be viewed as bounded
operators on a finite function space through `matrixOperator`.
-/

namespace LeanPhy.Mathematics

namespace Hilbert

open scoped ComplexConjugate

universe u v

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A bounded self-adjoint operator with the adjoint equation stored as an
invariant.  The use of `ContinuousLinearMap` makes boundedness explicit. -/
structure SelfAdjoint where
  op : E →L[𝕜] E
  selfAdjoint : ContinuousLinearMap.adjoint op = op

namespace SelfAdjoint

variable (A : SelfAdjoint (𝕜 := 𝕜) (E := E))

/-- The vector-state expectation of a bounded operator. -/
def expectation (ψ : E) : 𝕜 := inner 𝕜 ψ (A.op ψ)

theorem expectation_conjugate (ψ : E) :
    star (A.expectation ψ) = A.expectation ψ := by
  unfold expectation
  calc
    star (inner 𝕜 ψ (A.op ψ)) = inner 𝕜 (A.op ψ) ψ := by
      simpa using (inner_conj_symm (A.op ψ) ψ)
    _ = inner 𝕜 ((ContinuousLinearMap.adjoint A.op) ψ) ψ := by
      rw [A.selfAdjoint]
    _ = inner 𝕜 ψ (A.op ψ) := A.op.adjoint_inner_left ψ ψ

theorem expectation_re_im_zero (ψ : E) :
    RCLike.im (A.expectation ψ) = 0 := by
  have h := congrArg RCLike.im (A.expectation_conjugate ψ)
  simp only [RCLike.star_def, RCLike.conj_im] at h
  linarith

end SelfAdjoint

/-- A bounded unitary operator.  Both inverse equations are retained so the
interface remains valid on infinite-dimensional Hilbert spaces; a one-sided
isometry is not silently promoted to a surjective unitary. -/
structure Unitary where
  op : E →L[𝕜] E
  left_unitary : ContinuousLinearMap.adjoint op ∘SL op = 1
  right_unitary : op ∘SL ContinuousLinearMap.adjoint op = 1

namespace Unitary

variable (U : Unitary (𝕜 := 𝕜) (E := E))

theorem inner_preserved (x y : E) :
    inner 𝕜 (U.op x) (U.op y) = inner 𝕜 x y := by
  calc
    inner 𝕜 (U.op x) (U.op y) =
        inner 𝕜 x ((ContinuousLinearMap.adjoint U.op) (U.op y)) := by
      symm
      exact U.op.adjoint_inner_right x (U.op y)
    _ = inner 𝕜 x ((ContinuousLinearMap.adjoint U.op ∘SL U.op) y) := by
      rfl
    _ = inner 𝕜 x y := by
      rw [U.left_unitary]
      rfl

theorem norm_preserved (x : E) : ‖U.op x‖ = ‖x‖ := by
  have hsq : ‖U.op x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜),
      U.inner_preserved, ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜)]
  nlinarith [norm_nonneg (U.op x), norm_nonneg x]

noncomputable def adjoint : Unitary (𝕜 := 𝕜) (E := E) where
  op := ContinuousLinearMap.adjoint U.op
  left_unitary := by
    rw [ContinuousLinearMap.adjoint_adjoint]
    exact U.right_unitary
  right_unitary := by
    rw [ContinuousLinearMap.adjoint_adjoint]
    exact U.left_unitary

@[simp] theorem adjoint_op : U.adjoint.op = ContinuousLinearMap.adjoint U.op := rfl

noncomputable def compose (after before : Unitary (𝕜 := 𝕜) (E := E)) :
    Unitary (𝕜 := 𝕜) (E := E) where
  op := after.op ∘SL before.op
  left_unitary := by
    rw [ContinuousLinearMap.adjoint_comp]
    ext x
    calc
      (ContinuousLinearMap.adjoint before.op)
          ((ContinuousLinearMap.adjoint after.op) (after.op (before.op x))) =
          (ContinuousLinearMap.adjoint before.op)
            ((ContinuousLinearMap.adjoint after.op ∘SL after.op) (before.op x)) := by
              rfl
      _ = (ContinuousLinearMap.adjoint before.op) (before.op x) := by
        rw [after.left_unitary]
        rfl
      _ = (1 : E →L[𝕜] E) x := by
        rw [← ContinuousLinearMap.comp_apply]
        rw [before.left_unitary]
  right_unitary := by
    rw [ContinuousLinearMap.adjoint_comp]
    ext x
    calc
      (after.op ∘SL before.op)
          ((ContinuousLinearMap.adjoint before.op) ((ContinuousLinearMap.adjoint after.op) x)) =
          after.op ((before.op ∘SL ContinuousLinearMap.adjoint before.op)
            ((ContinuousLinearMap.adjoint after.op) x)) := by
              rfl
      _ = after.op ((ContinuousLinearMap.adjoint after.op) x) := by
        rw [before.right_unitary]
        rfl
      _ = (1 : E →L[𝕜] E) x := by
        rw [← ContinuousLinearMap.comp_apply]
        rw [after.right_unitary]

@[simp] theorem compose_op (after before : Unitary (𝕜 := 𝕜) (E := E)) :
    (compose after before).op = after.op ∘SL before.op := rfl

end Unitary

/-! A bounded-operator evolution interface.  It deliberately stores only the
algebraic semigroup laws; continuity, differentiability, positivity and
generator/domain statements remain separate certificates. -/

structure Flow where
  op : ℝ → E →L[𝕜] E
  zero : op 0 = 1
  add : ∀ t s, op (t + s) = op t ∘SL op s

namespace Flow

variable (F : Flow (𝕜 := 𝕜) (E := E))

@[simp] theorem op_zero : F.op 0 = 1 := F.zero

theorem op_add (t s : ℝ) : F.op (t + s) = F.op t ∘SL F.op s := F.add t s

def evolve (t : ℝ) (x : E) : E := F.op t x

@[simp] theorem evolve_zero (x : E) : F.evolve 0 x = x := by
  unfold evolve
  rw [F.zero]
  rfl

theorem evolve_add (t s : ℝ) (x : E) :
    F.evolve (t + s) x = F.evolve t (F.evolve s x) := by
  unfold evolve
  rw [F.add]
  rfl

end Flow

/-! **Explicit norm envelopes for bounded flows.**  A semigroup law alone does
    not provide stability.  This certificate keeps a time-dependent operator
    norm envelope visible, and derives the corresponding state and composition
    bounds without assuming differentiability, positivity or a generator. -/

structure FlowNormCertificate (F : Flow (𝕜 := 𝕜) (E := E))
    (bound : ℝ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ bound t
  op_le : ∀ t, ‖F.op t‖ ≤ bound t

namespace FlowNormCertificate

variable {F : Flow (𝕜 := 𝕜) (E := E)} {bound : ℝ → ℝ}

theorem one_le_bound_zero (h : FlowNormCertificate F bound)
    [NontrivialTopology E] :
    1 ≤ bound 0 := by
  have hz := h.op_le 0
  rw [F.op_zero] at hz
  change ‖ContinuousLinearMap.id 𝕜 E‖ ≤ bound 0 at hz
  rw [ContinuousLinearMap.norm_id] at hz
  exact hz

theorem evolve_norm_le (h : FlowNormCertificate F bound) (t : ℝ) (x : E) :
    ‖F.evolve t x‖ ≤ bound t * ‖x‖ := by
  exact (ContinuousLinearMap.le_opNorm (F.op t) x).trans
    (mul_le_mul_of_nonneg_right (h.op_le t) (norm_nonneg x))

theorem op_add_le (h : FlowNormCertificate F bound) (t s : ℝ) :
    ‖F.op (t + s)‖ ≤ bound t * bound s := by
  rw [F.op_add]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (h.op_le t) (h.op_le s) (norm_nonneg _) (h.nonneg t))

end FlowNormCertificate

/-! A finite matrix can be viewed as a bounded operator on the finite
function space `ι → ℂ`.  The application theorem is the bridge used by
future basis-free adapters. -/

noncomputable def matrixOperator {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  (Matrix.toLin' A).toContinuousLinearMap

@[simp] theorem matrixOperator_apply {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    matrixOperator A v = A.mulVec v := by
  change (Matrix.toLin' A) v = _
  exact Matrix.toLin'_apply A v

end Hilbert

end LeanPhy.Mathematics

/-! Physics-facing aliases.  They expose the continuous layer without forcing
finite-dimensional users to leave the `Quantum` namespace. -/

namespace LeanPhy.Quantum

abbrev HilbertSelfAdjoint {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :=
  LeanPhy.Mathematics.Hilbert.SelfAdjoint (𝕜 := 𝕜) (E := E)

abbrev HilbertUnitary {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :=
  LeanPhy.Mathematics.Hilbert.Unitary (𝕜 := 𝕜) (E := E)

end LeanPhy.Quantum
