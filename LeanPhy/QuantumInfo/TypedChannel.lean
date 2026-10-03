import LeanPhy.Quantum.FiniteDensity
import LeanPhy.QuantumInfo.KrausBundle
import LeanPhy.Mathematics.FiniteProcess
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Typed finite Kraus channels

The older finite-channel interfaces model an endomorphism of one fixed matrix
space.  Physical constructions such as an environment coupling, a measurement
instrument, a partial trace, or a coarse graining often change the label type.
This file supplies the missing typed layer.  A channel from `ι` to `κ` is a
finite Kraus family of rectangular matrices `Matrix κ ι ℂ`; its completeness
equation lives on the input space.  All statements remain finite-dimensional.
No claim about infinite-dimensional trace-class operators is made.
-/

namespace LeanPhy.QuantumInfo

open LeanPhy.Quantum
open scoped BigOperators Matrix ComplexOrder

/-- The operator-sum action of rectangular Kraus operators.

If `K k : Matrix κ ι ℂ`, then `typedApplyKraus K rho` is a matrix on the
output labels `κ`, for an input state on `ι`.
-/
noncomputable def typedApplyKraus {ι κ ξ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ξ] [DecidableEq ι]
    (K : ξ → Matrix κ ι ℂ) (rho : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  ∑ k, K k * rho * Matrix.conjTranspose (K k)

theorem typedKraus_trace {ι κ ξ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ξ] [DecidableEq ι]
    (K : ξ → Matrix κ ι ℂ) (rho : Matrix ι ι ℂ)
    (htp : (∑ k, Matrix.conjTranspose (K k) * K k) = 1) :
    Matrix.trace (typedApplyKraus K rho) = Matrix.trace rho := by
  unfold typedApplyKraus
  rw [Matrix.trace_sum]
  trans ∑ k, Matrix.trace (Matrix.conjTranspose (K k) * K k * rho)
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  rw [← Matrix.trace_sum]
  have hsum : (∑ k, Matrix.conjTranspose (K k) * K k * rho) =
      (∑ k, Matrix.conjTranspose (K k) * K k) * rho := by
    rw [Finset.sum_mul]
  rw [hsum, htp, Matrix.one_mul]

theorem typedKraus_posSemidef {ι κ ξ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ξ] [DecidableEq ι]
    (K : ξ → Matrix κ ι ℂ) (rho : Matrix ι ι ℂ)
    (hrho : rho.PosSemidef) :
    (typedApplyKraus K rho).PosSemidef := by
  unfold typedApplyKraus
  refine matrix_sum_posSemidef (fun k => K k * rho * Matrix.conjTranspose (K k)) ?_
  intro k
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hrho (K k)

/-- A rectangular finite Kraus family with its input completeness proof. -/
structure TypedKrausChannel (ι κ ξ : Type*)
    [Fintype ι] [Fintype κ] [Fintype ξ] [DecidableEq ι] where
  op : ξ → Matrix κ ι ℂ
  complete : (∑ k, Matrix.conjTranspose (op k) * op k) = 1

noncomputable def TypedKrausChannel.apply {ι κ ξ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ξ] [DecidableEq ι]
    (C : TypedKrausChannel ι κ ξ) (rho : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  typedApplyKraus C.op rho

theorem TypedKrausChannel.trace_preserving {ι κ ξ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ξ] [DecidableEq ι]
    (C : TypedKrausChannel ι κ ξ) (rho : Matrix ι ι ℂ) :
    Matrix.trace (C.apply rho) = Matrix.trace rho :=
  typedKraus_trace C.op rho C.complete

theorem TypedKrausChannel.map_pos {ι κ ξ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ξ] [DecidableEq ι]
    (C : TypedKrausChannel ι κ ξ) (rho : Matrix ι ι ℂ)
    (hrho : rho.PosSemidef) : (C.apply rho).PosSemidef :=
  typedKraus_posSemidef C.op rho hrho

theorem TypedKrausChannel.map_isFiniteDensity {ι κ ξ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ξ] [DecidableEq ι]
    (C : TypedKrausChannel ι κ ξ) (rho : Matrix ι ι ℂ)
    (hrho : IsFiniteDensity rho) :
    IsFiniteDensity (C.apply rho) := by
  have hpos := C.map_pos rho hrho.2.1
  refine ⟨hpos.isHermitian, hpos, ?_⟩
  exact (C.trace_preserving rho).trans hrho.2.2

/- The rectangular channel participates in the same state-map composition API
   as an abstract CPTP map.  The target predicate is checked by the finite
   density theorem above, so a cross-dimensional composition cannot forget
   positivity or trace one. -/
noncomputable def TypedKrausChannel.toStateMap
    {ι κ ξ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ξ] [DecidableEq ι]
    (C : TypedKrausChannel ι κ ξ) :
    LeanPhy.Mathematics.StateMap
      (Matrix ι ι ℂ) (Matrix κ κ ℂ)
      IsFiniteDensity IsFiniteDensity where
  toFun := C.apply
  preserves := fun rho hrho => C.map_isFiniteDensity rho hrho

theorem TypedKrausChannel.map_isNamedDensity {ι κ ξ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ξ] [DecidableEq ι]
    (C : TypedKrausChannel ι κ ξ) (rho : NamedState ι)
    (hrho : IsNamedDensity rho) :
    IsNamedDensity (C.apply rho) :=
  C.map_isFiniteDensity rho hrho

/-! ## Composition across different finite spaces -/

noncomputable def TypedKrausChannel.compose
    {ι κ μ ξ ζ : Type*}
    [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ξ] [Fintype ζ]
    [DecidableEq ι] [DecidableEq κ]
    (after : TypedKrausChannel κ μ ζ)
    (before : TypedKrausChannel ι κ ξ) :
    TypedKrausChannel ι μ (ζ × ξ) where
  op := fun p => after.op p.1 * before.op p.2
  complete := by
    simp only [Fintype.sum_prod_type]
    calc
      (∑ x, ∑ y,
          Matrix.conjTranspose (after.op x * before.op y) *
            (after.op x * before.op y))
          = ∑ y,
              Matrix.conjTranspose (before.op y) *
                (∑ x, Matrix.conjTranspose (after.op x) * after.op x) *
                before.op y := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y hy
        calc
          (∑ x,
              Matrix.conjTranspose (after.op x * before.op y) *
                (after.op x * before.op y))
              = ∑ x,
                  Matrix.conjTranspose (before.op y) *
                    (Matrix.conjTranspose (after.op x) * after.op x) *
                    before.op y := by
            apply Finset.sum_congr rfl
            intro x hx
            simp only [Matrix.conjTranspose_mul]
            simp only [Matrix.mul_assoc]
          _ = Matrix.conjTranspose (before.op y) *
                (∑ x, Matrix.conjTranspose (after.op x) * after.op x) *
                before.op y := by
            calc
              (∑ x, Matrix.conjTranspose (before.op y) *
                  (Matrix.conjTranspose (after.op x) * after.op x) *
                  before.op y) =
                  (∑ x, Matrix.conjTranspose (before.op y) *
                    (Matrix.conjTranspose (after.op x) * after.op x)) *
                  before.op y := by rw [Matrix.sum_mul]
              _ = (Matrix.conjTranspose (before.op y) *
                    (∑ x, Matrix.conjTranspose (after.op x) * after.op x)) *
                    before.op y := by rw [Matrix.mul_sum]
      _ = 1 := by
        rw [after.complete]
        simp [before.complete]

theorem TypedKrausChannel.compose_apply
    {ι κ μ ξ ζ : Type*}
    [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ξ] [Fintype ζ]
    [DecidableEq ι] [DecidableEq κ]
    (after : TypedKrausChannel κ μ ζ)
    (before : TypedKrausChannel ι κ ξ) (rho : Matrix ι ι ℂ) :
    (after.compose before).apply rho = after.apply (before.apply rho) := by
  unfold TypedKrausChannel.compose TypedKrausChannel.apply typedApplyKraus
  simp only [Fintype.sum_prod_type, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ y, after.op x *
        (before.op y * (rho *
          (Matrix.conjTranspose (before.op y) * Matrix.conjTranspose (after.op x))))) =
        after.op x *
          (∑ y, before.op y * (rho *
            (Matrix.conjTranspose (before.op y) * Matrix.conjTranspose (after.op x)))) := by
      rw [Matrix.mul_sum]
    _ = after.op x *
        (∑ y, (before.op y * (rho * Matrix.conjTranspose (before.op y))) *
          Matrix.conjTranspose (after.op x)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      simp only [Matrix.mul_assoc]
    _ = after.op x *
        ((∑ y, before.op y * (rho * Matrix.conjTranspose (before.op y))) *
          Matrix.conjTranspose (after.op x)) := by
      rw [Matrix.sum_mul]

theorem TypedKrausChannel.compose_map_isFiniteDensity
    {ι κ μ ξ ζ : Type*}
    [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ξ] [Fintype ζ]
    [DecidableEq ι] [DecidableEq κ]
    (after : TypedKrausChannel κ μ ζ)
    (before : TypedKrausChannel ι κ ξ) (rho : Matrix ι ι ℂ)
    (hrho : IsFiniteDensity rho) :
    IsFiniteDensity ((after.compose before).apply rho) := by
  exact (after.compose before).map_isFiniteDensity rho hrho

/-! ## Typed Schrödinger/Heisenberg duality -/

/-- Pull an output observable back to the input space by the finite Kraus dual. -/
noncomputable def typedAdjointKraus {ι κ ξ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ξ] [DecidableEq ι]
    (K : ξ → Matrix κ ι ℂ) (A : Matrix κ κ ℂ) : Matrix ι ι ℂ :=
  ∑ k, Matrix.conjTranspose (K k) * A * K k

theorem typedTracePairing {ι κ ξ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ξ] [DecidableEq ι]
    (K : ξ → Matrix κ ι ℂ) (rho : Matrix ι ι ℂ) (A : Matrix κ κ ℂ) :
    Matrix.trace (typedApplyKraus K rho * A) =
      Matrix.trace (rho * typedAdjointKraus K A) := by
  unfold typedApplyKraus typedAdjointKraus
  rw [Matrix.sum_mul, Matrix.trace_sum]
  calc
    (∑ k, Matrix.trace (K k * rho * Matrix.conjTranspose (K k) * A)) =
        ∑ k, Matrix.trace (rho * Matrix.conjTranspose (K k) * A * K k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [show K k * rho * Matrix.conjTranspose (K k) * A =
        (K k * rho) * (Matrix.conjTranspose (K k) * A) by
          simp only [Matrix.mul_assoc]]
      rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (rho * (∑ k,
        Matrix.conjTranspose (K k) * A * K k)) := by
      rw [Matrix.mul_sum, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Matrix.mul_assoc]

theorem typedAdjoint_complete {ι κ ξ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ξ] [DecidableEq ι] [DecidableEq κ]
    (K : ξ → Matrix κ ι ℂ)
    (htp : (∑ k, Matrix.conjTranspose (K k) * K k) = 1) :
    typedAdjointKraus K (1 : Matrix κ κ ℂ) = 1 := by
  unfold typedAdjointKraus
  simpa only [Matrix.mul_one] using htp

theorem TypedKrausChannel.adjoint_unital {ι κ ξ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ξ] [DecidableEq ι] [DecidableEq κ]
    (C : TypedKrausChannel ι κ ξ) :
    typedAdjointKraus C.op (1 : Matrix κ κ ℂ) = 1 :=
  typedAdjoint_complete C.op C.complete

end LeanPhy.QuantumInfo
