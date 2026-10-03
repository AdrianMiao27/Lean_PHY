import LeanPhy.Surface.Variance
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# Generic finite-dimensional typed tensors

`Surface.Variance` supplies the four-dimensional Lorentz metric.  This file
contains the dimension-parametric algebraic part: rank-two tensors over any
finite `Fin n`, with variance tags, typed mixed composition and typed traces.
No metric is assumed here, so the same API applies to colour, lattice, band,
and finite Hilbert-space indices.  Metric-dependent raising/lowering remains
in the four-dimensional module where its convention is explicit.
-/

namespace LeanPhy.Tensor

/-- A rank-two tensor over `Fin n`; the variance of each slot is part of its type. -/
structure Tensor2N (n : Nat) (left right : VarianceTag) where
  val : Fin n → Fin n → ℂ

instance (n : Nat) (left right : VarianceTag) : CoeFun (Tensor2N n left right)
    (fun _ => Fin n → Fin n → ℂ) := ⟨Tensor2N.val⟩

abbrev TensorUUN (n : Nat) := Tensor2N n .up .up
abbrev TensorUDN (n : Nat) := Tensor2N n .up .down
abbrev TensorDUN (n : Nat) := Tensor2N n .down .up
abbrev TensorDDN (n : Nat) := Tensor2N n .down .down

/-- Mixed composition `A^i_j B^j_k` in arbitrary finite dimension. -/
noncomputable def composeMixedN {n : Nat} (A B : TensorUDN n) : TensorUDN n :=
  ⟨fun i k => ∑ j, A i j * B j k⟩

/-- The dimension-parametric mixed identity `delta^i_j`. -/
noncomputable def mixedIdentityN (n : Nat) : TensorUDN n :=
  ⟨fun i j => if i = j then 1 else 0⟩

/-- Mixed trace in arbitrary finite dimension. -/
noncomputable def mixedTraceN {n : Nat} (T : TensorUDN n) : ℂ := ∑ i, T i i

theorem composeMixedN_assoc {n : Nat} (A B C : TensorUDN n) :
    composeMixedN (composeMixedN A B) C = composeMixedN A (composeMixedN B C) := by
  apply congrArg Tensor2N.mk
  funext i k
  simp only [composeMixedN]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem composeMixedN_identity_left {n : Nat} (A : TensorUDN n) :
    composeMixedN (mixedIdentityN n) A = A := by
  apply congrArg Tensor2N.mk
  funext i k
  simp [composeMixedN, mixedIdentityN]

theorem composeMixedN_identity_right {n : Nat} (A : TensorUDN n) :
    composeMixedN A (mixedIdentityN n) = A := by
  apply congrArg Tensor2N.mk
  funext i k
  simp [composeMixedN, mixedIdentityN]

theorem mixedTraceN_comp_comm {n : Nat} (A B : TensorUDN n) :
    mixedTraceN (composeMixedN A B) = mixedTraceN (composeMixedN B A) := by
  simp [mixedTraceN, composeMixedN]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! The variance tags are checked before proof search. -/

/-- error: Application type mismatch: The argument
  T
has type
  TensorUUN n
but is expected to have type
  TensorUDN ?m.1
in the application
  mixedTraceN T -/
#guard_msgs (error) in
example {n : Nat} (T : TensorUUN n) : mixedTraceN T = 0 := rfl

end LeanPhy.Tensor
