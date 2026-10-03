import LeanPhy.Surface.Variance
import Mathlib.Tactic

open scoped BigOperators

/-!
# Coefficient-generic finite tensors

`TypedTensor` provides a convenient complex-valued surface for quantum and
relativistic calculations.  Finite PDE, classical mechanics, lattice and
numerical models often use `ℝ`, a rational field, or an abstract coefficient
ring instead.  This module keeps the variance tags while making the scalar
type an explicit parameter.  No metric or analytic structure is introduced:
the layer is only finite index algebra.

The existing `Tensor2N`/`TensorUDN` names remain unchanged for source
compatibility.  New code that must work over several coefficient fields can
use `Tensor2Over` and its mixed composition/trace operations.
-/

namespace LeanPhy.Tensor

universe u

/-- A rank-two finite tensor over an explicit coefficient type.  Variance is
part of the type, so operations can reject an invalid contraction before
proof search. -/
structure Tensor2Over (R : Type u) (n : Nat)
    (left right : VarianceTag) where
  val : Fin n → Fin n → R

instance (R : Type u) (n : Nat) (left right : VarianceTag) :
    CoeFun (Tensor2Over R n left right) (fun _ => Fin n → Fin n → R) :=
  ⟨Tensor2Over.val⟩

abbrev TensorUUOver (R : Type u) (n : Nat) := Tensor2Over R n .up .up
abbrev TensorUDOver (R : Type u) (n : Nat) := Tensor2Over R n .up .down
abbrev TensorDUOver (R : Type u) (n : Nat) := Tensor2Over R n .down .up
abbrev TensorDDOver (R : Type u) (n : Nat) := Tensor2Over R n .down .down

variable {R : Type u} {n : Nat}

/-- Mixed composition `A^i_j B^j_k` over any commutative semiring. -/
noncomputable def composeMixedOver [Fintype (Fin n)] [CommSemiring R]
    (A B : TensorUDOver R n) : TensorUDOver R n :=
  ⟨fun i k => ∑ j, A i j * B j k⟩

/-- The mixed identity `δ^i_j` over the selected coefficient type. -/
noncomputable def mixedIdentityOver [Fintype (Fin n)] [CommSemiring R] :
    TensorUDOver R n :=
  ⟨fun i j => if i = j then 1 else 0⟩

/-- The finite mixed trace over the selected coefficient type. -/
noncomputable def mixedTraceOver [Fintype (Fin n)] [CommSemiring R]
    (T : TensorUDOver R n) : R :=
  ∑ i, T i i

theorem composeMixedOver_assoc [Fintype (Fin n)] [CommSemiring R]
    (A B C : TensorUDOver R n) :
    composeMixedOver (composeMixedOver A B) C =
      composeMixedOver A (composeMixedOver B C) := by
  apply congrArg Tensor2Over.mk
  funext i k
  simp only [composeMixedOver]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [mul_assoc]

theorem composeMixedOver_identity_left [Fintype (Fin n)] [CommSemiring R]
    (A : TensorUDOver R n) :
    composeMixedOver (mixedIdentityOver (R := R) (n := n)) A = A := by
  apply congrArg Tensor2Over.mk
  funext i k
  simp [mixedIdentityOver]

theorem composeMixedOver_identity_right [Fintype (Fin n)] [CommSemiring R]
    (A : TensorUDOver R n) :
    composeMixedOver A (mixedIdentityOver (R := R) (n := n)) = A := by
  apply congrArg Tensor2Over.mk
  funext i k
  simp [mixedIdentityOver]

theorem mixedTraceOver_comp_comm [Fintype (Fin n)] [CommSemiring R]
    (A B : TensorUDOver R n) :
    mixedTraceOver (composeMixedOver A B) =
      mixedTraceOver (composeMixedOver B A) := by
  simp only [mixedTraceOver, composeMixedOver]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  exact mul_comm _ _

/-! The variance boundary is intentionally visible in generic code as well. -/

/-- A mixed tensor can act on an upper vector by contracting its lower slot. -/
noncomputable def actUpOver [Fintype (Fin n)] [CommSemiring R]
    (T : TensorUDOver R n) (v : Fin n → R) : Fin n → R :=
  fun i => ∑ j, T i j * v j

theorem actUpOver_comp [Fintype (Fin n)] [CommSemiring R]
    (A B : TensorUDOver R n) (v : Fin n → R) :
    actUpOver (composeMixedOver A B) v =
      actUpOver A (actUpOver B v) := by
  funext i
  simp only [actUpOver, composeMixedOver]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [mul_assoc]

/- The same-variance contraction is rejected by the type checker. -/

/-- error: Application type mismatch: The argument
  T
has type
  TensorUUOver R n
but is expected to have type
  TensorUDOver R n
in the application
  mixedTraceOver T -/
#guard_msgs (error) in
example [Fintype (Fin n)] [CommSemiring R] (T : TensorUUOver R n) :
    mixedTraceOver (R := R) (n := n) T = 0 := rfl

end LeanPhy.Tensor
