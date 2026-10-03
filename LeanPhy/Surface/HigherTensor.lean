import LeanPhy.Surface.TypedTensor
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# Higher-rank finite tensors with variance-safe contractions

Rank-two mixed tensors are enough for matrix-like objects, but research
calculations routinely use rank-three structure constants and rank-four
response/curvature tensors.  This module extends the same type-level variance
discipline to those ranks.  The index set is finite, so every contraction is a
finite sum checked by the Lean kernel.  Differential geometry and continuum
integrals remain separate layers.
-/

namespace LeanPhy.Tensor

open scoped BigOperators

/-- A rank-one finite tensor whose variance is carried by its type. -/
structure Tensor1N (n : Nat) (v : VarianceTag) where
  val : Fin n → ℂ

instance (n : Nat) (v : VarianceTag) : CoeFun (Tensor1N n v) (fun _ => Fin n → ℂ) :=
  ⟨Tensor1N.val⟩

abbrev VecUpN (n : Nat) := Tensor1N n .up
abbrev VecDownN (n : Nat) := Tensor1N n .down

/-- A rank-three finite tensor with type-level variance in all slots. -/
structure Tensor3N (n : Nat) (a b c : VarianceTag) where
  val : Fin n → Fin n → Fin n → ℂ

instance (n : Nat) (a b c : VarianceTag) :
    CoeFun (Tensor3N n a b c) (fun _ => Fin n → Fin n → Fin n → ℂ) :=
  ⟨Tensor3N.val⟩

abbrev TensorUUUN (n : Nat) := Tensor3N n .up .up .up
abbrev TensorUUDN (n : Nat) := Tensor3N n .up .up .down
abbrev TensorUDUN (n : Nat) := Tensor3N n .up .down .up
abbrev TensorUDDN (n : Nat) := Tensor3N n .up .down .down

/-- A rank-four finite tensor with type-level variance in all slots. -/
structure Tensor4N (n : Nat) (a b c d : VarianceTag) where
  val : Fin n → Fin n → Fin n → Fin n → ℂ

instance (n : Nat) (a b c d : VarianceTag) :
    CoeFun (Tensor4N n a b c d)
      (fun _ => Fin n → Fin n → Fin n → Fin n → ℂ) :=
  ⟨Tensor4N.val⟩

abbrev TensorUDUDN (n : Nat) := Tensor4N n .up .down .up .down
abbrev TensorUUDDN (n : Nat) := Tensor4N n .up .up .down .down

/-- Swap the first two slots, including their variance tags. -/
noncomputable def permute12 {n : Nat} {a b c : VarianceTag}
    (T : Tensor3N n a b c) : Tensor3N n b a c :=
  ⟨fun i j k => T j i k⟩

/-- Swap the last two slots, including their variance tags. -/
noncomputable def permute23 {n : Nat} {a b c : VarianceTag}
    (T : Tensor3N n a b c) : Tensor3N n a c b :=
  ⟨fun i j k => T i k j⟩

theorem permute12_involutive {n : Nat} {a b c : VarianceTag}
    (T : Tensor3N n a b c) : permute12 (permute12 T) = T := by
  apply congrArg Tensor3N.mk
  funext i j k
  rfl

theorem permute23_involutive {n : Nat} {a b c : VarianceTag}
    (T : Tensor3N n a b c) : permute23 (permute23 T) = T := by
  apply congrArg Tensor3N.mk
  funext i j k
  rfl

/-- Contract an upper first index with a lower second index. -/
noncomputable def contract12 {n : Nat} {c : VarianceTag}
    (T : Tensor3N n .up .down c) : Tensor1N n c :=
  ⟨fun k => ∑ i, T i i k⟩

/-- Contract an upper second index with a lower third index. -/
noncomputable def contract23 {n : Nat} {a : VarianceTag}
    (T : Tensor3N n a .up .down) : Tensor1N n a :=
  ⟨fun i => ∑ j, T i j j⟩

/-- Kronecker insertion of a vector into a rank-three tensor. -/
noncomputable def deltaInsert12 {n : Nat} {c : VarianceTag}
    (v : Tensor1N n c) : Tensor3N n .up .down c :=
  ⟨fun i j k => if i = j then v k else 0⟩

theorem contract12_deltaInsert12 {n : Nat} {c : VarianceTag}
    (v : Tensor1N n c) :
    contract12 (deltaInsert12 v) =
      ⟨fun k => (n : ℂ) * v k⟩ := by
  apply congrArg Tensor1N.mk
  funext k
  simp [contract12, deltaInsert12]

theorem contract23_deltaInsert23 {n : Nat} {a : VarianceTag}
    (v : Tensor1N n a) :
    (contract23 (⟨fun i j k => if j = k then v i else 0⟩
      : Tensor3N n a .up .down)) =
      ⟨fun i => (n : ℂ) * v i⟩ := by
  apply congrArg Tensor1N.mk
  funext i
  simp [contract23]

/-- Double contraction of a `T^i_j^k_l` tensor. -/
noncomputable def contract12_34 {n : Nat}
    (T : TensorUDUDN n) : ℂ := ∑ i, ∑ k, T i i k k

/-- The alternative order of finite double contraction is equal. -/
theorem contract12_34_swap {n : Nat} (T : TensorUDUDN n) :
    contract12_34 T = ∑ k, ∑ i, T i i k k := by
  simp only [contract12_34]
  rw [Finset.sum_comm]

/-- Contract slots one and three, producing a mixed rank-two tensor. -/
noncomputable def contract13 {n : Nat} {b d : VarianceTag}
    (T : Tensor4N n .up b .down d) : Tensor2N n b d :=
  ⟨fun j l => ∑ i, T i j i l⟩

theorem contract13_apply {n : Nat} {b d : VarianceTag}
    (T : Tensor4N n .up b .down d) :
    contract13 T =
      ⟨fun j l => ∑ i, T i j i l⟩ := rfl

/-! The following rejected term documents the main safety property: a tensor
with two upper first slots cannot be passed to `contract12`. -/

/-- error: Application type mismatch: The argument
  T
has type
  Tensor3N n VarianceTag.up VarianceTag.up VarianceTag.down
but is expected to have type
  Tensor3N n VarianceTag.up VarianceTag.down VarianceTag.down
in the application
  contract12 T -/
#guard_msgs (error) in
noncomputable example {n : Nat} (T : Tensor3N n .up .up .down) : Tensor1N n .down :=
  contract12 T

end LeanPhy.Tensor
