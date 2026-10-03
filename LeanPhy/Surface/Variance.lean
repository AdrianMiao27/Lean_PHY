import LeanPhy.Relativity.Minkowski
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# Variance-aware four-vectors

A recurring source of silent errors in handwritten relativistic and field-theory
calculations is contracting two upper indices or two lower indices.  The existing
finite-index elaborator checks that an index is finite, but it does not yet track
variance.  This module introduces the smallest useful typed layer:

* `UpVec` and `DownVec` are distinct types, both four-component complex vectors;
* `lower : UpVec -> DownVec` and `raise : DownVec -> UpVec` use the explicit
  `(+---)` metric and are inverse maps;
* `contractUD` accepts an upper and a lower vector, while the opposite order has
  its own `contractDU`; there is intentionally no `contractUU` or `contractDD`;
* `minkowski` is the common physical contraction `x^mu y_mu`, with the explicit
  component formula and symmetry proved.

The type distinction catches variance mistakes before a proof is attempted.  The
metric convention and the fact that raising/lowering are inverse are explicit
algebraic assumptions encoded by the matrix `eta`; no differential geometry or
coordinate charts are hidden here.  A future tensor elaborator can generalise the
same pattern to indexed rank-2 tensors and automatic Einstein contraction.
-/

namespace LeanPhy.Tensor

open scoped BigOperators Matrix

/-- Four complex components with an upper Lorentz index. -/
abbrev V4 := Fin 4 → ℂ

/-- A contravariant four-vector. -/
structure UpVec where
  val : V4

/-- A covariant four-vector.  This is a different type from `UpVec` on purpose. -/
structure DownVec where
  val : V4

instance : CoeFun UpVec (fun _ => V4) := ⟨UpVec.val⟩
instance : CoeFun DownVec (fun _ => V4) := ⟨DownVec.val⟩

instance : Add UpVec := ⟨fun x y => ⟨x.val + y.val⟩⟩
instance : Add DownVec := ⟨fun x y => ⟨x.val + y.val⟩⟩

/-- The `(+---)` metric, now in the same coefficient field as the vectors. -/
noncomputable def eta : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

/-- Lower an upper index with `eta`. -/
noncomputable def lower (x : UpVec) : DownVec := ⟨eta *ᵥ x.val⟩

/-- Raise a lower index with `eta`. -/
noncomputable def raise (x : DownVec) : UpVec := ⟨eta *ᵥ x.val⟩

/-- Contract one upper and one lower vector. -/
noncomputable def contractUD (x : UpVec) (y : DownVec) : ℂ := ∑ μ, x μ * y μ

/-- The same contraction with the variance order reversed. -/
noncomputable def contractDU (x : DownVec) (y : UpVec) : ℂ := ∑ μ, x μ * y μ

/-- The Minkowski scalar product `x^mu y_mu`. -/
noncomputable def minkowski (x y : UpVec) : ℂ := contractUD x (lower y)

/-- Raising after lowering is the identity because `eta^2 = 1`. -/
theorem raise_lower (x : UpVec) : raise (lower x) = x := by
  cases x with
  | mk xv =>
    apply congrArg UpVec.mk
    funext μ
    fin_cases μ <;>
      simp [raise, lower, eta, Matrix.mul_apply, Fin.sum_univ_four] <;> rfl

/-- Lowering after raising is the identity. -/
theorem lower_raise (x : DownVec) : lower (raise x) = x := by
  cases x with
  | mk xv =>
    apply congrArg DownVec.mk
    funext μ
    fin_cases μ <;>
      simp [raise, lower, eta, Matrix.mul_apply, Fin.sum_univ_four] <;> rfl

/-- The typed contraction expands to the familiar `(+---)` component formula. -/
theorem contractUD_lower (x y : UpVec) :
    contractUD x (lower y) = x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3 := by
  simp [contractUD, lower, eta, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-- The reversed variance order has the same component formula. -/
theorem contractDU_lower (x y : UpVec) :
    contractDU (lower x) y = x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3 := by
  simp [contractDU, lower, eta, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-- The Minkowski product is symmetric. -/
theorem minkowski_comm (x y : UpVec) : minkowski x y = minkowski y x := by
  rw [minkowski, minkowski, contractUD_lower, contractUD_lower]
  ring

/-- The two legal variance orders agree after lowering the appropriate vector. -/
theorem contract_lower_symm (x y : UpVec) :
    contractUD x (lower y) = contractDU (lower x) y := by
  rw [contractUD_lower, contractDU_lower]

/-- Bilinearity in the upper slot. -/
theorem contractUD_add_left (x y : UpVec) (z : DownVec) :
    contractUD (x + y) z = contractUD x z + contractUD y z := by
  change (∑ μ, (x μ + y μ) * z μ) = (∑ μ, x μ * z μ) + (∑ μ, y μ * z μ)
  simp [Finset.sum_add_distrib, add_mul]

/-- Bilinearity in the lower slot. -/
theorem contractUD_add_right (x : UpVec) (y z : DownVec) :
    contractUD x (y + z) = contractUD x y + contractUD x z := by
  change (∑ μ, x μ * (y μ + z μ)) = (∑ μ, x μ * y μ) + (∑ μ, x μ * z μ)
  simp [Finset.sum_add_distrib, mul_add]

end LeanPhy.Tensor

namespace LeanPhy.Tensor

/-! ## Rank-two tensors and typed contractions

The vector layer above catches the simplest variance error.  Research
calculations also need mixed tensors such as `T^mu_nu`, their traces, and
composition.  `Tensor2` stores the variance of each slot in its type, so only
the operations below can perform the corresponding contractions.  The
implementation is deliberately finite (`Fin 4`) and algebraic; a future
elaborator can generalise the same API to arbitrary finite dimensions.
-/

inductive VarianceTag where
  | up
  | down
deriving DecidableEq, Repr

/-- A four-dimensional rank-two tensor whose two variance tags are type-level. -/
structure Tensor2 (left right : VarianceTag) where
  val : Fin 4 → Fin 4 → ℂ

instance (left right : VarianceTag) : CoeFun (Tensor2 left right)
    (fun _ => Fin 4 → Fin 4 → ℂ) := ⟨Tensor2.val⟩

abbrev TensorUU := Tensor2 .up .up
abbrev TensorUD := Tensor2 .up .down
abbrev TensorDU := Tensor2 .down .up
abbrev TensorDD := Tensor2 .down .down

/-- Lower the first index of a rank-two tensor. -/
noncomputable def lowerFirst {right : VarianceTag} (T : Tensor2 .up right) :
    Tensor2 .down right :=
  ⟨fun μ ν => ∑ α, eta μ α * T α ν⟩

/-- Raise the first index of a rank-two tensor. -/
noncomputable def raiseFirst {right : VarianceTag} (T : Tensor2 .down right) :
    Tensor2 .up right :=
  ⟨fun μ ν => ∑ α, eta μ α * T α ν⟩

/-- Lower the second index of a rank-two tensor. -/
noncomputable def lowerSecond {left : VarianceTag} (T : Tensor2 left .up) :
    Tensor2 left .down :=
  ⟨fun μ ν => ∑ α, T μ α * eta α ν⟩

/-- Raise the second index of a rank-two tensor. -/
noncomputable def raiseSecond {left : VarianceTag} (T : Tensor2 left .down) :
    Tensor2 left .up :=
  ⟨fun μ ν => ∑ α, T μ α * eta α ν⟩

theorem raiseFirst_lowerFirst {right : VarianceTag} (T : Tensor2 .up right) :
    raiseFirst (lowerFirst T) = T := by
  cases T with
  | mk f =>
    apply congrArg Tensor2.mk
    funext μ ν
    fin_cases μ <;> fin_cases ν <;>
      simp [raiseFirst, lowerFirst, eta, Fin.sum_univ_four] <;> ring

theorem lowerFirst_raiseFirst {right : VarianceTag} (T : Tensor2 .down right) :
    lowerFirst (raiseFirst T) = T := by
  cases T with
  | mk f =>
    apply congrArg Tensor2.mk
    funext μ ν
    fin_cases μ <;> fin_cases ν <;>
      simp [raiseFirst, lowerFirst, eta, Fin.sum_univ_four] <;> ring

theorem raiseSecond_lowerSecond {left : VarianceTag} (T : Tensor2 left .up) :
    raiseSecond (lowerSecond T) = T := by
  cases T with
  | mk f =>
    apply congrArg Tensor2.mk
    funext μ ν
    fin_cases μ <;> fin_cases ν <;>
      simp [raiseSecond, lowerSecond, eta, Fin.sum_univ_four] <;> ring

theorem lowerSecond_raiseSecond {left : VarianceTag} (T : Tensor2 left .down) :
    lowerSecond (raiseSecond T) = T := by
  cases T with
  | mk f =>
    apply congrArg Tensor2.mk
    funext μ ν
    fin_cases μ <;> fin_cases ν <;>
      simp [raiseSecond, lowerSecond, eta, Fin.sum_univ_four] <;> ring

/-- Composition `A^mu_nu B^nu_rho` of two mixed tensors. -/
noncomputable def composeMixed (A B : TensorUD) : TensorUD :=
  ⟨fun μ ρ => ∑ ν, A μ ν * B ν ρ⟩

/-- The mixed identity tensor `delta^mu_nu`. -/
noncomputable def mixedIdentity : TensorUD :=
  ⟨fun μ ν => if μ = ν then 1 else 0⟩

/-- Trace of a mixed tensor; the type prevents tracing two upper or two lower slots. -/
noncomputable def mixedTrace (T : TensorUD) : ℂ := ∑ μ, T μ μ

theorem composeMixed_assoc (A B C : TensorUD) :
    composeMixed (composeMixed A B) C = composeMixed A (composeMixed B C) := by
  apply congrArg Tensor2.mk
  funext μ ρ
  simp only [composeMixed]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  refine Finset.sum_congr rfl fun κ _ => ?_
  ring

theorem composeMixed_identity_left (A : TensorUD) :
    composeMixed mixedIdentity A = A := by
  apply congrArg Tensor2.mk
  funext μ ρ
  simp [composeMixed, mixedIdentity, Fin.sum_univ_four]

theorem composeMixed_identity_right (A : TensorUD) :
    composeMixed A mixedIdentity = A := by
  apply congrArg Tensor2.mk
  funext μ ρ
  simp [composeMixed, mixedIdentity, Fin.sum_univ_four]

theorem mixedTrace_comp_comm (A B : TensorUD) :
    mixedTrace (composeMixed A B) = mixedTrace (composeMixed B A) := by
  simp [mixedTrace, composeMixed]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

/-- A mixed tensor acting on an upper vector, `T^mu_nu v^nu`. -/
noncomputable def actUp (T : TensorUD) (v : UpVec) : UpVec :=
  ⟨fun μ => ∑ ν, T μ ν * v ν⟩

/-- A mixed tensor acting on a lower vector from the right, `v_mu T^mu_nu`. -/
noncomputable def actDown (T : TensorUD) (v : DownVec) : DownVec :=
  ⟨fun ν => ∑ μ, v μ * T μ ν⟩

theorem actUp_comp (A B : TensorUD) (v : UpVec) :
    actUp (composeMixed A B) v = actUp A (actUp B v) := by
  apply congrArg UpVec.mk
  funext μ
  simp only [actUp, composeMixed]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  refine Finset.sum_congr rfl fun κ _ => ?_
  ring

theorem actDown_comp (A B : TensorUD) (v : DownVec) :
    actDown (composeMixed A B) v = actDown B (actDown A v) := by
  apply congrArg DownVec.mk
  funext ν
  simp only [actDown, composeMixed]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  refine Finset.sum_congr rfl fun κ _ => ?_
  ring

end LeanPhy.Tensor

namespace LeanPhy.Tensor

/-! The negative test is a type-level guarantee: same-variance contraction never
reaches the theorem prover. -/

/-- error: Application type mismatch: The argument
  y
has type
  UpVec
but is expected to have type
  DownVec
in the application
  contractUD x y -/
#guard_msgs (error) in
example (x y : UpVec) : contractUD x y = 0 := rfl

/-! A mixed trace cannot be applied to a same-variance tensor. -/

/-- error: Application type mismatch: The argument
  T
has type
  TensorUU
but is expected to have type
  TensorUD
in the application
  mixedTrace T -/
#guard_msgs (error) in
example (T : TensorUU) : mixedTrace T = 0 := rfl

end LeanPhy.Tensor
