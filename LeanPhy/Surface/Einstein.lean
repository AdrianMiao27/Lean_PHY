import LeanPhy.Surface.IndexCalculus
import Mathlib.LinearAlgebra.Matrix.Notation

open scoped BigOperators

/-!
# Einstein summation as real surface syntax

Physics derivations write a contraction as a repeated index, not as an explicit
sum.  This file gives that convention a real elaborator instead of a plain
notation, so the *type* of the index is inferred from how the index is used:

    einsum k, M i k * N k j        -- k : Fin n inferred from M, N
    einsum (k : Fin n), M i k * N k j

Both forms elaborate to the finite sum over the index, so every statement is
still checked by the ordinary Lean kernel; nothing here is a new logic.  The
policy is the one stated throughout LeanPhy: v1 sums over finite index sets,
where the kernel decides every claim.  Continuum indices (spacetime integrals)
belong to the analysis layer and carry explicit hypotheses.

The elaborator reports two physics-facing diagnostics:

- if the index type cannot be inferred, it asks for the ascribed form;
- if the index does not occur in the summand, it warns about a likely typo.
-/

namespace LeanPhy.Einstein

open Lean Meta Elab Term
open LeanPhy.IndexCalculus

/-! ## A codomain-generic Kronecker delta -/

/-- The Kronecker delta, with values in any type carrying 0 and 1, so it can be
contracted over coefficients and over complex amplitudes alike. -/
def kdelta {ι α : Type} [DecidableEq ι] [Zero α] [One α] (i j : ι) : α :=
  if i = j then 1 else 0

@[simp] theorem kdelta_self {ι α : Type} [DecidableEq ι] [Zero α] [One α] (i : ι) :
    kdelta i i = (1 : α) := by
  simp [kdelta]

theorem kdelta_of_ne {ι α : Type} [DecidableEq ι] [Zero α] [One α] {i j : ι}
    (h : i ≠ j) : kdelta i j = (0 : α) := by
  simp [kdelta, h]

/-! ## The einsum binder -/

/-- Shared implementation of the two einsum elaborators: bind the index, close
the summand over it, form the finite sum, and emit contextual diagnostics. -/
private def mkEinsumBody (id : Name) (idxTy : Expr) (body : Syntax) : TermElabM Expr := do
  withLocalDeclD id idxTy fun x => do
    let bodyExpr ← elabTerm body none
    let bodyExpr ← instantiateMVars bodyExpr
    let idxTy ← instantiateMVars (← inferType x)
    if idxTy.isMVar then
      throwError m!"einsum: cannot infer the type of index {id}; write einsum ({id} : T), ... with a finite index type T"
    unless bodyExpr.containsFVar x.fvarId! do
      logWarning m!"einsum: index {id} does not occur in the summand; check for a typo"
    -- the index type must be finite, i.e. carry a Fintype instance
    try
      discard <| synthInstance (← mkAppM ``Fintype #[idxTy])
    catch _ =>
      throwError m!"einsum: index type {idxTy} is not finite; add a Fintype instance (continuum indices belong to the analysis layer)"
    let lam ← mkLambdaFVars #[x] bodyExpr
    let univ ← mkAppOptM ``Finset.univ #[some idxTy, none]
    try
      mkAppM ``Finset.sum #[univ, lam]
    catch _ =>
      throwError m!"einsum: the summand is not summable over {idxTy}; give it an AddCommMonoid instance (e.g. ℂ, ℤ, ℝ)"

elab "einsum" i:ident "," body:term : term => do
  let ty ← mkFreshTypeMVar
  mkEinsumBody i.getId ty body

elab "einsum" "(" i:ident ":" ty:term ")" "," body:term : term => do
  let tyExpr ← elabType ty
  mkEinsumBody i.getId tyExpr body

/-! ## Contraction lemmas (kernel-checked) -/

/-- Folding a Kronecker-like if-expression over the whole index set. -/
theorem sum_ite_eq_fst {ι α : Type} [Fintype ι] [DecidableEq ι] [AddCommMonoid α]
    (i₀ : ι) (f : ι → α) : (∑ i, (if i = i₀ then f i else 0)) = f i₀ := by
  rw [Finset.sum_eq_single i₀]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i₀) h

theorem sum_ite_eq_snd {ι α : Type} [Fintype ι] [DecidableEq ι] [AddCommMonoid α]
    (i₀ : ι) (f : ι → α) : (∑ i, (if i₀ = i then f i else 0)) = f i₀ := by
  rw [Finset.sum_eq_single i₀]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ i₀) h

/-- Contracting a vector with delta on its first index. -/
theorem sum_kdelta_mul_snd_index {ι α : Type} [Fintype ι] [DecidableEq ι] [Semiring α]
    (i₀ : ι) (v : ι → α) : (∑ j, kdelta i₀ j * v j) = v i₀ := by
  simp only [kdelta, ite_mul, one_mul, zero_mul]
  exact sum_ite_eq_snd i₀ v

/-- Contracting a vector with delta on its second index. -/
theorem sum_kdelta_mul_fst_index {ι α : Type} [Fintype ι] [DecidableEq ι] [Semiring α]
    (j₀ : ι) (v : ι → α) : (∑ i, kdelta i j₀ * v i) = v j₀ := by
  simp only [kdelta, ite_mul, one_mul, zero_mul]
  exact sum_ite_eq_fst j₀ v

/-- The same contraction with delta on the right of the product. -/
theorem sum_mul_kdelta_snd_index {ι α : Type} [Fintype ι] [DecidableEq ι] [Semiring α]
    (i₀ : ι) (v : ι → α) : (∑ j, v j * kdelta i₀ j) = v i₀ := by
  simp only [kdelta, mul_ite, mul_one, mul_zero]
  exact sum_ite_eq_snd i₀ v

/-- The same contraction with delta on the right of the product. -/
theorem sum_mul_kdelta_fst_index {ι α : Type} [Fintype ι] [DecidableEq ι] [Semiring α]
    (j₀ : ι) (v : ι → α) : (∑ i, v i * kdelta i j₀) = v j₀ := by
  simp only [kdelta, mul_ite, mul_one, mul_zero]
  exact sum_ite_eq_fst j₀ v

/-! ## What the elaborator buys: index-notation facts -/

/-- Index-notation matrix product: the einsum form is exactly the product. -/
theorem einsum_mul_apply {m n p : Nat} (M : Matrix (Fin m) (Fin n) ℂ)
    (N : Matrix (Fin n) (Fin p) ℂ) (i : Fin m) (j : Fin p) :
    (einsum k, M i k * N k j) = (M * N) i j := (Matrix.mul_apply).symm

/-- The trace as a contraction over one repeated index. -/
theorem einsum_trace {n : Nat} (M : Matrix (Fin n) (Fin n) ℂ) :
    (einsum i, M i i) = M.trace := rfl

/-- Trace of a product: summing M_ik N_ki over i and k is tr (M N). -/
theorem einsum_mul_trace {m n : Nat} (M : Matrix (Fin m) (Fin n) ℂ)
    (N : Matrix (Fin n) (Fin m) ℂ) :
    (einsum i, einsum k, M i k * N k i) = (M * N).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]

/-- Contracting a vector with delta reproduces the vector. -/
theorem einsum_kdelta_apply {n : Nat} (v : Fin n → ℂ) (i : Fin n) :
    (einsum j, kdelta i j * v j) = v i := sum_kdelta_mul_snd_index i v

/-- Chaining two deltas collapses the middle index, delta_ij delta_jk = delta_ik. -/
theorem einsum_delta_chain {n : Nat} (i k : Fin n) :
    (einsum (j : Fin n), kdelta (α := ℂ) i j * kdelta j k) = kdelta i k :=
  sum_kdelta_mul_snd_index i (fun j => kdelta j k)

/-- The dot product in index notation, a . b = sum_i a_i b_i. -/
theorem einsum_dot (a b : Fin 3 → ℂ) :
    (einsum i, a i * b i) = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [Fin.sum_univ_three]

/-- The cross product in index notation,
(a x b)_k = sum_{i,j} eps_{kji} a_j b_i, matching the definition crossProduct. -/
theorem einsum_cross (a b : Fin 3 → ℤ) (k : Fin 3) :
    (einsum j, einsum i, epsilon k j i * (a j * b i)) = crossProduct a b k := rfl

/-! ## Diagnostics as build-time regression tests -/

/-- error: einsum: cannot infer the type of index i; write einsum (i : T), ... with a finite index type T -/
#guard_msgs (error) in
#check (einsum i, (1 : ℂ))

/-- error: einsum: index type ℕ is not finite; add a Fintype instance (continuum indices belong to the analysis layer) -/
#guard_msgs (error) in
#check (einsum i, (i : ℕ))

/-- warning: einsum: index i does not occur in the summand; check for a typo -/
#guard_msgs (warning) in
example : (einsum (i : Fin 2), (0 : ℂ)) = 0 := by simp

end LeanPhy.Einstein
