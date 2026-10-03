import LeanPhy.Quantum.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open scoped BigOperators

/-!
# Index calculus: explicit contraction notation

Physics derivations are full of repeated (Einstein-summed) indices, the
Levi-Civita symbol and the Kronecker delta.  This file gives that layer an
explicit, kernel-checked meaning over finite index types:

- `delta i j` is the Kronecker delta;
- `sumOver f` is the Einstein sum `∑_i f_i` over a finite index type;
- `contract a b` is the full contraction `∑_i a_i b_i`;
- `epsilon i j k` is the Levi-Civita symbol in three dimensions, with its
  antisymmetry and the epsilon-delta identity proved by case analysis.

The design choice is deliberate: v1 sums over finite index sets, where the
kernel can decide every claim.  Continuum indices (spacetime integrals) belong
to the analysis layer and are handled with explicit hypotheses, never assumed
silently.
-/

namespace LeanPhy.IndexCalculus

/-- The Kronecker delta `δ_ij` as an integer. -/
def delta {ι : Type} [DecidableEq ι] (i j : ι) : ℤ := if i = j then 1 else 0

/-- The Einstein sum `∑_i f_i` over a finite index type. -/
def sumOver {ι α : Type} [Fintype ι] [AddCommMonoid α] (f : ι → α) : α := ∑ i, f i

/-- Full contraction of two index families, `∑_i a_i b_i`. -/
def contract {ι α : Type} [Fintype ι] [AddCommMonoid α] [Mul α] (a b : ι → α) : α :=
  ∑ i, a i * b i

/-- The Levi-Civita symbol in three dimensions, defined by its six nonzero
entries. -/
def epsilon (i j k : Fin 3) : ℤ :=
  if i = 0 ∧ j = 1 ∧ k = 2 then 1
  else if i = 1 ∧ j = 2 ∧ k = 0 then 1
  else if i = 2 ∧ j = 0 ∧ k = 1 then 1
  else if i = 0 ∧ j = 2 ∧ k = 1 then -1
  else if i = 2 ∧ j = 1 ∧ k = 0 then -1
  else if i = 1 ∧ j = 0 ∧ k = 2 then -1
  else 0

@[simp] theorem delta_self {ι : Type} [DecidableEq ι] (i : ι) : delta i i = 1 := by
  simp [delta]

theorem delta_of_ne {ι : Type} [DecidableEq ι] {i j : ι} (h : i ≠ j) : delta i j = 0 := by
  simp [delta, h]

@[simp] theorem sumOver_zero {ι α : Type} [Fintype ι] [AddCommMonoid α] :
    sumOver (fun _ : ι => (0 : α)) = 0 := by
  simp [sumOver]

theorem sumOver_add {ι α : Type} [Fintype ι] [AddCommMonoid α] (f g : ι → α) :
    sumOver (fun i => f i + g i) = sumOver f + sumOver g := by
  simp [sumOver, Finset.sum_add_distrib]

theorem contract_add_left {ι α : Type} [Fintype ι] [Ring α] (a b c : ι → α) :
    contract (fun i => a i + b i) c = contract a c + contract b c := by
  simp [contract, Finset.sum_add_distrib, add_mul]

theorem contract_add_right {ι α : Type} [Fintype ι] [Ring α] (a b c : ι → α) :
    contract a (fun i => b i + c i) = contract a b + contract a c := by
  simp [contract, Finset.sum_add_distrib, mul_add]

/-- A matrix-vector product is a contraction over the internal index,
`(M v)_i = ∑_j M_ij v_j`. -/
theorem mulVec_eq_contract (M : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) (i : Fin 3) :
    M.mulVec v i = sumOver (fun j => M i j * v j) := by
  simp [Matrix.mulVec, dotProduct, sumOver]

/-- The Levi-Civita symbol is totally antisymmetric under any transposition.
Proved by exhaustive case analysis over the six values of the three indices. -/
theorem epsilon_antisymm (i j k : Fin 3) : epsilon i j k = -epsilon i k j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- The epsilon-delta identity
`∑_i ε_{ijk} ε_{ilm} = δ_{jl} δ_{km} - δ_{jm} δ_{kl}`,
the workhorse behind `(a × b) · (c × d)` and vector-calculus identities. -/
theorem epsilon_delta (j k l m : Fin 3) :
    (∑ i : Fin 3, epsilon i j k * epsilon i l m)
      = delta j l * delta k m - delta j m * delta k l := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;> fin_cases m <;>
    simp only [Fin.sum_univ_three, epsilon, delta] <;> norm_num

/-- The contraction that produces the cross product of two vectors,
`(a × b)_i = ∑_{j,k} ε_{ijk} a_j b_k`; stated as the definition physics uses. -/
def crossProduct (a b : Fin 3 → ℤ) (i : Fin 3) : ℤ :=
  ∑ j : Fin 3, ∑ k : Fin 3, epsilon i j k * (a j * b k)

end LeanPhy.IndexCalculus
