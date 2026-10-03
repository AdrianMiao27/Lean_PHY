import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Order

/-!
# Finite indices and Einstein-style contractions

The first implementation keeps indices finite.  This is deliberate: finite
sums can be normalized and checked by the kernel, while continuum integrals
belong to a later analysis layer with explicit hypotheses.
-/

namespace LeanPhy

open scoped BigOperators

def einsteinSum {ι α : Type} [Fintype ι] [AddCommMonoid α]
    (f : ι → α) : α := ∑ i, f i

@[simp] theorem einsteinSum_zero {ι α : Type} [Fintype ι] [AddCommMonoid α] :
    einsteinSum (fun _ : ι => (0 : α)) = 0 := by
  simp [einsteinSum]

theorem einsteinSum_add {ι α : Type} [Fintype ι] [AddCommMonoid α]
    (f g : ι → α) :
    einsteinSum (fun i => f i + g i) = einsteinSum f + einsteinSum g := by
  simp [einsteinSum, Finset.sum_add_distrib]

def contract {ι α : Type} [Fintype ι] [AddCommMonoid α]
    [Mul α] (a b : ι → α) : α := ∑ i, a i * b i

theorem contract_add_left {ι α : Type} [Fintype ι] [Ring α]
    (a b c : ι → α) :
    contract (fun i => a i + b i) c = contract a c + contract b c := by
  simp [contract, Finset.sum_add_distrib, add_mul]

theorem contract_add_right {ι α : Type} [Fintype ι] [Ring α]
    (a b c : ι → α) :
    contract a (fun i => b i + c i) = contract a b + contract a c := by
  simp [contract, Finset.sum_add_distrib, mul_add]

end LeanPhy
