import LeanPhy.Mathematics.FinitePathIntegral
import Mathlib.Tactic

/-!
# Positive finite path weights and reflection certificates

This module connects two finite interfaces that are useful in lattice and
truncated Euclidean calculations.  A real non-negative weight gives a
constructive non-zero finite path integral, while a weighted Gram factorisation
gives a reflection-positive quadratic form.  The connection is deliberately
finite: no continuum measure, Osterwalder--Schrader axiom, reconstruction
theorem or Euclidean QFT existence result is inferred.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

universe u v

structure FinitePositivePathIntegral (ι : Type u) [Fintype ι] where
  weight : ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  partition_pos : 0 < ∑ i, weight i

namespace FinitePositivePathIntegral

variable {ι : Type u} [Fintype ι]

/-! The positive real object can be consumed by the complex finite path API. -/

noncomputable def toComplex (P : FinitePositivePathIntegral ι) :
    FinitePathIntegral ι where
  weight := fun i => (P.weight i : ℂ)
  partition_ne_zero := by
    intro h
    have hre : (∑ i, P.weight i) = 0 := by
      apply Complex.ofReal_inj.mp
      rw [Complex.ofReal_sum]
      exact h
    linarith [P.partition_pos]

@[simp] theorem toComplex_weight (P : FinitePositivePathIntegral ι) :
    (P.toComplex).weight = fun i => (P.weight i : ℂ) := rfl

theorem toComplex_partition_re (P : FinitePositivePathIntegral ι) :
    (P.toComplex).partition.re = ∑ i, P.weight i := by
  unfold toComplex FinitePathIntegral.partition
  change Complex.reCLM (∑ i, (P.weight i : ℂ)) = _
  rw [map_sum Complex.reCLM]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

theorem toComplex_partition_pos (P : FinitePositivePathIntegral ι) :
    0 < (P.toComplex).partition.re := by
  rw [P.toComplex_partition_re]
  exact P.partition_pos

/-! A real finite action is a convenient constructive source of this contract. -/

noncomputable def fromRealAction [Nonempty ι] (S : ι → ℝ) :
    FinitePositivePathIntegral ι where
  weight := fun i => Real.exp (-S i)
  weight_nonneg := fun i => le_of_lt (Real.exp_pos _)
  partition_pos := by
    apply Finset.sum_pos
    · intro i hi
      exact Real.exp_pos _
    · exact Finset.univ_nonempty

@[simp] theorem fromRealAction_weight (S : ι → ℝ) [Nonempty ι] :
    (fromRealAction S).weight = fun i => Real.exp (-S i) := rfl

theorem fromRealAction_toComplex (S : ι → ℝ) [Nonempty ι] :
    (fromRealAction S).toComplex = FinitePathIntegral.fromRealAction S := by
  rfl

end FinitePositivePathIntegral

/-! A weighted Gram kernel is the finite path-integral presentation of a
positive correlation kernel.  The weight and feature factorisation are inputs;
the kernel proves the quadratic non-negativity. -/

structure FiniteWeightedGramKernel (ι : Type u) (α : Type v)
    [Fintype ι] [Fintype α] where
  weight : α → ℝ
  feature : ι → α → ℝ
  weight_nonneg : ∀ a, 0 ≤ weight a

namespace FiniteWeightedGramKernel

variable {ι : Type u} {α : Type v} [Fintype ι] [Fintype α]

def fromPath (P : FinitePositivePathIntegral α) (feature : ι → α → ℝ) :
    FiniteWeightedGramKernel ι α where
  weight := P.weight
  feature := feature
  weight_nonneg := P.weight_nonneg

def kernel (G : FiniteWeightedGramKernel ι α) (i j : ι) : ℝ :=
  ∑ a, G.weight a * G.feature i a * G.feature j a

def quadratic (G : FiniteWeightedGramKernel ι α) (f : ι → ℝ) : ℝ :=
  ∑ a, G.weight a * (∑ i, f i * G.feature i a) ^ 2

def kernelQuadratic (G : FiniteWeightedGramKernel ι α) (f : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, f i * G.kernel i j * f j

theorem kernelQuadratic_eq_quadratic (G : FiniteWeightedGramKernel ι α)
    (f : ι → ℝ) :
    G.kernelQuadratic f = G.quadratic f := by
  unfold kernelQuadratic quadratic kernel
  calc
    (∑ i, ∑ j, f i * (∑ a, G.weight a * G.feature i a * G.feature j a) * f j) =
        ∑ i, ∑ j, ∑ a,
          f i * (G.weight a * G.feature i a * G.feature j a) * f j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ a, ∑ i, ∑ j,
          f i * (G.weight a * G.feature i a * G.feature j a) * f j := by
      calc
        (∑ i, ∑ j, ∑ a,
            f i * (G.weight a * G.feature i a * G.feature j a) * f j) =
            ∑ i, ∑ a, ∑ j,
              f i * (G.weight a * G.feature i a * G.feature j a) * f j := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.sum_comm]
        _ = ∑ a, ∑ i, ∑ j,
            f i * (G.weight a * G.feature i a * G.feature j a) * f j := by
              rw [Finset.sum_comm]
    _ = ∑ a, G.weight a *
          (∑ i, f i * G.feature i a) *
          (∑ j, f j * G.feature j a) := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        (∑ i, ∑ j,
            f i * (G.weight a * G.feature i a * G.feature j a) * f j) =
            ∑ i, (f i * (G.weight a * G.feature i a)) *
              (∑ j, G.feature j a * f j) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                ring
        _ = (∑ i, f i * (G.weight a * G.feature i a)) *
              (∑ j, G.feature j a * f j) := by
                rw [Finset.sum_mul]
        _ = (G.weight a * (∑ i, f i * G.feature i a)) *
              (∑ j, f j * G.feature j a) := by
                calc
                  (∑ i, f i * (G.weight a * G.feature i a)) *
                        (∑ j, G.feature j a * f j) =
                      (G.weight a * (∑ i, f i * G.feature i a)) *
                        (∑ j, G.feature j a * f j) := by
                        congr 1
                        calc
                          (∑ i, f i * (G.weight a * G.feature i a)) =
                              ∑ i, G.weight a * (f i * G.feature i a) := by
                                apply Finset.sum_congr rfl
                                intro i hi
                                ring
                          _ = G.weight a * (∑ i, f i * G.feature i a) := by
                                rw [Finset.mul_sum]
                  _ = (G.weight a * (∑ i, f i * G.feature i a)) *
                        (∑ j, f j * G.feature j a) := by
                        congr 1
                        apply Finset.sum_congr rfl
                        intro j hj
                        ring
    _ = ∑ a, G.weight a * (∑ i, f i * G.feature i a) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      ring

theorem quadratic_nonneg (G : FiniteWeightedGramKernel ι α) (f : ι → ℝ) :
    0 ≤ G.quadratic f := by
  unfold quadratic
  exact Finset.sum_nonneg (fun a ha =>
    mul_nonneg (G.weight_nonneg a) (sq_nonneg _))

theorem kernelQuadratic_nonneg (G : FiniteWeightedGramKernel ι α)
    (f : ι → ℝ) : 0 ≤ G.kernelQuadratic f := by
  rw [G.kernelQuadratic_eq_quadratic]
  exact G.quadratic_nonneg f

theorem fromPath_kernel (P : FinitePositivePathIntegral α)
    (feature : ι → α → ℝ) (i j : ι) :
    (fromPath P feature).kernel i j =
      ∑ a, P.weight a * feature i a * feature j a := rfl

end FiniteWeightedGramKernel

/-! Reflection is a checked finite permutation layered on the weighted Gram
kernel.  Involution is retained as data so an adapter cannot silently use a
non-reflection permutation. -/

structure FiniteWeightedReflectionCertificate (ι : Type u) (α : Type v)
    [Fintype ι] [Fintype α] where
  reflection : Equiv.Perm ι
  involutive : ∀ i, reflection (reflection i) = i
  gram : FiniteWeightedGramKernel ι α

namespace FiniteWeightedReflectionCertificate

variable {ι : Type u} {α : Type v} [Fintype ι] [Fintype α]

def fromPath (P : FinitePositivePathIntegral α) (feature : ι → α → ℝ)
    (reflection : Equiv.Perm ι)
    (involutive : ∀ i, reflection (reflection i) = i) :
    FiniteWeightedReflectionCertificate ι α where
  reflection := reflection
  involutive := involutive
  gram := FiniteWeightedGramKernel.fromPath P feature

def reflectedKernelQuadratic (C : FiniteWeightedReflectionCertificate ι α)
    (f : ι → ℝ) : ℝ :=
  C.gram.kernelQuadratic (fun i => f (C.reflection i))

theorem reflectedKernelQuadratic_nonneg
    (C : FiniteWeightedReflectionCertificate ι α) (f : ι → ℝ) :
    0 ≤ C.reflectedKernelQuadratic f := by
  exact C.gram.kernelQuadratic_nonneg _

theorem reflectedKernelQuadratic_eq_weighted_sum_sq
    (C : FiniteWeightedReflectionCertificate ι α) (f : ι → ℝ) :
    C.reflectedKernelQuadratic f =
      ∑ a, C.gram.weight a *
        (∑ i, f (C.reflection i) * C.gram.feature i a) ^ 2 := by
  unfold reflectedKernelQuadratic
  rw [C.gram.kernelQuadratic_eq_quadratic]
  rfl

theorem fromPath_weight
    (P : FinitePositivePathIntegral α) (feature : ι → α → ℝ)
    (reflection : Equiv.Perm ι)
    (hinv : ∀ i, reflection (reflection i) = i) :
    (fromPath P feature reflection hinv).gram.weight = P.weight := rfl

end FiniteWeightedReflectionCertificate

/-! Domain aliases expose the same finite contract to common physical
adaptors. -/

namespace FieldTheory
abbrev FinitePositiveEuclideanMeasure {ι : Type*} [Fintype ι] :=
  FinitePositivePathIntegral ι
abbrev FiniteWeightedReflectionPositivity {ι α : Type*}
    [Fintype ι] [Fintype α] :=
  FiniteWeightedReflectionCertificate ι α
end FieldTheory

namespace Condensed
abbrev FinitePositiveLatticeMeasure {ι : Type*} [Fintype ι] :=
  FinitePositivePathIntegral ι
end Condensed

namespace StatMech
abbrev FinitePositiveEuclideanMeasure {ι : Type*} [Fintype ι] :=
  FinitePositivePathIntegral ι
end StatMech

end LeanPhy.Mathematics
