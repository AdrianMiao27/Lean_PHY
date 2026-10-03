import LeanPhy.Mathematics.FinitePathIntegral
import Mathlib.Tactic

/-!
# Finite reflection-positive Gram kernels

Reflection positivity is an analytic condition in a continuum Euclidean field
theory.  A finite lattice or truncated model can still expose a useful,
auditable fragment: a reflected two-point kernel is supplied by a finite Gram
factorisation.  The kernel then proves non-negativity of every real quadratic
form built from that kernel.  The factorisation is explicit input; no measure,
continuum reflection map, reconstruction theorem or OS axiom is inferred.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

universe u v

structure FiniteGramKernel (ι : Type u) (α : Type v)
    [Fintype ι] [Fintype α] where
  feature : ι → α → ℝ

namespace FiniteGramKernel

variable {ι : Type u} {α : Type v} [Fintype ι] [Fintype α]

def kernel (G : FiniteGramKernel ι α) (i j : ι) : ℝ :=
  ∑ a, G.feature i a * G.feature j a

@[simp] theorem kernel_apply (G : FiniteGramKernel ι α) (i j : ι) :
    G.kernel i j = ∑ a, G.feature i a * G.feature j a := rfl

theorem kernel_symmetric (G : FiniteGramKernel ι α) (i j : ι) :
    G.kernel i j = G.kernel j i := by
  unfold kernel
  apply Finset.sum_congr rfl
  intro a ha
  ring

def quadratic (G : FiniteGramKernel ι α) (f : ι → ℝ) : ℝ :=
  ∑ a, (∑ i, f i * G.feature i a) ^ 2

@[simp] theorem quadratic_apply (G : FiniteGramKernel ι α) (f : ι → ℝ) :
    G.quadratic f = ∑ a, (∑ i, f i * G.feature i a) ^ 2 := rfl

theorem quadratic_eq_sum_sq (G : FiniteGramKernel ι α) (f : ι → ℝ) :
    G.quadratic f = ∑ a, (∑ i, f i * G.feature i a) ^ 2 := by
  rfl

theorem quadratic_nonneg (G : FiniteGramKernel ι α) (f : ι → ℝ) :
    0 ≤ G.quadratic f := by
  rw [G.quadratic_eq_sum_sq]
  exact Finset.sum_nonneg (fun a ha => sq_nonneg _)

/-! The kernel-facing presentation is the usual finite double sum.  The
factorisation bridge below is proved by finite sum rearrangement, so a user
can state a reflection-positivity claim with the kernel entries and still get
the auditable sum-of-squares certificate. -/

def kernelQuadratic (G : FiniteGramKernel ι α) (f : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, f i * G.kernel i j * f j

theorem kernelQuadratic_eq_quadratic (G : FiniteGramKernel ι α)
    (f : ι → ℝ) :
    G.kernelQuadratic f = G.quadratic f := by
  unfold kernelQuadratic quadratic kernel
  calc
    (∑ i, ∑ j, f i * (∑ a, G.feature i a * G.feature j a) * f j) =
        ∑ i, ∑ j, ∑ a,
          f i * (G.feature i a * G.feature j a) * f j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ a, ∑ i, ∑ j,
          f i * (G.feature i a * G.feature j a) * f j := by
      calc
        (∑ i, ∑ j, ∑ a,
            f i * (G.feature i a * G.feature j a) * f j) =
            ∑ i, ∑ a, ∑ j,
              f i * (G.feature i a * G.feature j a) * f j := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.sum_comm]
        _ = ∑ a, ∑ i, ∑ j,
            f i * (G.feature i a * G.feature j a) * f j := by
              rw [Finset.sum_comm]
    _ = ∑ a, (∑ i, f i * G.feature i a) *
          (∑ j, G.feature j a * f j) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ a, (∑ i, f i * G.feature i a) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [show (∑ j, G.feature j a * f j) =
          ∑ j, f j * G.feature j a by
        apply Finset.sum_congr rfl
        intro j hj
        ring]
      ring

theorem kernelQuadratic_nonneg (G : FiniteGramKernel ι α) (f : ι → ℝ) :
    0 ≤ G.kernelQuadratic f := by
  rw [G.kernelQuadratic_eq_quadratic]
  exact G.quadratic_nonneg f

end FiniteGramKernel

/-! A reflected finite correlator uses a supplied involution on labels.  The
Gram factorisation is the auditable finite replacement for a continuum
reflection-positivity argument. -/

structure FiniteReflectionCertificate (ι : Type u) (α : Type v)
    [Fintype ι] [Fintype α] where
  reflection : Equiv.Perm ι
  involutive : ∀ i, reflection (reflection i) = i
  gram : FiniteGramKernel ι α

namespace FiniteReflectionCertificate

variable {ι : Type u} {α : Type v} [Fintype ι] [Fintype α]

def reflectedQuadratic (C : FiniteReflectionCertificate ι α)
    (f : ι → ℝ) : ℝ :=
  C.gram.quadratic (fun i => f (C.reflection i))

theorem reflectedQuadratic_nonneg (C : FiniteReflectionCertificate ι α)
    (f : ι → ℝ) : 0 ≤ C.reflectedQuadratic f := by
  exact C.gram.quadratic_nonneg _

theorem reflectedQuadratic_eq_sum_sq (C : FiniteReflectionCertificate ι α)
    (f : ι → ℝ) :
    C.reflectedQuadratic f =
      ∑ a, (∑ i, f (C.reflection i) * C.gram.feature i a) ^ 2 := by
  exact C.gram.quadratic_eq_sum_sq _

def reflectedKernelQuadratic (C : FiniteReflectionCertificate ι α)
    (f : ι → ℝ) : ℝ :=
  C.gram.kernelQuadratic (fun i => f (C.reflection i))

theorem reflectedKernelQuadratic_eq_reflectedQuadratic
    (C : FiniteReflectionCertificate ι α) (f : ι → ℝ) :
    C.reflectedKernelQuadratic f = C.reflectedQuadratic f := by
  exact C.gram.kernelQuadratic_eq_quadratic _

theorem reflectedKernelQuadratic_nonneg
    (C : FiniteReflectionCertificate ι α) (f : ι → ℝ) :
    0 ≤ C.reflectedKernelQuadratic f := by
  rw [C.reflectedKernelQuadratic_eq_reflectedQuadratic]
  exact C.reflectedQuadratic_nonneg f

theorem reflectedKernelQuadratic_eq_sum_sq
    (C : FiniteReflectionCertificate ι α) (f : ι → ℝ) :
    C.reflectedKernelQuadratic f =
      ∑ a, (∑ i, f (C.reflection i) * C.gram.feature i a) ^ 2 := by
  rw [C.reflectedKernelQuadratic_eq_reflectedQuadratic]
  exact C.reflectedQuadratic_eq_sum_sq f

end FiniteReflectionCertificate

/-! Domain aliases keep the same explicit finite contract discoverable from
path-integral and lattice documentation. -/

namespace FieldTheory
abbrev FiniteReflectionKernel {ι α : Type*} [Fintype ι] [Fintype α] :=
  FiniteGramKernel ι α
abbrev FiniteReflectionPositivity {ι α : Type*} [Fintype ι] [Fintype α] :=
  FiniteReflectionCertificate ι α
end FieldTheory

namespace Condensed
abbrev FiniteLatticeReflectionKernel {ι α : Type*} [Fintype ι] [Fintype α] :=
  FiniteGramKernel ι α
end Condensed

namespace StatMech
abbrev FiniteEuclideanReflectionKernel {ι α : Type*} [Fintype ι] [Fintype α] :=
  FiniteGramKernel ι α
end StatMech

end LeanPhy.Mathematics
