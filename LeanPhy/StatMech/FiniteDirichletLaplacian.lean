import LeanPhy.StatMech.FiniteDirichlet
import Mathlib.Tactic

/-!
# Discrete Laplacian bridge for finite reversible dynamics

For a detailed-balanced finite kernel, the edge-based Dirichlet form is the
weighted pairing with the discrete Laplacian `I - K`.  This is the finite
algebraic bridge used by reversible Markov chains, lattice hopping, graph
Laplacians and finite-element stiffness forms.  No spectral-gap, mixing or
continuum statement is inferred.
-/

namespace LeanPhy.StatMech

open scoped BigOperators

namespace FiniteKernel

variable {ι : Type*} [Fintype ι]

noncomputable def laplacian (K : FiniteKernel ι) (f : ι → ℝ) : ι → ℝ :=
  fun i => f i - K.pullback f i

theorem dirichletForm_eq_laplacian_pairing (K : FiniteKernel ι)
    (p : FiniteProbability ι) (f g : ι → ℝ) (h : K.IsDetailedBalance p) :
    K.dirichletForm p f g =
      p.expectation (fun i => f i * K.laplacian g i) := by
  classical
  unfold FiniteKernel.dirichletForm laplacian FiniteProbability.expectation FiniteKernel.pullback
  have hdiagLeft :
      (∑ i, ∑ j, p.weight i * K.transition i j * f i * g i) =
        ∑ i, p.weight i * f i * g i := by
    calc
      (∑ i, ∑ j, p.weight i * K.transition i j * f i * g i) =
          ∑ i, (p.weight i * f i * g i) * ∑ j, K.transition i j := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          (∑ j, p.weight i * K.transition i j * f i * g i) =
              ∑ j, (p.weight i * f i * g i) * K.transition i j := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = (p.weight i * f i * g i) * ∑ j, K.transition i j := by
                rw [Finset.mul_sum]
      _ = ∑ i, p.weight i * f i * g i := by
        simp [K.row_normalized]
  have hdiagRight :
      (∑ i, ∑ j, p.weight i * K.transition i j * f j * g j) =
        ∑ i, p.weight i * f i * g i := by
    calc
      (∑ i, ∑ j, p.weight i * K.transition i j * f j * g j) =
          ∑ i, ∑ j, p.weight j * K.transition j i * f j * g j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [h i j]
      _ = ∑ j, ∑ i, p.weight j * K.transition j i * f j * g j := by
        rw [Finset.sum_comm]
      _ = ∑ j, p.weight j * f j * g j := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          (∑ i, p.weight j * K.transition j i * f j * g j) =
              ∑ i, (p.weight j * f j * g j) * K.transition j i := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
          _ = (p.weight j * f j * g j) * ∑ i, K.transition j i := by
                rw [Finset.mul_sum]
          _ = p.weight j * f j * g j := by simp [K.row_normalized]
  have hcross :
      (∑ i, ∑ j, p.weight i * K.transition i j * f j * g i) =
        ∑ i, ∑ j, p.weight i * K.transition i j * f i * g j := by
    calc
      (∑ i, ∑ j, p.weight i * K.transition i j * f j * g i) =
          ∑ i, ∑ j, p.weight j * K.transition j i * f j * g i := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [h i j]
      _ = ∑ j, ∑ i, p.weight j * K.transition j i * f j * g i := by
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, p.weight i * K.transition i j * f i * g j := by
        rfl
  have hcrossRight :
      (∑ i, ∑ j, p.weight i * K.transition i j * f i * g j) =
        ∑ i, p.weight i * f i * ∑ j, K.transition i j * g j := by
    calc
      (∑ i, ∑ j, p.weight i * K.transition i j * f i * g j) =
          ∑ i, ∑ j, (p.weight i * f i) * (K.transition i j * g j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ i, (p.weight i * f i) * ∑ j, K.transition i j * g j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
  calc
    (1 / 2 : ℝ) * ∑ i, ∑ j,
        p.weight i * K.transition i j * (f i - f j) * (g i - g j) =
      (1 / 2 : ℝ) * ((∑ i, ∑ j, p.weight i * K.transition i j * f i * g i) -
        (∑ i, ∑ j, p.weight i * K.transition i j * f i * g j) -
        (∑ i, ∑ j, p.weight i * K.transition i j * f j * g i) +
        (∑ i, ∑ j, p.weight i * K.transition i j * f j * g j)) := by
          congr 1
          calc
            (∑ i, ∑ j, p.weight i * K.transition i j * (f i - f j) * (g i - g j)) =
                ∑ i, ∑ j, (p.weight i * K.transition i j * f i * g i -
                  p.weight i * K.transition i j * f i * g j -
                  p.weight i * K.transition i j * f j * g i +
                  p.weight i * K.transition i j * f j * g j) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
            _ = (∑ i, ∑ j, p.weight i * K.transition i j * f i * g i) -
                (∑ i, ∑ j, p.weight i * K.transition i j * f i * g j) -
                (∑ i, ∑ j, p.weight i * K.transition i j * f j * g i) +
                (∑ i, ∑ j, p.weight i * K.transition i j * f j * g j) := by
                    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = (∑ i, p.weight i * f i * g i) -
        (∑ i, ∑ j, p.weight i * K.transition i j * f i * g j) := by
          rw [hdiagLeft, hdiagRight, hcross]
          ring
    _ = (∑ i, p.weight i * f i * g i) -
        (∑ i, p.weight i * f i * ∑ j, K.transition i j * g j) := by rw [hcrossRight]
    _ = ∑ i, p.weight i * (f i * (g i - ∑ j, K.transition i j * g j)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
end FiniteKernel

end LeanPhy.StatMech
