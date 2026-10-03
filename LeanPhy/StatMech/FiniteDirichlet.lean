import LeanPhy.StatMech.FiniteDetailedBalance
import Mathlib.Tactic

/-!
# Finite Dirichlet forms for reversible dynamics

The same quadratic form appears as the dissipation of a reversible Markov
chain, the hopping energy of a finite lattice, a graph Laplacian form, and the
finite part of several measurement/post-processing models.  This file keeps
that common algebraic layer separate from spectral-gap estimates, mixing
rates, continuum limits and analytic functional inequalities.

All sums are finite.  The kernel and probability structures carry the
non-negativity and normalisation certificates, so a negative transition or an
unnormalised weight cannot enter the form accidentally.
-/

namespace LeanPhy.StatMech

open scoped BigOperators

namespace FiniteKernel

variable {ι : Type*} [Fintype ι]

/-! ## Definition and elementary algebra -/

/-- The finite Dirichlet form associated with a kernel and a reference
probability.  The factor `1/2` removes double counting for reversible kernels.
For arbitrary kernels the expression is still a well-defined finite energy.
-/
noncomputable def dirichletForm (K : FiniteKernel ι) (p : FiniteProbability ι)
    (f g : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j,
    p.weight i * K.transition i j * (f i - f j) * (g i - g j)

@[simp] theorem dirichletForm_apply (K : FiniteKernel ι) (p : FiniteProbability ι)
    (f g : ι → ℝ) :
    dirichletForm K p f g =
      (1 / 2 : ℝ) * ∑ i, ∑ j,
        p.weight i * K.transition i j * (f i - f j) * (g i - g j) := rfl

/-- The form is symmetric in its two observables.  This is an algebraic fact,
while the stronger weighted self-adjointness of the Markov pullback needs
detailed balance and is proved in `FiniteDetailedBalance`.
-/
theorem dirichletForm_swap (K : FiniteKernel ι) (p : FiniteProbability ι)
    (f g : ι → ℝ) :
    dirichletForm K p f g = dirichletForm K p g f := by
  unfold dirichletForm
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The quadratic Dirichlet energy is nonnegative for every finite Markov
kernel and probability.  No reversibility assumption is needed for this
pointwise statement because every coefficient and every squared difference is
nonnegative.
-/
theorem dirichletForm_nonneg (K : FiniteKernel ι) (p : FiniteProbability ι)
    (f : ι → ℝ) :
    0 ≤ dirichletForm K p f f := by
  unfold dirichletForm
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  apply mul_nonneg hhalf
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  have hcoeff : 0 ≤ p.weight i * K.transition i j :=
    mul_nonneg (p.nonneg i) (K.nonneg i j)
  calc
    p.weight i * K.transition i j * (f i - f j) * (f i - f j) =
        (p.weight i * K.transition i j) * ((f i - f j) * (f i - f j)) := by ring
    _ ≥ 0 := mul_nonneg hcoeff (mul_self_nonneg _)

/-- Adding a constant to the right observable gives a zero energy. -/
theorem dirichletForm_const_right (K : FiniteKernel ι) (p : FiniteProbability ι)
    (f : ι → ℝ) (c : ℝ) :
    dirichletForm K p f (fun _ => c) = 0 := by
  unfold dirichletForm
  simp

/-- Adding a constant to the left observable gives a zero energy. -/
theorem dirichletForm_const_left (K : FiniteKernel ι) (p : FiniteProbability ι)
    (g : ι → ℝ) (c : ℝ) :
    dirichletForm K p (fun _ => c) g = 0 := by
  unfold dirichletForm
  simp

/-- Bilinearity in the first observable. -/
theorem dirichletForm_add_left (K : FiniteKernel ι) (p : FiniteProbability ι)
    (f g h : ι → ℝ) :
    dirichletForm K p (fun i => f i + g i) h =
      dirichletForm K p f h + dirichletForm K p g h := by
  unfold dirichletForm
  simp only [Pi.add_apply]
  have hpoint (i j : ι) :
      p.weight i * K.transition i j * ((f i + g i) - (f j + g j)) * (h i - h j) =
        (p.weight i * K.transition i j * (f i - f j) * (h i - h j) +
          p.weight i * K.transition i j * (g i - g j) * (h i - h j)) := by
    ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  ring

/-- Bilinearity in the second observable. -/
theorem dirichletForm_add_right (K : FiniteKernel ι) (p : FiniteProbability ι)
    (f g h : ι → ℝ) :
    dirichletForm K p f (fun i => g i + h i) =
      dirichletForm K p f g + dirichletForm K p f h := by
  unfold dirichletForm
  simp only [Pi.add_apply]
  have hpoint (i j : ι) :
      p.weight i * K.transition i j * (f i - f j) * ((g i + h i) - (g j + h j)) =
        (p.weight i * K.transition i j * (f i - f j) * (g i - g j) +
          p.weight i * K.transition i j * (f i - f j) * (h i - h j)) := by
    ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  ring

/-! ## Domain-facing aliases -/

/-- Reversible finite Markov chains and Gibbs samplers. -/
noncomputable abbrev reversibleEnergy {ι : Type*} [Fintype ι] :=
  dirichletForm (ι := ι)

end FiniteKernel

end LeanPhy.StatMech

/-! The same finite contract under names used by neighbouring physics areas. -/

namespace LeanPhy

namespace StatMech
noncomputable abbrev FiniteDirichletEnergy {ι : Type*} [Fintype ι] :=
  FiniteKernel.dirichletForm (ι := ι)
end StatMech

namespace Condensed
noncomputable abbrev FiniteHoppingEnergy {ι : Type*} [Fintype ι] :=
  StatMech.FiniteKernel.dirichletForm (ι := ι)
end Condensed

namespace GaugeTheory
noncomputable abbrev FiniteLatticeDirichletEnergy {ι : Type*} [Fintype ι] :=
  StatMech.FiniteKernel.dirichletForm (ι := ι)
end GaugeTheory

namespace QuantumInfo
noncomputable abbrev FiniteMeasurementDirichletEnergy {ι : Type*} [Fintype ι] :=
  StatMech.FiniteKernel.dirichletForm (ι := ι)
end QuantumInfo

namespace Mathematics
noncomputable abbrev FiniteGraphDirichletEnergy {ι : Type*} [Fintype ι] :=
  StatMech.FiniteKernel.dirichletForm (ι := ι)
end Mathematics

end LeanPhy
