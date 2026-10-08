import LeanPhy.GaugeTheory.LieGhostCohomology
import LeanPhy.GaugeTheory.LieGhostFamily
import LeanPhy.Examples.HeisenbergCohomology
import LeanPhy.Mathematics.SolvableLieFamily
import Mathlib.Data.ZMod.Basic

/-!
# Complete ghost H² calculations and nonzero classes

The quotient equivalence transfers an existing CE reduction to Heisenberg
ghosts. A parameter family retains every exceptional locus. No identification
with physical observables is asserted.
-/

namespace LeanPhy.Examples.GhostCohomology

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial
open scoped _root_.Classical

set_option maxSynthPendingDepth 7

noncomputable def heisenbergEquiv : GhostH2 HeisenbergCohomology.algebra ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  ghostH2ReductionEquiv HeisenbergCohomology.algebra HeisenbergCohomology.reduction

theorem heisenberg_dimension : Module.finrank ℚ (GhostH2 HeisenbergCohomology.algebra) = 2 := by
  rw [heisenbergEquiv.finrank_eq]
  simp

theorem heisenberg_boundary_iff (ω : HeisenbergCohomology.C2) :
    (∃ y, lieDifferential HeisenbergCohomology.algebra y = ghostTwo HeisenbergCohomology.algebra ω) ↔
      ω (Pi.single 0 1) (Pi.single 2 1) = 0 ∧ ω (Pi.single 1 1) (Pi.single 2 1) = 0 := by
  rw [ghostTwo_exact_iff]
  exact HeisenbergCohomology.boundary_iff ω

theorem heisenberg_all_degree_two_closed {x : GhostPolynomial ℚ 3} (hx : x ∈ natDegree 2) :
    lieDifferential HeisenbergCohomology.algebra x = 0 := by
  obtain ⟨ω, rfl⟩ := natDegree_two_le_range HeisenbergCohomology.algebra hx
  exact (ghostTwo_closed_iff _ ω).mpr (HeisenbergCohomology.all_closed ω)

theorem heisenberg_all_boundaries {x : GhostPolynomial ℚ 3} (hx : x ∈ natDegree 2) :
    (∃ y, lieDifferential HeisenbergCohomology.algebra y = x) ↔
      pairCoefficient 0 2 x = 0 ∧ pairCoefficient 1 2 x = 0 := by
  obtain ⟨ω, rfl⟩ := natDegree_two_le_range HeisenbergCohomology.algebra hx
  rw [pairCoefficient_ghostTwo _ ω 0 2 (by decide), pairCoefficient_ghostTwo _ ω 1 2 (by decide)]
  exact heisenberg_boundary_iff ω

theorem heisenberg_class_coordinates (ω : HeisenbergCohomology.C2) :
    heisenbergEquiv
      (twoGhostClass HeisenbergCohomology.algebra (ghostTwo HeisenbergCohomology.algebra ω)
        (ghostTwo_mem_natDegree _ ω) ((ghostTwo_closed_iff _ ω).mpr (HeisenbergCohomology.all_closed ω))) =
      HeisenbergCohomology.parameters ω := by
  exact (ghostH2ReductionEquiv_classOf _ _ ω (HeisenbergCohomology.all_closed ω)).trans (HeisenbergCohomology.project_eq_parameters ω)

/-- Nonzero ghost pairs need not be exact, even if arbitrary-degree primitives are allowed. -/
theorem family_pair_not_exact {R : Type*} [CommRing R] [Nontrivial R] (a b : R) :
    ¬∃ y, lieDifferential (LieGhostFamily.algebra a b) y = generator 1 * generator 2 := by
  rw [← ghostTwo_coordinateTwo (LieGhostFamily.algebra a b) 1 2 (by decide), ghostTwo_exact_iff]
  rintro ⟨φ, hφ⟩
  have h := congrArg (fun ω : LieCochain2 (LieGhostFamily.algebra a b)
    (trivialLieModule (LieGhostFamily.algebra a b) : LieModule (LieGhostFamily.algebra a b) R) =>
      ω (Pi.single 1 1) (Pi.single 2 1)) hφ
  have hzero : (![0, 0, 0] : Fin 3 → R) = 0 := by ext i; fin_cases i <;> rfl
  simp [hzero, differential1, trivialLieModule, LieGhostFamily.algebra, LieGhostFamily.bracket,
    coordinateTwo] at h

theorem family_pair_closed {R : Type*} [CommRing R] (a b : R) (h : a + b = 0) :
    lieDifferential (LieGhostFamily.algebra a b) (generator 1 * generator 2) = 0 :=
  (LieGhostFamily.pair_closed_iff a b).mpr h

theorem family_pair_class_nonzero {R : Type*} [CommRing R] [Nontrivial R]
    (a b : R) (h : a + b = 0) :
    twoGhostClass (LieGhostFamily.algebra a b) (generator 1 * generator 2)
      (mul_mem_natDegree (generator_mem_natDegree 1) (generator_mem_natDegree 2))
      (family_pair_closed a b h) ≠ 0 := by
  intro hz
  exact family_pair_not_exact a b ((twoGhostClass_eq_zero_iff (LieGhostFamily.algebra a b)
    (generator 1 * generator 2)
    (mul_mem_natDegree (generator_mem_natDegree 1) (generator_mem_natDegree 2))
    (family_pair_closed a b h)).mp hz)

private theorem coefficients_zero {K : Type*} [Field K] (a b : K) :
    SolvableLieFamily.coefficients a b 0 = trivialLieModule (SolvableLieFamily.algebra a b) := by
  unfold SolvableLieFamily.coefficients trivialLieModule
  congr 1
  funext x m
  simp

theorem family_dimension {K : Type*} [Field K] (a b : K) :
    Module.finrank K (GhostH2 (LieGhostFamily.algebra a b)) =
      (if a = 0 then 1 else 0) + (if b = 0 then 1 else 0) + (if a + b = 0 then 1 else 0) := by
  classical
  rw [← (h2GhostEquiv (LieGhostFamily.algebra a b)).finrank_eq]
  change Module.finrank K (H2 (trivialLieModule (SolvableLieFamily.algebra a b) :
    LieModule (SolvableLieFamily.algebra a b) K)) = _
  rw [← coefficients_zero]
  simpa only [eq_comm] using SolvableLieFamily.h2_finrank a b 0

theorem family_generic : Module.finrank ℚ (GhostH2 (LieGhostFamily.algebra (1 : ℚ) 1)) = 0 := by
  norm_num [family_dimension]

theorem family_resonant : Module.finrank ℚ (GhostH2 (LieGhostFamily.algebra (1 : ℚ) (-1))) = 1 := by
  norm_num [family_dimension]

theorem family_abelian : Module.finrank ℚ (GhostH2 (LieGhostFamily.algebra (0 : ℚ) 0)) = 3 := by
  norm_num [family_dimension]

theorem characteristic_two_dimension :
    Module.finrank (ZMod 2) (GhostH2 (LieGhostFamily.algebra (1 : ZMod 2) 1)) = 1 := by
  norm_num [family_dimension]
  decide

theorem zero_divisor_pair_nonzero :
    twoGhostClass (LieGhostFamily.algebra (3 : ZMod 6) 3) (generator 1 * generator 2)
      (mul_mem_natDegree (generator_mem_natDegree 1) (generator_mem_natDegree 2))
      (family_pair_closed 3 3 (by decide)) ≠ 0 := by
  let : Fact (1 < (6 : Nat)) := ⟨by decide⟩
  exact family_pair_class_nonzero 3 3 (by decide)

end LeanPhy.Examples.GhostCohomology
