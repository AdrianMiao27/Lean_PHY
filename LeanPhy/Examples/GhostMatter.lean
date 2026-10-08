import LeanPhy.GaugeTheory.LieGhostMatterCohomology
import LeanPhy.GaugeTheory.LieGhostFamily
import Mathlib.Data.ZMod.Basic

/-!
# Matter ghost calculations with parameter and torsion dependence

The adjoint matter action recovers the center as constant closed states.
A one-dimensional character shows why closedness cannot be inferred from
the pure ghost complex. Over rings with zero divisors, nonzero weights can
annihilate nonzero matter vectors; these states remain non-exact.
-/

namespace LeanPhy.Examples.GhostMatter

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial
open scoped TensorProduct

set_option maxSynthPendingDepth 7

variable {R : Type*} [CommRing R]

/-- A one-dimensional character of the solvable Lie family, valid over all rings. -/
def character (a b t : R) : LieModule (LieGhostFamily.algebra a b) R where
  act v m := t * v 0 * m
  act_add_left' := by intros; simp; ring
  act_smul_left' := by intros; simp; ring
  act_add_right' := by intros; ring
  act_smul_right' := by intros; simp; ring
  bracket_act' := by intros; simp [LieGhostFamily.algebra, LieGhostFamily.bracket]; ring

theorem character_constant (a b t m : R) :
    matterDifferential (character a b t) (matterZero m) = generator 0 ⊗ₜ[R] (t * m) := by
  rw [matterDifferential_zero]
  simp [matterOne, differential0, character, Fin.sum_univ_succ]

/-- Weight times vector, rather than weight alone, controls closure over rings. -/
theorem character_constant_closed_iff (a b t m : R) :
    matterDifferential (character a b t) (matterZero m) = 0 ↔ t * m = 0 := by
  rw [matterZero_closed_iff]
  constructor
  · intro h; simpa [character] using h (Pi.single 0 1)
  · intro h v
    change t * v 0 * m = 0
    calc
      _ = v 0 * (t * m) := by ring
      _ = 0 := by rw [h, mul_zero]

/-- Adjoint matter closure detects the full center, with all parameter degenerations. -/
theorem adjoint_constant_closed_iff (a b : R) (m : Fin 3 → R) :
    matterDifferential (adjointLieModule (LieGhostFamily.algebra a b)) (matterZero m) = 0 ↔
      a * m 0 = 0 ∧ b * m 0 = 0 ∧ a * m 1 = 0 ∧ b * m 2 = 0 := by
  rw [matterZero_closed_iff]
  constructor
  · intro h
    have h01 := congrFun (h (Pi.single 0 1)) 1
    have h02 := congrFun (h (Pi.single 0 1)) 2
    have h10 := congrFun (h (Pi.single 1 1)) 1
    have h20 := congrFun (h (Pi.single 2 1)) 2
    simp [adjointLieModule, LieGhostFamily.algebra, LieGhostFamily.bracket] at h01 h02 h10 h20
    exact ⟨h10, h20, h01, h02⟩
  · rintro ⟨ha0, hb0, ha1, hb2⟩ v
    ext i; fin_cases i
    · rfl
    · change a * (v 0 * m 1 - v 1 * m 0) = 0
      calc
        _ = v 0 * (a * m 1) - v 1 * (a * m 0) := by ring
        _ = 0 := by rw [ha0, ha1]; simp
    · change b * (v 0 * m 2 - v 2 * m 0) = 0
      calc
        _ = v 0 * (b * m 2) - v 2 * (b * m 0) := by ring
        _ = 0 := by rw [hb0, hb2]; simp

theorem charged_constant_not_closed :
    matterDifferential (character (1 : ℚ) 1 1) (matterZero (1 : ℚ)) ≠ 0 := by
  rw [ne_eq, character_constant_closed_iff]
  norm_num

theorem zero_divisor_constant_closed :
    matterDifferential (character (1 : ZMod 6) 1 2) (matterZero (3 : ZMod 6)) = 0 := by
  rw [character_constant_closed_iff]
  decide

theorem zero_divisor_constant_not_exact :
    ¬∃ y, matterDifferential (character (1 : ZMod 6) 1 2) y = matterZero (3 : ZMod 6) := by
  rw [matterZero_exact_iff]
  decide

theorem torsion_adjoint_closed :
    matterDifferential (adjointLieModule (LieGhostFamily.algebra (2 : ZMod 6) 3))
      (matterZero (![0, 3, 2] : Fin 3 → ZMod 6)) = 0 := by
  rw [adjoint_constant_closed_iff]
  decide

theorem torsion_adjoint_not_exact :
    ¬∃ y, matterDifferential (adjointLieModule (LieGhostFamily.algebra (2 : ZMod 6) 3)) y =
      matterZero (![0, 3, 2] : Fin 3 → ZMod 6) := by
  rw [matterZero_exact_iff]
  intro h
  have h1 := congrFun h 1
  exact (by decide : (3 : ZMod 6) ≠ 0) h1

end LeanPhy.Examples.GhostMatter
