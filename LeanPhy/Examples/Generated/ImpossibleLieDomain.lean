import LeanPhy.Mathematics.FiniteLieCohomology
import Mathlib.Tactic

/- Validity candidate only; no cohomology computation.
Input SHA-256: 157fc0e62181dcb456c28e158fea60db5015611db5990145756bdba509701697
Compile the entire file to check necessity and sufficiency of the conditions. -/

/- The model and every H2 conclusion below retain the declared parameter
conditions. The preceding matrices are connected to complete CE cochains. -/
namespace LeanPhy.Generated.ImpossibleLieDomain

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates
open scoped _root_.Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
set_option maxSynthPendingDepth 5
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

abbrev Space (K : Type*) := Fin 3 → K
abbrev Coeff (K : Type*) := Fin 1 → K

/-- All input constraints are proof fields, not unchecked metadata. -/
structure Conditions (p : Fin 0 → K) : Prop where
  q0 : (1 : K) = 0

def bracket (p : Fin 0 → K) (x y : Space K) : Space K := ![(1) * (x 0 * y 1 - x 1 * y 0), (1) * (x 1 * y 2 - x 2 * y 1), 0]

def algebra (p : Fin 0 → K) (hp : Conditions p) : LeanPhy.Mathematics.LieAlgebra K (Space K) where
  bracket := bracket p
  add_left := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  add_right := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  smul_left := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  smul_right := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  zero_left := by intros; ext r; fin_cases r <;> simp [bracket]
  alternating := by intros; ext r; fin_cases r <;> dsimp [bracket] <;> ring
  antisymm := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  jacobi := by rcases hp with ⟨q0⟩; intros; ext r; fin_cases r <;> simp [bracket] <;> (try ring_nf) <;> grind

def action (p : Fin 0 → K) (x : Space K) (v : Coeff K) : Coeff K := ![0]

def coefficients (p : Fin 0 → K) (hp : Conditions p) : LeanPhy.Mathematics.LieModule (algebra p hp) (Coeff K) where
  act := action p
  act_add_left' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  act_smul_left' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  act_add_right' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  act_smul_right' := by intros; ext r; fin_cases r <;> simp [action] <;> ring
  bracket_act' := by rcases hp with ⟨q0⟩; intros; ext r; fin_cases r <;> simp [algebra, bracket, action] <;> (try ring_nf) <;> grind

/-- Extra restrictions supplied by the user, separate from discovered laws. -/
structure UserConditions (p : Fin 0 → K) : Prop where


/-- The full laws on arbitrary vectors, independent of any parameter equations. -/
structure ModelLaws (p : Fin 0 → K) : Prop where
  jacobi : ∀ x y z : Space K,
    bracket p x (bracket p y z) + bracket p y (bracket p z x) + bracket p z (bracket p x y) = 0
  representation : ∀ (x y : Space K) (v : Coeff K),
    action p (bracket p x y) v = action p x (action p y v) - action p y (action p x v)

/-- Exact admissibility: neither a missing equation nor an unnecessary extra
law restriction can pass both directions of this theorem. -/
theorem conditions_iff (p : Fin 0 → K) :
    Conditions p ↔ UserConditions p ∧ ModelLaws p := by
  constructor
  · intro hp
    refine ⟨⟨⟩, ?_⟩
    constructor
    · exact (algebra p hp).jacobi
    · exact (coefficients p hp).bracket_act'
  · rintro ⟨hu, hl⟩
    constructor
    · have hs := congrFun (hl.jacobi (e 0) (e 1) (e 2)) 0
      norm_num [bracket, action, e] at hs
      all_goals (try norm_num [bracket, action, e]) <;> grind

/-- Actual Lie algebra and module structures exist with exactly the supplied
bracket/action iff the discovered equations and user restrictions hold. -/
theorem conditions_iff_model (p : Fin 0 → K) :
    Conditions p ↔ UserConditions p ∧
      ∃ L : LeanPhy.Mathematics.LieAlgebra K (Space K), L.bracket = bracket p ∧
        ∃ M : LeanPhy.Mathematics.LieModule L (Coeff K), M.act = action p := by
  constructor
  · intro hp
    exact ⟨((conditions_iff p).mp hp).1, algebra p hp, rfl, coefficients p hp, rfl⟩
  · rintro ⟨hu, L, hL, M, hM⟩
    apply (conditions_iff p).mpr
    refine ⟨hu, ?_⟩
    constructor
    · intro x y z
      simpa only [hL] using L.jacobi x y z
    · intro x y v
      simpa only [hL, hM] using M.bracket_act' x y v

theorem invalid_of_conditions_fail (p : Fin 0 → K)
    (hu : UserConditions p) (h : ¬Conditions p) : ¬ModelLaws p := by
  intro hl
  exact h ((conditions_iff p).mpr ⟨hu, hl⟩)

end
end LeanPhy.Generated.ImpossibleLieDomain
