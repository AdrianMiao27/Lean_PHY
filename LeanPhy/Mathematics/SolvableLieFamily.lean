import LeanPhy.Mathematics.DiagonalCohomology
import LeanPhy.Mathematics.FiniteLieCohomology

/-!
# A complete three-parameter Lie-cohomology family

The bracket is `[e₀,e₁] = a e₁`, `[e₀,e₂] = b e₂`, `[e₁,e₂] = 0`.
The scalar coefficient action is `e₀ · m = t m`, with the other generators
acting trivially. Over any field the full H2 has one coordinate for each of
`t = a`, `t = b`, and `t = a + b`, counted separately when conditions coincide.
The parameter-safe reduction supplies actual quotient equivalences and
primitives even on the intersecting exceptional sets.
-/

namespace LeanPhy.Mathematics.SolvableLieFamily

open LieCohomology LieCochainCoordinates
open scoped _root_.Classical

set_option maxSynthPendingDepth 5

noncomputable section

variable {K : Type*} [Field K]

abbrev Space (K : Type*) := Fin 3 → K

def bracket (a b : K) (x y : Space K) : Space K :=
  ![0, a * (x 0 * y 1 - x 1 * y 0), b * (x 0 * y 2 - x 2 * y 0)]

def algebra (a b : K) : LieAlgebra K (Space K) where
  bracket := bracket a b
  add_left := by intros; ext i; fin_cases i <;> simp [bracket] <;> ring
  add_right := by intros; ext i; fin_cases i <;> simp [bracket] <;> ring
  smul_left := by intros; ext i; fin_cases i <;> simp [bracket] <;> ring
  smul_right := by intros; ext i; fin_cases i <;> simp [bracket] <;> ring
  zero_left := by intros; ext i; fin_cases i <;> simp [bracket]
  alternating := by intros; ext i; fin_cases i <;> dsimp [bracket] <;> ring
  antisymm := by intros; ext i; fin_cases i <;> simp [bracket] <;> ring
  jacobi := by intros; ext i; fin_cases i <;> simp [bracket] <;> ring

def coefficients (a b t : K) : LieModule (algebra a b) K where
  act x m := t * x 0 * m
  act_add_left' := by intros; simp; ring
  act_smul_left' := by intros; simp; ring
  act_add_right' := by intros; ring
  act_smul_right' := by intros; simp; ring
  bracket_act' := by intros; simp [algebra, bracket]; ring

abbrev C2 (a b t : K) := LieCochain2 (algebra a b) (coefficients a b t)

def oneValues (φ : Space K →ₗ[K] K) : Fin 3 → K := ![φ (e 1), φ (e 2), φ (e 0)]

def oneFrom (c : Fin 3 → K) : Space K →ₗ[K] K where
  toFun x := c 0 * x 1 + c 1 * x 2 + c 2 * x 0
  map_add' := by intros; simp; ring
  map_smul' := by intros; simp; ring

/-- Reordering one-cochain coordinates makes the first CE matrix diagonal. -/
def oneCoordinates : (Space K →ₗ[K] K) ≃ₗ[K] (Fin 3 → K) where
  toFun := oneValues
  invFun := oneFrom
  left_inv φ := by
    apply (Pi.basisFun K (Fin 3)).ext
    intro i
    fin_cases i <;> simp [oneFrom, oneValues, e, Pi.basisFun_apply]
  right_inv c := by ext i; fin_cases i <;> simp [oneFrom, oneValues, e]
  map_add' := by intros; ext i; fin_cases i <;> simp [oneValues]
  map_smul' := by intros; ext i; fin_cases i <;> simp [oneValues]

def twoCoordinates (a b t : K) : C2 a b t ≃ₗ[K] (Fin 3 → K) :=
  twoEquiv (algebra a b) (coefficients a b t)

def boundaryWeights (a b t : K) : Fin 3 → K := ![t - a, t - b, 0]

def closureWeights (a b t : K) : Fin 3 → K := ![0, 0, t - (a + b)]

theorem weights_chain (a b t : K) (i : Fin 3) :
    closureWeights a b t i * boundaryWeights a b t i = 0 := by
  fin_cases i <;> simp [boundaryWeights, closureWeights]

def readThird : (Space K →ₗ[K] Space K →ₗ[K] Space K →ₗ[K] K) →ₗ[K] (Fin 3 → K) where
  toFun t := ![0, 0, t (e 0) (e 1) (e 2)]
  map_add' := by intros; ext i; fin_cases i <;> simp
  map_smul' := by intros; ext i; fin_cases i <;> simp

theorem readThird_detect (a b t : K) (ω : C2 a b t)
    (h : readThird (differential2 (coefficients a b t) ω) = 0) :
    differential2 (coefficients a b t) ω = 0 := by
  have hs : differential2 (coefficients a b t) ω (e 0) (e 1) (e 2) = 0 := congrFun h 2
  apply differential2_eq_zero_of_increasing
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hij <;> norm_num at hjk
  exact hs

theorem differential1_coordinates (a b t : K) (φ : Space K →ₗ[K] K) :
    twoCoordinates a b t (differential1 (coefficients a b t) φ) =
      DiagonalCohomology.diagonal (boundaryWeights a b t) (oneCoordinates φ) := by
  obtain ⟨c, rfl⟩ := oneCoordinates.symm.surjective φ
  rw [oneCoordinates.apply_symm_apply]
  change twoComponents (differential1 (coefficients a b t) (oneFrom c)) = _
  ext i
  fin_cases i <;>
    simp [twoComponents, differential1, coefficients, algebra, bracket, oneFrom, e,
      DiagonalCohomology.diagonal, boundaryWeights] <;> ring

theorem differential2_coordinates (a b t : K) (ω : C2 a b t) :
    DiagonalCohomology.diagonal (closureWeights a b t) (twoCoordinates a b t ω) =
      readThird (differential2 (coefficients a b t) ω) := by
  obtain ⟨c, rfl⟩ := (twoCoordinates a b t).symm.surjective ω
  rw [LinearEquiv.apply_symm_apply]
  change DiagonalCohomology.diagonal (closureWeights a b t) c =
    readThird (differential2 (coefficients a b t) (twoOfComponents c))
  ext i
  fin_cases i <;>
    simp [readThird, differential2_apply, coefficients, algebra, bracket, twoOfComponents, e,
      DiagonalCohomology.diagonal, closureWeights]; ring

/-- A dependent coordinate type retains all resonances, including their intersections. -/
abbrev Surviving (a b t : K) :=
  DiagonalCohomology.Surviving (boundaryWeights a b t) (closureWeights a b t)

def reduction (a b t : K) : Reduction (coefficients a b t) (Surviving a b t → K) :=
  (DiagonalCohomology.reduction (boundaryWeights a b t) (closureWeights a b t)
    (weights_chain a b t)).transport oneCoordinates (twoCoordinates a b t) readThird
      (differential1_coordinates a b t) (differential2_coordinates a b t) (readThird_detect a b t)

def h2Equiv (a b t : K) : H2 (coefficients a b t) ≃ₗ[K] (Surviving a b t → K) :=
  (reduction a b t).h2Equiv _

/-- Closedness is a parameter equation on the `12` component. -/
theorem cocycle_iff (a b t : K) (ω : C2 a b t) :
    IsTwoCocycle (coefficients a b t) ω ↔ (t - (a + b)) * ω (e 1) (e 2) = 0 := by
  constructor
  · intro h
    have hz := congrArg (fun t => readThird t 2) h
    rw [← differential2_coordinates] at hz
    exact hz
  · intro h
    apply readThird_detect a b t ω
    rw [← differential2_coordinates]
    ext i
    fin_cases i <;> simp [DiagonalCohomology.diagonal, closureWeights, twoCoordinates,
      twoEquiv, twoComponents, h]

/-- The exact dimension at every point, including coinciding resonance loci. -/
theorem h2_finrank (a b t : K) :
    Module.finrank K (H2 (coefficients a b t)) =
      (if t = a then 1 else 0) + (if t = b then 1 else 0) + (if t = a + b then 1 else 0) := by
  rw [(h2Equiv a b t).finrank_eq]
  simp only [Module.finrank_fintype_fun_eq_card]
  change Fintype.card {i : Fin 3 // boundaryWeights a b t i = 0 ∧ closureWeights a b t i = 0} = _
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Fin.sum_univ_succ]
  simp [boundaryWeights, closureWeights, sub_eq_zero, add_assoc]

theorem generic_h2_zero (a b t : K) (ha : t ≠ a) (hb : t ≠ b) (hab : t ≠ a + b) :
    Module.finrank K (H2 (coefficients a b t)) = 0 := by
  simp [h2_finrank, ha, hb, hab]

/-- Vanishing of precisely the resonant coordinates characterizes boundaries. -/
theorem boundary_iff (a b t : K) (ω : C2 a b t)
    (hω : IsTwoCocycle (coefficients a b t) ω) :
    IsTwoCoboundary (coefficients a b t) ω ↔
      (t = a → ω (e 0) (e 1) = 0) ∧
      (t = b → ω (e 0) (e 2) = 0) ∧
      (t = a + b → ω (e 1) (e 2) = 0) := by
  change (∃ φ, differential1Linear (coefficients a b t) φ = ω) ↔ _
  rw [(reduction a b t).exact_iff ω hω]
  change DiagonalCohomology.project (boundaryWeights a b t) (closureWeights a b t)
    (twoCoordinates a b t ω) = 0 ↔ _
  rw [DiagonalCohomology.project_eq_zero_iff]
  simp [Fin.forall_fin_succ, boundaryWeights, closureWeights, sub_eq_zero,
    twoCoordinates, twoEquiv, twoComponents]

/-- The supplied primitive is obtained by safe coordinate-wise division. -/
theorem primitive_coordinates (a b t : K) (ω : C2 a b t) :
    oneCoordinates ((reduction a b t).primitive ω) =
      ![(t - a)⁻¹ * ω (e 0) (e 1), (t - b)⁻¹ * ω (e 0) (e 2), 0] := by
  change oneCoordinates (oneCoordinates.symm
    (DiagonalCohomology.diagonal (fun i => (boundaryWeights a b t i)⁻¹)
      (twoCoordinates a b t ω))) = _
  rw [oneCoordinates.apply_symm_apply]
  ext i
  fin_cases i <;> simp [DiagonalCohomology.diagonal, boundaryWeights,
    twoCoordinates, twoEquiv, twoComponents]

/-- Away from all resonance loci every cocycle has this explicit primitive. -/
theorem generic_primitive (a b t : K) (ha : t ≠ a) (hb : t ≠ b) (hab : t ≠ a + b)
    (ω : C2 a b t) (hω : IsTwoCocycle (coefficients a b t) ω) :
    differential1 (coefficients a b t) ((reduction a b t).primitive ω) = ω := by
  have hex := (boundary_iff a b t ω hω).mpr (by simp [ha, hb, hab])
  have hp := ((reduction a b t).exact_iff ω hω).mp hex
  have hn := (reduction a b t).normal_form ω hω
  rw [hp, map_zero, add_zero] at hn
  change differential1 (coefficients a b t) ((reduction a b t).primitive ω) = ω at hn
  exact hn

/-- Field extension preserves the complete dimension formula for this family. -/
theorem h2_finrank_map {F : Type*} [Field F] (f : K →+* F) (a b t : K) :
    Module.finrank F (H2 (coefficients (f a) (f b) (f t))) =
      Module.finrank K (H2 (coefficients a b t)) := by
  simp only [h2_finrank, ← map_add, f.injective.eq_iff]

/-- Within the same resonance pattern, classes transport by keeping their
surviving coordinates. This is a cohomology equivalence, not a Lie-algebra isomorphism. -/
def stratumEquiv (a b t a' b' t' : K)
    (h₀ : t = a ↔ t' = a') (h₁ : t = b ↔ t' = b') (h₂ : t = a + b ↔ t' = a' + b') :
    H2 (coefficients a b t) ≃ₗ[K] H2 (coefficients a' b' t') :=
  (h2Equiv a b t).trans
    ((LinearEquiv.piCongrLeft K (fun _ : Surviving a' b' t' => K)
      (DiagonalCohomology.survivingEquiv _ _ _ _ (by
        intro i
        fin_cases i <;> simp [boundaryWeights, closureWeights, sub_eq_zero, h₀, h₁, h₂]))).trans
      (h2Equiv a' b' t').symm)

/-- The first basic cocycle persists at every parameter point. -/
def unit01 (a b t : K) : C2 a b t := twoOfComponents ![1, 0, 0]

theorem unit01_closed (a b t : K) : IsTwoCocycle (coefficients a b t) (unit01 a b t) := by
  rw [cocycle_iff]
  simp [unit01, twoOfComponents, e]

/-- Its class becomes nontrivial exactly on the first resonance locus. -/
theorem unit01_exact_iff (a b t : K) :
    IsTwoCoboundary (coefficients a b t) (unit01 a b t) ↔ t ≠ a := by
  rw [boundary_iff a b t _ (unit01_closed a b t)]
  simp [unit01, twoOfComponents, e]

theorem unit01_class_nonzero_iff (a b t : K) :
    classOf (coefficients a b t) (unit01 a b t) (unit01_closed a b t) ≠ 0 ↔ t = a := by
  rw [ne_eq, classOf_eq_zero_iff, unit01_exact_iff, not_not]

/-- A third coordinate is a cocycle only on its own resonance locus. -/
def unit12 (a b t : K) : C2 a b t := twoOfComponents ![0, 0, 1]

theorem unit12_closed_iff (a b t : K) :
    IsTwoCocycle (coefficients a b t) (unit12 a b t) ↔ t = a + b := by
  rw [cocycle_iff]
  simp [unit12, twoOfComponents, e, sub_eq_zero]

/-- Explicit decomposition holds uniformly, without excluding exceptional parameters. -/
theorem normal_form (a b t : K) (ω : C2 a b t)
    (hω : IsTwoCocycle (coefficients a b t) ω) :
    differential1 (coefficients a b t) ((reduction a b t).primitive ω) +
      (reduction a b t).represent ((reduction a b t).project ω) = ω :=
  (reduction a b t).normal_form ω hω

end

end LeanPhy.Mathematics.SolvableLieFamily
