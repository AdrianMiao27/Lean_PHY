import LeanPhy.Mathematics.CohomologyReduction
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Parameter-safe cohomology of a diagonal complex

For diagonal differentials with weights `u`, `v` and `v i * u i = 0`,
cohomology consists exactly of coordinates where both weights vanish.
The reduction uses total field inverses and explicit zero tests. It is valid
at every parameter value, including simultaneous degeneracies; no generic
nonvanishing assumption is silently used at exceptional points.
-/

namespace LeanPhy.Mathematics.DiagonalCohomology

open LeanPhy.Mathematics
open scoped _root_.Classical

noncomputable section

variable {K I : Type*} [Field K]

/-- Coordinate-wise multiplication, as a linear map. -/
def diagonal (u : I → K) : (I → K) →ₗ[K] (I → K) where
  toFun x i := u i * x i
  map_add' := by intros; ext i; simp [mul_add]
  map_smul' := by intros; ext i; simp [mul_left_comm]

@[simp] theorem diagonal_apply (u x : I → K) (i : I) : diagonal u x i = u i * x i := rfl

/-- A surviving coordinate is closed and cannot be reached by the previous map. -/
abbrev Surviving (u v : I → K) := {i : I // u i = 0 ∧ v i = 0}

def project (u v : I → K) : (I → K) →ₗ[K] (Surviving u v → K) where
  toFun x i := x i.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem project_eq_zero_iff (u v x : I → K) :
    project u v x = 0 ↔ ∀ i, u i = 0 → v i = 0 → x i = 0 := by
  constructor
  · intro h i hu hv; exact congrFun h ⟨i, hu, hv⟩
  · intro h; funext i; exact h i.val i.property.1 i.property.2

def represent (u v : I → K) : (Surviving u v → K) →ₗ[K] (I → K) where
  toFun x i := if h : u i = 0 ∧ v i = 0 then x ⟨i, h⟩ else 0
  map_add' := by intros; ext i; dsimp; split_ifs <;> simp
  map_smul' := by intros; ext i; dsimp; split_ifs <;> simp

/-- An unconditional reduction covering every vanishing pattern. -/
def reduction (u v : I → K) (huv : ∀ i, v i * u i = 0) :
    CohomologyReduction (diagonal u) (diagonal v) (Surviving u v → K) where
  project := project u v
  represent := represent u v
  primitive := diagonal (fun i => (u i)⁻¹)
  correction := diagonal (fun i => (v i)⁻¹)
  chain := by ext x i; change v i * (u i * x i) = 0; rw [← mul_assoc, huv, zero_mul]
  closed := by
    ext x i
    change v i * (if h : u i = 0 ∧ v i = 0 then x ⟨i, h⟩ else 0) = 0
    split_ifs with h
    · rw [h.2, zero_mul]
    · exact mul_zero _
  boundary := by
    ext x i
    change u i.val * x i.val = 0
    rw [i.property.1, zero_mul]
  retract := by
    ext x i
    change (if h : u i.val = 0 ∧ v i.val = 0 then x ⟨i.val, h⟩ else 0) = x i
    simp [i.property]
  decompose := by
    ext x i
    change u i * ((u i)⁻¹ * x i) +
      (if h : u i = 0 ∧ v i = 0 then x i else 0) + (v i)⁻¹ * (v i * x i) = x i
    by_cases hu : u i = 0
    · by_cases hv : v i = 0
      · simp [hu, hv]
      · simp [hu, hv]
    · have hv : v i = 0 := (mul_eq_zero.mp (huv i)).resolve_right hu
      simp [hu, hv]

/-- The actual quotient is equivalent to the surviving coordinate space. -/
def cohomologyEquiv (u v : I → K) (huv : ∀ i, v i * u i = 0) :
    CohomologyReduction.Cohomology (diagonal u) (diagonal v) ≃ₗ[K] (Surviving u v → K) :=
  (reduction u v huv).quotientEquiv

/-- Matching vanishing patterns identify the surviving coordinate labels. -/
def survivingEquiv (u v u' v' : I → K)
    (h : ∀ i, (u i = 0 ∧ v i = 0) ↔ (u' i = 0 ∧ v' i = 0)) :
    Surviving u v ≃ Surviving u' v' where
  toFun i := ⟨i.val, (h i.val).mp i.property⟩
  invFun i := ⟨i.val, (h i.val).mpr i.property⟩
  left_inv := by intro i; rfl
  right_inv := by intro i; rfl

/-- The cohomologies are explicitly equivalent within a fixed vanishing stratum. -/
def stratumEquiv (u v u' v' : I → K)
    (huv : ∀ i, v i * u i = 0) (huv' : ∀ i, v' i * u' i = 0)
    (h : ∀ i, (u i = 0 ∧ v i = 0) ↔ (u' i = 0 ∧ v' i = 0)) :
    CohomologyReduction.Cohomology (diagonal u) (diagonal v) ≃ₗ[K]
      CohomologyReduction.Cohomology (diagonal u') (diagonal v') :=
  (cohomologyEquiv u v huv).trans
    ((LinearEquiv.piCongrLeft K (fun _ : Surviving u' v' => K) (survivingEquiv u v u' v' h)).trans
      (cohomologyEquiv u' v' huv').symm)

/-- Exactness requires closedness and vanishing on the surviving coordinates. -/
theorem exact_iff (u v : I → K) (huv : ∀ i, v i * u i = 0)
    (x : I → K) (hx : diagonal v x = 0) :
    (∃ y, diagonal u y = x) ↔ ∀ i, u i = 0 → v i = 0 → x i = 0 := by
  rw [(reduction u v huv).exact_iff x hx]
  change (fun i : Surviving u v => x i.val) = 0 ↔ _
  constructor
  · intro h i hu hv; exact congrFun h ⟨i, hu, hv⟩
  · intro h; funext i; exact h i.val i.property.1 i.property.2

/-- Dimension counts vanishing coordinates rather than generic pivots. -/
theorem finrank_eq [Fintype I] (u v : I → K) (huv : ∀ i, v i * u i = 0) :
    Module.finrank K (CohomologyReduction.Cohomology (diagonal u) (diagonal v)) =
      Fintype.card (Surviving u v) := by
  rw [(cohomologyEquiv u v huv).finrank_eq]
  simp

end

end LeanPhy.Mathematics.DiagonalCohomology
