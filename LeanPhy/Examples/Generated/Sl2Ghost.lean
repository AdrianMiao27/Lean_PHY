import LeanPhy.GaugeTheory.LieGhostMatterCohomology

/- Generated candidate; compile and audit the entire file before accepting it.
Input SHA-256: cd693a789912436c0f9de4de93c44bbaa7c86176b4bf6ed66fa803ebe5a699c6
Finite ghosts; the optional matter extension requires a certified LieModule.
No physical cohomology identification is claimed. -/

namespace LeanPhy.Generated.Sl2Ghost

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial

set_option maxHeartbeats 800000
set_option maxRecDepth 4096
-- Fixed normalization sets serve every input dimension and sparsity pattern.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

abbrev Space := Fin 3 → ℚ
abbrev Ghosts := GhostPolynomial ℚ 3

def bracket (x y : Space) : Space := ![(1) * (x 1 * y 2 - x 2 * y 1), (2) * (x 0 * y 1 - x 1 * y 0), (-2) * (x 0 * y 2 - x 2 * y 0)]

def algebra : LeanPhy.Mathematics.LieAlgebra ℚ Space where
  bracket := bracket
  add_left := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  add_right := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  smul_left := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  smul_right := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  zero_left := by intros; ext r; fin_cases r <;> simp [bracket]
  alternating := by intros; ext r; fin_cases r <;> dsimp [bracket] <;> ring
  antisymm := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring
  jacobi := by intros; ext r; fin_cases r <;> simp [bracket] <;> ring

@[simp] theorem image_0 : lieImages algebra 0 = (-1 : ℚ) • (generator 1 * generator 2) := by
  norm_num [lieImages_formula, algebra, bracket, Fin.sum_univ_succ, Pi.single_apply]

@[simp] theorem image_1 : lieImages algebra 1 = (-2 : ℚ) • (generator 0 * generator 1) := by
  norm_num [lieImages_formula, algebra, bracket, Fin.sum_univ_succ, Pi.single_apply]

@[simp] theorem image_2 : lieImages algebra 2 = (2 : ℚ) • (generator 0 * generator 2) := by
  norm_num [lieImages_formula, algebra, bracket, Fin.sum_univ_succ, Pi.single_apply]

theorem image_closed_0 : lieDifferential algebra (lieImages algebra 0) = 0 :=
  lieImages_closed algebra 0

theorem image_closed_1 : lieDifferential algebra (lieImages algebra 1) = 0 :=
  lieImages_closed algebra 1

theorem image_closed_2 : lieDifferential algebra (lieImages algebra 2) = 0 :=
  lieImages_closed algebra 2

theorem images_closed : ∀ k, lieDifferential algebra (lieImages algebra k) = 0 :=
  lieImages_closed algebra

noncomputable def brst : GradedBRSTDifferential (grading (R := ℚ) (n := 3)) :=
  canonicalLieBRST algebra

/-- The same differential with its actual integer ghost degree. -/
noncomputable def integerBrst : GradedBRSTDifferential (lieDegreeGrading (R := ℚ) (n := 3)) :=
  integerLieBRST algebra

theorem integerBrst_eq (x : Ghosts) : integerBrst x = brst x := rfl

theorem brst_degree {d : Int} {x : Ghosts} (hx : x ∈ degree d) :
    brst x ∈ degree (d + 1) := lieDifferential_mem_degree algebra hx

theorem scalar_exact (r : ℚ) :
    brst.IsExact (algebraMap ℚ Ghosts r) ↔ r = 0 := scalar_exact_iff algebra r

theorem brst_nilpotent (x : Ghosts) : brst (brst x) = 0 := brst.nilpotent_apply x

theorem brst_leibniz (x y : Ghosts) :
    brst (x * y) = brst x * y + parityInvolution x * brst y :=
  lieDifferential_mul algebra x y

theorem ce_bridge (φ : Space →ₗ[ℚ] ℚ) :
    brst (ghostOne φ) = ghostTwo algebra (differential1 (trivialLieModule algebra) φ) :=
  lieDifferential_ghostOne algebra φ

theorem ce_two_bridge (ω : LieCochain2 algebra (trivialLieModule algebra : LieModule algebra ℚ)) :
    brst (ghostTwo algebra ω) = ghostThree algebra (differential2Cochain (trivialLieModule algebra) ω) :=
  lieDifferential_ghostTwo algebra ω

theorem ghost_closed_iff (ω : LieCochain2 algebra (trivialLieModule algebra : LieModule algebra ℚ)) :
    brst.IsClosed (ghostTwo algebra ω) ↔ IsTwoCocycle (trivialLieModule algebra) ω :=
  ghostTwo_closed_iff algebra ω

theorem ghost_exact_iff (ω : LieCochain2 algebra (trivialLieModule algebra : LieModule algebra ℚ)) :
    brst.IsExact (ghostTwo algebra ω) ↔ IsTwoCoboundary (trivialLieModule algebra) ω :=
  ghostTwo_exact_iff algebra ω

noncomputable def ghostH2Equiv : H2 (trivialLieModule algebra : LieModule algebra ℚ) ≃ₗ[ℚ] GhostH2 algebra :=
  h2GhostEquiv algebra

/-- A supplied, certified representation extends the generated ghost differential. -/
noncomputable def matterBrst {M : Type*} [AddCommGroup M] [Module ℚ M]
    (𝒨 : LieModule algebra M) : MatterGhost ℚ 3 M →ₗ[ℚ] MatterGhost ℚ 3 M :=
  matterDifferential 𝒨

theorem matter_nilpotent {M : Type*} [AddCommGroup M] [Module ℚ M]
    (𝒨 : LieModule algebra M) (x : MatterGhost ℚ 3 M) :
    matterBrst 𝒨 (matterBrst 𝒨 x) = 0 := matterDifferential_sq 𝒨 x

theorem matter_constant_closed_iff {M : Type*} [AddCommGroup M] [Module ℚ M]
    (𝒨 : LieModule algebra M) (m : M) :
    matterBrst 𝒨 (matterZero m) = 0 ↔ ∀ v, 𝒨.act v m = 0 := matterZero_closed_iff 𝒨 m

theorem matter_one_bridge {M : Type*} [AddCommGroup M] [Module ℚ M]
    (𝒨 : LieModule algebra M) (φ : LieCochain1 algebra 𝒨) :
    matterBrst 𝒨 (matterOne 𝒨 φ) = matterTwo 𝒨 (differential1 𝒨 φ) :=
  matterDifferential_one 𝒨 φ

end LeanPhy.Generated.Sl2Ghost
