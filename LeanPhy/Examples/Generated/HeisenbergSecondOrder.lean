import LeanPhy.Mathematics.LieDeformationGauge
import LeanPhy.Mathematics.LieDeformationReduction
import LeanPhy.Mathematics.FiniteLieCohomology
import Mathlib.LinearAlgebra.Dimension.Constructions

/- Generated candidate: compile with `lake env lean` before treating it as checked.
Input SHA-256: 4e839672b9535c60d48f3e63b3f63b40c2958abf3277f0eb8892e0c02c832a0c
The matrices below are the mathematical input; no physical interpretation is inferred. -/
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace LeanPhy.Generated.HeisenbergSecondOrderCE

open LeanPhy.Mathematics

def d1 : Matrix (Fin 9) (Fin 9) ℚ :=
  !![0, 0, 0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, -1, 0;
    1, 0, 0, 0, 1, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, -1, 0, 0]

def d2 : Matrix (Fin 3) (Fin 9) ℚ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 1, 0]

def project : Matrix (Fin 5) (Fin 9) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, -1;
    0, 1, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0]

def represent : Matrix (Fin 9) (Fin 5) ℚ :=
  !![1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 0, 0, 0;
    0, 0, 0, 0, -1;
    0, 0, 1, 0, 0;
    0, 0, 0, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1;
    0, 0, 0, 0, 0]

def primitive : Matrix (Fin 9) (Fin 9) ℚ :=
  !![0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0]

def correction : Matrix (Fin 9) (Fin 3) ℚ :=
  !![0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 1;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0]

def certificate : MatrixCohomologyReduction d1 d2 5 where
  project := project
  represent := represent
  primitive := primitive
  correction := correction
  chain := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project, represent, primitive, correction, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply]
  closed := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project, represent, primitive, correction, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply]
  boundary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project, represent, primitive, correction, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply]
  retract := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project, represent, primitive, correction, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply]
  decompose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project, represent, primitive, correction, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply]

noncomputable def cohomologyEquiv :
    CohomologyReduction.Cohomology d1.toLin' d2.toLin' ≃ₗ[ℚ] (Fin 5 → ℚ) :=
  certificate.toReduction.quotientEquiv

theorem exact_iff (x : Fin 9 → ℚ) (hx : d2.toLin' x = 0) :
    (∃ a, d1.toLin' a = x) ↔ project.toLin' x = 0 :=
  certificate.toReduction.exact_iff x hx

end LeanPhy.Generated.HeisenbergSecondOrderCE

/- The following namespace proves that the matrices above compute the actual
Lie H2 of the declared structure constants and coefficient representation. -/
namespace LeanPhy.Generated.HeisenbergSecondOrder

-- Three nested linear maps with vector coefficients need this elaboration depth.
set_option maxSynthPendingDepth 5

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates

abbrev Space := Fin 3 → ℚ
abbrev Coeff := Fin 3 → ℚ

def bracket (x y : Space) : Space := ![0, 0, (1) * (x 0 * y 1 - x 1 * y 0)]

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

def action (x : Space) (v : Coeff) : Coeff := bracket x v

def coefficients : LeanPhy.Mathematics.LieModule algebra Coeff := adjointLieModule algebra

theorem coefficients_adjoint : coefficients = adjointLieModule algebra := rfl

abbrev C2 := LieCochain2 algebra coefficients

def oneValues (φ : Space →ₗ[ℚ] Coeff) : Fin 9 → ℚ := ![φ (e 0) 0, φ (e 0) 1, φ (e 0) 2, φ (e 1) 0, φ (e 1) 1, φ (e 1) 2, φ (e 2) 0, φ (e 2) 1, φ (e 2) 2]

def oneFrom (a : Fin 9 → ℚ) : Space →ₗ[ℚ] Coeff where
  toFun x := ![a 0 * x 0 + a 3 * x 1 + a 6 * x 2, a 1 * x 0 + a 4 * x 1 + a 7 * x 2, a 2 * x 0 + a 5 * x 1 + a 8 * x 2]
  map_add' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul' := by intros; ext r; fin_cases r <;> simp <;> ring

noncomputable def oneCoordinates : (Space →ₗ[ℚ] Coeff) ≃ₗ[ℚ] (Fin 9 → ℚ) where
  toFun := oneValues
  invFun := oneFrom
  left_inv φ := by
    apply (Pi.basisFun ℚ (Fin 3)).ext
    intro i
    ext r
    fin_cases i <;> fin_cases r <;> simp [oneFrom, oneValues, e, Pi.basisFun_apply]
  right_inv a := by
    ext r
    fin_cases r <;> simp [oneFrom, oneValues, e]
  map_add' := by intros; ext r; fin_cases r <;> simp [oneValues]
  map_smul' := by intros; ext r; fin_cases r <;> simp [oneValues]

def twoValues (ω : C2) : Fin 9 → ℚ := ![ω (e 0) (e 1) 0, ω (e 0) (e 1) 1, ω (e 0) (e 1) 2, ω (e 0) (e 2) 0, ω (e 0) (e 2) 1, ω (e 0) (e 2) 2, ω (e 1) (e 2) 0, ω (e 1) (e 2) 1, ω (e 1) (e 2) 2]

def twoFrom (a : Fin 9 → ℚ) : C2 where
  eval x y := ![a 0 * (x 0 * y 1 - x 1 * y 0) + a 3 * (x 0 * y 2 - x 2 * y 0) + a 6 * (x 1 * y 2 - x 2 * y 1), a 1 * (x 0 * y 1 - x 1 * y 0) + a 4 * (x 0 * y 2 - x 2 * y 0) + a 7 * (x 1 * y 2 - x 2 * y 1), a 2 * (x 0 * y 1 - x 1 * y 0) + a 5 * (x 0 * y 2 - x 2 * y 0) + a 8 * (x 1 * y 2 - x 2 * y 1)]
  map_add_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_add_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_left' := by intros; ext r; fin_cases r <;> simp <;> ring
  map_smul_right' := by intros; ext r; fin_cases r <;> simp <;> ring
  alternating' := by intros; ext r; fin_cases r <;> dsimp <;> ring

noncomputable def twoCoordinates : C2 ≃ₗ[ℚ] (Fin 9 → ℚ) where
  toFun := twoValues
  invFun := twoFrom
  left_inv ω := by
    apply ext_basis
    intro i j
    ext r
    fin_cases i <;> fin_cases j <;> fin_cases r <;>
      simp [twoFrom, twoValues, e, LieCochain2.alternating]
    all_goals exact congrFun (ω.skew _ _).symm _
  right_inv a := by
    ext r
    fin_cases r <;> simp [twoFrom, twoValues, e]
  map_add' := by intros; ext r; fin_cases r <;> simp [twoValues]
  map_smul' := by intros; ext r; fin_cases r <;> simp [twoValues]

def readThird : (Space →ₗ[ℚ] Space →ₗ[ℚ] Space →ₗ[ℚ] Coeff) →ₗ[ℚ] (Fin 3 → ℚ) where
  toFun t := ![t (e 0) (e 1) (e 2) 0, t (e 0) (e 1) (e 2) 1, t (e 0) (e 1) (e 2) 2]
  map_add' := by intros; ext r; fin_cases r <;> rfl
  map_smul' := by intros; ext r; fin_cases r <;> rfl

theorem readThird_detect (ω : C2) (hz : readThird (differential2 coefficients ω) = 0) :
    differential2 coefficients ω = 0 := by
  have sample_0_1_2 : differential2 coefficients ω (e 0) (e 1) (e 2) = 0 := by
    ext r
    fin_cases r
    · exact congrFun hz 0
    · exact congrFun hz 1
    · exact congrFun hz 2
  apply differential2_eq_zero_of_increasing
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hij <;> norm_num at hjk
  all_goals first | omega | exact sample_0_1_2

theorem differential1_coordinates (φ : Space →ₗ[ℚ] Coeff) :
    twoCoordinates (differential1 coefficients φ) = HeisenbergSecondOrderCE.d1.toLin' (oneCoordinates φ) := by
  obtain ⟨a, rfl⟩ := oneCoordinates.symm.surjective φ
  rw [oneCoordinates.apply_symm_apply]
  change twoValues (differential1 coefficients (oneFrom a)) = HeisenbergSecondOrderCE.d1.toLin' a
  ext r
  fin_cases r <;>
    simp [twoValues, differential1, coefficients, adjointLieModule, action, algebra, bracket, oneFrom, e,
      HeisenbergSecondOrderCE.d1, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem differential2_coordinates (ω : C2) :
    HeisenbergSecondOrderCE.d2.toLin' (twoCoordinates ω) = readThird (differential2 coefficients ω) := by
  obtain ⟨a, rfl⟩ := twoCoordinates.symm.surjective ω
  rw [twoCoordinates.apply_symm_apply]
  change HeisenbergSecondOrderCE.d2.toLin' a = readThird (differential2 coefficients (twoFrom a))
  ext r
  fin_cases r <;>
    simp [readThird, differential2_apply, coefficients, adjointLieModule, action, algebra, bracket, twoFrom, e,
      HeisenbergSecondOrderCE.d2, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

noncomputable def reduction : Reduction coefficients (Fin 5 → ℚ) :=
  HeisenbergSecondOrderCE.certificate.toReduction.transport oneCoordinates twoCoordinates readThird
    differential1_coordinates differential2_coordinates readThird_detect

noncomputable def h2Equiv : H2 coefficients ≃ₗ[ℚ] (Fin 5 → ℚ) := reduction.h2Equiv coefficients

theorem h2_finrank : Module.finrank ℚ (H2 coefficients) = 5 := by
  rw [h2Equiv.finrank_eq]
  simp

theorem boundary_iff (ω : C2) (hω : IsTwoCocycle coefficients ω) :
    IsTwoCoboundary coefficients ω ↔ reduction.project ω = 0 :=
  reduction.exact_iff ω hω

theorem normal_form (ω : C2) (hω : IsTwoCocycle coefficients ω) :
    differential1 coefficients (reduction.primitive ω) +
      reduction.represent (reduction.project ω) = ω := reduction.normal_form ω hω

/-- Every coordinate tuple supplies a closed representative and an actual first-order Lie algebra. -/
noncomputable def representativeDeformation :=
  LieDeformation.Reduction.deformation (reduction)

/-- Closed deformation directions are equivalent exactly when their computed coordinates agree. -/
theorem deformation_equivalent_iff (ω η : (C2))
    (hω : IsTwoCocycle (coefficients) ω) (hη : IsTwoCocycle (coefficients) η) :
    Nonempty (LieDeformation.Equivalence ω η) ↔ (reduction).project ω = (reduction).project η :=
  LieDeformation.Reduction.equivalent_iff (reduction) ω η hω hη

/-- A concrete invertible generator change puts a closed direction in normal form. -/
noncomputable def normalizeDeformation (ω : (C2)) (hω : IsTwoCocycle (coefficients) ω) :
    LieDeformation.Equivalence ω ((reduction).represent ((reduction).project ω)) :=
  LieDeformation.Reduction.normalize (reduction) ω hω

theorem deformation_removable_iff (ω : (C2)) (hω : IsTwoCocycle (coefficients) ω) :
    Nonempty (LieDeformation.Equivalence ω 0) ↔ (reduction).project ω = 0 :=
  LieDeformation.Reduction.removable_iff (reduction) ω hω

/-- Vanishing coordinates give an explicit trivializing change of generators. -/
noncomputable def trivializeDeformation (ω : (C2)) (hω : IsTwoCocycle (coefficients) ω)
    (h : (reduction).project ω = 0) : LieDeformation.Equivalence ω 0 :=
  LieDeformation.Reduction.trivialize (reduction) ω hω h

end LeanPhy.Generated.HeisenbergSecondOrder

/- Generated candidate: compile with `lake env lean` before treating it as checked.
Input SHA-256: 4e839672b9535c60d48f3e63b3f63b40c2958abf3277f0eb8892e0c02c832a0c
The matrices below are the mathematical input; no physical interpretation is inferred. -/
namespace LeanPhy.Generated.HeisenbergSecondOrderSecondImage

open LeanPhy.Mathematics

def d1 : Matrix (Fin 3) (Fin 9) ℚ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 1, 0]

def d2 : Matrix (Fin 0) (Fin 3) ℚ :=
  0

def project : Matrix (Fin 2) (Fin 3) ℚ :=
  !![1, 0, 0;
    0, 1, 0]

def represent : Matrix (Fin 3) (Fin 2) ℚ :=
  !![1, 0;
    0, 1;
    0, 0]

def primitive : Matrix (Fin 9) (Fin 3) ℚ :=
  !![0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 1;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0;
    0, 0, 0]

def correction : Matrix (Fin 3) (Fin 0) ℚ :=
  0

def certificate : MatrixCohomologyReduction d1 d2 2 where
  project := project
  represent := represent
  primitive := primitive
  correction := correction
  chain := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project, represent, primitive, correction, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply]
  closed := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project, represent, primitive, correction, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply]
  boundary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project, represent, primitive, correction, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply]
  retract := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project, represent, primitive, correction, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply]
  decompose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d1, d2, project, represent, primitive, correction, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply]

noncomputable def cohomologyEquiv :
    CohomologyReduction.Cohomology d1.toLin' d2.toLin' ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  certificate.toReduction.quotientEquiv

theorem exact_iff (x : Fin 3 → ℚ) (hx : d2.toLin' x = 0) :
    (∃ a, d1.toLin' a = x) ↔ project.toLin' x = 0 :=
  certificate.toReduction.exact_iff x hx

end LeanPhy.Generated.HeisenbergSecondOrderSecondImage

namespace LeanPhy.Generated.HeisenbergSecondOrder
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Mathematics.LieCochainCoordinates LeanPhy.Mathematics.LieDeformation
set_option maxSynthPendingDepth 5

/-- The independently generated image matrix is the actual adjoint CE matrix. -/
theorem image_differential : HeisenbergSecondOrderSecondImage.d1 = HeisenbergSecondOrderCE.d2 := by rfl

noncomputable def secondOrderSolver :
    SecondOrderSolver algebra (Fin 9 → ℚ) (Fin 3 → ℚ) (Fin 2 → ℚ) where
  coordinates := twoCoordinates
  readThird := readThird
  differential := HeisenbergSecondOrderSecondImage.d1.toLin'
  project := HeisenbergSecondOrderSecondImage.project.toLin'
  lift := HeisenbergSecondOrderSecondImage.primitive.toLin'
  boundary := HeisenbergSecondOrderSecondImage.certificate.toReduction.project_boundary
  solve := by
    intro b hb
    have hn := HeisenbergSecondOrderSecondImage.certificate.toReduction.normal_form b (by
      change HeisenbergSecondOrderSecondImage.d2.toLin' b = 0
      simp [HeisenbergSecondOrderSecondImage.d2])
    change HeisenbergSecondOrderSecondImage.d1.toLin' (HeisenbergSecondOrderSecondImage.primitive.toLin' b) +
      HeisenbergSecondOrderSecondImage.represent.toLin' (HeisenbergSecondOrderSecondImage.project.toLin' b) = b at hn
    simpa only [hb,map_zero,add_zero] using hn
  bridge := by intro ν; rw [image_differential]; exact differential2_coordinates ν
  detect := by
    intro ω ν hz
    have sample_0_1_2 : secondResidual ω ν (e 0) (e 1) (e 2) = 0 := by
      ext r
      fin_cases r
      · exact congrFun hz 0
      · exact congrFun hz 1
      · exact congrFun hz 2
    apply secondResidual_eq_zero_of_increasing
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hij <;> norm_num at hjk
    all_goals first | omega | exact sample_0_1_2

/-- Quadratic Jacobi samples, without dividing by two. -/
def quadraticValues (a : Fin 9 → ℚ) : Fin 3 → ℚ := ![(1) * (a 0 * a 7) + (-1) * (a 1 * a 6) + (1) * (a 3 * a 8) + (-1) * (a 5 * a 6), (-1) * (a 0 * a 4) + (1) * (a 1 * a 3) + (1) * (a 4 * a 8) + (-1) * (a 5 * a 7), (-1) * (a 0 * a 5) + (-1) * (a 1 * a 8) + (1) * (a 2 * a 3) + (1) * (a 2 * a 7)]

/-- Equations for membership of the quadratic term in the image of d₂. -/
def obstructionValues (a : Fin 9 → ℚ) : Fin 2 → ℚ := ![(1) * (a 0 * a 7) + (-1) * (a 1 * a 6) + (1) * (a 3 * a 8) + (-1) * (a 5 * a 6), (-1) * (a 0 * a 4) + (1) * (a 1 * a 3) + (1) * (a 4 * a 8) + (-1) * (a 5 * a 7)]

/-- One computed second-order correction, defined even off the solvability locus. -/
def correctionValues (a : Fin 9 → ℚ) : Fin 9 → ℚ := ![0, 0, 0, (1) * (a 0 * a 5) + (1) * (a 1 * a 8) + (-1) * (a 2 * a 3) + (-1) * (a 2 * a 7), 0, 0, 0, 0, 0]

theorem quadratic_bridge (a : Fin 9 → ℚ) :
    readThird (obstructionTrilinear (twoFrom a)) = quadraticValues a := by
  ext r
  fin_cases r <;> simp [readThird, obstructionTrilinear, obstruction, twoFrom, e, quadraticValues] <;> ring

theorem obstruction_coordinates (a : Fin 9 → ℚ) :
    secondOrderSolver.obstructionCoordinates (twoFrom a) = obstructionValues a := by
  change HeisenbergSecondOrderSecondImage.project.toLin' (readThird (obstructionTrilinear (twoFrom a))) = _
  rw [quadratic_bridge]
  ext r
  fin_cases r <;> simp [quadraticValues, obstructionValues, HeisenbergSecondOrderSecondImage.project,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem correction_coordinates (a : Fin 9 → ℚ) :
    secondOrderSolver.correction (twoFrom a) = twoFrom (correctionValues a) := by
  change twoCoordinates.symm (HeisenbergSecondOrderSecondImage.primitive.toLin'
    (-readThird (obstructionTrilinear (twoFrom a)))) = twoCoordinates.symm (correctionValues a)
  congr 1
  rw [quadratic_bridge]
  ext r
  fin_cases r <;> simp [quadraticValues, correctionValues, HeisenbergSecondOrderSecondImage.primitive,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem closed_coordinates (a : Fin 9 → ℚ) :
    IsTwoCocycle coefficients (twoFrom a) ↔ HeisenbergSecondOrderCE.d2.toLin' a = 0 := by
  have ht : twoCoordinates (twoFrom a) = a := twoCoordinates.apply_symm_apply a
  have hb := differential2_coordinates (twoFrom a)
  rw [ht] at hb
  constructor
  · intro hc; rw [hb,hc,map_zero]
  · intro hc; exact readThird_detect _ (hb.symm.trans hc)

/-- Linear closedness and quadratic obstruction equations are both necessary. -/
def SecondOrderConditions (a : Fin 9 → ℚ) : Prop :=
  HeisenbergSecondOrderCE.d2.toLin' a = 0 ∧ obstructionValues a = 0

/-- Quantifies over every possible correction and actual second-jet Lie algebra. -/
theorem second_order_exists_iff (a : Fin 9 → ℚ) :
    (∃ ν : C2, ∃ D : LeanPhy.Mathematics.LieAlgebra ℚ (Space × Space × Space),
      D.bracket = secondBracket (twoFrom a) ν) ↔ SecondOrderConditions a := by
  refine (secondOrderSolver.model_exists_iff (twoFrom a)).trans ?_
  change IsTwoCocycle coefficients (twoFrom a) ∧ _ ↔ _
  rw [closed_coordinates, obstruction_coordinates]
  rfl

noncomputable def secondOrderModel (a : Fin 9 → ℚ) (ha : SecondOrderConditions a) :
    LeanPhy.Mathematics.LieAlgebra ℚ (Space × Space × Space) :=
  secondAlgebra (twoFrom a) (twoFrom (correctionValues a))
    ((closed_coordinates a).mpr ha.1) ((secondResidual_eq_zero_iff _ _).mp (by
      rw [← correction_coordinates]
      exact secondOrderSolver.correction_cancels _ (by rw [obstruction_coordinates]; exact ha.2)))

theorem secondOrderModel_bracket (a : Fin 9 → ℚ) (ha : SecondOrderConditions a) :
    (secondOrderModel a ha).bracket = secondBracket (twoFrom a) (twoFrom (correctionValues a)) := rfl

theorem all_corrections_iff (a : Fin 9 → ℚ) (ν : C2) (h : obstructionValues a = 0) :
    secondResidual (twoFrom a) ν = 0 ↔
      IsTwoCocycle coefficients (ν - twoFrom (correctionValues a)) := by
  rw [← correction_coordinates]
  exact secondOrderSolver.all_corrections_iff _ ν (by rw [obstruction_coordinates]; exact h)

/-- The obstruction equations in the complete H² representative coordinates. -/
def representativeObstructionValues (a : Fin 5 → ℚ) : Fin 2 → ℚ :=
  ![(1) * (a 0 * a 4) + (-1) * (a 1 * a 3), (-1) * (a 0 * a 2) + (-1) * (a 1 * a 4)]

theorem representative_obstruction_coordinates (a : Fin 5 → ℚ) :
    secondOrderSolver.obstructionCoordinates (reduction.represent a) =
      representativeObstructionValues a := by
  change secondOrderSolver.obstructionCoordinates (twoFrom (HeisenbergSecondOrderCE.represent.toLin' a)) = _
  rw [obstruction_coordinates]
  ext r
  fin_cases r <;> simp [obstructionValues, representativeObstructionValues, HeisenbergSecondOrderCE.represent,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- For closed directions, normalization preserves the actual obstruction values. -/
theorem normalized_obstruction (ω : C2) (hω : IsTwoCocycle coefficients ω) :
    secondOrderSolver.obstructionCoordinates ω = representativeObstructionValues (reduction.project ω) := by
  exact (LieDeformation.Reduction.obstructionCoordinates_normalize reduction secondOrderSolver ω hω).trans
    (representative_obstruction_coordinates _)

theorem normalized_extension_iff (ω : C2) (hω : IsTwoCocycle coefficients ω) :
    SecondExtendable ω ↔ representativeObstructionValues (reduction.project ω) = 0 := by
  rw [secondOrderSolver.extendable_iff ω hω, normalized_obstruction ω hω]

noncomputable def normalizedCorrection (ω : C2) (hω : IsTwoCocycle coefficients ω) : C2 :=
  LieDeformation.Reduction.correctionFromRepresentative reduction secondOrderSolver ω hω

theorem normalizedCorrection_cancels (ω : C2) (hω : IsTwoCocycle coefficients ω)
    (h : representativeObstructionValues (reduction.project ω) = 0) :
    secondResidual ω (normalizedCorrection ω hω) = 0 :=
  LieDeformation.Reduction.correctionFromRepresentative_cancels reduction secondOrderSolver ω hω
    ((representative_obstruction_coordinates _).trans h)

noncomputable def normalizedModel (ω : C2) (hω : IsTwoCocycle coefficients ω)
    (h : representativeObstructionValues (reduction.project ω) = 0) :
    LeanPhy.Mathematics.LieAlgebra ℚ (Space × Space × Space) :=
  LieDeformation.Reduction.modelFromRepresentative reduction secondOrderSolver ω hω
    ((representative_obstruction_coordinates _).trans h)

/-- The computed representative solution is genuinely equivalent to the
solution in the original generators, including its second-order correction. -/
noncomputable def normalizationEquivalence (ω : C2) (hω : IsTwoCocycle coefficients ω)
    (h : representativeObstructionValues (reduction.project ω) = 0) :
    SecondEquivalence (reduction.represent (reduction.project ω))
      (secondOrderSolver.correction (reduction.represent (reduction.project ω)))
      ω (normalizedCorrection ω hω) :=
  LieDeformation.Reduction.equivalenceFromRepresentative reduction secondOrderSolver ω hω
    ((representative_obstruction_coordinates _).trans h)

end LeanPhy.Generated.HeisenbergSecondOrder
