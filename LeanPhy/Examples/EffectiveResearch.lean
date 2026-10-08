import LeanPhy.Mathematics.FormalBlockElimination
import LeanPhy.Mathematics.EliminationError
import LeanPhy.Quantum.EffectiveHamiltonian
import LeanPhy.FieldTheory.HeavyFieldElimination
import LeanPhy.FieldTheory.HeavyFieldInterval
import LeanPhy.Workflow.Core

set_option autoImplicit false

/-! Cross-domain clients for retained-order operators, exact elimination,
induced sources/observables and independent norm bounds. Model inputs are
variable; small exact regressions isolate errors in order, sign and metric. -/

namespace LeanPhy.Examples.EffectiveResearch

open LeanPhy.Mathematics LeanPhy.Mathematics.FormalExpansion
open LeanPhy.Mathematics.BlockElimination LeanPhy.FieldTheory
open LeanPhy.Quantum.EnergyElimination LeanPhy.Workflow PowerSeries
open scoped Matrix

/-- Unequal sector dimensions share the same exact source/readout API. -/
theorem generic_block_reduction {L H : Type*} [Fintype L] [Fintype H] [DecidableEq H]
    (S : System ℂ L H) (x : L → ℂ) (y : H → ℂ) (jL : L → ℂ) (jH : H → ℂ) :
    S.fullMatrix.mulVec (Sum.elim x y) = Sum.elim jL jH ↔
      S.effective.mulVec x = S.effectiveSource jL jH ∧ y = S.reconstruct x jH := by
  rw [S.fullMatrix_equation_iff, S.satisfies_iff]

noncomputable def drivenBlock : System ℚ Unit Unit where
  light := fun _ _ => 7
  toLight := fun _ _ => 3
  toHeavy := fun _ _ => 5
  heavy := ⟨(fun _ _ => 2 : Matrix Unit Unit ℚ), (fun _ _ => 1 / 2 : Matrix Unit Unit ℚ),
    by ext i j; change (∑ _k : Unit, (2 : ℚ) * (1 / 2)) = _; norm_num,
    by ext i j; change (∑ _k : Unit, (1 / 2 : ℚ) * 2) = _; norm_num⟩

theorem driven_inverse : (↑(drivenBlock.heavy⁻¹) : Matrix Unit Unit ℚ) =
    (fun _ _ => 1 / 2) := rfl

theorem driven_source_and_reconstruction :
    drivenBlock.effective () () = -1 / 2 ∧
    drivenBlock.effectiveSource (fun _ => 11) (fun _ => 13) () = -17 / 2 ∧
    drivenBlock.reconstruct (fun _ => 17) (fun _ => 13) () = -36 := by
  simp only [System.effective, System.effectiveSource, System.reconstruct, driven_inverse]
  change (7 - (∑ _k : Unit, (∑ _j : Unit, (3 : ℚ) * (1 / 2)) * 5) = -1 / 2) ∧
    (11 - (∑ _k : Unit, (∑ _j : Unit, (3 : ℚ) * (1 / 2)) * 13) = -17 / 2) ∧
    (∑ _k : Unit, (1 / 2 : ℚ) * (13 - ∑ _j : Unit, (5 : ℚ) * 17)) = -36
  norm_num

/-- A heavy linear probe needs both its induced coefficient and source offset. -/
theorem driven_readout :
    drivenBlock.effectiveReadout (fun _ : Unit => fun _ => 2) (fun _ => fun _ => 3) () () = -11 / 2 ∧
    drivenBlock.readoutOffset (fun _ : Unit => fun _ => 3) (fun _ => 13) () = 39 / 2 := by
  simp only [System.effectiveReadout, System.readoutOffset, driven_inverse]
  change (2 - (∑ _k : Unit, (∑ _j : Unit, (3 : ℚ) * (1 / 2)) * 5) = -11 / 2) ∧
    (∑ _k : Unit, (∑ _j : Unit, (3 : ℚ) * (1 / 2)) * 13) = 39 / 2
  norm_num

/-- Noncommuting coefficients distinguish BC from CB already at order two. -/
def forward : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]
def backward : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]

theorem order_two_is_ordered :
    coeff 2 ((PowerSeries.X * C forward) * (PowerSeries.X * C backward)) ≠
      coeff 2 ((PowerSeries.X * C backward) * (PowerSeries.X * C forward)) := by
  intro h
  have h2 : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
  have h1 : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
  simp only [coeff_mul, h2] at h
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ => A 0 0) h
  norm_num [h1, forward, backward, Matrix.mul_apply] at he

/-- Coefficient computation after block inversion does not assume commuting D₀,D₁. -/
theorem formal_heavy_inverse_first {H : Type*} [Fintype H] [DecidableEq H]
    (D : PowerSeries (Matrix H H ℚ)) (u : (Matrix H H ℚ)ˣ)
    (hD : constantCoeff D = u) (i j : H) :
    coeff 1 ((↑((matrixUnit D u hD)⁻¹) : Matrix H H (PowerSeries ℚ)) i j) =
      (-(↑(u⁻¹) : Matrix H H ℚ) * coeff 1 D * (↑(u⁻¹) : Matrix H H ℚ)) i j := by
  rw [matrixUnit_inv_val, coeff_matrix, inverse_coeff_one]

/-- A retained-order statement does not assert equality of entire series. -/
theorem truncation_is_not_exact :
    Below 2 (1 + (PowerSeries.X : PowerSeries ℚ)^2) 1 ∧
      (1 + (PowerSeries.X : PowerSeries ℚ)^2) ≠ 1 := by
  constructor
  · intro k hk
    interval_cases k <;> norm_num
  · intro h
    have he := congrArg (coeff 2) h
    norm_num at he

noncomputable def mixedModel : Model Unit Unit where
  light := 1
  toLight := 1
  toHeavy := 1
  heavy := 1
  energy := 0
  resolvent := 1
  resolvent_eq := by simp

/-- Exact zero-energy eigenstates still need the induced normalization metric. -/
theorem mixed_metric : mixedModel.normMetric () () = 2 := by
  rw [Model.normMetric_eq]
  norm_num [mixedModel, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem mixed_reconstructed_eigenstate :
    mixedModel.hamiltonian.mulVec
      (mixedModel.liftMatrix.mulVec (fun _ => 1)) = 0 := by
  rw [Model.liftMatrix_mulVec]
  have h := (mixedModel.eigen_equation_iff (fun _ => 1)
    (mixedModel.system.reconstruct (fun _ => 1) 0)).mpr
      ⟨by simp [Model.effectiveHamiltonian, mixedModel], rfl⟩
  simpa [mixedModel] using h

theorem arbitrary_induced_action {Field : Type*} (m : ℝ) (hm : m ≠ 0)
    (V J : MvPolynomial Field ℝ) :
    HeavyFieldElimination.eliminate m J (HeavyFieldElimination.action m V J) =
      V - MvPolynomial.C ((2 * m)⁻¹) * J ^ 2 :=
  HeavyFieldElimination.action_eliminated m hm V J

/-- There is a genuine finite-N remainder, even for a scalar convergent example. -/
theorem geometric_remainder_regression :
    1 - (1 - (1 / 2 : ℝ)) * EliminationError.geometricInverse (1 / 2 : ℝ) 3 = 1 / 8 := by
  rw [EliminationError.geometric_residual]
  norm_num

def package : TheoryPackage :=
  TheoryPackage.empty "effective theory operations" "condensed matter and tree-level field theory"
    |>.addTheorem "full and effective equations" "arbitrary finite sectors preserve both sources and solutions"
      "generic_block_reduction" (@generic_block_reduction.{0,0})
    |>.addTheorem "ordered inverse coefficients" "formal inversion retains noncommuting factors"
      "formal_heavy_inverse_first" (@formal_heavy_inverse_first.{0})
    |>.addTheorem "formal truncation boundary" "retained coefficients do not imply exact equality"
      "truncation_is_not_exact" truncation_is_not_exact
    |>.addTheorem "driven source transform" "heavy sources alter the effective source and reconstructed component"
      "driven_source_and_reconstruction" driven_source_and_reconstruction
    |>.addTheorem "induced readout" "linear probes inherit a coefficient and an affine source offset"
      "driven_readout" driven_readout
    |>.addTheorem "reconstruction metric" "light norm alone misses heavy admixture"
      "mixed_metric" mixed_metric
    |>.addTheorem "polynomial induced action" "arbitrary light polynomials yield the exact algebraic heavy-field action"
      "arbitrary_induced_action" (@arbitrary_induced_action.{0})
    |>.addTheorem "inverse residual budget" "an actual residual produces a norm error certificate"
      "LeanPhy.Mathematics.EliminationError.effective_error" (@EliminationError.effective_error.{0})
    |>.addTheorem "coupled propagating residual"
      "arbitrary mass mixing and derivative couplings produce an exact finite-order heavy equation residual"
      "LeanPhy.FieldTheory.PropagatingHeavy.Model.residual_field"
      (@PropagatingHeavy.Model.residual_field.{0,0,0})
    |>.addTheorem "actual heavy first variation"
      "the heavy equation follows from the actual interval action with endpoint flux retained"
      "LeanPhy.FieldTheory.PropagatingHeavy.Interval.hasDerivAt_action"
      (@PropagatingHeavy.Interval.hasDerivAt_action.{0,0})
    |>.addTheorem "propagating action matching"
      "substituted and effective interval actions differ by the computed residual and boundary terms"
      "LeanPhy.FieldTheory.PropagatingHeavy.Interval.action_matching"
      (@PropagatingHeavy.Interval.action_matching.{0,0})
    |>.addTheorem "heavy source contacts"
      "finite matching preserves both mixed source insertions and the quadratic source term"
      "LeanPhy.FieldTheory.PropagatingHeavy.Model.effective_source_shift"
      (@PropagatingHeavy.Model.effective_source_shift.{0,0,0})
    |>.addTheorem "matched action error"
      "uniform residual and endpoint budgets bound the actual substituted-action discrepancy"
      "LeanPhy.FieldTheory.PropagatingHeavy.Interval.action_error"
      (@PropagatingHeavy.Interval.action_error.{0,0})
    |>.addTheorem "heavy readout transport"
      "the reconstructed heavy field transports a probe together with a changed source"
      "LeanPhy.FieldTheory.PropagatingHeavy.Model.readout_source_shift"
      (@PropagatingHeavy.Model.readout_source_shift.{0,0,0})
    |>.addObligationText "low-energy validity" "establish a target energy domain and uniform inverse or gap bounds"
      "model-dependent spectral analysis"
    |>.addObligationText "Green functions and quantum matching"
      "construct boundary-value inverses and uniform errors; extend nonquadratic sectors, measures and determinants"
      "boundary-value analysis and quantum field-theory matching"
    |>.addObligationText "unitary low-energy dynamics" "construct an energy-independent unitary reduction and its error"
      "operator dynamics"

example : package.claimCount = 14 := rfl
example : package.obligationCount = 3 := rfl
example : package.hasErrors = false := by decide

end LeanPhy.Examples.EffectiveResearch
