import LeanPhy.Quantum.DynamicalResponse
import LeanPhy.Quantum.FiniteThermalState
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false

/-!
# Noncommuting finite thermal perturbations

Differentiate `Tr(exp(-β H) O) / Tr(exp(-β H))` under `H + ε V` and
`O + ε O'`. Duhamel supplies the weight derivative; the quotient rule supplies
the normalization subtraction. Hermitian input identifies this readout with
the actual positive, trace-one Gibbs state. No differentiable eigenbasis,
nondegenerate spectrum, or commutation of H and V is required.
-/

namespace LeanPhy.Quantum.ThermalPerturbation

open LeanPhy.Mathematics
open scoped Matrix Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def weight (H : Matrix ι ι ℂ) (β : ℝ) : Matrix ι ι ℂ := Duhamel.flow H (-β)

noncomputable def partition (H : Matrix ι ι ℂ) (β : ℝ) : ℂ := Matrix.trace (weight H β)

noncomputable def mean (H O : Matrix ι ι ℂ) (β : ℝ) : ℂ :=
  Matrix.trace (weight H β * O) / partition H β

theorem weight_eq_exp (H : Matrix ι ι ℂ) (β : ℝ) :
    weight H β = NormedSpace.exp ((-β : ℂ) • H) := by
  unfold weight Duhamel.flow
  congr 1
  rw [neg_smul, neg_smul]
  congr 1

theorem mean_eq_thermal [Nonempty ι] (H O : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) :
    mean H O β = Matrix.trace ((finiteThermalState H hH β).rho * O) := by
  rw [finiteThermalState_eq_exp]
  simp [mean, partition, weight_eq_exp, div_eq_mul_inv, mul_comm]

theorem partition_ne_zero [Nonempty ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) :
    partition H β ≠ 0 := by
  intro h
  have hp := finiteThermalState_partition_pos H hH β
  have hz : Matrix.trace (NormedSpace.exp ((-β : ℂ) • H)) = 0 := by
    simpa [partition, weight_eq_exp] using h
  rw [hz] at hp
  exact (lt_irrefl (0 : ℝ)) hp

noncomputable def weightVariation (H V : Matrix ι ι ℂ) (β : ℝ) : Matrix ι ι ℂ :=
  Duhamel.insertion H V (-β)

theorem weight_perturbation (H V : Matrix ι ι ℂ) (β : ℝ) :
    HasDerivAt (fun ε : ℝ => weight (H + ε • V) β) (weightVariation H V β) 0 := by
  exact Duhamel.hasDerivAt_perturbation H V (-β)

/-- Includes the probe contact term and the derivative of normalization. -/
noncomputable def response (H V O O' : Matrix ι ι ℂ) (β : ℝ) : ℂ :=
  ((Matrix.trace (weightVariation H V β * O + weight H β * O')) * partition H β -
    Matrix.trace (weight H β * O) * Matrix.trace (weightVariation H V β)) / partition H β ^ 2

theorem mean_perturbation (H V O O' : Matrix ι ι ℂ) (β : ℝ) (hZ : partition H β ≠ 0) :
    HasDerivAt (fun ε : ℝ => mean (H + ε • V) (O + ε • O') β)
      (response H V O O' β) 0 := by
  have hw := weight_perturbation H V β
  have hO := (hasDerivAt_const (0 : ℝ) O).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const O')
  have hn := Dynamics.hasDerivAt_trace (hw.fun_mul hO)
  have hd := Dynamics.hasDerivAt_trace hw
  have hz : Matrix.trace (weight (H + (0 : ℝ) • V) β) ≠ 0 := by simpa [partition] using hZ
  simpa [mean, partition, response] using! hn.fun_div hd hz

/-- Hermitian couplings keep the whole real-parameter family physical. -/
theorem perturbed_hermitian (H V : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (hV : V.IsHermitian) (ε : ℝ) : (H + ε • V).IsHermitian :=
  hH.add (hV.smul (IsSelfAdjoint.all ε))

theorem thermal_expectation_perturbation [Nonempty ι]
    (H V O O' : Matrix ι ι ℂ) (hH : H.IsHermitian) (hV : V.IsHermitian) (β : ℝ) :
    HasDerivAt (fun ε : ℝ => Matrix.trace
      ((finiteThermalState (H + ε • V) (perturbed_hermitian H V hH hV ε) β).rho *
        (O + ε • O'))) (response H V O O' β) 0 := by
  simp_rw [← mean_eq_thermal]
  exact mean_perturbation H V O O' β (partition_ne_zero H hH β)

/-- A commuting perturbation recovers the covariance rule, with its minus β.
The probe itself need not commute with H or V. -/
theorem response_of_commute (H V O O' : Matrix ι ι ℂ) (β : ℝ)
    (hHV : Commute H V) (hZ : partition H β ≠ 0) :
    response H V O O' β = mean H O' β - (β : ℂ) *
      (mean H (V * O) β - mean H O β * mean H V β) := by
  have hi : weightVariation H V β = (-β : ℂ) • (weight H β * V) := by
    unfold weightVariation weight
    rw [Duhamel.insertion_of_commute H V (-β) hHV, neg_smul, neg_smul]
    congr 1
  simp only [response, mean, hi, Matrix.trace_add, Matrix.smul_mul, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_assoc]
  field_simp
  ring

theorem response_identity (H V : Matrix ι ι ℂ) (β : ℝ) : response H V 1 0 β = 0 := by
  simp [response, partition, mul_comm]

end LeanPhy.Quantum.ThermalPerturbation
