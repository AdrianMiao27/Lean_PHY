import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Finite commutator response and Kubo algebra

Linear-response calculations in condensed matter, statistical mechanics,
finite quantum systems and scattering theory repeatedly use the weighted
commutator `Tr (rho [A,B])`.  This module packages only the finite matrix
algebra.  It checks exchange signs, linearity, and the cyclic rewriting that
turns a response into a commutator with the state.  Time ordering, step
functions, Fourier transforms, positivity of a state and thermodynamic limits
remain explicit higher-level inputs.
-/

namespace LeanPhy.Mathematics

open scoped Matrix

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The finite weighted commutator response `Tr (rho [A,B])`. -/
def commutatorResponse (rho A B : Matrix ι ι ℂ) : ℂ :=
  Matrix.trace (rho * (A * B - B * A))

@[simp] theorem commutatorResponse_apply (rho A B : Matrix ι ι ℂ) :
    commutatorResponse rho A B = Matrix.trace (rho * (A * B - B * A)) := rfl

/-- Expand a weighted commutator into the difference of two finite
correlators. -/
theorem commutatorResponse_eq_correlator_sub (rho A B : Matrix ι ι ℂ) :
    commutatorResponse rho A B =
      Matrix.trace (rho * A * B) - Matrix.trace (rho * B * A) := by
  unfold commutatorResponse
  rw [Matrix.mul_sub, Matrix.trace_sub]
  simp only [Matrix.mul_assoc]

/-- Exchanging the two probes reverses the response sign. -/
theorem commutatorResponse_swap (rho A B : Matrix ι ι ℂ) :
    commutatorResponse rho B A = -commutatorResponse rho A B := by
  rw [commutatorResponse_eq_correlator_sub,
    commutatorResponse_eq_correlator_sub]
  ring

/-- A commuting pair has zero weighted commutator response. -/
theorem commutatorResponse_eq_zero_of_commute (rho A B : Matrix ι ι ℂ)
    (hAB : A * B = B * A) :
    commutatorResponse rho A B = 0 := by
  unfold commutatorResponse
  rw [hAB, sub_self, Matrix.mul_zero, Matrix.trace_zero]

theorem commutatorResponse_add_left (rho A B C : Matrix ι ι ℂ) :
    commutatorResponse rho (A + B) C =
      commutatorResponse rho A C + commutatorResponse rho B C := by
  rw [commutatorResponse_eq_correlator_sub,
    commutatorResponse_eq_correlator_sub,
    commutatorResponse_eq_correlator_sub]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
  ring

theorem commutatorResponse_add_right (rho A B C : Matrix ι ι ℂ) :
    commutatorResponse rho A (B + C) =
      commutatorResponse rho A B + commutatorResponse rho A C := by
  rw [commutatorResponse_eq_correlator_sub,
    commutatorResponse_eq_correlator_sub,
    commutatorResponse_eq_correlator_sub]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  ring

theorem commutatorResponse_smul_left (c : ℂ) (rho A B : Matrix ι ι ℂ) :
    commutatorResponse (c • rho) A B = c * commutatorResponse rho A B := by
  unfold commutatorResponse
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

theorem commutatorResponse_smul_probe (c : ℂ) (rho A B : Matrix ι ι ℂ) :
    commutatorResponse rho (c • A) B = c * commutatorResponse rho A B := by
  rw [commutatorResponse_eq_correlator_sub,
    commutatorResponse_eq_correlator_sub]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul]
  ring

/-- Finite cyclicity rewrites the response as the state--probe commutator
`Tr ([rho,A] B)`.  This is the algebraic core of the Kubo identity. -/
theorem commutatorResponse_eq_state_commutator (rho A B : Matrix ι ι ℂ) :
    commutatorResponse rho A B =
      Matrix.trace ((rho * A - A * rho) * B) := by
  calc
    commutatorResponse rho A B =
        Matrix.trace (rho * A * B) - Matrix.trace (rho * B * A) :=
      commutatorResponse_eq_correlator_sub rho A B
    _ = Matrix.trace ((rho * A - A * rho) * B) := by
      rw [Matrix.sub_mul, Matrix.trace_sub]
      have hcycle : Matrix.trace (A * rho * B) = Matrix.trace (rho * B * A) := by
        calc
          Matrix.trace (A * rho * B) = Matrix.trace (B * A * rho) :=
            Matrix.trace_mul_cycle A rho B
          _ = Matrix.trace (rho * B * A) :=
            Matrix.trace_mul_cycle B A rho
      rw [hcycle]

end LeanPhy.Mathematics

/-! Domain aliases for the same finite Kubo/response contract. -/

namespace LeanPhy

namespace QuantumInfo
abbrev FiniteKuboResponse {ι : Type} [Fintype ι] [DecidableEq ι] :=
  Mathematics.commutatorResponse (ι := ι)
end QuantumInfo

namespace Condensed
abbrev FiniteLinearResponse {ι : Type} [Fintype ι] [DecidableEq ι] :=
  Mathematics.commutatorResponse (ι := ι)
end Condensed

namespace StatMech
abbrev FiniteKuboCorrelation {ι : Type} [Fintype ι] [DecidableEq ι] :=
  Mathematics.commutatorResponse (ι := ι)
end StatMech

namespace HighEnergy
abbrev FiniteScatteringResponse {ι : Type} [Fintype ι] [DecidableEq ι] :=
  Mathematics.commutatorResponse (ι := ι)
end HighEnergy

namespace Classical
abbrev FinitePoissonResponse {ι : Type} [Fintype ι] [DecidableEq ι] :=
  Mathematics.commutatorResponse (ι := ι)
end Classical

end LeanPhy
