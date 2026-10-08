import LeanPhy.Mathematics.RationalMatrix
import LeanPhy.Mathematics.ResidualInverse
import LeanPhy.Mathematics.ExternalCertificate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

/-!
# Executable complex matrix inverse certificates

Only exact rational row inequalities enter `Accepted`. The nominal matrix is
an index of the checker, not an interchangeable name in a payload. The soundness
bridge constructs a genuine inverse for every actual matrix in the certified
norm ball and proves inverse norm/error bounds. A positive uncertainty radius
requires a proof relating the actual model to the nominal data.
-/

namespace LeanPhy.Mathematics.MatrixCertificate

open scoped Matrix.Norms.Operator

structure Candidate (n : ℕ) where
  inverse : RationalMatrix n n
  inverseBound : ℚ
  residualBound : ℚ
  modelRadius : ℚ

namespace Candidate

variable {n : ℕ}

def residual (A : RationalMatrix n n) (c : Candidate n) : RationalMatrix n n :=
  (RationalMatrix.one n).sub (A.mul c.inverse)

def totalResidual (c : Candidate n) : ℚ := c.residualBound + c.modelRadius * c.inverseBound

/-- Every inequality is exact and decidable. Non-strict margin one is rejected. -/
def Accepted (A : RationalMatrix n n) (c : Candidate n) : Prop :=
  c.inverse.Bounded c.inverseBound ∧
  (c.residual A).Bounded c.residualBound ∧
  0 ≤ c.modelRadius ∧ c.totalResidual < 1

instance (A : RationalMatrix n n) (c : Candidate n) : Decidable (c.Accepted A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

@[simp] theorem realize_residual (A : RationalMatrix n n) (c : Candidate n) :
    (c.residual A).realize = 1 - A.realize * c.inverse.realize := by simp [residual]

theorem inverse_norm (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A) :
    ‖c.inverse.realize‖ ≤ (c.inverseBound : ℝ) := c.inverse.norm_le _ h.1

theorem nominal_residual_norm (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A) :
    ‖1 - A.realize * c.inverse.realize‖ ≤ (c.residualBound : ℝ) := by
  simpa using (c.residual A).norm_le _ h.2.1

theorem residual_norm (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : ‖D - A.realize‖ ≤ (c.modelRadius : ℝ)) :
    ‖1 - D * c.inverse.realize‖ ≤ (c.totalResidual : ℝ) := by
  simpa [totalResidual] using ResidualInverse.perturbed_residual
    A.realize D c.inverse.realize c.inverseBound c.residualBound c.modelRadius
    (c.inverse_norm A h) (c.nominal_residual_norm A h) hD

/-- The resulting unit is the actual model matrix, including its uncertainty. -/
noncomputable def unit (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : ‖D - A.realize‖ ≤ (c.modelRadius : ℝ)) :
    (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  ResidualInverse.unit D c.inverse.realize
    ((c.residual_norm A h D hD).trans_lt (by exact_mod_cast h.2.2.2))

@[simp] theorem unit_val (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : ‖D - A.realize‖ ≤ (c.modelRadius : ℝ)) :
    (c.unit A h D hD : Matrix (Fin n) (Fin n) ℂ) = D := rfl

/-- Explicit certified bound, with numerical and model errors both retained. -/
def normBound (c : Candidate n) : ℚ := c.inverseBound / (1 - c.totalResidual)

def errorBound (c : Candidate n) : ℚ := c.normBound * c.totalResidual

theorem actual_inverse_norm (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : ‖D - A.realize‖ ≤ (c.modelRadius : ℝ)) :
    ‖(↑((c.unit A h D hD)⁻¹) : Matrix (Fin n) (Fin n) ℂ)‖ ≤ (c.normBound : ℝ) := by
  simpa [normBound] using ResidualInverse.inverse_norm_bound
    (c.unit A h D hD) c.inverse.realize c.inverseBound c.totalResidual
    (c.inverse_norm A h) (c.residual_norm A h D hD) (by exact_mod_cast h.2.2.2)

theorem inverse_error (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : ‖D - A.realize‖ ≤ (c.modelRadius : ℝ)) :
    ErrorCertificate (↑((c.unit A h D hD)⁻¹) : Matrix (Fin n) (Fin n) ℂ)
      c.inverse.realize (c.errorBound : ℝ) := by
  simpa [errorBound, normBound] using ResidualInverse.inverse_error_bound
    (c.unit A h D hD) c.inverse.realize c.inverseBound c.totalResidual
    (c.inverse_norm A h) (c.residual_norm A h D hD) (by exact_mod_cast h.2.2.2)

end Candidate

/-- A checked conclusion over the whole declared model ball. -/
def Valid {n : ℕ} (A : RationalMatrix n n) (c : Candidate n) : Prop :=
  ∀ D : Matrix (Fin n) (Fin n) ℂ, ‖D - A.realize‖ ≤ (c.modelRadius : ℝ) →
    ∃ U : (Matrix (Fin n) (Fin n) ℂ)ˣ, (U : Matrix (Fin n) (Fin n) ℂ) = D ∧
      ‖(↑(U⁻¹) : Matrix (Fin n) (Fin n) ℂ)‖ ≤ (c.normBound : ℝ) ∧
      ErrorCertificate (↑(U⁻¹) : Matrix (Fin n) (Fin n) ℂ) c.inverse.realize (c.errorBound : ℝ)

theorem sound {n : ℕ} (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A) :
    Valid A c := by
  intro D hD
  exact ⟨c.unit A h D hD, rfl, c.actual_inverse_norm A h D hD, c.inverse_error A h D hD⟩

/-- Reuse the existing external-certificate trust boundary, with an actual
finite-data checker. The candidate value is fixed in the conclusion. -/
def checker {n : ℕ} (A : RationalMatrix n n) (c : Candidate n) :
    CertificateChecker (Valid A c) (Candidate n) where
  check payload := payload = c ∧ payload.Accepted A
  sound := fun {_} h => sound A c (h.1 ▸ h.2)

end LeanPhy.Mathematics.MatrixCertificate
