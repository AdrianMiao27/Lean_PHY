import LeanPhy.Mathematics.CertifiedElimination
import LeanPhy.Quantum.EffectiveHamiltonian
import Mathlib.Algebra.Algebra.Spectrum.Basic

set_option autoImplicit false

/-!
# Certified finite resolvent domains from rational residuals

A checked nominal inverse at a center energy certifies an entire complex
energy disk, when the disk radius fits the model uncertainty budget. This
constructs the missing resolvent input of energy-dependent elimination and
excludes that disk from the actual finite spectrum. It is not a certified
individual eigenvalue, a unitary low-energy transformation or an infinite-volume
spectral gap. The norm convention is the L-infinity operator norm throughout.
-/

namespace LeanPhy.Quantum.CertifiedResolvent

open LeanPhy.Mathematics LeanPhy.Mathematics.MatrixCertificate
open scoped Matrix.Norms.Operator

variable {l n : ℕ} [NeZero n]

theorem energy_near (H : Matrix (Fin n) (Fin n) ℂ) (center z : ℂ) (radius : ℝ)
    (hz : ‖z - center‖ ≤ radius) :
    ‖(H - z • 1) - (H - center • 1)‖ ≤ radius := by
  have heq : (H - z • 1) - (H - center • 1) = (center - z) • 1 := by module
  rw [heq, norm_smul, norm_one, mul_one, norm_sub_rev]
  exact hz

/-- The data-to-Hamiltonian relation is an equality of actual matrices. -/
noncomputable def unit (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (H : Matrix (Fin n) (Fin n) ℂ) (center : ℂ)
    (hA : A.realize = H - center • 1) (z : ℂ)
    (hz : ‖z - center‖ ≤ (c.modelRadius : ℝ)) : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  c.unit A h (H - z • 1) (hA ▸ energy_near H center z _ hz)

@[simp] theorem unit_val (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (H : Matrix (Fin n) (Fin n) ℂ) (center : ℂ)
    (hA : A.realize = H - center • 1) (z : ℂ)
    (hz : ‖z - center‖ ≤ (c.modelRadius : ℝ)) :
    (unit A c h H center hA z hz : Matrix (Fin n) (Fin n) ℂ) = H - z • 1 := rfl

theorem excludes_spectrum (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (H : Matrix (Fin n) (Fin n) ℂ) (center : ℂ)
    (hA : A.realize = H - center • 1) (z : ℂ)
    (hz : ‖z - center‖ ≤ (c.modelRadius : ℝ)) : z ∉ spectrum ℂ H := by
  apply spectrum.notMem_iff.mpr
  have hu := (unit A c h H center hA z hz).isUnit.neg
  simpa only [unit_val, neg_sub, Algebra.algebraMap_eq_smul_one] using hu

theorem inverse_norm (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (H : Matrix (Fin n) (Fin n) ℂ) (center : ℂ)
    (hA : A.realize = H - center • 1) (z : ℂ)
    (hz : ‖z - center‖ ≤ (c.modelRadius : ℝ)) :
    ‖(↑((unit A c h H center hA z hz)⁻¹) : Matrix (Fin n) (Fin n) ℂ)‖ ≤
      (c.normBound : ℝ) :=
  c.actual_inverse_norm A h _ (hA ▸ energy_near H center z _ hz)

/-- Construct the existing physical elimination model without supplying an inverse. -/
noncomputable def model (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (H : Matrix (Fin n) (Fin n) ℂ) (center : ℂ)
    (hA : A.realize = H - center • 1) (z : ℂ)
    (hz : ‖z - center‖ ≤ (c.modelRadius : ℝ))
    (L : Matrix (Fin l) (Fin l) ℂ) (B : Matrix (Fin l) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin l) ℂ) : EnergyElimination.Model (Fin l) (Fin n) where
  light := L
  toLight := B
  toHeavy := C
  heavy := H
  energy := z
  resolvent := unit A c h H center hA z hz
  resolvent_eq := rfl

/-- A uniform certified resolvent supplies an effective-Hamiltonian error at every
energy in the disk, keeping the matrix representation and approximation explicit. -/
theorem effective_error (A : RationalMatrix n n) (c : Candidate n) (h : c.Accepted A)
    (H : Matrix (Fin n) (Fin n) ℂ) (center : ℂ)
    (hA : A.realize = H - center • 1) (z : ℂ)
    (hz : ‖z - center‖ ≤ (c.modelRadius : ℝ))
    (L : Matrix (Fin l) (Fin l) ℂ) (B : Matrix (Fin l) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin l) ℂ) :
    ErrorCertificate (model A c h H center hA z hz L B C).effectiveHamiltonian
      (L - B * c.inverse.realize * C) (‖B‖ * (c.errorBound : ℝ) * ‖C‖) :=
  CertifiedElimination.effective_error A c h (H - z • 1)
    (hA ▸ energy_near H center z _ hz) L B C

end LeanPhy.Quantum.CertifiedResolvent
