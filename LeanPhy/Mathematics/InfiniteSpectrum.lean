import LeanPhy.Mathematics.Hilbert
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Bounded-operator spectrum certificates

This module is the analytic boundary between LeanPhy's finite spectral
calculations and genuine Hilbert-space operators.  It exposes mathlib's
spectrum and resolvent for bounded continuous linear maps.  A resolvent claim
is accepted only with an explicit bounded inverse and both inverse equations;
the kernel therefore checks the operator identity rather than trusting a
numerical eigenvalue routine.

The module intentionally stops at bounded operators.  Domains of unbounded
self-adjoint operators, essential/continuous spectrum, spectral measures and
Stone's theorem remain separate obligations.
-/

namespace LeanPhy.Mathematics

universe u v

/-! A convenient name for the bounded operator type used by the bridge. -/
abbrev BoundedOperator (𝕜 : Type u) (E : Type v) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] := E →L[𝕜] E

/-! A two-sided inverse witness for `algebraMap 𝕜 z - A`.

The definition is proposition-valued, so it cannot hide executable data in a
proof.  The inverse is an existential witness that must itself be checked by
the two displayed equations.
-/
def ResolventCertificate {𝕜 : Type u} {E : Type v} [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (A : E →L[𝕜] E) (z : 𝕜) : Prop :=
  ∃ R : E →L[𝕜] E,
    (algebraMap 𝕜 (E →L[𝕜] E) z - A) * R = 1 ∧
      R * (algebraMap 𝕜 (E →L[𝕜] E) z - A) = 1

namespace ResolventCertificate

variable {𝕜 : Type u} {E : Type v} [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {A : E →L[𝕜] E} {z : 𝕜}

/-! The existential certificate is intentionally proof-valued.  This
noncomputable selector exposes its inverse only after the certificate has
already been checked, so it cannot turn an unverified numerical inverse into a
theorem. -/

noncomputable def inverse (h : ResolventCertificate A z) : E →L[𝕜] E :=
  Classical.choose h

theorem inverse_spec (h : ResolventCertificate A z) :
    (algebraMap 𝕜 (E →L[𝕜] E) z - A) * h.inverse = 1 ∧
      h.inverse * (algebraMap 𝕜 (E →L[𝕜] E) z - A) = 1 :=
  Classical.choose_spec h

theorem inverse_eq_of_spec (h : ResolventCertificate A z)
    {R : E →L[𝕜] E}
    (_hleft : (algebraMap 𝕜 (E →L[𝕜] E) z - A) * R = 1)
    (hright : R * (algebraMap 𝕜 (E →L[𝕜] E) z - A) = 1) :
    h.inverse = R := by
  rcases h.inverse_spec with ⟨hinv_left, _⟩
  calc
    h.inverse = 1 * h.inverse := by simp
    _ = (R * (algebraMap 𝕜 (E →L[𝕜] E) z - A)) * h.inverse := by
      rw [hright]
    _ = R * ((algebraMap 𝕜 (E →L[𝕜] E) z - A) * h.inverse) := by
      noncomm_ring
    _ = R * 1 := by rw [hinv_left]
    _ = R := by simp

/-- A point outside mathlib's spectrum yields a checked two-sided inverse. -/
theorem of_not_mem (h : z ∉ spectrum 𝕜 A) : ResolventCertificate A z := by
  rw [spectrum.mem_iff] at h
  have hu : IsUnit ((algebraMap 𝕜 (E →L[𝕜] E) z) - A) := by
    exact Classical.byContradiction fun hn => h hn
  refine ⟨↑hu.unit⁻¹, hu.mul_val_inv, hu.val_inv_mul⟩

/-- The inverse equations are sufficient to prove spectral non-membership. -/
theorem not_mem (h : ResolventCertificate A z) : z ∉ spectrum 𝕜 A := by
  rw [spectrum.mem_iff]
  intro hs
  rcases h with ⟨R, hl, hr⟩
  exact hs ⟨Units.mk _ R hl hr, rfl⟩

theorem iff_not_mem : ResolventCertificate A z ↔ z ∉ spectrum 𝕜 A := by
  constructor
  · exact not_mem
  · exact of_not_mem

end ResolventCertificate

/-! **Resolvent identity.**  The convention here is
`(z - A)⁻¹ - (z - B)⁻¹ = (z - A)⁻¹ (A - B) (z - B)⁻¹`.
Both inverse equations are consumed explicitly; this is the algebraic core of
bounded spectral perturbation and linear-response estimates. -/

theorem resolvent_identity
    {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {A B : E →L[𝕜] E} {z : 𝕜}
    (hA : ResolventCertificate A z) (hB : ResolventCertificate B z) :
    hA.inverse - hB.inverse = hA.inverse * (A - B) * hB.inverse := by
  rcases hA.inverse_spec with ⟨hAl, hAr⟩
  rcases hB.inverse_spec with ⟨hBl, hBr⟩
  calc
    hA.inverse - hB.inverse =
        hA.inverse * ((algebraMap 𝕜 (E →L[𝕜] E) z - B) * hB.inverse) -
          (hA.inverse * (algebraMap 𝕜 (E →L[𝕜] E) z - A)) * hB.inverse := by
            rw [hBl, hAr]
            simp
    _ = hA.inverse * ((algebraMap 𝕜 (E →L[𝕜] E) z - B) -
          (algebraMap 𝕜 (E →L[𝕜] E) z - A)) * hB.inverse := by
            noncomm_ring
    _ = hA.inverse * (A - B) * hB.inverse := by
            congr 2
            module

/-! **Quantitative resolvent perturbation.**  The algebraic identity above is
    useful in applications only after it is paired with norm estimates.  This
    theorem keeps every numerical envelope explicit: the kernel supplies no
    estimate for an inverse or for an operator difference by itself. -/

theorem resolvent_perturbation_bound
    {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {A B : E →L[𝕜] E} {z : 𝕜}
    (hA : ResolventCertificate A z) (hB : ResolventCertificate B z)
    {rA rB δ : ℝ}
    (hrA : ‖hA.inverse‖ ≤ rA) (hrB : ‖hB.inverse‖ ≤ rB)
    (hδ : ‖A - B‖ ≤ δ) :
    ‖hA.inverse - hB.inverse‖ ≤ rA * δ * rB := by
  have hrA0 : 0 ≤ rA := (norm_nonneg _).trans hrA
  have hrB0 : 0 ≤ rB := (norm_nonneg _).trans hrB
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  rw [resolvent_identity hA hB]
  calc
    ‖hA.inverse * (A - B) * hB.inverse‖ ≤
        ‖hA.inverse‖ * ‖A - B‖ * ‖hB.inverse‖ := by
      calc
        ‖hA.inverse * (A - B) * hB.inverse‖ ≤
            ‖hA.inverse * (A - B)‖ * ‖hB.inverse‖ := norm_mul_le _ _
        _ ≤ (‖hA.inverse‖ * ‖A - B‖) * ‖hB.inverse‖ := by
          gcongr
          exact norm_mul_le _ _
    _ ≤ rA * δ * rB := by
      gcongr

/-! Operator norm bounds -/

/-! A pointwise bound that can be consumed by `opNorm_le`.  The bound is
    deliberately an explicit hypothesis: it can come from an analytic proof,
    a finite matrix certificate, or a separately checked numerical envelope. -/
structure OperatorNormBound {𝕜 : Type u} {E : Type v}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A : E →L[𝕜] E) (bound : ℝ) : Prop where
  nonneg : 0 ≤ bound
  pointwise : ∀ v : E, ‖A v‖ ≤ bound * ‖v‖

theorem OperatorNormBound.opNorm_le {𝕜 : Type u} {E : Type v}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {A : E →L[𝕜] E} {bound : ℝ} (h : OperatorNormBound A bound) :
    ‖A‖ ≤ bound :=
  A.opNorm_le_bound h.nonneg h.pointwise

theorem resolvent_perturbation_bound_of_operator_norm
    {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {A B : E →L[𝕜] E} {z : 𝕜}
    (hA : ResolventCertificate A z) (hB : ResolventCertificate B z)
    {rA rB δ : ℝ} (hRA : OperatorNormBound hA.inverse rA)
    (hRB : OperatorNormBound hB.inverse rB)
    (hδ : OperatorNormBound (A - B) δ) :
    ‖hA.inverse - hB.inverse‖ ≤ rA * δ * rB := by
  exact resolvent_perturbation_bound hA hB hRA.opNorm_le hRB.opNorm_le
    hδ.opNorm_le

/-! A norm envelope is a direct spectral exclusion criterion for a nonzero
    complex parameter.  The identity norm is available because the Hilbert
    space is assumed topologically nontrivial. -/
theorem resolvent_of_norm_bound {E : Type v} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] [NontrivialTopology E]
    (A : E →L[ℂ] E) (z : ℂ) (hA : ‖A‖ < ‖z‖) :
    ResolventCertificate A z := by
  apply ResolventCertificate.of_not_mem
  have hz : ‖A‖ * ‖(1 : E →L[ℂ] E)‖ < ‖z‖ := by
    simpa using hA
  have hres := spectrum.mem_resolventSet_of_norm_lt_mul hz
  rw [spectrum.mem_iff]
  exact not_not.mpr hres

/-! **Neumann spectral exclusion.**  This is the standard contraction criterion:
if a bounded operator has norm strictly below one, then `1 - A` is a unit.
The certificate stores the inverse equations produced by mathlib's unit
witness; it does not assert convergence of a series or extend the result to
unbounded operators. -/
theorem resolvent_of_neumann
    {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (A : E →L[𝕜] E) (hA : ‖A‖ < 1) :
    ResolventCertificate A 1 := by
  have hu : IsUnit ((1 : E →L[𝕜] E) - A) :=
    isUnit_one_sub_of_norm_lt_one hA
  refine ⟨↑hu.unit⁻¹, ?_, ?_⟩
  · simpa using hu.mul_val_inv
  · simpa using hu.val_inv_mul

/-! Compactness is available for proper scalar fields (in particular ℂ).
    We expose it as a theorem rather than putting a compactness field into a
    certificate, because compactness is a property of the ambient Banach
    algebra and needs no user-supplied proof. -/
theorem spectrum_compact {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [ProperSpace 𝕜] (A : E →L[𝕜] E) : IsCompact (spectrum 𝕜 A) := by
  exact spectrum.isCompact A

theorem spectrum_closed {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (A : E →L[𝕜] E) : IsClosed (spectrum 𝕜 A) := by
  exact spectrum.isClosed A

end LeanPhy.Mathematics
