import LeanPhy.Mathematics.ContinuousEvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Energy and dissipation budgets

Energy estimates are the common formal core of dissipative PDE, finite-volume
fluid schemes, Langevin dynamics and turbulence closures.  The certificate in
this file records an integrated inequality; it does not assert that a field,
velocity or weak solution exists.  All regularity and boundary conditions are
therefore represented by the integrability and pointwise hypotheses supplied
by the user.
-/

namespace LeanPhy.Mathematics

open MeasureTheory
open scoped Interval

universe u

structure EnergyDissipationCertificate
    (energy dissipation forcing : ℝ → ℝ) (a b : ℝ) : Prop where
  ordered : a ≤ b
  energy_nonneg : ∀ t, 0 ≤ energy t
  dissipation_nonneg : ∀ t, 0 ≤ dissipation t
  dissipation_integrable : IntervalIntegrable dissipation volume a b
  forcing_integrable : IntervalIntegrable forcing volume a b
  balance_le :
    energy b + ∫ t in a..b, dissipation t ≤
      energy a + ∫ t in a..b, forcing t

namespace EnergyDissipationCertificate

variable {energy dissipation forcing : ℝ → ℝ} {a b : ℝ}

theorem dissipation_integral_nonneg
    (h : EnergyDissipationCertificate energy dissipation forcing a b) :
    0 ≤ ∫ t in a..b, dissipation t :=
  intervalIntegral.integral_nonneg_of_forall h.ordered h.dissipation_nonneg

theorem energy_end_le
    (h : EnergyDissipationCertificate energy dissipation forcing a b) :
    energy b ≤ energy a + ∫ t in a..b, forcing t := by
  linarith [h.balance_le, h.dissipation_integral_nonneg]

theorem total_dissipation_le
    (h : EnergyDissipationCertificate energy dissipation forcing a b) :
    ∫ t in a..b, dissipation t ≤
      energy a + ∫ t in a..b, forcing t := by
  linarith [h.balance_le, h.energy_nonneg b]

theorem energy_end_le_of_forcing_bound
    (h : EnergyDissipationCertificate energy dissipation forcing a b)
    {majorant : ℝ → ℝ}
    (hmajorant_integrable : IntervalIntegrable majorant volume a b)
    (hmajorant : ∀ t ∈ Set.Icc a b, forcing t ≤ majorant t) :
    energy b ≤ energy a + ∫ t in a..b, majorant t := by
  have hforcing : ∫ t in a..b, forcing t ≤ ∫ t in a..b, majorant t := by
    exact intervalIntegral.integral_mono_on h.ordered h.forcing_integrable
      hmajorant_integrable hmajorant
  linarith [h.energy_end_le, hforcing]

theorem dissipation_time_average_le
    (h : EnergyDissipationCertificate energy dissipation forcing a b)
    {majorant : ℝ → ℝ}
    (hmajorant_integrable : IntervalIntegrable majorant volume a b)
    (hmajorant : ∀ t ∈ Set.Icc a b, forcing t ≤ majorant t)
    (hwidth : 0 < b - a) :
    (∫ t in a..b, dissipation t) / (b - a) ≤
      (energy a + ∫ t in a..b, majorant t) / (b - a) := by
  have hforcing : ∫ t in a..b, forcing t ≤ ∫ t in a..b, majorant t :=
    intervalIntegral.integral_mono_on h.ordered h.forcing_integrable
      hmajorant_integrable hmajorant
  have htotal := h.total_dissipation_le
  have htotal' : ∫ t in a..b, dissipation t ≤
      energy a + ∫ t in a..b, majorant t := by
    linarith [htotal, hforcing]
  exact div_le_div_of_nonneg_right htotal' (le_of_lt hwidth)

end EnergyDissipationCertificate

/-! A residual form is convenient for approximate numerical trajectories. -/

structure EnergyResidualCertificate
    (energy dissipation forcing residual : ℝ → ℝ) (a b : ℝ) : Prop where
  ordered : a ≤ b
  residual_nonneg : ∀ t, 0 ≤ residual t
  dissipation_integrable : IntervalIntegrable dissipation volume a b
  forcing_integrable : IntervalIntegrable forcing volume a b
  residual_integrable : IntervalIntegrable residual volume a b
  inequality :
    energy b + ∫ t in a..b, dissipation t ≤
      energy a + ∫ t in a..b, forcing t + ∫ t in a..b, residual t

namespace EnergyResidualCertificate

variable {energy dissipation forcing residual : ℝ → ℝ} {a b : ℝ}

theorem energy_end_le
    (h : EnergyResidualCertificate energy dissipation forcing residual a b)
    (hdissipation_nonneg : ∀ t, 0 ≤ dissipation t) :
    energy b ≤ energy a + ∫ t in a..b, forcing t +
      ∫ t in a..b, residual t := by
  have hD : 0 ≤ ∫ t in a..b, dissipation t :=
    intervalIntegral.integral_nonneg_of_forall h.ordered hdissipation_nonneg
  linarith [h.inequality, hD]

end EnergyResidualCertificate

end LeanPhy.Mathematics
