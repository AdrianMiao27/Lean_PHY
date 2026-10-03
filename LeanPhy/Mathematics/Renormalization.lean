import LeanPhy.Mathematics.ContinuousAnalysis
import Mathlib.Tactic

/-!
# Regulator and renormalisation-limit certificates

Renormalisation arguments usually have three logically separate pieces: an
identity at each regulator, a limit for the regulated quantity, and a proof
that changing the subtraction scheme does not change that limit.  The records
below keep those pieces explicit.  They do not construct a path measure,
prove a BPHZ/flow equation, or infer convergence from a formal counterterm.
-/

namespace LeanPhy.Mathematics

open Filter
open scoped Topology

universe u v

structure RenormalizationCertificate
    {E : Type u} [AddCommGroup E] [TopologicalSpace E] [T2Space E]
    [ContinuousAdd E] [ContinuousNeg E] [ContinuousSub E]
    (bare counterterm renormalized : ℕ → E) (value : E) : Prop where
  relation : ∀ n, renormalized n = bare n - counterterm n
  limit_tendsto : Tendsto renormalized atTop (𝓝 value)

namespace RenormalizationCertificate

variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [T2Space E]
  [ContinuousAdd E] [ContinuousNeg E] [ContinuousSub E]
  {bare counterterm renormalized : ℕ → E} {value : E}

theorem of_limits
    (hbare : Tendsto bare atTop (𝓝 bareLimit))
    (hcounterterm : Tendsto counterterm atTop (𝓝 countertermLimit)) :
    RenormalizationCertificate bare counterterm
      (fun n => bare n - counterterm n) (bareLimit - countertermLimit) := by
  refine { relation := ?_, limit_tendsto := ?_ }
  · intro n
    rfl
  · exact hbare.sub hcounterterm

theorem value_unique
    {value₁ value₂ : E}
    (h₁ : RenormalizationCertificate bare counterterm renormalized value₁)
    (h₂ : RenormalizationCertificate bare counterterm renormalized value₂) :
    value₁ = value₂ := by
  exact tendsto_nhds_unique h₁.limit_tendsto h₂.limit_tendsto

theorem values_eq_of_difference_tendsto_zero
    {bare₁ counterterm₁ renormalized₁ : ℕ → E} {value₁ : E}
    {bare₂ counterterm₂ renormalized₂ : ℕ → E} {value₂ : E}
    (h₁ : RenormalizationCertificate bare₁ counterterm₁ renormalized₁ value₁)
    (h₂ : RenormalizationCertificate bare₂ counterterm₂ renormalized₂ value₂)
    (hzero : Tendsto (fun n => renormalized₁ n - renormalized₂ n)
      atTop (𝓝 0)) :
    value₁ = value₂ := by
  have hdiff : Tendsto (fun n => renormalized₁ n - renormalized₂ n)
      atTop (𝓝 (value₁ - value₂)) := h₁.limit_tendsto.sub h₂.limit_tendsto
  have hvalues : value₁ - value₂ = 0 :=
    tendsto_nhds_unique hdiff hzero
  exact sub_eq_zero.mp hvalues

theorem values_eq_of_bare_counterterm_differences
    {bare₁ counterterm₁ renormalized₁ : ℕ → E} {value₁ : E}
    {bare₂ counterterm₂ renormalized₂ : ℕ → E} {value₂ : E}
    (h₁ : RenormalizationCertificate bare₁ counterterm₁ renormalized₁ value₁)
    (h₂ : RenormalizationCertificate bare₂ counterterm₂ renormalized₂ value₂)
    (hbare : Tendsto (fun n => bare₁ n - bare₂ n) atTop (𝓝 0))
    (hcounterterm : Tendsto (fun n => counterterm₁ n - counterterm₂ n)
      atTop (𝓝 0)) :
    value₁ = value₂ := by
  apply h₁.values_eq_of_difference_tendsto_zero h₂
  have hzero := hbare.sub hcounterterm
  have hzero' : Tendsto (fun n => renormalized₁ n - renormalized₂ n)
      atTop (𝓝 0) := by
    convert hzero using 1
    · funext n
      rw [h₁.relation n, h₂.relation n]
      abel
    · simp
  exact hzero'

end RenormalizationCertificate

/-! A stronger record keeps the counterterm decomposition available to
downstream error ledgers while exposing the same limit theorem. -/

structure RegulatedObservable
    {E : Type u} [AddCommGroup E] [TopologicalSpace E] [T2Space E]
    [ContinuousAdd E] [ContinuousNeg E] [ContinuousSub E]
    (bare counterterm : ℕ → E) where
  renormalized : ℕ → E
  value : E
  certificate : RenormalizationCertificate bare counterterm renormalized value

namespace RegulatedObservable

variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [T2Space E]
  [ContinuousAdd E] [ContinuousNeg E] [ContinuousSub E]
  {bare counterterm : ℕ → E}

theorem tendsto (R : RegulatedObservable bare counterterm) :
    Tendsto R.renormalized atTop (𝓝 R.value) :=
  R.certificate.limit_tendsto

theorem relation (R : RegulatedObservable bare counterterm) (n : ℕ) :
    R.renormalized n = bare n - counterterm n :=
  R.certificate.relation n

end RegulatedObservable

end LeanPhy.Mathematics
