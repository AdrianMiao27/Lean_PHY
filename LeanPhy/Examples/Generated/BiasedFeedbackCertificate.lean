import LeanPhy.StatMech.GibbsCertificate

/- Untrusted generated candidates; all numerical acceptance is kernel checked.
   Input digest: aeee2be9c2bc1c56eac7d6cd19ad063692179aebb0c174a85968923b9129fe93. -/
namespace LeanPhy.Generated.GibbsCertificates.BiasedFeedback

open LeanPhy.Mathematics LeanPhy.StatMech
open GibbsCertificate
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def action : Fin 2 → ℚ := ![(0 / 1 : ℚ), (0 / 1 : ℚ)]
def observables : Fin 1 → Fin 2 → ℚ := ![![(1 / 1 : ℚ), (-1 / 1 : ℚ)]]
def bias : Fin 1 → ℚ := ![(1 / 3 : ℚ)]
def coupling : Fin 1 → Fin 1 → ℚ := ![![(1 / 8 : ℚ)]]
def point : Fin 1 → ℚ := ![(361413 / 1000000 : ℚ)]
def candidates : Fin 1 → Candidate := ![{ shift := (0 / 1 : ℚ), depth := 0, order := 10, value := (361413 / 1000000 : ℚ), error := (1 / 100000 : ℚ) }]
def error : ℚ := (1 / 100000 : ℚ)

-- Exponents are derived from this model in Lean, not copied from Python.
theorem accepted : ∀ a, (candidates a).Accepted
    (exponent action observables (feedbackSource bias coupling point)) (observables a) :=
  by decide +kernel

theorem error_nonneg : 0 ≤ error := by decide +kernel
theorem values_match : ∀ a, (candidates a).value = point a := by decide +kernel
theorem errors_fit : ∀ a, (candidates a).error ≤ error := by decide +kernel

theorem valid : ErrorCertificate (fun a => (point a : ℝ))
    (SourceFeedback.feedback (fun i => (action i : ℝ)) (fun a i => (observables a i : ℝ))
      (fun a => (bias a : ℝ)) (fun a b => (coupling a b : ℝ)) (fun a => (point a : ℝ)))
      (error : ℝ) :=
  feedback_residual action observables bias coupling point candidates error
    error_nonneg values_match errors_fit accepted

theorem solution_bound
    (e : SourceFeedback.Envelope (fun a i => (observables a i : ℝ)) (fun a b => (coupling a b : ℝ)))
    (hsmall : e.rate < 1) :
    ErrorCertificate (fun a => (point a : ℝ))
      (e.solution (fun i => (action i : ℝ)) (fun a => (bias a : ℝ)) hsmall)
      ((error : ℝ) / (1 - e.rate)) :=
  e.solution_error _ _ hsmall _ _ valid

end LeanPhy.Generated.GibbsCertificates.BiasedFeedback
