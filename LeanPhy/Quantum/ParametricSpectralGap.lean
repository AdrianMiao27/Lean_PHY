import LeanPhy.Quantum.SpectralGap

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Uniform finite spectral gaps for parameter families

Many finite physics models are not a single matrix but a finite family
indexed by momentum, a boundary sector, a flavor label, or a finite-volume
configuration.  A pointwise resolvent statement is weaker than a uniform
gap.  This module keeps the distinction explicit: `HasUniformFiniteSpectralGap`
contains one radius and a gap proof for every member of the family.

The result is intentionally finite and algebraic.  It does not claim a
thermodynamic-limit gap, continuity in a real momentum, or a minimum over a
compact set.  Those are separate analysis obligations which can later be
bridged to this interface.
-/

namespace LeanPhy.Quantum

open scoped Matrix

/-- A common real-energy gap certificate for a finite family of finite
operators.  The same `center` and strictly positive `radius` must work at
every parameter value. -/
def HasUniformFiniteSpectralGap {κ ι : Type*} [Fintype κ]
    [Fintype ι] [DecidableEq ι]
    (A : κ → Matrix ι ι ℂ) (center radius : ℝ) : Prop :=
  0 < radius ∧ ∀ k, IsFiniteSpectralGap (A k) center radius

theorem HasUniformFiniteSpectralGap.pointwise
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {A : κ → Matrix ι ι ℂ} {center radius : ℝ}
    (h : HasUniformFiniteSpectralGap A center radius) (k : κ) :
    IsFiniteSpectralGap (A k) center radius :=
  h.2 k

/-- Uniform gaps are preserved by a parameter-dependent unitary change of
basis.  This covers momentum-dependent Bloch/BdG bases and finite flavor
mixing matrices. -/
theorem uniform_conjugate_isFiniteSpectralGap_iff
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (U : κ → FiniteUnitary ι) (A : κ → Matrix ι ι ℂ)
    (center radius : ℝ) :
    HasUniformFiniteSpectralGap (fun k => (U k).conjugate (A k)) center radius ↔
      HasUniformFiniteSpectralGap A center radius := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro k
    exact ((U k).conjugate_isFiniteSpectralGap_iff (A k) center radius).mp (h.2 k)
  · intro h
    refine ⟨h.1, ?_⟩
    intro k
    exact ((U k).conjugate_isFiniteSpectralGap_iff (A k) center radius).mpr (h.2 k)

/-- A pointwise quadratic relation plus one common lower bound constructs a
uniform finite gap.  The lower bound is a supplied certificate; no hidden
compactness or continuity theorem is used. -/
theorem hasUniformFiniteSpectralGap_of_square
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (A : κ → Matrix ι ι ℂ) (q : κ → ℝ) (radius : ℝ)
    (hHerm : ∀ k, (A k).IsHermitian)
    (hA : ∀ k, A k * A k = (q k : ℂ) • (1 : Matrix ι ι ℂ))
    (hr : 0 < radius) (hq : ∀ k, radius ^ 2 ≤ q k) :
    HasUniformFiniteSpectralGap A 0 radius := by
  refine ⟨hr, ?_⟩
  intro k
  exact isFiniteSpectralGap_of_square (A k) (q k) radius
    (hHerm k) (hA k) hr (hq k)

end LeanPhy.Quantum
