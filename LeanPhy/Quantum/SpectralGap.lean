import LeanPhy.Quantum.Unitary
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite resolvents and spectral gaps

For finite models, the statement that an energy `λ` is absent from the
spectrum can be expressed without invoking a spectral-existence theorem:
provide a two-sided matrix inverse for `H - λ I`.  This is the algebraic
resolvent predicate used here.  It is strong enough for Bloch and BdG
Hamiltonians, finite-volume QFT truncations, scattering matrices and flavor
mixing, while keeping analytic spectral measures and continuum limits
outside the definition.

The main structural theorem says that a finite unitary change of basis
preserves this predicate.  The inverse is transported explicitly by the same
similarity transformation, so the result is auditable by the kernel.
-/

namespace LeanPhy.Quantum

open scoped Matrix

/-- A two-sided inverse witness for the shifted finite operator `A - λ I`. -/
def HasFiniteResolvent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (z : ℂ) : Prop :=
  ∃ R : Matrix ι ι ℂ,
    (A - z • (1 : Matrix ι ι ℂ)) * R = 1 ∧
      R * (A - z • (1 : Matrix ι ι ℂ)) = 1

/-- A genuine real-energy gap: a Hermitian matrix has no spectrum in the open
interval `(center - radius, center + radius)`, with a strictly positive radius.
This is for one finite operator, not a uniform thermodynamic-limit gap. -/
def IsFiniteSpectralGap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (center radius : ℝ) : Prop :=
  0 < radius ∧ A.IsHermitian ∧
    ∀ E : ℝ, |E - center| < radius → HasFiniteResolvent A (E : ℂ)

/-- Exact bridge to the existing mathlib determinant criterion. -/
theorem hasFiniteResolvent_iff_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (z : ℂ) :
    HasFiniteResolvent A z ↔ (A - z • (1 : Matrix ι ι ℂ)).det ≠ 0 := by
  constructor
  · rintro ⟨R, hR, _⟩
    exact Matrix.det_ne_zero_of_right_inverse hR
  · intro h
    exact ⟨_, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h),
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)⟩

/-- Our explicit inverse uses `A - z I`; mathlib's resolvent uses `z I - A`.
The sign changes the inverse but not membership in the resolvent set. -/
theorem hasFiniteResolvent_iff_not_mem_spectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (z : ℂ) :
    HasFiniteResolvent A z ↔ z ∉ spectrum ℂ A := by
  rw [spectrum.mem_iff, not_not, Algebra.algebraMap_eq_smul_one,
    IsUnit.sub_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact hasFiniteResolvent_iff_det_ne_zero A z

/-- No nonzero eigenvector can occur at a resolvent point. -/
theorem HasFiniteResolvent.eq_zero_of_eigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} {z : ℂ} (h : HasFiniteResolvent A z)
    (v : ι → ℂ) (hv : A.mulVec v = z • v) : v = 0 := by
  rcases h with ⟨R, _, hR⟩
  have hzero : (A - z • (1 : Matrix ι ι ℂ)).mulVec v = 0 := by
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec, hv]
  calc
    v = (R * (A - z • (1 : Matrix ι ι ℂ))).mulVec v := by rw [hR]; simp
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hzero]; simp

private theorem conjugate_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : FiniteUnitary ι) (A : Matrix ι ι ℂ) (z : ℂ) :
    U.conjugate A - z • (1 : Matrix ι ι ℂ) =
      U.op * (A - z • (1 : Matrix ι ι ℂ)) * Matrix.conjTranspose U.op := by
  have hscalar : U.op * (z • (1 : Matrix ι ι ℂ)) *
      Matrix.conjTranspose U.op = z • (1 : Matrix ι ι ℂ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
    simp [Matrix.mul_one, U.right_unitary]
  unfold FiniteUnitary.conjugate
  calc
    U.op * A * Matrix.conjTranspose U.op - z • (1 : Matrix ι ι ℂ) =
        U.op * A * Matrix.conjTranspose U.op -
          U.op * (z • (1 : Matrix ι ι ℂ)) * Matrix.conjTranspose U.op := by
            rw [hscalar]
    _ = U.op * (A - z • (1 : Matrix ι ι ℂ)) *
        Matrix.conjTranspose U.op := by
          simp only [sub_mul, mul_sub, Matrix.mul_smul, Matrix.smul_mul]

theorem FiniteUnitary.conjugate_hasFiniteResolvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : FiniteUnitary ι) (A : Matrix ι ι ℂ) (z : ℂ)
    (hA : HasFiniteResolvent A z) :
    HasFiniteResolvent (U.conjugate A) z := by
  rcases hA with ⟨R, hleft, hright⟩
  refine ⟨U.op * R * Matrix.conjTranspose U.op, ?_, ?_⟩
  · rw [conjugate_shift U A z]
    calc
      (U.op * (A - z • (1 : Matrix ι ι ℂ)) * Matrix.conjTranspose U.op) *
          (U.op * R * Matrix.conjTranspose U.op) =
          U.op * (A - z • (1 : Matrix ι ι ℂ)) *
            (Matrix.conjTranspose U.op * U.op) * R *
            Matrix.conjTranspose U.op := by
              noncomm_ring
      _ = U.op * ((A - z • (1 : Matrix ι ι ℂ)) * R) *
            Matrix.conjTranspose U.op := by
              rw [U.unitary]
              simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = U.op * (1 : Matrix ι ι ℂ) * Matrix.conjTranspose U.op := by
            rw [hleft]
      _ = 1 := by rw [Matrix.mul_one, U.right_unitary]
  · rw [conjugate_shift U A z]
    calc
      (U.op * R * Matrix.conjTranspose U.op) *
          (U.op * (A - z • (1 : Matrix ι ι ℂ)) * Matrix.conjTranspose U.op) =
          U.op * R * (Matrix.conjTranspose U.op * U.op) *
            (A - z • (1 : Matrix ι ι ℂ)) * Matrix.conjTranspose U.op := by
              noncomm_ring
      _ = U.op * (R * (A - z • (1 : Matrix ι ι ℂ))) *
            Matrix.conjTranspose U.op := by
              rw [U.unitary]
              simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = U.op * (1 : Matrix ι ι ℂ) * Matrix.conjTranspose U.op := by
            rw [hright]
      _ = 1 := by rw [Matrix.mul_one, U.right_unitary]

theorem FiniteUnitary.adjoint_conjugate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : FiniteUnitary ι) (A : Matrix ι ι ℂ) :
    U.adjoint.conjugate (U.conjugate A) = A := by
  unfold FiniteUnitary.adjoint FiniteUnitary.conjugate
  simp only [Matrix.conjTranspose_conjTranspose]
  calc
    Matrix.conjTranspose U.op * (U.op * A * Matrix.conjTranspose U.op) * U.op =
        (Matrix.conjTranspose U.op * U.op) * A *
          (Matrix.conjTranspose U.op * U.op) := by
            noncomm_ring
    _ = A := by rw [U.unitary]; simp

theorem FiniteUnitary.conjugate_hasFiniteResolvent_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : FiniteUnitary ι) (A : Matrix ι ι ℂ) (z : ℂ) :
    HasFiniteResolvent (U.conjugate A) z ↔ HasFiniteResolvent A z := by
  constructor
  · intro h
    have hback := U.adjoint.conjugate_hasFiniteResolvent
      (U.conjugate A) z h
    rw [U.adjoint_conjugate] at hback
    exact hback
  · exact fun h => U.conjugate_hasFiniteResolvent A z h

theorem FiniteUnitary.conjugate_isFiniteSpectralGap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : FiniteUnitary ι) (A : Matrix ι ι ℂ) (center radius : ℝ)
    (h : IsFiniteSpectralGap A center radius) :
    IsFiniteSpectralGap (U.conjugate A) center radius := by
  refine ⟨h.1, Matrix.isHermitian_mul_mul_conjTranspose U.op h.2.1, ?_⟩
  intro E hE
  exact U.conjugate_hasFiniteResolvent A E (h.2.2 E hE)

theorem FiniteUnitary.conjugate_isFiniteSpectralGap_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : FiniteUnitary ι) (A : Matrix ι ι ℂ) (center radius : ℝ) :
    IsFiniteSpectralGap (U.conjugate A) center radius ↔
      IsFiniteSpectralGap A center radius := by
  constructor
  · intro h
    have hb := U.adjoint.conjugate_isFiniteSpectralGap (U.conjugate A) center radius h
    rwa [U.adjoint_conjugate] at hb
  · exact U.conjugate_isFiniteSpectralGap A center radius

/-- Certified inverse for quadratic operator relations.  The convention is
`(A - z I)⁻¹ = (q - z²)⁻¹ (A + z I)` when `A² = q I`.  The denominator
condition is mandatory, including at poles of a Dirac or BdG propagator. -/
theorem quadratic_resolvent_certificate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (q z : ℂ) (hA : A * A = q • (1 : Matrix ι ι ℂ))
    (hq : q - z ^ 2 ≠ 0) :
    let R := (q - z ^ 2)⁻¹ • (A + z • (1 : Matrix ι ι ℂ))
    (A - z • (1 : Matrix ι ι ℂ)) * R = 1 ∧
      R * (A - z • (1 : Matrix ι ι ℂ)) = 1 := by
  dsimp
  have hl : (A - z • (1 : Matrix ι ι ℂ)) *
      (A + z • (1 : Matrix ι ι ℂ)) = (q - z ^ 2) • (1 : Matrix ι ι ℂ) := by
    simp only [sub_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_one, smul_smul, hA]
    module
  have hr : (A + z • (1 : Matrix ι ι ℂ)) *
      (A - z • (1 : Matrix ι ι ℂ)) = (q - z ^ 2) • (1 : Matrix ι ι ℂ) := by
    simp only [add_mul, mul_sub, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_one, smul_smul, hA]
    module
  constructor
  · rw [Matrix.mul_smul, hl, smul_smul, inv_mul_cancel₀ hq, one_smul]
  · rw [Matrix.smul_mul, hr, smul_smul, inv_mul_cancel₀ hq, one_smul]

theorem hasFiniteResolvent_of_square
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (q z : ℂ) (hA : A * A = q • (1 : Matrix ι ι ℂ))
    (hq : q - z ^ 2 ≠ 0) : HasFiniteResolvent A z :=
  ⟨_, quadratic_resolvent_certificate A q z hA hq⟩

/-- A lower bound on a real scalar square certifies a whole open interval.
The radius is explicit so the theorem can be reused uniformly over momentum,
parameters, or volume without inferring uniformity from pointwise gaps. -/
theorem isFiniteSpectralGap_of_square
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (q radius : ℝ) (hHerm : A.IsHermitian)
    (hA : A * A = (q : ℂ) • (1 : Matrix ι ι ℂ))
    (hr : 0 < radius) (hq : radius ^ 2 ≤ q) :
    IsFiniteSpectralGap A 0 radius := by
  refine ⟨hr, hHerm, ?_⟩
  intro E hE
  have hE' : |E| < radius := by simpa using hE
  have hs : E ^ 2 < radius ^ 2 := by
    nlinarith [sq_nonneg (radius - |E|), sq_abs E, abs_nonneg E]
  apply hasFiniteResolvent_of_square A q E hA
  have hn : q - E ^ 2 ≠ 0 := ne_of_gt (by linarith)
  exact_mod_cast hn

end LeanPhy.Quantum
