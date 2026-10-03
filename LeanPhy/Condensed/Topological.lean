import LeanPhy.Quantum.Pauli
import LeanPhy.Quantum.SpectralGap
import LeanPhy.Quantum.ParametricSpectralGap
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# Two-band Bloch algebra

`bloch d1 d2 d3 = d · σ` is defined for complex coefficients.  In that
algebraic generality `blochNorm` is the bilinear sum `d1² + d2² + d3²`,
not a positive norm: `(1, i, 0)` has zero square but is nonzero.

For real coefficients the matrix is Hermitian and the sum of squares
vanishes exactly at the origin.  A topological transition can require a gap
closing, but gap closing alone does not prove a transition.  Topological
invariants, bulk-boundary statements and thermodynamic limits are not
established here.  `GapModels` supplies real interval gap certificates.
-/

namespace LeanPhy.Condensed

open LeanPhy.Quantum
open scoped BigOperators Matrix

/-- The bilinear square `d1² + d2² + d3²`; a squared Euclidean norm only
when all three coefficients are real. -/
noncomputable def blochNorm (d1 d2 d3 : ℂ) : ℂ := d1 * d1 + d2 * d2 + d3 * d3

/-- The two-band Bloch Hamiltonian `H = d1 sigma_x + d2 sigma_y + d3 sigma_z`,
written directly as the `2 x 2` matrix. -/
noncomputable def bloch (d1 d2 d3 : ℂ) : Operator 2 :=
  !![d3, d1 - Complex.I * d2; d1 + Complex.I * d2, -d3]

/-- The Pauli decomposition `H = d1 sigma_x + d2 sigma_y + d3 sigma_z`. -/
theorem bloch_eq_pauli (d1 d2 d3 : ℂ) :
    bloch d1 d2 d3 = d1 • pauliX + d2 • pauliY + d3 • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bloch, pauliX, pauliY, pauliZ, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply] <;>
    ring

/-- **The Bloch Hamiltonian squares to the norm.**  `H^2 = (d . d) 1` is the
quadratic relation obeyed by the matrix; Hermiticity requires real coefficients. -/
theorem bloch_sq (d1 d2 d3 : ℂ) :
    bloch d1 d2 d3 * bloch d1 d2 d3 = blochNorm d1 d2 d3 • (1 : Operator 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [bloch, blochNorm, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.empty_val'] <;>
    norm_num <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring_nf)

/-- Both bands have opposite energy, so the Bloch Hamiltonian is traceless. -/
theorem bloch_trace (d1 d2 d3 : ℂ) : Matrix.trace (bloch d1 d2 d3) = 0 := by
  simp [bloch, Matrix.trace, Matrix.diag_apply]

/-- The determinant is the negative of the norm: `det H = -(d . d)`. -/
theorem bloch_det (d1 d2 d3 : ℂ) :
    Matrix.det (bloch d1 d2 d3) = -blochNorm d1 d2 d3 := by
  simp only [bloch, blochNorm, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.head_fin_const]
  ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring_nf)

/-- Over complex coefficients this is a determinant criterion only.
The further equivalence with a vanishing vector requires real coefficients. -/
theorem bloch_gap_closed_iff (d1 d2 d3 : ℂ) :
    Matrix.det (bloch d1 d2 d3) = 0 ↔ blochNorm d1 d2 d3 = 0 := by
  rw [bloch_det, neg_eq_zero]

/-- A nonzero bilinear square excludes a zero eigenvalue.  A quantitative
real interval gap and uniformity over momentum are separate assertions. -/
theorem bloch_nondegenerate (d1 d2 d3 : ℂ) (h : blochNorm d1 d2 d3 ≠ 0) :
    Matrix.det (bloch d1 d2 d3) ≠ 0 := by
  rw [bloch_det]; exact neg_ne_zero.mpr h

/-- **Spectral polynomial.**  Any `lam` with `lam^2 = d . d` satisfies
`(H - lam I)(H + lam I) = 0`.  This is a polynomial identity; it does
not supply eigenvectors or a uniform band gap. -/
theorem bloch_spectral_poly (d1 d2 d3 lam : ℂ) (h : lam * lam = blochNorm d1 d2 d3) :
    (bloch d1 d2 d3 - lam • (1 : Operator 2))
        * (bloch d1 d2 d3 + lam • (1 : Operator 2)) = 0 := by
  have hs := bloch_sq d1 d2 d3
  have expand :
      (bloch d1 d2 d3 - lam • (1 : Operator 2))
          * (bloch d1 d2 d3 + lam • (1 : Operator 2))
        = bloch d1 d2 d3 * bloch d1 d2 d3 - (lam * lam) • (1 : Operator 2) := by
    rw [sub_mul, mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul,
      smul_add, smul_smul]
    abel
  rw [expand, hs, h, sub_self]

section Chiral

/-- **Chiral (sublattice) symmetry.**  When the `d3` term is absent the
Hamiltonian anticommutes with `sigma_z`, `sigma_z H sigma_z = -H`.  This checks the
anticommutation relation; boundary modes and their protection need additional
boundary, spectral and topological hypotheses. -/
theorem bloch_chiral_symmetry (d1 d2 : ℂ) :
    pauliZ * bloch d1 d2 0 = -(bloch d1 d2 0 * pauliZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bloch, pauliZ, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Consequence: a chiral-symmetric Bloch Hamiltonian is traceless, hence has
the symmetric spectrum `{+lam, -lam}`. -/
theorem bloch_chiral_trace (d1 d2 : ℂ) : Matrix.trace (bloch d1 d2 0) = 0 :=
  bloch_trace d1 d2 0

end Chiral

/-- A concrete gapped example: the `d = (0, 0, 1)` insulator has `H = sigma_z`,
`det H = -1 ≠ 0`, so it is gapped.  The kernel evaluates the witness. -/
theorem bloch_gapped_witness : Matrix.det (bloch 0 0 1) ≠ 0 := by
  rw [bloch_det, blochNorm]
  norm_num

/-- A concrete gap-closing example: the `d = (1, 0, 0)` point has
`d . d = 1 ≠ 0` but the `d = (0, 0, 0)` point has `det H = 0`, the
zero matrix; no claim about a topological transition is implied.  Both are evaluated by the kernel. -/
theorem bloch_gap_witness : Matrix.det (bloch 0 0 0) = 0 := by
  rw [bloch_det, blochNorm]; ring

/-- Real Bloch coefficients supply the Hermiticity needed for spectral gaps. -/
theorem bloch_real_isHermitian (x y z : ℝ) :
    (bloch x y z).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bloch, Matrix.conjTranspose_apply, Complex.ofReal_mul] <;> ring

/-- Correct zero-energy closing criterion for Hermitian two-band models. -/
theorem bloch_real_det_zero_iff (x y z : ℝ) :
    (bloch x y z).det = 0 ↔ x = 0 ∧ y = 0 ∧ z = 0 := by
  rw [bloch_gap_closed_iff]
  constructor
  · intro h
    have hreal := congrArg Complex.re h
    simp [blochNorm] at hreal
    have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg y, sq_nonneg z]
    have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg z]
    have hz : z ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    exact ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp [blochNorm]

/-- Non-Hermitian regression: a nonzero Bloch vector can have zero square. -/
theorem bloch_complex_null_counterexample :
    blochNorm 1 Complex.I 0 = 0 ∧ bloch 1 Complex.I 0 ≠ 0 := by
  constructor
  · norm_num [blochNorm, Complex.I_sq]
  · intro h
    have he := congrFun (congrFun h 0) 1
    norm_num [bloch, Complex.I_sq] at he

/-! ### Finite real Bloch-family gap adapter

For a finite momentum mesh, a pointwise nonzero Bloch vector can be promoted
to one common interval gap once a common lower-bound certificate is supplied.
The theorem does not infer a continuum minimum or a topological invariant. -/

theorem bloch_real_uniform_finite_spectral_gap
    {κ : Type*} [Fintype κ]
    (x y z : κ → ℝ) (radius : ℝ) (hr : 0 < radius)
    (hgap : ∀ k, radius ^ 2 ≤ x k ^ 2 + y k ^ 2 + z k ^ 2) :
    LeanPhy.Quantum.HasUniformFiniteSpectralGap
      (fun k => bloch (x k) (y k) (z k)) 0 radius := by
  apply LeanPhy.Quantum.hasUniformFiniteSpectralGap_of_square
    (q := fun k => x k ^ 2 + y k ^ 2 + z k ^ 2)
  · intro k
    exact bloch_real_isHermitian (x k) (y k) (z k)
  · intro k
    convert bloch_sq (x k) (y k) (z k) using 1
    simp [blochNorm]
    ring
  · exact hr
  · exact hgap

end LeanPhy.Condensed
