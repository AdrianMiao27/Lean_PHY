import LeanPhy.FieldTheory.CCR
import LeanPhy.Condensed.Majorana
import LeanPhy.Quantum.Pauli
import LeanPhy.Quantum.ParametricSpectralGap
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Legacy BCS coefficient algebra and real-pairing gap adapter

This module proves complex-orthogonal Clifford identities and identities for
the complex-symmetric matrix `[[eps, Delta], [Delta, -eps]]`. Its finite
Hermitian gap adapter explicitly restricts both parameters to real values.
General complex pairing is implemented by `Condensed.ComplexPairing`, and
the full Nambu/CAR operator bridge by `FieldTheory.FermionBdG` and
`FieldTheory.FermionHamiltonian`.

`MeanField` records a supplied algebraic gap relation. It does not construct
the state-dependent self-consistency map or establish a nonzero solution. -/

namespace LeanPhy.Condensed

open LeanPhy.Quantum
open LeanPhy.FieldTheory
open scoped BigOperators

local notation "M2" => Matrix (Fin 2) (Fin 2) ℂ

/-! ## The Bogoliubov transformation as a rotation of Majorana modes

A physical Majorana pair uses `g1 = c + c†`, `g2 = -i (c - c†)` and an
adjoint relation. The structure below carries only the square and
anticommutation laws. A complex orthogonal rotation preserves these algebraic
laws, but need not preserve self-adjointness. The adjoint-compatible CAR
construction is in `FieldTheory.PhysicalMajorana`. -/

/-- Clifford algebra data without an assumed star operation or adjoint law. -/
structure CliffordPair where
  /-- Carrier ring of operators. -/
  A : Type
  [ringA : Ring A]
  [algA : Algebra ℂ A]
  /-- First Majorana mode. -/
  g1 : A
  /-- Second Majorana mode. -/
  g2 : A
  /-- g1^2 = 1. -/
  sq1 : g1 * g1 = 1
  /-- g2^2 = 1. -/
  sq2 : g2 * g2 = 1
  /-- {g1, g2} = 0. -/
  anti : g1 * g2 + g2 * g1 = 0

attribute [instance] CliffordPair.ringA CliffordPair.algA

namespace CliffordPair

variable (P : CliffordPair)

/-- **Bogoliubov invariance of the self-square.**  A rotation `c g1 + s g2` of
the two Majorana modes with `c^2 + s^2 = 1` is again an involution. -/
theorem bogoliubov_rotation (c s : ℂ) (h : c * c + s * s = 1) :
    (c • P.g1 + s • P.g2) * (c • P.g1 + s • P.g2) = 1 := by
  have ex : (c • P.g1 + s • P.g2) * (c • P.g1 + s • P.g2)
      = (c*c) • (P.g1*P.g1) + (c*s) • (P.g1*P.g2 + P.g2*P.g1)
        + (s*s) • (P.g2*P.g2) := by
    rw [add_mul, mul_add, mul_add]
    rw [smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm]
    rw [mul_comm s c, smul_add]
    abel
  rw [ex, P.sq1, P.sq2, P.anti, smul_zero]
  rw [show (c*c) • (1 : P.A) + 0 + (s*s) • (1 : P.A) = (c*c + s*s) • (1 : P.A) from by
        rw [add_zero, ← add_smul]]
  rw [h, one_smul]

/-- **Bogoliubov invariance of the anticommutator.**  The rotated pair
`(c g1 + s g2, -s g1 + c g2)` still anticommutes, so the transformation is an
automorphism of the Clifford pair. -/
theorem bogoliubov_anticommute (c s : ℂ) :
    (c • P.g1 + s • P.g2) * ((-s) • P.g1 + c • P.g2)
      + ((-s) • P.g1 + c • P.g2) * (c • P.g1 + s • P.g2) = 0 := by
  have e1 : (c • P.g1 + s • P.g2) * ((-s) • P.g1 + c • P.g2)
      = (-(c*s)) • (P.g1*P.g1) + (c*c) • (P.g1*P.g2) + (-(s*s)) • (P.g2*P.g1)
        + (s*c) • (P.g2*P.g2) := by
    rw [add_mul, mul_add, mul_add]
    rw [smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm]
    simp only [neg_mul, mul_neg, mul_one, one_mul]
    abel
  have e2 : ((-s) • P.g1 + c • P.g2) * (c • P.g1 + s • P.g2)
      = (-(s*c)) • (P.g1*P.g1) + (-(s*s)) • (P.g1*P.g2) + (c*c) • (P.g2*P.g1)
        + (c*s) • (P.g2*P.g2) := by
    rw [add_mul, mul_add, mul_add]
    rw [smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm]
    simp only [neg_mul, mul_neg, mul_one, one_mul]
    abel
  rw [e1, e2, P.sq1, P.sq2]
  have hneg : P.g2 * P.g1 = -(P.g1 * P.g2) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact P.anti
  rw [hneg]
  simp only [smul_neg]
  rw [mul_comm s c]
  simp only [neg_smul, one_smul]
  abel

end CliffordPair

/-! ## The BdG matrix and its spectrum -/

/-- Legacy complex-symmetric coefficient block; real inputs give a Hermitian block.
For general complex pairing use `ComplexPairing.block`. -/
def bdg (eps Delta : ℂ) : M2 := !![eps, Delta; Delta, -eps]

/-- The Bogoliubov rotation `R(u, v) = [[u, -v], [v, u]]`, the matrix form of
`u g1 + v g2` on the Majorana basis. -/
def bogoMatrix (u v : ℂ) : M2 := !![u, -v; v, u]

/-- Algebraic square of the legacy block. General complex inputs do not
imply Hermiticity or a positive excitation gap. -/
theorem bdg_sq (eps Delta : ℂ) : bdg eps Delta * bdg eps Delta
    = (eps ^ 2 + Delta ^ 2) • (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdg, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
    ring

/-- The BdG matrix is traceless, so its two eigenvalues sum to zero. -/
theorem bdg_trace (eps Delta : ℂ) : Matrix.trace (bdg eps Delta) = 0 := by
  simp [bdg, Matrix.trace, Fin.sum_univ_two]

/-- Determinant identity; a physical gap additionally needs the real-input
and nonvanishing conditions consumed by the adapter below. -/
theorem bdg_det (eps Delta : ℂ) : Matrix.det (bdg eps Delta) = -(eps ^ 2 + Delta ^ 2) := by
  simp [bdg, Matrix.det_fin_two]
  ring

/-- The BdG matrix is the Pauli combination `eps sigma_z + Delta sigma_x`, the
textbook form of the mean-field Hamiltonian. -/
theorem bdg_eq_pauli (eps Delta : ℂ) :
    bdg eps Delta = eps • pauliZ + Delta • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdg, pauliZ, pauliX, Matrix.add_apply, Matrix.smul_apply]

/-! ### Finite real BdG gap adapter

The matrix identities above are pointwise.  The following adapter connects
them to the common finite-family gap interface, so a discrete momentum or
finite-volume BdG table can carry one explicit radius.  A continuum minimum
or thermodynamic-limit statement is intentionally not inferred. -/

theorem bdg_real_isHermitian (eps Delta : ℝ) :
    (bdg eps Delta).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdg, Matrix.conjTranspose_apply] <;> ring

theorem bdg_uniform_finite_spectral_gap
    {κ : Type*} [Fintype κ]
    (eps Delta : κ → ℝ) (radius : ℝ) (hr : 0 < radius)
    (hgap : ∀ k, radius ^ 2 ≤ eps k ^ 2 + Delta k ^ 2) :
    LeanPhy.Quantum.HasUniformFiniteSpectralGap
      (fun k => bdg (eps k) (Delta k)) 0 radius := by
  apply LeanPhy.Quantum.hasUniformFiniteSpectralGap_of_square
    (q := fun k => eps k ^ 2 + Delta k ^ 2)
  · intro k
    exact bdg_real_isHermitian (eps k) (Delta k)
  · intro k
    convert bdg_sq (eps k) (Delta k) using 1 <;> norm_num
  · exact hr
  · exact hgap

/-- Unitary matrix conjugation flips `eps`. This identity does not apply
complex conjugation and is not an antiunitary particle-hole operation. -/
theorem bdg_sigmaX_conj (eps Delta : ℂ) :
    pauliX * bdg eps Delta * pauliX = bdg (-eps) Delta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdg, pauliX, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- Conjugating by `sigma_z` flips the sign of the gap `Delta`, the pairing
reflection. -/
theorem bdg_sigmaZ_conj (eps Delta : ℂ) :
    pauliZ * bdg eps Delta * pauliZ = bdg eps (-Delta) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdg, pauliZ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- The Bogoliubov rotation is orthogonal: `R^T R = 1` when `u^2 + v^2 = 1`, the
matrix form of the invariance proved at the operator level. -/
theorem bogoMatrix_orthogonal (u v : ℂ) (h : u ^ 2 + v ^ 2 = 1) :
    (bogoMatrix u v).transpose * bogoMatrix u v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bogoMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_two] <;>
    ring_nf <;> linear_combination h

/-! ## The mean-field gap equation -/

/-- Mean-field data of a superconductor: the pairing amplitude and the gap are
related by the coupling.  The self-consistency of the gap is what a fixed-point
argument would add; here it is an explicit equation, so the theorem states the
algebraic relation a derivation reads off. -/
structure MeanField where
  /-- The pairing amplitude of the condensate. -/
  pairingAmp : ℂ
  /-- The BCS coupling. -/
  g : ℂ
  /-- The gap order parameter. -/
  gap : ℂ
  /-- The mean-field gap equation `gap = -g * pairingAmp`. -/
  gap_eq : gap = -g * pairingAmp

/-- The gap is set by the pairing amplitude: `gap + g * pairingAmp = 0`. -/
theorem MeanField.gap_relation (M : MeanField) : M.gap + M.g * M.pairingAmp = 0 := by
  rw [M.gap_eq, neg_mul, neg_add_cancel]

/-- Substituting `g = -V` yields this algebraic relation. No positivity of V,
nonzero gap or state-dependent self-consistent solution is asserted. -/
theorem MeanField.gap_real_attractive (M : MeanField) (V : ℝ)
    (hg : M.g = -(V : ℂ)) : M.gap = (V : ℂ) * M.pairingAmp := by
  rw [M.gap_eq, hg, neg_neg]

end LeanPhy.Condensed
