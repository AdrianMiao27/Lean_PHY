import LeanPhy.Condensed.BCS
import LeanPhy.FieldTheory.FermionBdG

set_option autoImplicit false

/-!
# Complex Hermitian pairing blocks

The reduced `(c_up,c_down†)` block uses the conjugate pairing entry. It is
not the full Nambu doubling of a single spinless mode: that mode cannot have
on-site pairing. The full two-mode antisymmetric pairing matrix below embeds
this reduced block. A gap bound uses `|Δ|²`, not the complex number `Δ²`.
-/

namespace LeanPhy.Condensed.ComplexPairing

open LeanPhy.Quantum LeanPhy.FieldTheory.FermionBdG
open scoped Matrix

def block (ε : ℝ) (Δ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(ε : ℂ), Δ; star Δ, -(ε : ℂ)]

theorem hermitian (ε : ℝ) (Δ : ℂ) : (block ε Δ).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block, Matrix.conjTranspose_apply]

theorem square (ε : ℝ) (Δ : ℂ) :
    block ε Δ * block ε Δ = ((ε ^ 2 + Complex.normSq Δ : ℝ) : ℂ) •
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hΔ := Complex.mul_conj Δ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, Matrix.mul_apply, Fin.sum_univ_two, hΔ, mul_comm] <;> ring

theorem real_pairing (ε Δ : ℝ) : block ε (Δ : ℂ) = bdg ε Δ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block, bdg]

/-- The sign on Im Δ follows the stated upper-right pairing convention. -/
theorem pauli_decomposition (ε : ℝ) (Δ : ℂ) :
    block ε Δ = (ε : ℂ) • pauliZ + (Δ.re : ℂ) • pauliX - (Δ.im : ℂ) • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;> simp [block, pauliZ, pauliX, pauliY] <;> ring

/-- Every pairing phase has the same square and the same certified gap radius. -/
theorem uniform_gap {κ : Type*} [Fintype κ] (ε : κ → ℝ) (Δ : κ → ℂ)
    (radius : ℝ) (hr : 0 < radius)
    (hgap : ∀ k, radius ^ 2 ≤ ε k ^ 2 + Complex.normSq (Δ k)) :
    HasUniformFiniteSpectralGap (fun k => block (ε k) (Δ k)) 0 radius := by
  exact hasUniformFiniteSpectralGap_of_square _ _ radius
    (fun k => hermitian (ε k) (Δ k)) (fun k => square (ε k) (Δ k)) hr hgap

/-- Full two-mode coefficients: pairing is antisymmetric in physical modes. -/
def pairedModes (ε : ℝ) (Δ : ℂ) : Coefficients (Fin 2) where
  normal := (ε : ℂ) • 1
  pairing := !![0, Δ; -Δ, 0]
  normal_hermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  pairing_skew := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

def reducedIndex : Fin 2 → Fin 2 ⊕ Fin 2 := ![Sum.inl 0, Sum.inr 1]

theorem full_to_reduced (ε : ℝ) (Δ : ℂ) :
    (pairedModes ε Δ).matrix.submatrix reducedIndex reducedIndex = block ε Δ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairedModes, Coefficients.matrix, reducedIndex, Matrix.submatrix,
      Matrix.conjTranspose_apply, block]

end LeanPhy.Condensed.ComplexPairing
