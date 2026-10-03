import LeanPhy.Surface.DiracNotation
import LeanPhy.Quantum.Pauli
import LeanPhy.Quantum.Spin
import LeanPhy.Quantum.Oscillator
import Mathlib.LinearAlgebra.Matrix.Notation

open scoped BigOperators
open scoped LeanPhy.Dirac

namespace LeanPhy.Examples

open LeanPhy.Quantum
open scoped LeanPhy.Quantum

/-!
# Worked example: the one-dimensional harmonic oscillator, end to end

This is the end-to-end acceptance case the feasibility plan singled out.  It
threads the finite-dimensional surface together with the algebraic field layer:

1. define the ladder operators of a truncation, and the number operator;
2. prove the ladder identity `[N, a†] = a†` at the abstract ring level (where
   the CCR is the only hypothesis);
3. read the same statement off in Dirac notation on a concrete two-level
   truncation, so the notation and the algebra are visibly the same fact.

Nothing analytic (an infinite Fock space, domains, convergence) is claimed;
the CCR is an explicit hypothesis, exactly as in `LeanPhy/FieldTheory`.
-/

/-- Abstract oscillator: the CCR is the only input. -/
theorem number_ladder {A : Type} [Ring A] (a adag : A) (h : commutator a adag = 1) :
    commutator (adag * a) adag = adag :=
  LeanPhy.Quantum.number_commutator a adag h

/-- The same fact with an explicit `N := a† a`, phrased for physics reading. -/
theorem number_ladder' {A : Type} [Ring A] (a adag : A)
    (N : A) (hN : N = adag * a) (h : commutator a adag = 1) :
    commutator N adag = adag := by
  subst hN
  exact number_ladder a adag h

/-! ## A concrete two-level truncation -/

/-- The truncated annihilation operator `a` on a 2-level space, `|1> -> |0>`. -/
def truncA : Operator 2 := !![0, 1; 0, 0]

/-- Its adjoint `a†`, `|0> -> |1>`. -/
def truncAdag : Operator 2 := !![0, 0; 1, 0]

/-- The truncated number operator `N = a† a = diag(0, 1)`. -/
def truncN : Operator 2 := !![0, 0; 0, 1]

/-- `N` really is `a† a` in the truncation. -/
theorem truncN_eq : truncN = truncAdag * truncA := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [truncN, truncAdag, truncA, Matrix.mul_apply]

/-- The truncated ladder raises: `[N, a†] = a†`.  This is the finite shadow of
the abstract identity above; the truncation drops the `aa†` term that only
matters above the cutoff, which is exactly why the abstract theorem is the
trustworthy statement and this is its illustration. -/
theorem truncN_ladder :
    truncN * truncAdag - truncAdag * truncN = truncAdag := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [truncN, truncAdag]

/-- Dirac-notation reading: the number operator acts diagonally, `N|1> = |1>`. -/
theorem truncN_on_state : truncN.mulVec (|(1 : Fin 2)⟩ : Ket 2) = (|(1 : Fin 2)⟩ : Ket 2) := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, truncN, basisKet]

/-- ... and the raising operator moves `|0>` to `|1>`. -/
theorem truncAdag_on_state : truncAdag.mulVec (|(0 : Fin 2)⟩ : Ket 2) = (|(1 : Fin 2)⟩ : Ket 2) := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, truncAdag, basisKet]

end LeanPhy.Examples
