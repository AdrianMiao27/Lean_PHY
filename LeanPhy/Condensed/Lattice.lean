import LeanPhy.Quantum.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Complex.Basic

open scoped BigOperators

/-!
# Finite lattice algebra for condensed-matter prototypes

Everything here is a finite sum identity.  A hopping term is written
`g † c + conj g c †`, so that a real coupling makes the coefficient self-adjoint;
the point is to isolate the algebraic content that later phases will use when
proving properties of concrete lattice Hamiltonians.
-/

namespace LeanPhy.Condensed

open LeanPhy.Quantum

variable {ι : Type} [Fintype ι]

/-- A nearest-neighbour hopping term with coupling `g`, pairing the creation and
annihilation directions with conjugate weights. -/
def hoppingTerm (g : ℂ) (c cdag : ι → ℂ) : ι → ℂ :=
  fun i => g * cdag i + star g * c i

/-- Sum of a per-site local term. -/
def localSum (f : ι → ℂ) : ℂ := ∑ i, f i

@[simp] theorem localSum_zero : localSum (fun _ : ι => (0 : ℂ)) = 0 := by
  simp [localSum]

theorem localSum_add (f g : ι → ℂ) :
    localSum (fun i => f i + g i) = localSum f + localSum g := by
  simp [localSum, Finset.sum_add_distrib]

theorem localSum_smul (c : ℂ) (f : ι → ℂ) :
    localSum (fun i => c * f i) = c * localSum f := by
  simp [localSum, Finset.mul_sum]

/-- The conjugate of a hopping term with real coupling swaps the two directions. -/
theorem hoppingTerm_real_conj {ι : Type} (t : ℝ) (c cdag : ι → ℂ) :
    hoppingTerm (t : ℂ) c cdag = fun i => (t : ℂ) * cdag i + (t : ℂ) * c i := by
  funext i
  simp [hoppingTerm, Complex.conj_ofReal]

def totalOccupation (n : ι → ℂ) : ℂ := localSum n

theorem totalOccupation_add (n m : ι → ℂ) :
    totalOccupation (fun i => n i + m i) = totalOccupation n + totalOccupation m := by
  simpa only [totalOccupation] using localSum_add n m

end LeanPhy.Condensed
