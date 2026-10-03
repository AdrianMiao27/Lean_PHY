import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# The no-cloning theorem

The no-cloning theorem says that no physical process can copy an arbitrary
unknown quantum state.  This module proves the algebraic core of the standard
argument, in the form physicists state it.

Suppose a linear map `U` (the would-be cloner, acting on the state together with
a fixed blank ancilla `b`) copies both basis states,

    U (|0> (x) b) = |0> (x) |0>,     U (|1> (x) b) = |1> (x) |1>.

Because `U` is linear, acting on the superposition `|0> + |1>` forces

    U ((|0> + |1>) (x) b) = |0> (x) |0> + |1> (x) |1>,

and the right-hand side is the entangled Bell state `|00> + |11>`, which is *not*
a product `(|0> + |1>) (x) P` for any `P`.  So the same linear `U` cannot clone the
superposition, and the assumption that a single machine clones every state is
inconsistent.  The kernel checks both halves:

* `clone_zero_one_form`: linearity gives the entangled output;
* `sum_clone_ne`: `|00> + |11>` is not a product state.

Cloning the *basis* states is of course possible; the obstruction is exactly the
linearity of a quantum operation.  The proof is over `ℂ` with the explicit
vectors `e0 = |0>`, `e1 = |1>`, so no analysis enters.  The unitary completion of
`U` and the density-matrix (mixed-state) formulation are out of scope.
-/

namespace LeanPhy.QuantumInfo

open scoped BigOperators Matrix

/-- The ket `|0>` on a qubit. -/
def e0 : Fin 2 → ℂ := ![1, 0]

/-- The ket `|1>` on a qubit. -/
def e1 : Fin 2 → ℂ := ![0, 1]

/-- The tensor product of two qubit vectors `x (x) y`, indexed by `Fin 2 × Fin 2`. -/
def tv (x y : Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ := fun p => x p.1 * y p.2

theorem tv_add_left (x y b : Fin 2 → ℂ) : tv (x + y) b = tv x b + tv y b := by
  funext p; simp [tv, Pi.add_apply]; ring

theorem tv_add_right (x b c : Fin 2 → ℂ) : tv x (b + c) = tv x b + tv x c := by
  funext p; simp [tv, Pi.add_apply]; ring

/-- **Linearity forces an entangled output.** If a linear `U` copies `|0>` and
`|1>`, then it must send the superposition `|0> + |1>` to `|00> + |11>`. -/
theorem clone_zero_one_form (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (b : Fin 2 → ℂ)
    (h0 : U *ᵥ tv e0 b = tv e0 e0) (h1 : U *ᵥ tv e1 b = tv e1 e1) :
    U *ᵥ tv (e0 + e1) b = tv e0 e0 + tv e1 e1 := by
  rw [tv_add_left, Matrix.mulVec_add, h0, h1]

/-- **That output is not a product state.** `|00> + |11>` cannot be written as
`(|0> + |1>) (x) P` for any `P`, so no linear `U` clones every state. -/
theorem sum_clone_ne (P : Fin 2 → ℂ) :
    tv e0 e0 + tv e1 e1 ≠ tv (e0 + e1) P := by
  intro h
  have h00 := congrFun h (0, 0)
  have h10 := congrFun h (1, 0)
  simp [tv, e0, e1, Pi.add_apply] at h00 h10
  have : (1 : ℂ) = 0 := h00.trans h10.symm
  norm_num at this

/-- **No-cloning theorem.** A linear `U` that copies both basis states cannot
copy their superposition. -/
theorem no_cloning (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (b : Fin 2 → ℂ)
    (h0 : U *ᵥ tv e0 b = tv e0 e0) (h1 : U *ᵥ tv e1 b = tv e1 e1) :
    U *ᵥ tv (e0 + e1) b ≠ tv (e0 + e1) (e0 + e1) := by
  rw [clone_zero_one_form U b h0 h1]
  exact sum_clone_ne (e0 + e1)

end LeanPhy.QuantumInfo
