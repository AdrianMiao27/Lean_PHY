import LeanPhy.Quantum.Pauli
import Mathlib.Tactic

/-!
# The single-qubit Pauli group: trace orthogonality, the twirl, and depolarisation

Quantum error correction and the theory of decoherence are written in the Pauli group of
the qubit.  Two algebraic facts everything rests on are:

* the four Pauli matrices obey `sigma_a^2 = 1` and are trace-orthogonal,
  `tr (sigma_a sigma_b) = 2 delta_ab`;
* the **Pauli twirl** `sum_a sigma_a M sigma_a = 2 tr (M) 1` for any `2 x 2`
  matrix `M`, whose normalised form
  `(1/4) sum_a sigma_a M sigma_a = (tr M / 2) 1` is the completely depolarising
  channel.  This identity turns any single-qubit noise into a Pauli channel and
  Bell-diagonalises a two-qubit state.

Everything is checked entrywise on the explicit matrices; the twirl constant `2`
is a kernel-evaluated trace, not a convention.
-/

namespace LeanPhy.Quantum

open scoped BigOperators Matrix

/-- `i^2 = -1`, in the normal form consumed by `ring_nf`. -/
@[simp] theorem I_sq : Complex.I ^ 2 = -1 := by rw [pow_two, Complex.I_mul_I]

/-- The four Pauli matrices as one family indexed by `Fin 4`:
`1, sigma_x, sigma_y, sigma_z`. -/
noncomputable def pauli : Fin 4 → Operator 2
  | 0 => 1 | 1 => pauliX | 2 => pauliY | 3 => pauliZ

@[simp] theorem pauli_zero : pauli 0 = 1 := rfl
@[simp] theorem pauli_one : pauli 1 = pauliX := rfl
@[simp] theorem pauli_two : pauli 2 = pauliY := rfl
@[simp] theorem pauli_three : pauli 3 = pauliZ := rfl

/-- Each Pauli matrix squares to the identity. -/
theorem pauli_sq (a : Fin 4) : pauli a * pauli a = 1 := by
  fin_cases a <;> simp [pauli, pauliX_sq, pauliY_sq, pauliZ_sq, identity]

/-- **Trace orthogonality of the Pauli matrices**, `tr (sigma_a sigma_b) = 2 delta_ab`. -/
theorem pauli_trace_orthonormal (a b : Fin 4) :
    (pauli a * pauli b).trace = 2 * (if a = b then 1 else 0) := by
  fin_cases a <;> fin_cases b <;>
    norm_num [pauli, Matrix.trace, Matrix.diag, Matrix.mul_apply, pauliX, pauliY, pauliZ,
      Matrix.one_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- **The Pauli twirl**: `sum_a sigma_a M sigma_a = 2 tr (M) 1` for any `2 x 2`
matrix `M`.  Averaging the adjoint action of the Pauli group leaves only the trace:
the twirl forgets everything about `M` except `tr M`. -/
theorem pauli_twirl (M : Operator 2) :
    (∑ a : Fin 4, pauli a * M * pauli a) = (2 * M.trace) • (1 : Operator 2) := by
  rw [Fin.sum_univ_four]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauli, Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply,
      Matrix.smul_apply, Matrix.trace, Matrix.diag, pauliX, pauliY, pauliZ,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Fin.sum_univ_two] <;>
    norm_num <;> ring_nf <;> simp only [I_sq] <;> ring

/-- **Trace preservation of the twirl**: the normalised twirl
`(1/4) sum_a sigma_a M sigma_a` has the same trace as `M`, so it is a valid
channel (the completely depolarising channel in Pauli form). -/
theorem pauli_twirl_trace (M : Operator 2) :
    (1 / 4 : Complex) * (∑ a : Fin 4, (pauli a * M * pauli a).trace) = M.trace := by
  rw [← Matrix.trace_sum]
  rw [pauli_twirl]
  simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_two,
    reduceIte]
  ring

/-- **Depolarisation**: the normalised twirl of any operator is the maximally mixed qubit
times its trace.  This is the algebraic content of the statement that the twirl destroys
every single-qubit coherence. -/
theorem pauli_twirl_depolarise (M : Operator 2) :
    (1 / 4 : Complex) • (∑ a : Fin 4, pauli a * M * pauli a)
      = (M.trace / 2) • (1 : Operator 2) := by
  rw [pauli_twirl, smul_smul]
  congr 1
  ring

end LeanPhy.Quantum
