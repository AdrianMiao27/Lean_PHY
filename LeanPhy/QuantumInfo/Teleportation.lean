import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# Quantum teleportation: the three-qubit algebraic identity

Teleportation is a useful test of a physics-facing formalisation because it
combines a general input state, a pre-shared Bell pair, Bell-basis expansion and
conditional Pauli corrections in one short derivation.

For an arbitrary qubit `|psi> = a |0> + b |1>` and the unnormalised Bell pair
`|Phi+> = |00> + |11>`, the kernel checks the standard identity

    |psi> (x) |Phi+>
      = 1/2 [ |Phi+> (x) |psi>
             + |Phi-> (x) Z|psi>
             + |Psi+> (x) X|psi>
             + |Psi-> (x) XZ|psi> ].

The first two qubits are Alice's Bell-measurement register and the last is
Bob's output.  After the classical two-bit outcome, Bob applies the matching
correction: `Z` on `Z|psi>`, `X` on `X|psi>`, and `ZX` on `XZ|psi>`; each is
proved to return exactly `|psi>` (no untracked global phase in the chosen
convention).  The statement is pure finite-dimensional linear algebra over
`C`: normalisation factors, measurement probabilities and the physical
classical communication channel are deliberately left explicit/out of scope.
-/

namespace LeanPhy.QuantumInfo

open scoped BigOperators Matrix

/-- The three-qubit index, with the first two qubits measured and the third sent. -/
abbrev TeleIdx := (Fin 2 × Fin 2) × Fin 2

/-- An arbitrary input qubit `a |0> + b |1>`. -/
noncomputable def telePsi (a b : Complex) : Fin 2 → Complex := ![a, b]

/-- The four unnormalised Bell vectors on the first two qubits. -/
noncomputable def bellPhiPlus : Fin 2 × Fin 2 → Complex := fun p =>
  if p = (0, 0) then 1 else if p = (1, 1) then 1 else 0
noncomputable def bellPhiMinus : Fin 2 × Fin 2 → Complex := fun p =>
  if p = (0, 0) then 1 else if p = (1, 1) then -1 else 0
noncomputable def bellPsiPlus : Fin 2 × Fin 2 → Complex := fun p =>
  if p = (0, 1) then 1 else if p = (1, 0) then 1 else 0
noncomputable def bellPsiMinus : Fin 2 × Fin 2 → Complex := fun p =>
  if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0

/-- Tensor a Bell vector on the first two slots with Bob's qubit. -/
noncomputable def bellTensor (bell : Fin 2 × Fin 2 → Complex)
    (v : Fin 2 → Complex) : TeleIdx → Complex := fun p => bell p.1 * v p.2

/-- The input state together with the shared `Phi+` pair. -/
noncomputable def teleportInput (a b : Complex) : TeleIdx → Complex := fun p =>
  telePsi a b p.1.1 * (if p.1.2 = p.2 then 1 else 0)

/-- The four Pauli-corrected output states. -/
noncomputable def teleZ (a b : Complex) : Fin 2 → Complex := ![a, -b]
noncomputable def teleX (a b : Complex) : Fin 2 → Complex := ![b, a]
noncomputable def teleXZ (a b : Complex) : Fin 2 → Complex := ![-b, a]
/-- The `ZX` correction used on the `XZ|psi>` branch. -/
noncomputable def teleZX (a b : Complex) : Fin 2 → Complex := ![b, -a]

/-- **Teleportation identity.** The Bell-basis expansion of an arbitrary input
qubit and an unnormalised `Phi+` resource pair. -/
theorem teleportation_identity (a b : Complex) :
    teleportInput a b = (1 / 2 : Complex) •
      (bellTensor bellPhiPlus (telePsi a b)
        + bellTensor bellPhiMinus (teleZ a b)
        + bellTensor bellPsiPlus (teleX a b)
        + bellTensor bellPsiMinus (teleXZ a b)) := by
  funext p
  fin_cases p <;>
    simp [teleportInput, bellTensor, telePsi, bellPhiPlus, bellPhiMinus,
      bellPsiPlus, bellPsiMinus, teleZ, teleX, teleXZ] <;> ring

/-- The `Z` correction recovers the input on the `Phi-` branch. -/
theorem teleport_correction_Z (a b : Complex) :
    teleZ (teleZ a b 0) (teleZ a b 1) = telePsi a b := by
  funext i; fin_cases i <;> simp [teleZ, telePsi]

/-- The `X` correction recovers the input on the `Psi+` branch. -/
theorem teleport_correction_X (a b : Complex) :
    teleX (teleX a b 0) (teleX a b 1) = telePsi a b := by
  funext i; fin_cases i <;> simp [teleX, telePsi]

/-- The `ZX` correction recovers the input on the `Psi-` branch. -/
theorem teleport_correction_ZX (a b : Complex) :
    teleZX (teleXZ a b 0) (teleXZ a b 1) = telePsi a b := by
  funext i; fin_cases i <;> simp [teleZX, teleXZ, telePsi]

end LeanPhy.QuantumInfo
