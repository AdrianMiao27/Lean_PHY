import LeanPhy.Mathematics.LieRepresentation
import LeanPhy.Quantum.SpinOne
import LeanPhy.Surface.IndexCalculus
import LeanPhy.Relativity.LorentzAlgebra
import LeanPhy.Particles.ColorAlgebra
import Mathlib.Tactic

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# Concrete Lie-representation adapters

This module turns one concrete family already used by physics calculations into
the reusable `LieAlgebra`/`Representation` interface.  The carrier is the
three-component coefficient space of `su(2)` and the representation is the
explicit spin-one matrix family.  Thus a theorem proved once for an abstract
representation (Jacobi, central elements, adjoint actions) can be applied to
spin, and the same adapter shape can later be instantiated by Lorentz, colour,
gauge and lattice generator tables.

Only finite algebra is asserted here.  No Lie-group exponentiation or physical
interpretation of the generators is built into the adapter.
-/

namespace LeanPhy.Mathematics

open LeanPhy.IndexCalculus
open LeanPhy.Quantum
open scoped BigOperators Matrix

abbrev SU2Coefficients := Fin 3 → ℂ
abbrev SU2Matrices := Matrix (Fin 3) (Fin 3) ℂ

/-! ## A common table-level adapter -/

/-- A finite family of matrix generators.  The family itself is deliberately
only data; all Lie identities are inherited from the associative matrix
commutator, so a domain need not duplicate Jacobi proofs for every generator
table. -/
abbrev MatrixGeneratorFamily (ι n : Nat) :=
  Fin ι → Matrix (Fin n) (Fin n) ℂ

theorem matrixGeneratorFamily_jacobi {ι n : Nat}
    (G : MatrixGeneratorFamily ι n) (a b c : Fin ι) :
    ringCommutator (G a) (ringCommutator (G b) (G c)) +
        ringCommutator (G b) (ringCommutator (G c) (G a)) +
        ringCommutator (G c) (ringCommutator (G a) (G b)) = 0 := by
  exact ringCommutator_jacobi (G a) (G b) (G c)

/-- The six explicit Lorentz generators as one table, ready for generic
commutator/Jacobi automation. -/
noncomputable def lorentzGeneratorFamily : MatrixGeneratorFamily 6 4 :=
  ![LeanPhy.Relativity.R1, LeanPhy.Relativity.R2, LeanPhy.Relativity.R3,
    LeanPhy.Relativity.B1, LeanPhy.Relativity.B2, LeanPhy.Relativity.B3]

/-- The eight Gell-Mann matrices as one colour-generator table. -/
noncomputable def colourGeneratorFamily : MatrixGeneratorFamily 8 3 :=
  LeanPhy.Particles.gm

/-- The coefficient-space `su(2)` bracket, with the convention
`[S_i,S_j] = i ε_ijk S_k`. -/
def su2Bracket (x y : SU2Coefficients) : SU2Coefficients := fun i =>
  Complex.I * ∑ j : Fin 3, ∑ k : Fin 3,
    (epsilon i j k : ℂ) * x j * y k

theorem su2Bracket_add_left (x y z : SU2Coefficients) :
    su2Bracket (x + y) z = su2Bracket x z + su2Bracket y z := by
  funext i
  simp [su2Bracket, Pi.add_apply, Finset.sum_add_distrib, mul_add, add_mul]

theorem su2Bracket_add_right (x y z : SU2Coefficients) :
    su2Bracket x (y + z) = su2Bracket x y + su2Bracket x z := by
  funext i
  simp [su2Bracket, Pi.add_apply, Finset.sum_add_distrib, mul_add]

theorem su2Bracket_smul_left (r : ℂ) (x y : SU2Coefficients) :
    su2Bracket (r • x) y = r • su2Bracket x y := by
  funext i
  simp [su2Bracket, Pi.smul_apply, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem su2Bracket_smul_right (r : ℂ) (x y : SU2Coefficients) :
    su2Bracket x (r • y) = r • su2Bracket x y := by
  funext i
  simp [su2Bracket, Pi.smul_apply, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem su2Bracket_zero_left (x : SU2Coefficients) :
    su2Bracket 0 x = 0 := by
  funext i
  simp [su2Bracket]

theorem su2Bracket_alternating (x : SU2Coefficients) :
    su2Bracket x x = 0 := by
  funext i
  fin_cases i <;>
    simp [su2Bracket, epsilon, Fin.sum_univ_three, Complex.I_mul_I] <;> ring

theorem su2Bracket_antisymm (x y : SU2Coefficients) :
    su2Bracket x y = -su2Bracket y x := by
  funext i
  fin_cases i <;>
    simp [su2Bracket, epsilon, Fin.sum_univ_three, Complex.I_mul_I] <;> ring

theorem su2Bracket_jacobi (x y z : SU2Coefficients) :
    su2Bracket x (su2Bracket y z) +
        su2Bracket y (su2Bracket z x) +
        su2Bracket z (su2Bracket x y) = 0 := by
  funext i
  fin_cases i <;>
    simp [su2Bracket, epsilon, Fin.sum_univ_three, Complex.I_mul_I] <;> ring

/-- The abstract coefficient-space Lie algebra used by the spin-one adapter. -/
def su2LieAlgebra : LieAlgebra ℂ SU2Coefficients where
  bracket := su2Bracket
  add_left := su2Bracket_add_left
  add_right := su2Bracket_add_right
  smul_left := su2Bracket_smul_left
  smul_right := su2Bracket_smul_right
  zero_left := su2Bracket_zero_left
  alternating := su2Bracket_alternating
  antisymm := su2Bracket_antisymm
  jacobi := su2Bracket_jacobi

/-- Send coefficient triples to the explicit spin-one matrices. -/
noncomputable def spinOneGeneratorMap : SU2Coefficients → SU2Matrices := fun x =>
  x 0 • S1 + x 1 • S2 + x 2 • S3

theorem spinOneGeneratorMap_zero : spinOneGeneratorMap 0 = 0 := by
  simp [spinOneGeneratorMap]

theorem spinOneGeneratorMap_add (x y : SU2Coefficients) :
    spinOneGeneratorMap (x + y) = spinOneGeneratorMap x + spinOneGeneratorMap y := by
  simp [spinOneGeneratorMap, add_smul, add_assoc, add_left_comm, add_comm]

theorem spinOneGeneratorMap_smul (r : ℂ) (x : SU2Coefficients) :
    spinOneGeneratorMap (r • x) = r • spinOneGeneratorMap x := by
  simp [spinOneGeneratorMap, smul_add, smul_smul]

theorem spinOneGeneratorMap_bracket (x y : SU2Coefficients) :
    ringCommutator (spinOneGeneratorMap x) (spinOneGeneratorMap y) =
      spinOneGeneratorMap (su2Bracket x y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ringCommutator, spinOneGeneratorMap, su2Bracket, S1, S2, S3,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, epsilon, Complex.I_mul_I] <;> ring

/-- The explicit spin-one matrices as a reusable `Representation`. -/
noncomputable def spinOneRepresentation : Representation su2LieAlgebra SU2Matrices where
  toFun := spinOneGeneratorMap
  map_zero' := spinOneGeneratorMap_zero
  map_add' := spinOneGeneratorMap_add
  map_smul' := spinOneGeneratorMap_smul
  bracket_compat' := spinOneGeneratorMap_bracket

theorem spinOneRepresentation_preserves_jacobi (x y z : SU2Coefficients) :
    ringCommutator (spinOneRepresentation x)
        (ringCommutator (spinOneRepresentation y) (spinOneRepresentation z)) +
      ringCommutator (spinOneRepresentation y)
        (ringCommutator (spinOneRepresentation z) (spinOneRepresentation x)) +
      ringCommutator (spinOneRepresentation z)
        (ringCommutator (spinOneRepresentation x) (spinOneRepresentation y)) = 0 :=
  Representation.preserves_jacobi spinOneRepresentation x y z

/-! ## Lorentz `so(3,1)` adapter -/

abbrev LorentzCoefficients := SU2Coefficients × SU2Coefficients
abbrev LorentzMatrices := LeanPhy.Relativity.M4L

/-- The complexified three-vector cross product used in the Lorentz structure
constants. -/
def complexCross (x y : SU2Coefficients) : SU2Coefficients := fun i =>
  ∑ j : Fin 3, ∑ k : Fin 3,
    (epsilon i j k : ℂ) * x j * y k

/-- Coefficient-space `so(3,1)` bracket.  For `(r,b)` and `(s,d)` it is
`(r×s - b×d, r×d + b×s)`, matching `[R,R]=R`, `[R,B]=B` and
`[B,B]=-R` for the explicit matrices. -/
def lorentzBracket (x y : LorentzCoefficients) : LorentzCoefficients :=
  (complexCross x.1 y.1 - complexCross x.2 y.2,
    complexCross x.1 y.2 + complexCross x.2 y.1)

theorem lorentzBracket_add_left (x y z : LorentzCoefficients) :
    lorentzBracket (x + y) z = lorentzBracket x z + lorentzBracket y z := by
  rcases x with ⟨xr, xb⟩
  rcases y with ⟨yr, yb⟩
  rcases z with ⟨zr, zb⟩
  apply Prod.ext <;> funext i <;>
    simp [lorentzBracket, complexCross, Pi.add_apply, Finset.sum_add_distrib,
      mul_add, add_mul] <;> ring

theorem lorentzBracket_add_right (x y z : LorentzCoefficients) :
    lorentzBracket x (y + z) = lorentzBracket x y + lorentzBracket x z := by
  rcases x with ⟨xr, xb⟩
  rcases y with ⟨yr, yb⟩
  rcases z with ⟨zr, zb⟩
  apply Prod.ext <;> funext i <;>
    simp [lorentzBracket, complexCross, Pi.add_apply, Finset.sum_add_distrib,
      mul_add, add_mul] <;> ring

theorem lorentzBracket_smul_left (r : ℂ) (x y : LorentzCoefficients) :
    lorentzBracket (r • x) y = r • lorentzBracket x y := by
  rcases x with ⟨xr, xb⟩
  rcases y with ⟨yr, yb⟩
  apply Prod.ext <;> funext i <;>
    simp [lorentzBracket, complexCross, Pi.smul_apply, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm] <;>
    simp only [← Finset.mul_sum] <;> ring

theorem lorentzBracket_smul_right (r : ℂ) (x y : LorentzCoefficients) :
    lorentzBracket x (r • y) = r • lorentzBracket x y := by
  rcases x with ⟨xr, xb⟩
  rcases y with ⟨yr, yb⟩
  apply Prod.ext <;> funext i <;>
    simp [lorentzBracket, complexCross, Pi.smul_apply, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm] <;>
    simp only [← Finset.mul_sum] <;> ring

theorem lorentzBracket_zero_left (x : LorentzCoefficients) :
    lorentzBracket 0 x = 0 := by
  rcases x with ⟨xr, xb⟩
  apply Prod.ext <;> funext i <;> simp [lorentzBracket, complexCross]

theorem lorentzBracket_alternating (x : LorentzCoefficients) :
    lorentzBracket x x = 0 := by
  rcases x with ⟨xr, xb⟩
  apply Prod.ext <;> funext i <;>
    fin_cases i <;>
      simp [lorentzBracket, complexCross, epsilon, Fin.sum_univ_three] <;> ring

theorem lorentzBracket_antisymm (x y : LorentzCoefficients) :
    lorentzBracket x y = -lorentzBracket y x := by
  rcases x with ⟨xr, xb⟩
  rcases y with ⟨yr, yb⟩
  apply Prod.ext <;> funext i <;>
    fin_cases i <;>
      simp [lorentzBracket, complexCross, epsilon, Fin.sum_univ_three] <;> ring

theorem lorentzBracket_jacobi (x y z : LorentzCoefficients) :
    lorentzBracket x (lorentzBracket y z) +
        lorentzBracket y (lorentzBracket z x) +
        lorentzBracket z (lorentzBracket x y) = 0 := by
  rcases x with ⟨xr, xb⟩
  rcases y with ⟨yr, yb⟩
  rcases z with ⟨zr, zb⟩
  apply Prod.ext <;> funext i <;>
    fin_cases i <;>
      simp [lorentzBracket, complexCross, epsilon, Fin.sum_univ_three] <;> ring

def lorentzLieAlgebra : LieAlgebra ℂ LorentzCoefficients where
  bracket := lorentzBracket
  add_left := lorentzBracket_add_left
  add_right := lorentzBracket_add_right
  smul_left := lorentzBracket_smul_left
  smul_right := lorentzBracket_smul_right
  zero_left := lorentzBracket_zero_left
  alternating := lorentzBracket_alternating
  antisymm := lorentzBracket_antisymm
  jacobi := lorentzBracket_jacobi

/-- Send Lorentz coefficient pairs to the explicit vector and boost matrices. -/
noncomputable def lorentzGeneratorMap : LorentzCoefficients → LorentzMatrices := fun x =>
  x.1 0 • LeanPhy.Relativity.R1 + x.1 1 • LeanPhy.Relativity.R2 +
    x.1 2 • LeanPhy.Relativity.R3 + x.2 0 • LeanPhy.Relativity.B1 +
    x.2 1 • LeanPhy.Relativity.B2 + x.2 2 • LeanPhy.Relativity.B3

theorem lorentzGeneratorMap_zero : lorentzGeneratorMap 0 = 0 := by
  simp [lorentzGeneratorMap]

theorem lorentzGeneratorMap_add (x y : LorentzCoefficients) :
    lorentzGeneratorMap (x + y) = lorentzGeneratorMap x + lorentzGeneratorMap y := by
  rcases x with ⟨xr, xb⟩
  rcases y with ⟨yr, yb⟩
  simp [lorentzGeneratorMap, Pi.add_apply, add_smul, add_assoc, add_left_comm, add_comm]

theorem lorentzGeneratorMap_smul (r : ℂ) (x : LorentzCoefficients) :
    lorentzGeneratorMap (r • x) = r • lorentzGeneratorMap x := by
  rcases x with ⟨xr, xb⟩
  simp [lorentzGeneratorMap, Pi.smul_apply, smul_add, smul_smul]

theorem lorentzGeneratorMap_bracket (x y : LorentzCoefficients) :
    ringCommutator (lorentzGeneratorMap x) (lorentzGeneratorMap y) =
      lorentzGeneratorMap (lorentzBracket x y) := by
  rcases x with ⟨xr, xb⟩
  rcases y with ⟨yr, yb⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ringCommutator, lorentzGeneratorMap, lorentzBracket, complexCross,
      LeanPhy.Relativity.R1, LeanPhy.Relativity.R2, LeanPhy.Relativity.R3,
      LeanPhy.Relativity.B1, LeanPhy.Relativity.B2, LeanPhy.Relativity.B3,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_four, epsilon] <;> ring

noncomputable def lorentzRepresentation : Representation lorentzLieAlgebra LorentzMatrices where
  toFun := lorentzGeneratorMap
  map_zero' := lorentzGeneratorMap_zero
  map_add' := lorentzGeneratorMap_add
  map_smul' := lorentzGeneratorMap_smul
  bracket_compat' := lorentzGeneratorMap_bracket

theorem lorentzRepresentation_preserves_jacobi (x y z : LorentzCoefficients) :
    ringCommutator (lorentzRepresentation x)
        (ringCommutator (lorentzRepresentation y) (lorentzRepresentation z)) +
      ringCommutator (lorentzRepresentation y)
        (ringCommutator (lorentzRepresentation z) (lorentzRepresentation x)) +
      ringCommutator (lorentzRepresentation z)
        (ringCommutator (lorentzRepresentation x) (lorentzRepresentation y)) = 0 :=
  Representation.preserves_jacobi lorentzRepresentation x y z

end LeanPhy.Mathematics
