import LeanPhy.Quantum.Pauli
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Spin-1/2 angular momentum

The dimensionless angular-momentum operators J_i = sigma_i / 2 satisfy the
su(2) commutation relations [Jx, Jy] = i Jz and its cyclic partners, together
with the Casimir identity Jx^2 + Jy^2 + Jz^2 = (3/4) I.  Both are proved on the
explicit two-dimensional representation, so the spin-1/2 algebra used in
high-energy and condensed-matter spin models is kernel-checked rather than
assumed.
-/

namespace LeanPhy.Quantum

local notation "𝕚" => Complex.I

noncomputable def Jx : Operator 2 := ((2 : ℂ)⁻¹) • pauliX
noncomputable def Jy : Operator 2 := ((2 : ℂ)⁻¹) • pauliY
noncomputable def Jz : Operator 2 := ((2 : ℂ)⁻¹) • pauliZ

theorem Jx_commutator_Jy : commutator Jx Jy = 𝕚 • Jz := by
  rw [commutator, Jx, Jy, Jz, smul_mul_smul, smul_mul_smul,
    pauliX_pauliY, pauliY_pauliX]
  simp only [smul_smul]
  module

theorem Jy_commutator_Jz : commutator Jy Jz = 𝕚 • Jx := by
  rw [commutator, Jx, Jy, Jz, smul_mul_smul, smul_mul_smul,
    pauliY_pauliZ, pauliZ_pauliY]
  simp only [smul_smul]
  module

theorem Jz_commutator_Jx : commutator Jz Jx = 𝕚 • Jy := by
  rw [commutator, Jx, Jy, Jz, smul_mul_smul, smul_mul_smul,
    pauliZ_pauliX, pauliX_pauliZ]
  simp only [smul_smul]
  module

/-- The quadratic Casimir of the spin-1/2 representation. -/
noncomputable def casimir : Operator 2 := Jx * Jx + Jy * Jy + Jz * Jz

/-- The Casimir equals (3/4) I for spin 1/2, the value j(j+1) at j = 1/2. -/
theorem casimir_eq : casimir = ((3 / 4 : ℂ)) • identity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [casimir, Jx, Jy, Jz, pauliX, pauliY, pauliZ, identity,
      Matrix.add_apply, Matrix.smul_apply]
  all_goals
    ring_nf
    simp only [Complex.I_sq]
    ring

/-- The Casimir commutes with every generator, as it must in any
representation of a Lie algebra. -/
theorem casimir_commutes_Jx : commutator casimir Jx = 0 := by
  rw [casimir_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutator, Jx, pauliX, identity, Matrix.sub_apply]

end LeanPhy.Quantum
