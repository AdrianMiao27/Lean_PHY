import LeanPhy.Quantum.Basic
import LeanPhy.HighEnergy.Gamma5
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-!
# The Lorentz algebra on Dirac spinors

The generators S^{mu nu} = (i/4) [gamma^mu, gamma^nu] realise the Lorentz Lie
algebra on the four-dimensional spinor representation.  Writing
J_i = S^{jk} for the rotations and K_i = S^{0i} for the boosts, the standard
commutation relations are proved on the explicit matrices:

* [J_1, J_2] = i J_3 and cyclic,
* [K_1, K_2] = -i J_3 and cyclic,
* [J_1, K_2] = i K_3 and cyclic.

The explicit matrices are shown to coincide with (i/4) [gamma^mu, gamma^nu]
in the linkage lemmas at the end, so the algebra is really the spinor
representation of so(1,3) and not an unrelated matrix set.
-/

namespace LeanPhy.HighEnergy

open LeanPhy.Quantum

local notation "𝕚" => Complex.I
local notation "M4" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### Explicit generators in the chiral basis -/

noncomputable def J1 : M4 := !![0, 1/2, 0, 0; 1/2, 0, 0, 0; 0, 0, 0, 1/2; 0, 0, 1/2, 0]
noncomputable def J2 : M4 := !![0, -1/2*𝕚, 0, 0; 1/2*𝕚, 0, 0, 0; 0, 0, 0, -1/2*𝕚; 0, 0, 1/2*𝕚, 0]
noncomputable def J3 : M4 := !![1/2, 0, 0, 0; 0, -1/2, 0, 0; 0, 0, 1/2, 0; 0, 0, 0, -1/2]
noncomputable def K1 : M4 := !![0, -1/2*𝕚, 0, 0; -1/2*𝕚, 0, 0, 0; 0, 0, 0, 1/2*𝕚; 0, 0, 1/2*𝕚, 0]
noncomputable def K2 : M4 := !![0, -1/2, 0, 0; 1/2, 0, 0, 0; 0, 0, 0, 1/2; 0, 0, -1/2, 0]
noncomputable def K3 : M4 := !![-1/2*𝕚, 0, 0, 0; 0, 1/2*𝕚, 0, 0; 0, 0, 1/2*𝕚, 0; 0, 0, 0, -1/2*𝕚]

/-! ### Rotations: [J_i, J_j] = i eps_ijk J_k -/

theorem J1_commutator_J2 : J1 * J2 - J2 * J1 = 𝕚 • J3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J1, J2, J3, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    (try (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)))

theorem J2_commutator_J3 : J2 * J3 - J3 * J2 = 𝕚 • J1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J1, J2, J3, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    (try (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)))

theorem J3_commutator_J1 : J3 * J1 - J1 * J3 = 𝕚 • J2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J1, J2, J3, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    (try (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)))

/-! ### Boosts: [K_i, K_j] = -i eps_ijk J_k -/

theorem K1_commutator_K2 : K1 * K2 - K2 * K1 = -(𝕚 • J3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K1, K2, J3, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    (try (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)))

theorem K2_commutator_K3 : K2 * K3 - K3 * K2 = -(𝕚 • J1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K1, K2, K3, J1, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    (try (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)))

theorem K3_commutator_K1 : K3 * K1 - K1 * K3 = -(𝕚 • J2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K1, K3, J2, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    (try (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)))

/-! ### Mixed: [J_i, K_j] = i eps_ijk K_k -/

theorem J1_commutator_K2 : J1 * K2 - K2 * J1 = 𝕚 • K3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J1, K2, K3, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    (try (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)))

theorem J2_commutator_K3 : J2 * K3 - K3 * J2 = 𝕚 • K1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J2, K3, K1, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    (try (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)))

theorem J3_commutator_K1 : J3 * K1 - K1 * J3 = 𝕚 • K2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J3, K1, K2, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    (try (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)))

/-! ### Linkage to the gamma matrices

These show that the explicit generators really are (i/4) [gamma^mu, gamma^nu].
-/

/-- The Lorentz generator S^{mu nu} = (i/4) [gamma^mu, gamma^nu]. -/
noncomputable def lorentzGen (mu nu : Fin 4) : M4 :=
  (𝕚 / 4) • (gammaFin mu * gammaFin nu - gammaFin nu * gammaFin mu)

theorem lorentzGen_J1 : lorentzGen 2 3 = J1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzGen, J1, gammaFin, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply,
      Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    (try (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)))

theorem lorentzGen_J2 : lorentzGen 3 1 = J2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzGen, J2, gammaFin, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply,
      Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    (try (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)))

theorem lorentzGen_J3 : lorentzGen 1 2 = J3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzGen, J3, gammaFin, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply,
      Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    (try (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)))

theorem lorentzGen_K1 : lorentzGen 0 1 = K1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzGen, K1, gammaFin, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply,
      Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    (try (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)))

theorem lorentzGen_K2 : lorentzGen 0 2 = K2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzGen, K2, gammaFin, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply,
      Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    (try (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)))

theorem lorentzGen_K3 : lorentzGen 0 3 = K3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzGen, K3, gammaFin, gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply,
      Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    (try (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)))

end LeanPhy.HighEnergy
