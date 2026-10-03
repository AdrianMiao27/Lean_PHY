import LeanPhy.Quantum.Pauli
import LeanPhy.Quantum.Unitary
import Mathlib.Tactic

/-!
# CKM quark mixing: unitarity of the three-generation mixing matrix

In the Standard Model the charged-current couplings of quarks are rotated by the
Cabibbo-Kobayashi-Maskawa matrix `V`, and the whole observed pattern of quark
flavour change and `CP` violation is read off from it.  Everything the theory
predicts rests on one structural fact: `V` is **unitary**, `V Vᴴ = 1`.

This module reconstructs `V` the way it is built in practice, as a product of two
real rotations in the (1,2) and (2,3) planes and one phase-carrying (1,3) rotation,
`V = R_23 (gamma) P (delta) R_12 (theta)`, and proves each factor unitary, hence the
product.  Unitarity is the source of the **unitarity-triangle** relations
`sum_i V_ij V_ik^* = delta_jk`, in particular the three complex numbers
`V_ud V_ub^* + V_cd V_cb^* + V_td V_tb^* = 0` whose closure is the standard
CP-violation triangle.  The phase is carried as an abstract unit-modulus complex
number `u` (`u^* u = 1`) rather than `exp (i delta)`, so no analysis enters: the
algebra is exact and kernel-checked, and the input is the mixing angles and the
phase as hypotheses.  The fermion content and the angles are hypotheses, so this is
conditional correctness.
-/

namespace LeanPhy.Particles

open scoped BigOperators Matrix

/-- The `3 x 3` complex matrices of the flavour sector. -/
abbrev M3 := Matrix (Fin 3) (Fin 3) Complex

/-- Lift `c^2 + s^2 = 1` to `Complex` in power form. -/
theorem c_sq_add (c s : Real) (hc : c^2 + s^2 = 1) :
    (↑c : Complex) ^ 2 + (↑s : Complex) ^ 2 = 1 := by
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, hc, Complex.ofReal_one]

/-- The same with the two terms exchanged. -/
theorem s_sq_add (c s : Real) (hc : c^2 + s^2 = 1) :
    (↑s : Complex) ^ 2 + (↑c : Complex) ^ 2 = 1 := by
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
    show s^2 + c^2 = (1:Real) from by nlinarith [hc], Complex.ofReal_one]

/-- In product form, for the entrywise closers. -/
theorem c_mul_add (c s : Real) (hc : c^2 + s^2 = 1) :
    (↑c : Complex) * ↑c + ↑s * ↑s = 1 := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
  rw [show c*c + s*s = (1:Real) from by nlinarith [hc], Complex.ofReal_one]

theorem s_mul_add (c s : Real) (hc : c^2 + s^2 = 1) :
    (↑s : Complex) * ↑s + ↑c * ↑c = 1 := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
  rw [show s*s + c*c = (1:Real) from by nlinarith [hc], Complex.ofReal_one]

/-- A real rotation in the (1,2) plane (the Cabibbo rotation). -/
noncomputable def rot12 (c s : Real) : M3 :=
  !![(c:Complex), (s:Complex), 0; -(s:Complex), (c:Complex), 0; 0, 0, 1]

/-- A real rotation in the (2,3) plane. -/
noncomputable def rot23 (c s : Real) : M3 :=
  !![1, 0, 0; 0, (c:Complex), (s:Complex); 0, -(s:Complex), (c:Complex)]

/-- The phase-carrying (1,3) rotation; `u` is a unit-modulus complex number. -/
noncomputable def phaseRot13 (c s : Real) (u : Complex) : M3 :=
  !![(c:Complex), 0, (s:Complex) * (starRingEnd Complex) u; 0, 1, 0;
     -((s:Complex) * u), 0, (c:Complex)]

/-- The CKM matrix in the standard product parametrisation. -/
noncomputable def ckm (t12 t13 t23 : Real) (u : Complex) : M3 :=
  rot23 (Real.cos t23) (Real.sin t23) * phaseRot13 (Real.cos t13) (Real.sin t13) u
    * rot12 (Real.cos t12) (Real.sin t12)

/-- The diagonal entries of the phase rotation, reduced by `u^* u = 1`. -/
theorem phase_diag1 (c s : Real) (u : Complex) (hc : c^2 + s^2 = 1)
    (hu : (starRingEnd Complex) u * u = 1) :
    (↑c : Complex) * ↑c + ↑s * (starRingEnd Complex) u * (↑s * u) = 1 := by
  have hs : (↑s : Complex) * (starRingEnd Complex) u * (↑s * u) = ↑s ^ 2 := by
    rw [show (↑s : Complex) * (starRingEnd Complex) u * (↑s * u)
          = ↑s ^ 2 * ((starRingEnd Complex) u * u) from by ring, hu, mul_one]
  rw [hs, show (↑c : Complex) * ↑c = ↑c ^ 2 from by ring, c_sq_add c s hc]

theorem phase_diag2 (c s : Real) (u : Complex) (hc : c^2 + s^2 = 1)
    (hu : (starRingEnd Complex) u * u = 1) :
    (↑s : Complex) * u * (↑s * (starRingEnd Complex) u) + ↑c * ↑c = 1 := by
  have hs : (↑s : Complex) * u * (↑s * (starRingEnd Complex) u) = ↑s ^ 2 := by
    rw [show (↑s : Complex) * u * (↑s * (starRingEnd Complex) u)
          = ↑s ^ 2 * (u * (starRingEnd Complex) u) from by ring,
      show u * (starRingEnd Complex) u = 1 from by rw [mul_comm]; exact hu, mul_one]
  rw [hs, show (↑c : Complex) * ↑c = ↑c ^ 2 from by ring, s_sq_add c s hc]

/-- The `(1,2)` rotation is unitary. -/
theorem rot12_unitary (c s : Real) (hc : c^2 + s^2 = 1) :
    rot12 c s * (rot12 c s)ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot12, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.conj_ofReal,
      Fin.sum_univ_three] <;>
    first
    | exact c_mul_add c s hc
    | exact s_mul_add c s hc
    | ring

/-- The `(2,3)` rotation is unitary. -/
theorem rot23_unitary (c s : Real) (hc : c^2 + s^2 = 1) :
    rot23 c s * (rot23 c s)ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot23, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.conj_ofReal,
      Fin.sum_univ_three] <;>
    first
    | exact c_mul_add c s hc
    | exact s_mul_add c s hc
    | ring

/-- The phase-carrying rotation is unitary whenever `u` has unit modulus. -/
theorem phaseRot13_unitary (c s : Real) (u : Complex)
    (hc : c^2 + s^2 = 1) (hu : (starRingEnd Complex) u * u = 1) :
    phaseRot13 c s u * (phaseRot13 c s u)ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseRot13, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.conj_ofReal,
      Fin.sum_univ_three] <;>
    first
    | exact phase_diag1 c s u hc hu
    | exact phase_diag2 c s u hc hu
    | ring

/-- A product of three unitary `3 x 3` matrices is unitary (contravariance of `ᴴ`). -/
theorem unitary_mul3 (A Bc C : M3) (hA : A * Aᴴ = 1) (hB : Bc * Bcᴴ = 1)
    (hC : C * Cᴴ = 1) : (A * Bc * C) * (A * Bc * C)ᴴ = 1 := by
  have key : (A * Bc * C) * (A * Bc * C)ᴴ = A * (Bc * (C * (Cᴴ * (Bcᴴ * Aᴴ)))) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    noncomm_ring
  rw [key, ← Matrix.mul_assoc C Cᴴ (Bcᴴ * Aᴴ), hC, Matrix.one_mul,
    ← Matrix.mul_assoc Bc Bcᴴ Aᴴ, hB, Matrix.one_mul, hA]

/-- **The CKM matrix is unitary.**  With the three mixing angles real and the phase
carried by a unit-modulus `u`, the reconstructed `V` satisfies `V Vᴴ = 1`, so
its rows (and columns) are orthonormal. -/
theorem ckm_unitary (t12 t13 t23 : Real) (u : Complex)
    (hu : (starRingEnd Complex) u * u = 1) :
    ckm t12 t13 t23 u * (ckm t12 t13 t23 u)ᴴ = 1 := by
  unfold ckm
  exact unitary_mul3 _ _ _
    (rot23_unitary _ _ (Real.cos_sq_add_sin_sq t23))
    (phaseRot13_unitary _ _ _ (Real.cos_sq_add_sin_sq t13) hu)
    (rot12_unitary _ _ (Real.cos_sq_add_sin_sq t12))

/-! The high-energy convention now enters the shared quantum dynamics API. -/

noncomputable def ckm_unitaryOperator (t12 t13 t23 : Real) (u : Complex)
    (hu : (starRingEnd Complex) u * u = 1) :
    LeanPhy.Quantum.UnitaryOperator 3 :=
  LeanPhy.Quantum.UnitaryOperator.ofRight
    (ckm t12 t13 t23 u) (ckm_unitary t12 t13 t23 u hu)

/-- **Unitarity-triangle relation**: the rows of `V` are orthonormal,
`sum_k V_ik (V_jk)^* = delta_ij`.  The `(i, j) = (0, 2)` case is the
closure of the standard CP-violation triangle. -/
theorem ckm_row_orthonormal (t12 t13 t23 : Real) (u : Complex)
    (hu : (starRingEnd Complex) u * u = 1) (i j : Fin 3) :
    (∑ k : Fin 3, ckm t12 t13 t23 u i k * (starRingEnd Complex) (ckm t12 t13 t23 u j k))
      = if i = j then 1 else 0 := by
  have h := congrFun (congrFun (ckm_unitary t12 t13 t23 u hu) i) j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h

end LeanPhy.Particles
