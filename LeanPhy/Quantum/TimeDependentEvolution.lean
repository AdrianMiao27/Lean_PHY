import LeanPhy.Quantum.DynamicalResponse
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false

/-!
# Actual finite time-dependent Schrödinger evolution

`Evolution H a` contains a curve with initial value one and the differential
equation `U' = -i H(t) U`. Unitarity is a theorem, not a field of the structure.
The API does not assert existence for every continuous Hamiltonian. An
autonomous constructor and driven constructors supply actual solutions;
other models must discharge the same differential equation.

All curves here are differentiable on the real line. Conclusions use finite
oriented intervals. No commutativity between Hamiltonians at different times
is assumed, and `U(t)†` must not be replaced by `U(-t)` for general drives.
-/

namespace LeanPhy.Quantum.TimeDependent

open LeanPhy.Mathematics LeanPhy.Quantum.Dynamics MeasureTheory
open scoped Matrix Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure Evolution (H : ℝ → Matrix ι ι ℂ) (a : ℝ) where
  op : ℝ → Matrix ι ι ℂ
  hermitian : ∀ t, (H t).IsHermitian
  initial : op a = 1
  equation : ∀ t, HasDerivAt op (-Complex.I • (H t * op t)) t

/-- Real-linear adjoint, compatible with the chosen matrix norm. -/
noncomputable def adjointMap : Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := by intro c M; simp }

theorem hasDerivAt_adjoint {f : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ} {t : ℝ}
    (hf : HasDerivAt f D t) : HasDerivAt (fun s => (f s)ᴴ) Dᴴ t := by
  convert! (adjointMap (ι := ι)).hasFDerivAt.comp_hasDerivAt t hf using 1

variable {H K : ℝ → Matrix ι ι ℂ} {a : ℝ}

theorem Evolution.continuous (U : Evolution H a) : Continuous U.op :=
  continuous_iff_continuousAt.mpr (fun t => (U.equation t).continuousAt)

theorem Evolution.adjoint_derivative (U : Evolution H a) (t : ℝ) :
    HasDerivAt (fun s => (U.op s)ᴴ) (Complex.I • ((U.op t)ᴴ * H t)) t := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, star_neg, Complex.star_def, map_neg,
    Complex.conj_I, neg_neg, (U.hermitian t).eq] using! hasDerivAt_adjoint (U.equation t)

theorem Evolution.unitary (U : Evolution H a) (t : ℝ) : (U.op t)ᴴ * U.op t = 1 := by
  have hd (s : ℝ) : HasDerivAt (fun s => (U.op s)ᴴ * U.op s) 0 s := by
    convert (U.adjoint_derivative s).mul (U.equation s) using 1 <;> try rfl
    simp only [Matrix.smul_mul, Matrix.mul_smul, neg_smul, Matrix.mul_neg, neg_mul, Matrix.mul_assoc]
    abel
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := t)
    (fun s _ => hd s) ((continuous_const : Continuous (fun _ : ℝ => (0 : Matrix ι ι ℂ))).intervalIntegrable a t)
  simp only [U.initial, Matrix.conjTranspose_one, one_mul,
    intervalIntegral.integral_zero] at hi
  exact sub_eq_zero.mp hi.symm

noncomputable def Evolution.asUnitary (U : Evolution H a) (t : ℝ) : FiniteUnitary ι :=
  ⟨U.op t, U.unitary t⟩

theorem Evolution.right_unitary (U : Evolution H a) (t : ℝ) :
    U.op t * (U.op t)ᴴ = 1 := (U.asUnitary t).right_unitary

/-- Transport from s to t, in Schrödinger order. -/
noncomputable def Evolution.between (U : Evolution H a) (s t : ℝ) : Matrix ι ι ℂ :=
  U.op t * (U.op s)ᴴ

theorem Evolution.between_comp (U : Evolution H a) (s u t : ℝ) :
    U.between u t * U.between s u = U.between s t := by
  simp only [Evolution.between]
  calc
    _ = U.op t * ((U.op u)ᴴ * U.op u) * (U.op s)ᴴ := by noncomm_ring
    _ = _ := by rw [U.unitary]; simp

noncomputable def Evolution.restart (U : Evolution H a) (s : ℝ) : Evolution H s where
  op := U.between s
  hermitian := U.hermitian
  initial := U.right_unitary s
  equation t := by
    convert (U.equation t).mul_const (U.op s)ᴴ using 1 <;> try rfl
    simp only [Evolution.between, Matrix.smul_mul, Matrix.mul_assoc]

noncomputable def Evolution.observable (U : Evolution H a)
    (O : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ := (U.op t)ᴴ * O * U.op t

noncomputable def Evolution.state (U : Evolution H a)
    (ρ : FiniteDensity ι) (t : ℝ) : FiniteDensity ι := (U.asUnitary t).evolveDensity ρ

theorem Evolution.state_expectation (U : Evolution H a)
    (ρ : FiniteDensity ι) (O : Matrix ι ι ℂ) (t : ℝ) :
    Matrix.trace ((U.state ρ t).rho * O) = Matrix.trace (ρ.rho * U.observable O t) := by
  change Matrix.trace ((U.op t * ρ.rho * (U.op t)ᴴ) * O) = _
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  congr 1
  simp only [Evolution.observable]
  noncomm_ring

/-- The instantaneous Hamiltonian remains inside the time-dependent conjugation. -/
theorem Evolution.observable_derivative (U : Evolution H a)
    (O : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (U.observable O)
      (Complex.I • U.observable (H t * O - O * H t) t) t := by
  convert ((U.adjoint_derivative t).mul_const O).mul (U.equation t) using 1 <;> try rfl
  simp only [Evolution.observable, Matrix.smul_mul, Matrix.mul_smul,
    neg_smul, Matrix.mul_neg, neg_mul, smul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- Exact comparison of two actual evolutions, before any amplitude limit. -/
theorem Evolution.comparison (U : Evolution H a) (W : Evolution K a)
    (hKH : Continuous (fun s => K s - H s)) (t : ℝ) :
    (U.op t)ᴴ * W.op t - 1 = ∫ s in a..t,
      -Complex.I • ((U.op s)ᴴ * (K s - H s) * W.op s) := by
  have hd (s : ℝ) : HasDerivAt (fun s => (U.op s)ᴴ * W.op s)
      (-Complex.I • ((U.op s)ᴴ * (K s - H s) * W.op s)) s := by
    convert (U.adjoint_derivative s).mul (W.equation s) using 1 <;> try rfl
    simp only [Matrix.smul_mul, Matrix.mul_smul, neg_smul, Matrix.mul_neg, neg_mul, smul_sub,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  have hc : Continuous (fun s => -Complex.I •
      ((U.op s)ᴴ * (K s - H s) * W.op s)) :=
    by
      have hu := U.continuous
      have hw := W.continuous
      fun_prop
  simpa only [U.initial, W.initial, Matrix.conjTranspose_one, one_mul] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (hc.intervalIntegrable a t)).symm

/-- Initial data and the equation determine the supplied solution uniquely. -/
theorem Evolution.unique (U W : Evolution H a) : U.op = W.op := by
  funext t
  have h := U.comparison W (by simpa using
    (continuous_const : Continuous (fun _ : ℝ => (0 : Matrix ι ι ℂ)))) t
  simp only [sub_self, Matrix.mul_zero, Matrix.zero_mul, smul_zero,
    intervalIntegral.integral_zero, sub_eq_zero] at h
  have hh := congrArg (fun X => U.op t * X) h
  simpa only [← Matrix.mul_assoc, U.right_unitary t, one_mul, mul_one] using hh.symm

/-- Constant Hermitian Hamiltonians supply an actual Schrödinger solution. -/
noncomputable def autonomous (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (a : ℝ) :
    Evolution (fun _ => H) a where
  op t := propagator H (a - t)
  hermitian _ := hH
  initial := by simp [propagator]
  equation t := by
    have h := (Duhamel.flow_derivative_left (Complex.I • H) (a - t)).scomp t
      ((hasDerivAt_const t a).sub (hasDerivAt_id t))
    simpa only [Function.comp_apply, zero_sub, one_smul, neg_smul,
      smul_mul_assoc, propagator] using! h

theorem autonomous_observable (H O : Matrix ι ι ℂ) (hH : H.IsHermitian) (a t : ℝ) :
    (autonomous H hH a).observable O t = heisenberg H O (t - a) := by
  change (propagator H (a - t))ᴴ * O * propagator H (a - t) =
    propagator H (t - a) * O * propagator H (-(t - a))
  rw [← propagator_neg_eq_adjoint H hH]
  congr 2 <;> congr 1 <;> ring

theorem autonomous_observable_of_commute (H O : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hO : Commute H O) (a t : ℝ) :
    (autonomous H hH a).observable O t = O := by
  rw [autonomous_observable, heisenberg_eq_conjugate H O hH]
  exact finiteHamiltonianFlow_conjugate_of_conserved H hH (t - a) O
    (sub_eq_zero.mpr hO.eq)

end LeanPhy.Quantum.TimeDependent
