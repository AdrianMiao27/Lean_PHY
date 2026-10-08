import LeanPhy.FieldTheory.FermionVacuumWick
import LeanPhy.Quantum.FiniteThermalState

set_option autoImplicit false

/-!
# Unitary transport of finite fermion vacua

An orbital rotation or a finite free-fermion quench transports the many-body
density and every CAR generator by the same finite unitary.  This file makes
that construction explicit and proves that all ordered probe moments, hence
the terminating vacuum Wick recursion, are transported without changing the
contraction kernel.  It is a constructive bridge for finite free models; it
does not claim a thermal or interacting Wick theorem.
-/

namespace LeanPhy.FieldTheory

open LeanPhy.Quantum
open scoped Matrix

namespace FermionVacuum

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

private theorem conjugate_add (U : FiniteUnitary σ) (A B : Matrix σ σ ℂ) :
    U.conjugate (A + B) = U.conjugate A + U.conjugate B := by
  simp [FiniteUnitary.conjugate, add_mul, mul_add]

private theorem conjugate_sum_smul (U : FiniteUnitary σ) (f : ι → ℂ)
    (A : ι → Matrix σ σ ℂ) :
    U.conjugate (∑ i, f i • A i) = ∑ i, f i • U.conjugate (A i) := by
  simp only [FiniteUnitary.conjugate, Finset.smul_sum, Finset.sum_smul,
    Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm]

private theorem conjugate_star (U : FiniteUnitary σ) (A : Matrix σ σ ℂ) :
    (U.conjugate A)ᴴ = U.conjugate Aᴴ := by
  simp [FiniteUnitary.conjugate, Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem conjugate_product (U : FiniteUnitary σ)
    (ps : List (Matrix σ σ ℂ)) :
    U.conjugate ps.prod = (ps.map U.conjugate).prod := by
  induction ps with
  | nil => simp [FiniteUnitary.conjugate, U.right_unitary]
  | cons A ps ih =>
      simp only [List.prod_cons, List.map_cons]
      calc
        U.conjugate (A * ps.prod) = U.conjugate A * U.conjugate ps.prod :=
          (U.conjugate_mul A ps.prod).symm
        _ = U.conjugate A * (List.map U.conjugate ps).prod := by rw [ih]

private theorem conjugate_expectation_product (U : FiniteUnitary σ)
    (rho : Matrix σ σ ℂ) (ps : List (Matrix σ σ ℂ)) :
    Matrix.trace (U.conjugate rho * (ps.map U.conjugate).prod) =
      Matrix.trace (rho * ps.prod) := by
  rw [← conjugate_product U ps, U.conjugate_expectation]

private theorem conjugate_anticommutator (U : FiniteUnitary σ)
    (A B : Matrix σ σ ℂ) :
    ⟪U.conjugate A, U.conjugate B⟫ = U.conjugate ⟪A, B⟫ := by
  simp only [anticommutator, U.conjugate_mul, ← conjugate_add U]

/-- Transport an actual finite vacuum by a common many-body unitary. -/
noncomputable def transport (U : FiniteUnitary σ) (V : FermionVacuum ι σ) :
    FermionVacuum ι σ where
  car := {
    ann := fun i => U.conjugate (V.car.ann i)
    cre := fun i => U.conjugate (V.car.cre i)
    car_ann_cre := by
      intro i j
      rw [conjugate_anticommutator U, V.car.car_ann_cre]
      by_cases h : i = j <;> simp [h, FiniteUnitary.conjugate, U.right_unitary]
    car_ann_ann := by
      intro i j
      rw [conjugate_anticommutator U, V.car.car_ann_ann]
      simp [FiniteUnitary.conjugate]
    car_cre_cre := by
      intro i j
      rw [conjugate_anticommutator U, V.car.car_cre_cre]
      simp [FiniteUnitary.conjugate] }
  adjoint := by
    intro i
    rw [conjugate_star]
    exact congrArg U.conjugate (V.adjoint i)
  state := U.evolveDensity V.state
  annihilates := by
    intro i
    change U.conjugate (V.car.ann i) * U.conjugate V.state.rho = 0
    rw [U.conjugate_mul, V.annihilates]
    simp [FiniteUnitary.conjugate]

@[simp] theorem transport_car_ann (U : FiniteUnitary σ) (V : FermionVacuum ι σ)
    (i : ι) : (transport U V).car.ann i = U.conjugate (V.car.ann i) := rfl

@[simp] theorem transport_car_cre (U : FiniteUnitary σ) (V : FermionVacuum ι σ)
    (i : ι) : (transport U V).car.cre i = U.conjugate (V.car.cre i) := rfl

@[simp] theorem transport_state (U : FiniteUnitary σ) (V : FermionVacuum ι σ) :
    (transport U V).state.rho = U.conjugate V.state.rho := by
  simp [transport, FiniteUnitary.evolveDensity]

theorem transport_probe (U : FiniteUnitary σ) (V : FermionVacuum ι σ)
    (p : FermionProbe ι) :
    p.operator (transport U V).car = U.conjugate (p.operator V.car) := by
  simp only [FermionProbe.operator, MultiModeCAR.annihilation,
    MultiModeCAR.creation, transport_car_ann, transport_car_cre]
  rw [conjugate_add, conjugate_sum_smul, conjugate_sum_smul]

theorem transport_probeProduct (U : FiniteUnitary σ) (V : FermionVacuum ι σ)
    (ps : List (FermionProbe ι)) :
    (transport U V).probeProduct ps = U.conjugate (V.probeProduct ps) := by
  induction ps with
  | nil => simp [FermionVacuum.probeProduct, FiniteUnitary.conjugate, U.right_unitary]
  | cons p ps ih =>
      simp only [probeProduct_cons]
      rw [transport_probe, ih, U.conjugate_mul]

theorem transport_expectation (U : FiniteUnitary σ) (V : FermionVacuum ι σ)
    (A : Matrix σ σ ℂ) :
    (transport U V).expectation (U.conjugate A) = V.expectation A := by
  rw [expectation, transport_state, U.conjugate_expectation]
  rfl

/-- Every ordered probe moment is invariant under common finite-unitary transport. -/
theorem transport_moment (U : FiniteUnitary σ) (V : FermionVacuum ι σ)
    (ps : List (FermionProbe ι)) :
    (transport U V).moment ps = V.moment ps := by
  rw [moment, transport_probeProduct, transport_expectation]
  rfl

theorem transport_moment_eq (U : FiniteUnitary σ) (V : FermionVacuum ι σ)
    (ps : List (FermionProbe ι)) :
    (transport U V).moment ps = FermionicWick.moment FermionProbe.contraction ps := by
  rw [transport_moment]
  exact V.moment_eq ps

end FermionVacuum
end LeanPhy.FieldTheory
