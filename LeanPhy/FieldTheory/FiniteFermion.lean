import LeanPhy.Condensed.JordanWigner
import LeanPhy.FieldTheory.FermionHamiltonian
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false

/-!
# Constructed finite fermion representations

A new mode is appended with the existing fermion parity string. CAR and
adjoints are proved compositionally using Kronecker identities, without
enumerating the exponentially large matrix. Iteration constructs n actual
modes on a 2^n-dimensional occupation space; no CAR proof is requested from
the user of the constructor.
-/

namespace LeanPhy.FieldTheory.FiniteFermion

open LeanPhy.Quantum LeanPhy.Condensed
open scoped Matrix Kronecker

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

structure Representation (ι σ : Type) [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] where
  car : MultiModeCAR ι (Matrix σ σ ℂ)
  adjoint : ∀ i, car.cre i = (car.ann i)ᴴ
  parity : Matrix σ σ ℂ
  parity_sq : parity * parity = 1
  parity_hermitian : parity.IsHermitian
  odd : ∀ i, parity * car.ann i + car.ann i * parity = 0

namespace Representation

variable (S : Representation ι σ)

theorem odd_cre (i : ι) : S.parity * S.car.cre i + S.car.cre i * S.parity = 0 := by
  have h := congrArg Matrix.conjTranspose (S.odd i)
  have hp : S.parityᴴ = S.parity := S.parity_hermitian
  simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_zero,
    ← S.adjoint, hp, add_comm] using h

private theorem tensor_same (a b : Matrix σ σ ℂ) :
    ⟪a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ), b ⊗ₖ 1⟫ = ⟪a, b⟫ ⊗ₖ 1 := by
  simp only [anticommutator, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    ← Matrix.add_kronecker]

private theorem tensor_cross (a b : Matrix σ σ ℂ) (c : Matrix (Fin 2) (Fin 2) ℂ) :
    ⟪a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ), b ⊗ₖ c⟫ = ⟪a, b⟫ ⊗ₖ c := by
  simp only [anticommutator, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    ← Matrix.add_kronecker]

private theorem tensor_parity (a b : Matrix (Fin 2) (Fin 2) ℂ) :
    ⟪S.parity ⊗ₖ a, S.parity ⊗ₖ b⟫ = (1 : Matrix σ σ ℂ) ⊗ₖ ⟪a, b⟫ := by
  simp only [anticommutator, ← Matrix.mul_kronecker_mul, S.parity_sq,
    ← Matrix.kronecker_add]

/-- Append one occupied/unoccupied factor with its Jordan-Wigner parity string. -/
noncomputable def append : Representation (ι ⊕ Unit) (σ × Fin 2) where
  car := {
    ann := Sum.elim (fun i => S.car.ann i ⊗ₖ 1) (fun _ => S.parity ⊗ₖ smMat)
    cre := Sum.elim (fun i => S.car.cre i ⊗ₖ 1) (fun _ => S.parity ⊗ₖ spMat)
    car_ann_cre := by
      intro i j
      rcases i with i | i <;> rcases j with j | j
      all_goals simp only [Sum.elim_inl, Sum.elim_inr]
      · rw [tensor_same, S.car.car_ann_cre]
        by_cases h : i = j <;> simp [h]
      · rw [tensor_cross]
        have h : ⟪S.car.ann i, S.parity⟫ = 0 := by
          simpa [anticommutator, add_comm] using S.odd i
        simp [h]
      · rw [anticommutator_comm, tensor_cross]
        have h : ⟪S.car.cre j, S.parity⟫ = 0 := by
          simpa [anticommutator, add_comm] using S.odd_cre j
        simp [h]
      · rw [S.tensor_parity]
        simp [anticommutator, sm_sp_sum]
    car_ann_ann := by
      intro i j
      rcases i with i | i <;> rcases j with j | j
      all_goals simp only [Sum.elim_inl, Sum.elim_inr]
      · rw [tensor_same, S.car.car_ann_ann]; simp
      · rw [tensor_cross]
        have h : ⟪S.car.ann i, S.parity⟫ = 0 := by
          simpa [anticommutator, add_comm] using S.odd i
        simp [h]
      · rw [anticommutator_comm, tensor_cross]
        have h : ⟪S.car.ann j, S.parity⟫ = 0 := by
          simpa [anticommutator, add_comm] using S.odd j
        simp [h]
      · rw [S.tensor_parity]; simp [anticommutator, sm_sm_zero]
    car_cre_cre := by
      intro i j
      rcases i with i | i <;> rcases j with j | j
      all_goals simp only [Sum.elim_inl, Sum.elim_inr]
      · rw [tensor_same, S.car.car_cre_cre]; simp
      · rw [tensor_cross]
        have h : ⟪S.car.cre i, S.parity⟫ = 0 := by
          simpa [anticommutator, add_comm] using S.odd_cre i
        simp [h]
      · rw [anticommutator_comm, tensor_cross]
        have h : ⟪S.car.cre j, S.parity⟫ = 0 := by
          simpa [anticommutator, add_comm] using S.odd_cre j
        simp [h]
      · rw [S.tensor_parity]; simp [anticommutator, sp_sp_zero] }
  adjoint := by
    intro i
    cases i with
    | inl i => simp [Matrix.conjTranspose_kronecker, S.adjoint]
    | inr i =>
      have h : smMatᴴ = spMat := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [smMat, spMat, Matrix.conjTranspose_apply]
      have hp : S.parityᴴ = S.parity := S.parity_hermitian
      simp [Matrix.conjTranspose_kronecker, hp, h]
  parity := S.parity ⊗ₖ zMat
  parity_sq := by rw [← Matrix.mul_kronecker_mul, S.parity_sq, sz_sz_one]; simp
  parity_hermitian := by
    have hz : zMatᴴ = zMat := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [zMat, Matrix.conjTranspose_apply]
    change (S.parity ⊗ₖ zMat)ᴴ = S.parity ⊗ₖ zMat
    rw [Matrix.conjTranspose_kronecker, S.parity_hermitian, hz]
  odd := by
    intro i
    cases i with
    | inl i =>
      simp only [Sum.elim_inl, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
        ← Matrix.add_kronecker, S.odd, Matrix.zero_kronecker]
    | inr i =>
      simp only [Sum.elim_inr, ← Matrix.mul_kronecker_mul, S.parity_sq,
        ← Matrix.kronecker_add, sz_sm_anticomm, Matrix.kronecker_zero]

noncomputable def relabel {κ : Type} [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) : Representation κ σ where
  car := {
    ann := fun i => S.car.ann (e i)
    cre := fun i => S.car.cre (e i)
    car_ann_cre := by intro i j; simpa using S.car.car_ann_cre (e i) (e j)
    car_ann_ann := fun i j => S.car.car_ann_ann (e i) (e j)
    car_cre_cre := fun i j => S.car.car_cre_cre (e i) (e j) }
  adjoint := fun i => S.adjoint (e i)
  parity := S.parity
  parity_sq := S.parity_sq
  parity_hermitian := S.parity_hermitian
  odd := fun i => S.odd (e i)

/-- Coupling tables produce an operator on the actual occupation representation. -/
noncomputable def hamiltonian (K : FermionBdG.Coefficients ι) : Matrix σ σ ℂ :=
  S.car.quadratic K.normal K.pairing

theorem hamiltonian_hermitian (K : FermionBdG.Coefficients ι) :
    (S.hamiltonian K).IsHermitian := FermionBdG.manyBody_hermitian S.car S.adjoint K

/-- Thermal density on the represented many-body space, not on Nambu indices. -/
noncomputable def thermalState [Nonempty σ] (K : FermionBdG.Coefficients ι) (β : ℝ) :
    FiniteDensity σ := finiteThermalState (S.hamiltonian K) (S.hamiltonian_hermitian K) β

end Representation

def Occupation : ℕ → Type
  | 0 => Unit
  | n + 1 => Occupation n × Fin 2

instance occupationFintype (n : ℕ) : Fintype (Occupation n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Occupation n × Fin 2))

instance occupationDecidableEq (n : ℕ) : DecidableEq (Occupation n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Occupation n × Fin 2))

instance occupationNonempty (n : ℕ) : Nonempty (Occupation n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Nonempty (Occupation n × Fin 2))

theorem occupation_card (n : ℕ) : Fintype.card (Occupation n) = 2 ^ n := by
  induction n with
  | zero =>
    change Fintype.card Unit = 1
    exact Fintype.card_unique
  | succ n ih =>
    change Fintype.card (Occupation n × Fin 2) = 2 ^ (n + 1)
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]

noncomputable def vacuum : Representation (Fin 0) (Occupation 0) where
  car := {
    ann := Fin.elim0
    cre := Fin.elim0
    car_ann_cre := fun i => Fin.elim0 i
    car_ann_ann := fun i => Fin.elim0 i
    car_cre_cre := fun i => Fin.elim0 i }
  adjoint := fun i => Fin.elim0 i
  parity := 1
  parity_sq := by simp
  parity_hermitian := by simp
  odd := fun i => Fin.elim0 i

/-- Every n obtains concrete, adjoint-compatible CAR matrices by recursion. -/
noncomputable def modes : (n : ℕ) → Representation (Fin n) (Occupation n)
  | 0 => vacuum
  | n + 1 => (modes n).append.relabel
      ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).symm.trans
        (Equiv.sumCongr (Equiv.refl (Fin n)) (Equiv.ofUnique (Fin 1) Unit)))

/-- Supply the mode order explicitly when labels encode sites, orbitals or spin. -/
noncomputable def ofOrder {n : ℕ} (e : ι ≃ Fin n) : Representation ι (Occupation n) :=
  (modes n).relabel e

/-- A default ordering is available when only a finite label type is supplied. -/
noncomputable def namedModes (ι : Type) [Fintype ι] [DecidableEq ι] :
    Representation ι (Occupation (Fintype.card ι)) := ofOrder (Fintype.equivFin ι)

end LeanPhy.FieldTheory.FiniteFermion
