import LeanPhy.FieldTheory.FiniteFermion
import LeanPhy.FieldTheory.FermionLinear
import LeanPhy.FieldTheory.FermionicQuasiFree

set_option autoImplicit false

/-!
# Vacuum contractions for variable finite fermion models

A physical vacuum is specified by an actual density and annihilation of that
density by the CAR generators. Wick identities are derived from this condition,
not stored as inputs. Linear probes may mix creation and annihilation parts
with arbitrary complex coefficients; they need not be canonical modes.

The occupation-space constructor supplies the vacuum condition for every finite
mode count. This module proves two- and four-point readouts, not general thermal
Gaussian factorization or a time-ordered/continuum Wick theorem.
-/

namespace LeanPhy.FieldTheory

open LeanPhy.Quantum
open scoped Matrix

/-- Independent coefficients in a linear fermion probe. No conjugation is implicit. -/
structure FermionProbe (ι : Type) where
  ann : ι → ℂ
  cre : ι → ℂ

namespace FermionProbe

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

noncomputable def operator (p : FermionProbe ι) (M : MultiModeCAR ι (Matrix σ σ ℂ)) :
    Matrix σ σ ℂ := M.annihilation p.ann + M.creation p.cre

/-- Ordered vacuum contraction; reversing probes includes a CAR contact term. -/
noncomputable def contraction (p q : FermionProbe ι) : ℂ := ∑ i, p.ann i * q.cre i

end FermionProbe

/-- A vacuum condition on an actual represented density, not a Wick assumption. -/
structure FermionVacuum (ι σ : Type) [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] where
  car : MultiModeCAR ι (Matrix σ σ ℂ)
  adjoint : ∀ i, car.cre i = (car.ann i)ᴴ
  state : FiniteDensity σ
  annihilates : ∀ i, car.ann i * state.rho = 0

namespace FermionVacuum

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable (V : FermionVacuum ι σ)

noncomputable def expectation (A : Matrix σ σ ℂ) : ℂ := Matrix.trace (V.state.rho * A)

@[simp] theorem expectation_one : V.expectation 1 = 1 := by
  simpa [expectation] using V.state.valid.2.2

@[simp] theorem expectation_add (A B : Matrix σ σ ℂ) :
    V.expectation (A + B) = V.expectation A + V.expectation B := by
  simp [expectation, mul_add, Matrix.trace_add]

@[simp] theorem expectation_sub (A B : Matrix σ σ ℂ) :
    V.expectation (A - B) = V.expectation A - V.expectation B := by
  simp [expectation, mul_sub, Matrix.trace_sub]

@[simp] theorem expectation_smul (z : ℂ) (A : Matrix σ σ ℂ) :
    V.expectation (z • A) = z * V.expectation A := by
  simp [expectation, Matrix.trace_smul]

theorem rho_creation (i : ι) : V.state.rho * V.car.cre i = 0 := by
  have h := congrArg Matrix.conjTranspose (V.annihilates i)
  have hrho : V.state.rhoᴴ = V.state.rho := V.state.valid.1
  simpa only [Matrix.conjTranspose_mul, hrho, ← V.adjoint,
    Matrix.conjTranspose_zero] using h

theorem annihilation_rho (f : ι → ℂ) : V.car.annihilation f * V.state.rho = 0 := by
  simp [MultiModeCAR.annihilation, Finset.sum_mul, V.annihilates]

theorem rho_creation_linear (f : ι → ℂ) : V.state.rho * V.car.creation f = 0 := by
  simp [MultiModeCAR.creation, Finset.mul_sum, V.rho_creation]

@[simp] theorem expectation_right_ann (f : ι → ℂ) (A : Matrix σ σ ℂ) :
    V.expectation (A * V.car.annihilation f) = 0 := by
  rw [expectation, ← mul_assoc, Matrix.trace_mul_comm, ← mul_assoc,
    V.annihilation_rho]
  simp

@[simp] theorem expectation_left_cre (f : ι → ℂ) (A : Matrix σ σ ℂ) :
    V.expectation (V.car.creation f * A) = 0 := by
  simp [expectation, ← mul_assoc, V.rho_creation_linear]

theorem expectation_probe_left (p : FermionProbe ι) (A : Matrix σ σ ℂ) :
    V.expectation (p.operator V.car * A) =
      V.expectation (V.car.annihilation p.ann * A) := by
  simp [FermionProbe.operator, add_mul]

theorem ann_probe_exchange (p q : FermionProbe ι) :
    V.car.annihilation p.ann * q.operator V.car =
      p.contraction q • (1 : Matrix σ σ ℂ) - q.operator V.car * V.car.annihilation p.ann := by
  have h : ⟪V.car.annihilation p.ann, q.operator V.car⟫ =
      p.contraction q • (1 : Matrix σ σ ℂ) := by
    calc
      _ = ⟪V.car.annihilation p.ann, V.car.annihilation q.ann⟫ +
          ⟪V.car.annihilation p.ann, V.car.creation q.cre⟫ := by
        simp only [FermionProbe.operator, anticommutator, mul_add, add_mul]
        abel
      _ = _ := by rw [V.car.annihilation_annihilation, V.car.annihilation_creation, zero_add]; rfl
  exact eq_sub_of_add_eq h

theorem ann_probe_tail (p q : FermionProbe ι) (A : Matrix σ σ ℂ) :
    V.car.annihilation p.ann * (q.operator V.car * A) =
      p.contraction q • A - q.operator V.car * (V.car.annihilation p.ann * A) := by
  rw [← mul_assoc, V.ann_probe_exchange]
  simp only [sub_mul, smul_mul_assoc, one_mul, mul_assoc]

/-- Actual two-point trace derived from CAR and the vacuum condition. -/
theorem twoPoint (p q : FermionProbe ι) :
    V.expectation (p.operator V.car * q.operator V.car) = p.contraction q := by
  rw [V.expectation_probe_left, V.ann_probe_exchange]
  simp

/-- Four-point factorization for arbitrary finite labels and linear probes. -/
theorem fourPoint (p q r s : FermionProbe ι) :
    V.expectation (p.operator V.car * q.operator V.car * r.operator V.car * s.operator V.car) =
      p.contraction q * r.contraction s - p.contraction r * q.contraction s +
        p.contraction s * q.contraction r := by
  have move : V.car.annihilation p.ann * q.operator V.car * r.operator V.car * s.operator V.car =
      p.contraction q • (r.operator V.car * s.operator V.car) -
      p.contraction r • (q.operator V.car * s.operator V.car) +
      p.contraction s • (q.operator V.car * r.operator V.car) -
      (q.operator V.car * r.operator V.car * s.operator V.car) * V.car.annihilation p.ann := by
    simp only [mul_assoc]
    rw [V.ann_probe_tail p q, V.ann_probe_tail p r, V.ann_probe_exchange p s]
    simp only [mul_sub, mul_smul_comm, mul_one]
    abel
  calc
    _ = V.expectation (V.car.annihilation p.ann * q.operator V.car *
        r.operator V.car * s.operator V.car) := by
      simpa only [mul_assoc] using
        V.expectation_probe_left p (q.operator V.car * r.operator V.car * s.operator V.car)
    _ = _ := by rw [move]; simp [V.twoPoint]

noncomputable def orderedContraction (p : Fin 4 → FermionProbe ι) (i j : Fin 4) : ℂ :=
  if i < j then (p i).contraction (p j)
  else if j < i then -(p j).contraction (p i) else 0

omit [DecidableEq ι] in
theorem orderedContraction_antisymm (p : Fin 4 → FermionProbe ι) (i j : Fin 4) :
    orderedContraction p j i = -orderedContraction p i j := by
  unfold orderedContraction
  by_cases hij : i < j
  · have hji : ¬ j < i := not_lt_of_gt hij
    simp [hij, hji]
  · by_cases hji : j < i
    · simp [hij, hji]
    · simp [hij, hji]

/-- A public certificate produced from the vacuum condition and probe data. -/
noncomputable def certificate (p : Fin 4 → FermionProbe ι) :
    OrderedQuasiFreeCertificate σ (Fin 4) where
  state := V.state
  generator := fun i => (p i).operator V.car
  slots := id
  contraction := orderedContraction p
  contraction_antisymm := orderedContraction_antisymm p
  twoPoint_ordered := by
    intro i j hij
    simpa only [orderedContraction, ite_eq_left hij, expectation, id_eq] using
      (V.twoPoint (p i) (p j)).symm
  fourPoint_wick := by
    simpa [FermionicWick.fourPoint, orderedContraction, expectation] using
      V.fourPoint (p 0) (p 1) (p 2) (p 3)

end FermionVacuum

namespace FiniteFermion

open LeanPhy.Condensed
open scoped Kronecker ComplexOrder

/-- The empty occupation, independent of any expansion into a flat matrix. -/
def emptyOccupation : (n : ℕ) → Occupation n
  | 0 => ()
  | n + 1 => (emptyOccupation n, 0)

theorem ann_empty_column (n : ℕ) (i : Fin n) (x : Occupation n) :
    (modes n).car.ann i x (emptyOccupation n) = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rcases x with ⟨x, b⟩
    change (modes n).append.car.ann
      (((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).symm.trans
        (Equiv.sumCongr (Equiv.refl (Fin n)) (Equiv.ofUnique (Fin 1) Unit))) i)
      (x, b) (emptyOccupation n, 0) = 0
    generalize (((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).symm.trans
        (Equiv.sumCongr (Equiv.refl (Fin n)) (Equiv.ofUnique (Fin 1) Unit))) i) = k
    rcases k with k | k
    · change ((modes n).car.ann k ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (x, b) (emptyOccupation n, 0) = 0
      simp [ih k x]
    · change ((modes n).parity ⊗ₖ smMat) (x, b) (emptyOccupation n, 0) = 0
      fin_cases b <;> simp [smMat]

noncomputable def emptyKet (n : ℕ) : Occupation n → ℂ :=
  fun x => if x = emptyOccupation n then 1 else 0

noncomputable def vacuumRho (n : ℕ) : Matrix (Occupation n) (Occupation n) ℂ :=
  Matrix.vecMulVec (emptyKet n) (star (emptyKet n))

theorem vacuumRho_pos (n : ℕ) : (vacuumRho n).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (emptyKet n)

theorem vacuumRho_trace (n : ℕ) : Matrix.trace (vacuumRho n) = 1 := by
  simp [vacuumRho, emptyKet, Matrix.trace, Matrix.vecMulVec]

noncomputable def vacuumDensity (n : ℕ) : FiniteDensity (Occupation n) :=
  ⟨vacuumRho n, (vacuumRho_pos n).isHermitian, vacuumRho_pos n, vacuumRho_trace n⟩

theorem annihilates_vacuum (n : ℕ) (i : Fin n) :
    (modes n).car.ann i * (vacuumDensity n).rho = 0 := by
  ext x y
  simp [vacuumDensity, vacuumRho, emptyKet, Matrix.vecMulVec,
    Matrix.mul_apply, mul_ite, ann_empty_column]

/-- A constructed vacuum for any finite number of modes, including zero. -/
noncomputable def vacuumState (n : ℕ) : FermionVacuum (Fin n) (Occupation n) where
  car := (modes n).car
  adjoint := (modes n).adjoint
  state := vacuumDensity n
  annihilates := annihilates_vacuum n

/-- Site, orbital and spin labels may use the same explicitly chosen ordering. -/
noncomputable def vacuumOfOrder {ι : Type} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (e : ι ≃ Fin n) : FermionVacuum ι (Occupation n) where
  car := (ofOrder e).car
  adjoint := (ofOrder e).adjoint
  state := vacuumDensity n
  annihilates := fun i => annihilates_vacuum n (e i)

end FiniteFermion
end LeanPhy.FieldTheory
