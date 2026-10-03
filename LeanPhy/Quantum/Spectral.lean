import LeanPhy.Quantum.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

/-!
# Finite spectral statements for research calculations

Eigenvalue arguments recur in quantum mechanics, band theory, lattice models,
spin systems and finite-volume field theory.  This module keeps the useful
algebraic core separate from spectral-analysis claims: an eigenvector is an
exact matrix-vector equation, while existence, completeness and continuous
spectra belong to the analysis layer.
-/

namespace LeanPhy.Quantum

open scoped Matrix

/-- An exact finite-dimensional eigenvector equation. -/
def IsEigenvector {n : Nat} (A : Operator n) (e : ℂ) (v : Ket n) : Prop :=
  A.mulVec v = e • v

theorem isEigenvector_iff {n : Nat} (A : Operator n) (e : ℂ) (v : Ket n) :
    IsEigenvector A e v ↔ A.mulVec v = e • v := Iff.rfl

theorem zero_isEigenvector {n : Nat} (A : Operator n) (e : ℂ) :
    IsEigenvector A e (0 : Ket n) := by
  simp [IsEigenvector]

theorem commuting_preserves_eigenvector {n : Nat}
    (H A : Operator n) (e : ℂ) (v : Ket n)
    (hcomm : H * A = A * H) (hv : IsEigenvector H e v) :
    IsEigenvector H e (A.mulVec v) := by
  unfold IsEigenvector at hv ⊢
  rw [Matrix.mulVec_mulVec, hcomm]
  rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

theorem commutator_eigenvector_shift {n : Nat}
    (H A : Operator n) (e c : ℂ) (v : Ket n)
    (hshift : commutator H A = c • A)
    (hv : IsEigenvector H e v) :
    IsEigenvector H (e + c) (A.mulVec v) := by
  unfold IsEigenvector at hv ⊢
  have hmul : H * A = c • A + A * H := by
    exact eq_add_of_sub_eq hshift
  rw [Matrix.mulVec_mulVec, hmul, Matrix.add_mulVec, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  rw [add_smul]
  simp [add_comm]

theorem commuting_preserves_eigenspace {n : Nat}
    (H A : Operator n) (e : ℂ) (v : Ket n)
    (hcomm : H * A = A * H) (hv : IsEigenvector H e v) :
    IsEigenvector H e (A.mulVec v) :=
  commuting_preserves_eigenvector H A e v hcomm hv

theorem power_eigenvector {n : Nat} (A : Operator n) (e : ℂ) (v : Ket n)
    (k : Nat) (hv : IsEigenvector A e v) :
    IsEigenvector (A ^ k) (e ^ k) v := by
  induction k with
  | zero =>
      unfold IsEigenvector
      simp
  | succ k ih =>
      unfold IsEigenvector at ih ⊢
      rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih]
      rw [pow_succ, mul_smul]
      simp [smul_smul, mul_comm]

theorem polynomial_power_shadow {n : Nat} (A : Operator n) (e : ℂ) (v : Ket n)
    (k : Nat) (hv : IsEigenvector A e v) :
    (A ^ k).mulVec v = (e ^ k) • v :=
  power_eigenvector A e v k hv

/-! ## Characteristic-polynomial interface -/

/-- The characteristic polynomial is monic for every finite operator. -/
theorem characteristicPolynomial_monic {n : Nat} (A : Operator n) :
    (Matrix.charpoly A).Monic :=
  Matrix.charpoly_monic A

/-- Its degree is exactly the dimension of the finite state space. -/
theorem characteristicPolynomial_degree {n : Nat} (A : Operator n) :
    (Matrix.charpoly A).natDegree = n := by
  simpa using Matrix.charpoly_natDegree_eq_dim A

/-- Cayley–Hamilton: every finite operator annihilates its characteristic
polynomial.  This is the bridge from a concrete matrix calculation to a
finite spectral constraint; no existence or completeness of eigenvectors is
asserted here. -/
theorem cayleyHamilton {n : Nat} (A : Operator n) :
    Polynomial.aeval A (Matrix.charpoly A) = 0 :=
  Matrix.aeval_self_charpoly A

end LeanPhy.Quantum
