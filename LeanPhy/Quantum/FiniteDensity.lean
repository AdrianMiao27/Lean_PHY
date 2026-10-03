import LeanPhy.Quantum.Unitary
import LeanPhy.Quantum.NamedFinite
import LeanPhy.Quantum.NamedChannel
import LeanPhy.Mathematics.FiniteProcess

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# A common finite density-state invariant

`State n` and `NamedState ι` are useful surface aliases, but their validity
conditions used to be duplicated as `IsDensity` and `IsNamedDensity`.  This
module provides the shared finite-index predicate and an optional bundled
object.  It is deliberately finite-dimensional: trace one, Hermiticity and
positive semidefiniteness are the complete invariant here; no spectral or
infinite-dimensional claim is hidden.
-/

namespace LeanPhy.Quantum

open scoped Matrix ComplexOrder

/-- A density matrix on any finite label type. -/
def IsFiniteDensity {ι : Type*} [Fintype ι] (rho : Matrix ι ι ℂ) : Prop :=
  rho.IsHermitian ∧ rho.PosSemidef ∧ Matrix.trace rho = 1

/-- A finite density matrix bundled with its kernel-checked invariant. -/
structure FiniteDensity (ι : Type*) [Fintype ι] where
  rho : Matrix ι ι ℂ
  valid : IsFiniteDensity rho

instance {ι : Type*} [Fintype ι] : CoeFun (FiniteDensity ι)
    (fun _ => Matrix ι ι ℂ) := ⟨FiniteDensity.rho⟩

theorem isDensity_iff_isFiniteDensity {n : Nat} (rho : State n) :
    IsDensity rho ↔ IsFiniteDensity rho := by
  rfl

theorem isNamedDensity_iff_isFiniteDensity {ι : Type*} [Fintype ι]
    (rho : NamedState ι) :
    IsNamedDensity rho ↔ IsFiniteDensity rho := by
  rfl

/-- Finite unitary conjugation preserves the common density invariant. -/
theorem FiniteUnitary.conjugate_isFiniteDensity {ι : Type*} [Fintype ι]
    [DecidableEq ι] (U : FiniteUnitary ι) (rho : Matrix ι ι ℂ)
    (hrho : IsFiniteDensity rho) :
    IsFiniteDensity (U.conjugate rho) := by
  have hpos : (U.conjugate rho).PosSemidef :=
    U.conjugate_posSemidef rho hrho.2.1
  refine ⟨hpos.isHermitian, hpos, ?_⟩
  exact (U.conjugate_trace rho).trans hrho.2.2

theorem namedFiniteChannel_isFiniteDensity {ι : Type*} [Fintype ι]
    (C : NamedFiniteChannel ι) (rho : NamedState ι)
    (hrho : IsFiniteDensity rho) :
    IsFiniteDensity (C rho) := by
  apply (isNamedDensity_iff_isFiniteDensity (C rho)).mp
  apply namedFiniteChannel_isDensity C rho
  exact (isNamedDensity_iff_isFiniteDensity rho).mpr hrho

theorem namedApplyKraus_isFiniteDensity {ι κ : Type*} [Fintype ι]
    [Fintype κ] [DecidableEq ι] (K : κ → NamedState ι)
    (htp : (∑ k, Matrix.conjTranspose (K k) * K k) = 1)
    (rho : NamedState ι) (hrho : IsFiniteDensity rho) :
    IsFiniteDensity (namedApplyKraus K rho) := by
  apply (isNamedDensity_iff_isFiniteDensity (namedApplyKraus K rho)).mp
  apply namedApplyKraus_isDensity K rho _ htp
  exact (isNamedDensity_iff_isFiniteDensity rho).mpr hrho

/-- A bundled finite density state transported by a finite unitary. -/
def FiniteUnitary.evolveDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : FiniteUnitary ι) (rho : FiniteDensity ι) : FiniteDensity ι :=
  ⟨U.conjugate rho.rho, U.conjugate_isFiniteDensity rho.rho rho.valid⟩

/-- A finite unitary evolution is a proof-preserving endoprocess on bundled
    density states.  This exposes the same composition/iterate API as CPTP and
    Markov updates while keeping the unitary proof in the adapter. -/
def FiniteUnitary.toStateMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : FiniteUnitary ι) :
    LeanPhy.Mathematics.StateMap (FiniteDensity ι) (FiniteDensity ι)
      (fun _ => True) (fun _ => True) where
  toFun := U.evolveDensity
  preserves := by intro rho _; exact trivial

@[simp] theorem FiniteUnitary.evolveDensity_rho {ι : Type*} [Fintype ι]
    [DecidableEq ι] (U : FiniteUnitary ι) (rho : FiniteDensity ι) :
    (U.evolveDensity rho).rho = U.conjugate rho.rho :=
  rfl

end LeanPhy.Quantum
