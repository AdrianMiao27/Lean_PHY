import LeanPhy.Quantum.NamedFinite
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-!
# Kraus channels on arbitrary finite label types

This is the named-index counterpart of `QuantumInfo.Channel`.  It packages
finite Kraus maps, trace preservation, positivity and finite ancillary complete
positivity for matrices indexed by any finite types.  It is useful when the
index itself carries physics meaning (colour, lattice site, band, spin, or
polarization).  No infinite-dimensional operator-algebra claim is made.
-/

namespace LeanPhy.Quantum

open scoped BigOperators Matrix ComplexOrder

noncomputable def namedApplyKraus {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : κ → NamedState ι) (rho : NamedState ι) : NamedState ι :=
  ∑ k, K k * rho * Matrix.conjTranspose (K k)

theorem namedKraus_trace {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (K : κ → NamedState ι) (rho : NamedState ι)
    (htp : (∑ k, Matrix.conjTranspose (K k) * K k) = 1) :
    namedTrace (namedApplyKraus K rho) = namedTrace rho := by
  unfold namedTrace namedApplyKraus
  rw [Matrix.trace_sum]
  trans ∑ k, Matrix.trace (Matrix.conjTranspose (K k) * K k * rho)
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.trace_mul_cycle]
  rw [← Matrix.trace_sum]
  have hsum : (∑ k, Matrix.conjTranspose (K k) * K k * rho) =
      (∑ k, Matrix.conjTranspose (K k) * K k) * rho := by
    rw [Finset.sum_mul]
  rw [hsum, htp, Matrix.one_mul]

theorem namedKraus_term_posSemidef {ι : Type*} [Fintype ι]
    (K : NamedState ι) (rho : NamedState ι) (hrho : rho.PosSemidef) :
    (K * rho * Matrix.conjTranspose K).PosSemidef :=
  Matrix.PosSemidef.mul_mul_conjTranspose_same hrho K

theorem namedMatrix_sum_posSemidef {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → NamedState ι) (hA : ∀ k, (A k).PosSemidef) :
    (∑ k, A k).PosSemidef := by
  classical
  refine Finset.induction_on (Finset.univ : Finset κ) ?_ ?_
  · simpa using (Matrix.PosSemidef.zero : (0 : NamedState ι).PosSemidef)
  · intro k s hk ih
    rw [Finset.sum_insert hk]
    exact (hA k).add ih

theorem namedApplyKraus_posSemidef {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : κ → NamedState ι) (rho : NamedState ι) (hrho : rho.PosSemidef) :
    (namedApplyKraus K rho).PosSemidef := by
  unfold namedApplyKraus
  apply namedMatrix_sum_posSemidef
  intro k
  exact namedKraus_term_posSemidef (K k) rho hrho

theorem namedApplyKraus_isDensity {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (K : κ → NamedState ι) (rho : NamedState ι) (hrho : IsNamedDensity rho)
    (htp : (∑ k, Matrix.conjTranspose (K k) * K k) = 1) :
    IsNamedDensity (namedApplyKraus K rho) := by
  have hpos := namedApplyKraus_posSemidef K rho hrho.2.1
  refine ⟨hpos.isHermitian, hpos, ?_⟩
  exact (namedKraus_trace K rho htp).trans hrho.2.2

/-- Explicit finite ancillary extension of a named Kraus family. -/
noncomputable def namedApplyKrausWithAncilla {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α]
    (K : κ → NamedState ι) (rho : Matrix (α × ι) (α × ι) ℂ) :
    Matrix (α × ι) (α × ι) ℂ := by
  classical
  exact ∑ k,
    Matrix.kroneckerMap (· * ·) (1 : Matrix α α ℂ) (K k) * rho *
      Matrix.conjTranspose (Matrix.kroneckerMap (· * ·)
        (1 : Matrix α α ℂ) (K k))

def NamedCompletelyPositiveKraus {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : κ → NamedState ι) : Prop :=
  ∀ (α : Type*) (_ : Fintype α)
    (rho : Matrix (α × ι) (α × ι) ℂ), rho.PosSemidef →
      (namedApplyKrausWithAncilla K rho).PosSemidef

theorem namedApplyKraus_completelyPositive {ι κ : Type*}
    [Fintype ι] [Fintype κ] (K : κ → NamedState ι) :
    NamedCompletelyPositiveKraus K := by
  intro α hα rho hrho
  classical
  unfold namedApplyKrausWithAncilla
  apply namedMatrix_sum_posSemidef
  intro k
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hrho _

structure NamedFiniteChannel (ι : Type*) [Fintype ι] where
  toFun : NamedState ι → NamedState ι
  map_add : ∀ rho sig, toFun (rho + sig) = toFun rho + toFun sig
  map_smul : ∀ (c : ℂ) rho, toFun (c • rho) = c • toFun rho
  map_pos : ∀ rho, rho.PosSemidef → (toFun rho).PosSemidef
  trace_preserving : ∀ rho, namedTrace (toFun rho) = namedTrace rho

instance {ι : Type*} [Fintype ι] : CoeFun (NamedFiniteChannel ι)
    (fun _ => NamedState ι → NamedState ι) := ⟨NamedFiniteChannel.toFun⟩

def namedIdentityChannel {ι : Type*} [Fintype ι] : NamedFiniteChannel ι where
  toFun := id
  map_add := by intro rho sig; rfl
  map_smul := by intro c rho; rfl
  map_pos := by intro rho h; simpa using h
  trace_preserving := by intro rho; rfl

noncomputable def namedChannelFromKraus {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (K : κ → NamedState ι)
    (htp : (∑ k, Matrix.conjTranspose (K k) * K k) = 1) :
    NamedFiniteChannel ι where
  toFun := namedApplyKraus K
  map_add := by
    intro rho sig
    simp [namedApplyKraus, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul := by
    intro c rho
    unfold namedApplyKraus
    simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  map_pos := fun rho hrho => namedApplyKraus_posSemidef K rho hrho
  trace_preserving := fun rho => namedKraus_trace K rho htp

def namedChannelCompose {ι : Type*} [Fintype ι]
    (after before : NamedFiniteChannel ι) : NamedFiniteChannel ι where
  toFun := fun rho => after (before rho)
  map_add := by intro rho sig; rw [before.map_add, after.map_add]
  map_smul := by intro c rho; rw [before.map_smul, after.map_smul]
  map_pos := fun rho h => after.map_pos _ (before.map_pos rho h)
  trace_preserving := fun rho =>
    (after.trace_preserving _).trans (before.trace_preserving rho)

/-- A bundled named channel transports the complete finite density invariant. -/
theorem namedFiniteChannel_isDensity {ι : Type*} [Fintype ι]
    (C : NamedFiniteChannel ι) (rho : NamedState ι)
    (hrho : IsNamedDensity rho) :
    IsNamedDensity (C rho) := by
  have hpos := C.map_pos rho hrho.2.1
  refine ⟨hpos.isHermitian, hpos, ?_⟩
  exact (C.trace_preserving rho).trans hrho.2.2

/-- A Kraus completeness proof is enough to build a named CPTP channel. -/
theorem namedChannelFromKraus_isDensity {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (K : κ → NamedState ι)
    (htp : (∑ k, Matrix.conjTranspose (K k) * K k) = 1)
    (rho : NamedState ι) (hrho : IsNamedDensity rho) :
    IsNamedDensity (namedChannelFromKraus K htp rho) := by
  exact namedFiniteChannel_isDensity (namedChannelFromKraus K htp) rho hrho

/-- The singleton identity Kraus family is a reusable named channel witness. -/
noncomputable def namedIdentityKrausChannel {ι : Type*} [Fintype ι] [DecidableEq ι] :
    NamedFiniteChannel ι :=
  namedChannelFromKraus (fun _ : Unit => (1 : NamedState ι)) (by simp)

@[simp] theorem namedIdentityKrausChannel_apply {ι : Type*} [Fintype ι]
    [DecidableEq ι] (rho : NamedState ι) :
    namedIdentityKrausChannel rho = rho := by
  unfold namedIdentityKrausChannel namedChannelFromKraus namedApplyKraus
  simp

theorem namedChannelCompose_isDensity {ι : Type*} [Fintype ι]
    (after before : NamedFiniteChannel ι) (rho : NamedState ι)
  (hrho : IsNamedDensity rho) :
    IsNamedDensity (namedChannelCompose after before rho) := by
  change IsNamedDensity (after (before rho))
  have hpos := after.map_pos _ (before.map_pos rho hrho.2.1)
  refine ⟨hpos.isHermitian, hpos, ?_⟩
  exact (namedChannelCompose after before).trace_preserving rho |>.trans hrho.2.2

end LeanPhy.Quantum
