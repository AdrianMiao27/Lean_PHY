import LeanPhy.QuantumInfo.TypedChannel
import LeanPhy.Mathematics.FiniteProcess
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite completely-positive trace-preserving maps

`TypedKrausChannel` is the constructive operator-sum representation used by
most finite models.  Research code also needs to pass around a channel after
forgetting its Kraus presentation: a coarse graining, a measurement
post-processing map, or a map imported from another finite formalisation may
be known to be CPTP without exposing its individual operators.  This module
provides that abstract bundle.

The ancillary extension is defined entrywise on finite block matrices.  Thus
complete positivity is a proposition carried by the map itself, rather than a
comment or a runtime flag.  The API remains finite-dimensional; trace-class
and infinite-dimensional operator-algebraic versions are separate obligations.
-/

namespace LeanPhy.QuantumInfo

open LeanPhy.Quantum
open scoped BigOperators Matrix ComplexOrder

/-! ## Finite ancillary extension -/

/-- Apply a finite linear map independently to every matrix block indexed by
an ancillary label.  For `rho : (Fin m × ι)² → ℂ`, each `(a,b)` block is an
`ι × ι` matrix and the result is a `κ × κ` block. -/
def ancillaExtend {ι κ : Type*} [Fintype ι] [Fintype κ] (m : Nat)
    (Φ : Matrix ι ι ℂ → Matrix κ κ ℂ)
    (rho : Matrix (Fin m × ι) (Fin m × ι) ℂ) :
    Matrix (Fin m × κ) (Fin m × κ) ℂ :=
  fun a b => Φ (fun i j => rho (a.1, i) (b.1, j)) a.2 b.2

@[simp] theorem ancillaExtend_id {ι : Type*} [Fintype ι] (m : Nat)
    (rho : Matrix (Fin m × ι) (Fin m × ι) ℂ) :
    ancillaExtend m (fun x => x) rho = rho := by
  rfl

theorem ancillaExtend_comp
    {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (m : Nat) (after : Matrix κ κ ℂ → Matrix μ μ ℂ)
    (before : Matrix ι ι ℂ → Matrix κ κ ℂ)
    (rho : Matrix (Fin m × ι) (Fin m × ι) ℂ) :
    ancillaExtend m (fun x => after (before x)) rho =
      ancillaExtend m after (ancillaExtend m before rho) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rfl

/-! ## Abstract finite CPTP bundle -/

/-- A completely-positive trace-preserving map between finite matrix spaces.

The fields deliberately mirror the hypotheses that are often scattered across
physics derivations.  Once a value is constructed, composition and state
transport cannot forget any of them. -/
structure FiniteCPTPMap (ι κ : Type*) [Fintype ι] [Fintype κ] where
  toFun : Matrix ι ι ℂ → Matrix κ κ ℂ
  map_add : ∀ rho sig, toFun (rho + sig) = toFun rho + toFun sig
  map_smul : ∀ (c : ℂ) rho, toFun (c • rho) = c • toFun rho
  map_pos : ∀ rho, rho.PosSemidef → (toFun rho).PosSemidef
  trace_preserving : ∀ rho, Matrix.trace (toFun rho) = Matrix.trace rho
  completely_positive : ∀ (m : Nat)
    (rho : Matrix (Fin m × ι) (Fin m × ι) ℂ),
    rho.PosSemidef → (ancillaExtend m toFun rho).PosSemidef

instance {ι κ : Type*} [Fintype ι] [Fintype κ] :
    CoeFun (FiniteCPTPMap ι κ) (fun _ => Matrix ι ι ℂ → Matrix κ κ ℂ) :=
  ⟨FiniteCPTPMap.toFun⟩

theorem FiniteCPTPMap.map_isFiniteDensity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : FiniteCPTPMap ι κ) (rho : Matrix ι ι ℂ)
    (hrho : IsFiniteDensity rho) :
    IsFiniteDensity (C rho) := by
  have hpos : (C rho).PosSemidef := C.map_pos rho hrho.2.1
  refine ⟨hpos.isHermitian, hpos, ?_⟩
  exact (C.trace_preserving rho).trans hrho.2.2

/- A CPTP map is a proof-preserving state map once its source and target are
   restricted to finite density matrices.  This adapter is intentionally
   separate from the raw matrix map: callers cannot accidentally compose a
   channel while dropping the density invariant. -/
def FiniteCPTPMap.toStateMap
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : FiniteCPTPMap ι κ) :
    LeanPhy.Mathematics.StateMap
      (Matrix ι ι ℂ) (Matrix κ κ ℂ)
      IsFiniteDensity IsFiniteDensity where
  toFun := C.toFun
  preserves := fun rho hrho => C.map_isFiniteDensity rho hrho

/-! ## Identity and composition -/

def FiniteCPTPMap.identity {ι : Type*} [Fintype ι] : FiniteCPTPMap ι ι where
  toFun := fun rho => rho
  map_add := by intro rho sig; rfl
  map_smul := by intro c rho; rfl
  map_pos := by intro rho h; exact h
  trace_preserving := by intro rho; rfl
  completely_positive := by
    intro m rho h
    simpa only [ancillaExtend_id] using h

def FiniteCPTPMap.compose
    {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (after : FiniteCPTPMap κ μ) (before : FiniteCPTPMap ι κ) :
    FiniteCPTPMap ι μ where
  toFun := fun rho => after (before rho)
  map_add := by
    intro rho sig
    rw [before.map_add, after.map_add]
  map_smul := by
    intro c rho
    rw [before.map_smul, after.map_smul]
  map_pos := by
    intro rho h
    exact after.map_pos _ (before.map_pos rho h)
  trace_preserving := by
    intro rho
    exact (after.trace_preserving _).trans (before.trace_preserving rho)
  completely_positive := by
    intro m rho h
    have hBefore := before.completely_positive m rho h
    have hAfter := after.completely_positive m (ancillaExtend m before rho) hBefore
    rw [ancillaExtend_comp]
    exact hAfter

@[simp] theorem FiniteCPTPMap.compose_apply
    {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (after : FiniteCPTPMap κ μ) (before : FiniteCPTPMap ι κ)
    (rho : Matrix ι ι ℂ) :
    after.compose before rho = after (before rho) := rfl

@[simp] theorem FiniteCPTPMap.compose_identity_left
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : FiniteCPTPMap ι κ) (rho : Matrix ι ι ℂ) :
    (C.compose FiniteCPTPMap.identity) rho = C rho := by
  rfl

@[simp] theorem FiniteCPTPMap.compose_identity_right
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : FiniteCPTPMap ι κ) (rho : Matrix ι ι ℂ) :
    (FiniteCPTPMap.identity.compose C) rho = C rho := by
  rfl

/-! ## A proof-producing constructor for an arbitrary finite map -/

/-- Construct the abstract bundle when a research development already has a
finite map and explicit certificates for its four invariants.  The complete
positivity argument is intentionally a parameter: this keeps the boundary
honest for maps imported from a CAS or another formalisation, while Kraus
models can prove it using their operator-sum lemmas. -/
def FiniteCPTPMap.ofCertificates
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Φ : Matrix ι ι ℂ → Matrix κ κ ℂ)
    (hadd : ∀ rho sig, Φ (rho + sig) = Φ rho + Φ sig)
    (hsmul : ∀ (c : ℂ) rho, Φ (c • rho) = c • Φ rho)
    (hpos : ∀ rho, rho.PosSemidef → (Φ rho).PosSemidef)
    (htrace : ∀ rho, Matrix.trace (Φ rho) = Matrix.trace rho)
    (hcp : ∀ (m : Nat) (rho : Matrix (Fin m × ι) (Fin m × ι) ℂ),
      rho.PosSemidef → (ancillaExtend m Φ rho).PosSemidef) :
    FiniteCPTPMap ι κ :=
  { toFun := Φ
    map_add := hadd
    map_smul := hsmul
    map_pos := hpos
    trace_preserving := htrace
    completely_positive := hcp }

/-! ## Regression facts -/

example {ι : Type*} [Fintype ι]
    (rho : Matrix (Fin 0 × ι) (Fin 0 × ι) ℂ)
    (hrho : rho.PosSemidef) :
    (ancillaExtend 0 (FiniteCPTPMap.identity (ι := ι)) rho).PosSemidef := by
  simpa [FiniteCPTPMap.identity] using hrho

example {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : FiniteCPTPMap ι κ) (rho : Matrix ι ι ℂ)
    (hrho : IsFiniteDensity rho) :
    IsFiniteDensity (C rho) :=
  C.map_isFiniteDensity rho hrho

end LeanPhy.QuantumInfo
