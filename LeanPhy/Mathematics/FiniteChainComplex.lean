import Mathlib.Tactic

/-!
# Finite chain complexes and discrete Stokes identities

This module supplies the finite incidence algebra behind lattice gauge fields,
Berry/Chern meshes, finite-element boundary operators, network circulation and
discrete fluid models.  A chain complex is represented by two finite boundary
tables whose composite is explicitly zero.  The transposed finite sums give
the corresponding coboundary identity, a chain/ cochain pairing, and a
discrete Stokes theorem.

No manifold, orientation atlas, integration, homology computation or
quantisation theorem is inferred.  Those layers must provide their own finite
labels and hypotheses.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

universe u v w z

/-- Finite boundary tables `C₂ → C₁ → A` and `C₁ → C₀ → A` with the explicit
boundary-of-boundary cancellation law. -/
structure FiniteChainComplex (C0 : Type u) (C1 : Type v) (C2 : Type w)
    (A : Type z) [Fintype C0] [Fintype C1] [Fintype C2] [CommRing A] where
  boundary10 : C1 → C0 → A
  boundary21 : C2 → C1 → A
  boundary_sq : ∀ f v, ∑ e, boundary21 f e * boundary10 e v = 0

namespace FiniteChainComplex

variable {C0 : Type u} {C1 : Type v} {C2 : Type w} {A : Type z}
  [Fintype C0] [Fintype C1] [Fintype C2] [CommRing A]
  (K : FiniteChainComplex C0 C1 C2 A)

/-- Boundary of a finite one-chain. -/
def boundary1 (c : C1 → A) : C0 → A :=
  fun v => ∑ e, c e * K.boundary10 e v

/-- Boundary of a finite two-chain. -/
def boundary2 (c : C2 → A) : C1 → A :=
  fun e => ∑ f, c f * K.boundary21 f e

/-- Coboundary of a finite zero-cochain. -/
def coboundary0 (φ : C0 → A) : C1 → A :=
  fun e => ∑ v, K.boundary10 e v * φ v

/-- Coboundary of a finite one-cochain. -/
def coboundary1 (α : C1 → A) : C2 → A :=
  fun f => ∑ e, K.boundary21 f e * α e

/-- Pair a finite cochain and chain using the finite sum convention. -/
def pairing {C : Type*} [Fintype C] (cochain chain : C → A) : A :=
  ∑ c, cochain c * chain c

@[simp] theorem boundary1_apply (c : C1 → A) (v : C0) :
    K.boundary1 c v = ∑ e, c e * K.boundary10 e v := rfl

@[simp] theorem boundary2_apply (c : C2 → A) (e : C1) :
    K.boundary2 c e = ∑ f, c f * K.boundary21 f e := rfl

@[simp] theorem coboundary0_apply (φ : C0 → A) (e : C1) :
    K.coboundary0 φ e = ∑ v, K.boundary10 e v * φ v := rfl

@[simp] theorem coboundary1_apply (α : C1 → A) (f : C2) :
    K.coboundary1 α f = ∑ e, K.boundary21 f e * α e := rfl

@[simp] theorem pairing_apply {C : Type u} [Fintype C]
    (cochain chain : C → A) : pairing cochain chain = ∑ c, cochain c * chain c := rfl

/-- Boundary of a boundary vanishes by the supplied incidence law. -/
theorem boundary1_boundary2 (c : C2 → A) :
    K.boundary1 (K.boundary2 c) = 0 := by
  funext v
  unfold boundary1 boundary2
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro f hf
  calc
    (∑ x, c f * K.boundary21 f x * K.boundary10 x v) =
        c f * (∑ x, K.boundary21 f x * K.boundary10 x v) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = 0 := by rw [K.boundary_sq]; simp

/-- The dual coboundary complex also squares to zero. -/
theorem coboundary1_coboundary0 (φ : C0 → A) :
    K.coboundary1 (K.coboundary0 φ) = 0 := by
  funext f
  unfold coboundary1 coboundary0
  calc
    (∑ e, K.boundary21 f e * (∑ v, K.boundary10 e v * φ v)) =
        ∑ e, ∑ v, K.boundary21 f e * (K.boundary10 e v * φ v) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.mul_sum]
    _ = ∑ v, ∑ e, K.boundary21 f e * (K.boundary10 e v * φ v) := by
          rw [Finset.sum_comm]
    _ = ∑ v, (∑ e, K.boundary21 f e * K.boundary10 e v) * φ v := by
          apply Finset.sum_congr rfl
          intro v hv
          calc
            (∑ e, K.boundary21 f e * (K.boundary10 e v * φ v)) =
                ∑ e, (K.boundary21 f e * K.boundary10 e v) * φ v := by
                  apply Finset.sum_congr rfl
                  intro e he
                  ring
            _ = (∑ e, K.boundary21 f e * K.boundary10 e v) * φ v := by
                  rw [Finset.sum_mul]
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro v hv
          rw [K.boundary_sq]
          simp

/-- Discrete Stokes: pairing a coboundary with a chain equals pairing the
cochain with the chain boundary. -/
theorem pairing_coboundary0_boundary1
    (φ : C0 → A) (c : C1 → A) :
    pairing (K.coboundary0 φ) c = pairing φ (K.boundary1 c) := by
  unfold pairing coboundary0 boundary1
  calc
    (∑ e, (∑ v, K.boundary10 e v * φ v) * c e) =
        ∑ e, ∑ v, (K.boundary10 e v * φ v) * c e := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.sum_mul]
    _ = ∑ v, ∑ e, (K.boundary10 e v * φ v) * c e := by
          rw [Finset.sum_comm]
    _ = ∑ v, φ v * (∑ e, c e * K.boundary10 e v) := by
          apply Finset.sum_congr rfl
          intro v hv
          calc
            (∑ e, (K.boundary10 e v * φ v) * c e) =
                ∑ e, φ v * (c e * K.boundary10 e v) := by
                  apply Finset.sum_congr rfl
                  intro e he
                  ring
            _ = φ v * (∑ e, c e * K.boundary10 e v) := by
                  rw [Finset.mul_sum]

/-! ## Finite cycle/cocycle interface

These predicates are deliberately quotient-free.  They are enough to state
the algebraic part of homology/cohomology calculations while leaving quotient
construction, ranks and topological interpretation to a later layer.
-/

/-- A one-chain is a cycle when its finite boundary vanishes. -/
def IsCycle1 (c : C1 → A) : Prop := K.boundary1 c = 0

/-- A one-chain is a boundary when it is the boundary of a finite two-chain. -/
def IsBoundary1 (c : C1 → A) : Prop := ∃ b : C2 → A, K.boundary2 b = c

/-- A finite two-chain is closed when its one-boundary vanishes.  This is the
algebraic surface condition needed for a discrete flux/Chern pairing; no
three-chain or topological manifold is assumed. -/
def IsCycle2 (c : C2 → A) : Prop := K.boundary2 c = 0

/-- A one-cochain is a cocycle when its finite coboundary vanishes. -/
def IsCocycle1 (α : C1 → A) : Prop := K.coboundary1 α = 0

/-- A one-cochain is exact when it is the coboundary of a zero-cochain. -/
def IsExact1 (α : C1 → A) : Prop := ∃ φ : C0 → A, K.coboundary0 φ = α

theorem boundary_isCycle1 (b : C2 → A) : IsCycle1 K (K.boundary2 b) := by
  exact K.boundary1_boundary2 b

theorem exact_isCocycle1 (φ : C0 → A) :
    IsCocycle1 K (K.coboundary0 φ) := by
  exact K.coboundary1_coboundary0 φ

theorem boundary1_isCycle1 {c : C1 → A} (h : IsBoundary1 K c) :
    IsCycle1 K c := by
  rcases h with ⟨b, rfl⟩
  exact K.boundary1_boundary2 b

theorem exact1_isCocycle1 {α : C1 → A} (h : IsExact1 K α) :
    IsCocycle1 K α := by
  rcases h with ⟨φ, rfl⟩
  exact K.coboundary1_coboundary0 φ

/-! Degree-one Stokes pairing. -/

theorem pairing_coboundary1_boundary2
    (α : C1 → A) (c : C2 → A) :
    pairing (K.coboundary1 α) c = pairing α (K.boundary2 c) := by
  unfold pairing coboundary1 boundary2
  calc
    (∑ f, (∑ e, K.boundary21 f e * α e) * c f) =
        ∑ f, ∑ e, (K.boundary21 f e * α e) * c f := by
          apply Finset.sum_congr rfl
          intro f hf
          rw [Finset.sum_mul]
    _ = ∑ e, ∑ f, (K.boundary21 f e * α e) * c f := by
          rw [Finset.sum_comm]
    _ = ∑ e, α e * (∑ f, c f * K.boundary21 f e) := by
          apply Finset.sum_congr rfl
          intro e he
          calc
            (∑ f, (K.boundary21 f e * α e) * c f) =
                ∑ f, α e * (c f * K.boundary21 f e) := by
                  apply Finset.sum_congr rfl
                  intro f hf
                  ring
            _ = α e * (∑ f, c f * K.boundary21 f e) := by
                  rw [Finset.mul_sum]

theorem cocycle_pairing_boundary_zero
    (α : C1 → A) (c : C2 → A)
    (hcocycle : IsCocycle1 K α) :
    pairing α (K.boundary2 c) = 0 := by
  rw [← K.pairing_coboundary1_boundary2, hcocycle]
  simp [pairing]

theorem exact_pairing_cycle_zero
    (φ : C0 → A) (c : C1 → A)
    (hcycle : IsCycle1 K c) :
    pairing (K.coboundary0 φ) c = 0 := by
  change K.boundary1 c = 0 at hcycle
  rw [K.pairing_coboundary0_boundary1, hcycle]
  simp [pairing]

/-- A coboundary has zero pairing with every finite cycle. -/
theorem exact_pairing_zero
    (φ : C0 → A) (c : C1 → A)
    (hcycle : K.boundary1 c = 0) :
    pairing (K.coboundary0 φ) c = 0 := by
  rw [K.pairing_coboundary0_boundary1, hcycle]
  simp [pairing]

/-- A two-coboundary has zero pairing with every finite two-chain. -/
theorem exact_two_pairing_zero
    (φ : C0 → A) (c : C2 → A) :
    pairing (K.coboundary1 (K.coboundary0 φ)) c = 0 := by
  rw [K.coboundary1_coboundary0]
  simp [pairing]

/-! ## Closed-surface flux/Chern pairing -/

theorem coboundary1_pairing_cycle2_zero
    (α : C1 → A) (c : C2 → A)
    (hcycle : IsCycle2 K c) :
    pairing (K.coboundary1 α) c = 0 := by
  rw [K.pairing_coboundary1_boundary2, hcycle]
  simp [pairing]

theorem pairing_add_coboundary1_cycle2
    (β : C2 → A) (α : C1 → A) (c : C2 → A)
    (hcycle : IsCycle2 K c) :
    pairing (fun e => β e + K.coboundary1 α e) c = pairing β c := by
  unfold pairing
  simp only [add_mul, Finset.sum_add_distrib]
  have hzero := K.coboundary1_pairing_cycle2_zero α c hcycle
  unfold pairing at hzero
  rw [hzero]
  simp

end FiniteChainComplex

/-! Domain vocabulary for the same finite chain-complex contract. -/

namespace GaugeTheory
abbrev LatticeChainComplex (C0 C1 C2 : Type*) (A : Type*)
    [Fintype C0] [Fintype C1] [Fintype C2] [CommRing A] :=
  FiniteChainComplex C0 C1 C2 A
end GaugeTheory

namespace Condensed
abbrev BerryChainComplex (C0 C1 C2 : Type*) (A : Type*)
    [Fintype C0] [Fintype C1] [Fintype C2] [CommRing A] :=
  FiniteChainComplex C0 C1 C2 A
end Condensed

namespace Classical
abbrev FiniteElementChainComplex (C0 C1 C2 : Type*) (A : Type*)
    [Fintype C0] [Fintype C1] [Fintype C2] [CommRing A] :=
  FiniteChainComplex C0 C1 C2 A
end Classical

namespace StatMech
abbrev NetworkChainComplex (C0 C1 C2 : Type*) (A : Type*)
    [Fintype C0] [Fintype C1] [Fintype C2] [CommRing A] :=
  FiniteChainComplex C0 C1 C2 A
end StatMech

namespace GaugeTheory
abbrev ClosedFluxSurface {C0 C1 C2 A : Type*}
    [Fintype C0] [Fintype C1] [Fintype C2] [CommRing A]
    (K : FiniteChainComplex C0 C1 C2 A) :=
  FiniteChainComplex.IsCycle2 K
end GaugeTheory

namespace Condensed
abbrev ChernMeshCycle {C0 C1 C2 A : Type*}
    [Fintype C0] [Fintype C1] [Fintype C2] [CommRing A]
    (K : FiniteChainComplex C0 C1 C2 A) :=
  FiniteChainComplex.IsCycle2 K
end Condensed

namespace Classical
abbrev ClosedFiniteElementSurface {C0 C1 C2 A : Type*}
    [Fintype C0] [Fintype C1] [Fintype C2] [CommRing A]
    (K : FiniteChainComplex C0 C1 C2 A) :=
  FiniteChainComplex.IsCycle2 K
end Classical

end LeanPhy.Mathematics
