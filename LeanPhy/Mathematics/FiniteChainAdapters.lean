import LeanPhy.Mathematics.FiniteChainComplex
import LeanPhy.Mathematics.FiniteDivergence
import Mathlib.Tactic

/-!
# Adapters from finite chain complexes to graph currents

This module connects the incidence-table API with the existing finite
divergence contract.  A directed graph is the one-dimensional truncation of a
chain complex: its edge boundary is the incoming-minus-outgoing incidence
matrix, while the two-chain type is empty.  The adapter is useful when a
network, lattice current, hopping model or finite-volume scheme should move
between chain language and conservation-certificate language without copying
the finite-sum proof.

The construction is finite and algebraic.  It does not add a boundary flux,
continuum divergence theorem, topology or dynamics.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

universe u v w

namespace FiniteChainAdapters

variable {V : Type u} {E : Type v} {A : Type w}

/-- The signed incidence coefficient of an oriented edge at a vertex. -/
def incidenceBoundary10 [DecidableEq V]
    (tail head : E → V) (e : E) (v : V) : ℤ :=
  (if head e = v then 1 else 0) + (if tail e = v then -1 else 0)

/-- A graph as a chain complex with no two-cells.  The coefficient ring is
kept explicit so the same incidence table works for integer, real or complex
currents. -/
def graphChainComplex [Fintype V] [Fintype E] [DecidableEq V]
    [CommRing A] (tail head : E → V) :
    FiniteChainComplex V E PEmpty A where
  boundary10 := fun e v =>
    (if head e = v then 1 else 0) + (if tail e = v then -1 else 0)
  boundary21 := fun f => PEmpty.elim f
  boundary_sq := by
    intro f
    exact PEmpty.elim f

@[simp] theorem graphChainComplex_boundary10 [Fintype V] [Fintype E]
    [DecidableEq V] [CommRing A] (tail head : E → V) (e : E) (v : V) :
    (graphChainComplex tail head).boundary10 e v =
      (if head e = v then 1 else 0) + (if tail e = v then -1 else 0) := rfl

/-- The graph chain boundary is definitionally the finite divergence. -/
theorem graph_boundary1_eq_divergence [Fintype V] [Fintype E]
    [DecidableEq V] [CommRing A] (tail head : E → V) (current : E → A) :
    (graphChainComplex tail head).boundary1 current =
      FiniteDivergence.divergence tail head current := by
  funext v
  unfold FiniteChainComplex.boundary1 graphChainComplex
  unfold FiniteDivergence.divergence
  change (∑ e, current e *
      ((if head e = v then 1 else 0) + (if tail e = v then -1 else 0))) = _
  calc
    (∑ e, current e *
        ((if head e = v then 1 else 0) + (if tail e = v then -1 else 0))) =
        (∑ e, current e * (if head e = v then 1 else 0)) +
          (∑ e, current e * (if tail e = v then -1 else 0)) := by
            simp only [mul_add, Finset.sum_add_distrib]
    _ = (∑ e, if head e = v then current e else 0) +
          (∑ e, if tail e = v then -current e else 0) := by
            congr 1
            · apply Finset.sum_congr rfl
              intro e he
              by_cases hh : head e = v <;> simp [hh]
            · apply Finset.sum_congr rfl
              intro e he
              by_cases ht : tail e = v <;> simp [ht]
    _ = (∑ e, if head e = v then current e else 0) -
          (∑ e, if tail e = v then current e else 0) := by
            have hneg : (∑ e, if tail e = v then -current e else 0) =
                -(∑ e, if tail e = v then current e else 0) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro e he
              by_cases ht : tail e = v <;> simp [ht]
            rw [hneg]
            simp only [sub_eq_add_neg]

/-- Any conservation certificate for a graph current can be consumed as the
corresponding zero-boundary statement by the chain-complex API. -/
theorem graph_conservation_boundary_eq_source [Fintype V] [Fintype E]
    [DecidableEq V] [CommRing A] (tail head : E → V) (current : E → A)
    (source : V → A)
    (h : FiniteDivergence.ConservationCertificate tail head current source) :
    (graphChainComplex tail head).boundary1 current = source := by
  rw [graph_boundary1_eq_divergence]
  exact funext h.equation

end FiniteChainAdapters

/-! Domain names for the same graph-to-chain bridge. -/

namespace GaugeTheory
abbrev GraphChainComplex (V E A : Type*) [Fintype V] [Fintype E]
    [DecidableEq V] [CommRing A] (tail head : E → V) :=
  FiniteChainAdapters.graphChainComplex (A := A) tail head
end GaugeTheory

namespace Condensed
abbrev HoppingChainComplex (V E A : Type*) [Fintype V] [Fintype E]
    [DecidableEq V] [CommRing A] (tail head : E → V) :=
  FiniteChainAdapters.graphChainComplex (A := A) tail head
end Condensed

namespace Classical
abbrev FiniteVolumeChainComplex (V E A : Type*) [Fintype V] [Fintype E]
    [DecidableEq V] [CommRing A] (tail head : E → V) :=
  FiniteChainAdapters.graphChainComplex (A := A) tail head
end Classical

namespace StatMech
abbrev NetworkGraphChainComplex (V E A : Type*) [Fintype V] [Fintype E]
    [DecidableEq V] [CommRing A] (tail head : E → V) :=
  FiniteChainAdapters.graphChainComplex (A := A) tail head
end StatMech

end LeanPhy.Mathematics
