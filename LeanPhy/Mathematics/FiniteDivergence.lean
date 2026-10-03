import Mathlib.Tactic

/-!
# Finite divergence and conservation certificates

Finite-volume schemes, lattice gauge models, network transport, kinetic
discretisations, and measurement post-processing all use the same local law:
the incoming current minus the outgoing current equals a source.  On a closed
finite graph the sum of that source over all vertices must vanish, because
every internal edge appears once with each orientation.

This module records only that finite incidence algebra.  It does not assume a
metric, a continuum divergence theorem, differentiability, a boundary
condition, positivity, or a physical interpretation of the current.  A model
that has external boundary edges must include them explicitly in its vertex or
edge types; the zero-total theorem then applies to the closed part only.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

universe u v w

namespace FiniteDivergence

variable {V : Type u} {E : Type v} {A : Type w}

/-- Incoming minus outgoing current at a vertex.  `tail` and `head` give the
orientation of every finite internal edge. -/
def divergence [Fintype E] [Fintype V] [DecidableEq V]
    [AddCommGroup A] (tail head : E → V) (current : E → A) (v : V) : A :=
  (∑ e, if head e = v then current e else 0) -
    (∑ e, if tail e = v then current e else 0)

@[simp] theorem divergence_apply [Fintype E] [Fintype V] [DecidableEq V]
    [AddCommGroup A] (tail head : E → V) (current : E → A) (v : V) :
    divergence tail head current v =
      (∑ e, if head e = v then current e else 0) -
        (∑ e, if tail e = v then current e else 0) := rfl

/-- Every finite internal edge contributes once positively and once
negatively, so the total divergence is zero. -/
theorem total_divergence_zero [Fintype E] [Fintype V] [DecidableEq V]
    [AddCommGroup A] (tail head : E → V) (current : E → A) :
    ∑ v, divergence tail head current v = 0 := by
  unfold divergence
  calc
    (∑ v : V, ((∑ e : E, if head e = v then current e else 0) -
        (∑ e : E, if tail e = v then current e else 0))) =
        (∑ v : V, ∑ e : E, if head e = v then current e else 0) -
          (∑ v : V, ∑ e : E, if tail e = v then current e else 0) := by
            rw [Finset.sum_sub_distrib]
    _ = (∑ e, current e) - (∑ e, current e) := by
      congr 1
      · rw [Finset.sum_comm]
        simp
      · rw [Finset.sum_comm]
        simp
    _ = 0 := sub_self _

/-- A local continuity equation is a certificate that a current has the given
source field.  It is a proposition, so a downstream theorem cannot silently
replace the source by an unverified expression. -/
structure ConservationCertificate [Fintype E] [Fintype V] [DecidableEq V]
    [AddCommGroup A] (tail head : E → V) (current : E → A) (source : V → A) : Prop where
  equation : ∀ v, divergence tail head current v = source v

theorem ConservationCertificate.total_source_zero
    [Fintype E] [Fintype V] [DecidableEq V] [AddCommGroup A]
    {tail head : E → V} {current : E → A} {source : V → A}
    (h : ConservationCertificate tail head current source) :
    ∑ v, source v = 0 := by
  calc
    (∑ v, source v) = ∑ v, divergence tail head current v := by
      exact Finset.sum_congr rfl (fun v _ => (h.equation v).symm)
    _ = 0 := total_divergence_zero tail head current

theorem ConservationCertificate.of_zero_source
    [Fintype E] [Fintype V] [DecidableEq V] [AddCommGroup A]
    {tail head : E → V} {current : E → A}
    (hlocal : ∀ v, divergence tail head current v = 0) :
    ConservationCertificate tail head current (fun _ => 0) := by
  exact ⟨fun v => by simpa using hlocal v⟩

/-- The residual of a discrete continuity equation.  Its radius-zero form is
useful for exact lattice identities; a numerical scheme may attach a separate
`ErrorCertificate` to this function. -/
def residual [Fintype E] [Fintype V] [DecidableEq V]
    [AddCommGroup A] (tail head : E → V) (current : E → A) (source : V → A)
    (v : V) : A := divergence tail head current v - source v

theorem residual_zero_iff [Fintype E] [Fintype V] [DecidableEq V]
    [AddCommGroup A] (tail head : E → V) (current : E → A) (source : V → A) :
    (∀ v, residual tail head current source v = 0) ↔
      ConservationCertificate tail head current source := by
  constructor
  · intro h
    refine ⟨fun v => ?_⟩
    have hv := h v
    unfold residual at hv
    exact sub_eq_zero.mp hv
  · intro h v
    unfold residual
    rw [h.equation v]
    simp

end FiniteDivergence

/-! Domain vocabulary aliases.  They preserve the same finite semantics while
allowing a paper-facing model to keep its physical name. -/

end LeanPhy.Mathematics

namespace LeanPhy

namespace GaugeTheory
abbrev LatticeCurrentConservation {V E A : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [AddCommGroup A]
    (tail head : E → V) (current : E → A) (source : V → A) : Prop :=
  Mathematics.FiniteDivergence.ConservationCertificate tail head current source
end GaugeTheory

namespace Condensed
abbrev HoppingCurrentConservation {V E A : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [AddCommGroup A]
    (tail head : E → V) (current : E → A) (source : V → A) : Prop :=
  Mathematics.FiniteDivergence.ConservationCertificate tail head current source
end Condensed

namespace Classical
abbrev FiniteVolumeConservation {V E A : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [AddCommGroup A]
    (tail head : E → V) (current : E → A) (source : V → A) : Prop :=
  Mathematics.FiniteDivergence.ConservationCertificate tail head current source
end Classical

namespace StatMech
abbrev ProbabilityCurrentConservation {V E A : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [AddCommGroup A]
    (tail head : E → V) (current : E → A) (source : V → A) : Prop :=
  Mathematics.FiniteDivergence.ConservationCertificate tail head current source
end StatMech

namespace FieldTheory
abbrev DiscreteNoetherCurrent {V E A : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [AddCommGroup A]
    (tail head : E → V) (current : E → A) (source : V → A) : Prop :=
  Mathematics.FiniteDivergence.ConservationCertificate tail head current source
end FieldTheory

namespace QuantumInfo
abbrev OutcomeFlowConservation {V E A : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [AddCommGroup A]
    (tail head : E → V) (current : E → A) (source : V → A) : Prop :=
  Mathematics.FiniteDivergence.ConservationCertificate tail head current source
end QuantumInfo

end LeanPhy
