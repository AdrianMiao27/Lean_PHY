import LeanPhy.Mathematics.DiscreteCochain

/-!
# Finite integer winding/flux certificates

An integer lift of a phase, flux or circulation is often the part that is
safe to compute before invoking topology or analysis.  This module records
that lift explicitly.  A `WindingCertificate` says that a finite cyclic sum
of integer increments equals a claimed integer.  Gauge shifts are integer
coboundaries and telescope by the permutation theorem from `DiscreteCochain`.

The name is deliberately qualified as *finite*: no winding-number theorem,
Chern integral, continuum homotopy class or quantisation statement is hidden
here.  A physical adapter must provide the lift and the mesh hypotheses that
connect it to those analytic/topological objects.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

namespace DiscreteCochain

universe u

variable {V : Type u} [Fintype V]

/-- Integer increments on a finite cycle. -/
def integerWinding (link : V → ℤ) : ℤ := cycleSum link

@[simp] theorem integerWinding_eq (link : V → ℤ) :
    integerWinding link = ∑ x, link x := rfl

/-- An integer gauge coboundary on the cycle. -/
def integerGauge (g link : V → ℤ) (step : Equiv.Perm V) : V → ℤ :=
  cycleGauge g link step

theorem integerWinding_gauge_invariant (g link : V → ℤ) (step : Equiv.Perm V) :
    integerWinding (integerGauge g link step) = integerWinding link := by
  exact cycleGauge_sum_invariant g link step

/-- A checked claim that a finite integer lift has winding/flux `w`. -/
structure WindingCertificate (link : V → ℤ) (step : Equiv.Perm V) (w : ℤ) : Prop where
  value : integerWinding link = w

namespace WindingCertificate

theorem gauge_invariant {g link : V → ℤ} {step : Equiv.Perm V} {w : ℤ}
    (h : WindingCertificate link step w) :
    WindingCertificate (integerGauge g link step) step w := by
  refine ⟨?_⟩
  rw [integerWinding_gauge_invariant]
  exact h.value

theorem of_eq {link : V → ℤ} {step : Equiv.Perm V} {w : ℤ}
    (h : integerWinding link = w) : WindingCertificate link step w :=
  ⟨h⟩

end WindingCertificate

end DiscreteCochain

end LeanPhy.Mathematics

/-! Domain vocabulary for the finite integer certificate. -/

namespace LeanPhy

namespace GaugeTheory

abbrev IntegerFluxCertificate {V : Type} [Fintype V]
    (link : V → ℤ) (step : Equiv.Perm V) (flux : ℤ) : Prop :=
  Mathematics.DiscreteCochain.WindingCertificate link step flux

end GaugeTheory

namespace Condensed

abbrev FiniteWindingCertificate {V : Type} [Fintype V]
    (link : V → ℤ) (step : Equiv.Perm V) (winding : ℤ) : Prop :=
  Mathematics.DiscreteCochain.WindingCertificate link step winding

end Condensed

namespace Classical

abbrev IntegerCirculationCertificate {V : Type} [Fintype V]
    (link : V → ℤ) (step : Equiv.Perm V) (circulation : ℤ) : Prop :=
  Mathematics.DiscreteCochain.WindingCertificate link step circulation

end Classical

end LeanPhy
