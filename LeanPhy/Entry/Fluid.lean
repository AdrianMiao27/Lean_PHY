import LeanPhy.Entry.Classical
import LeanPhy.Mathematics.FiniteDivergence

/-!
# Fluid and plasma entry point

This profile exposes finite-volume and lattice conservation contracts using
the same incidence algebra used by gauge currents and network transport.
Vorticity is represented by the discrete exterior derivative in the classical
profile.  Navier--Stokes existence, closures, kinetic limits and continuum
boundary estimates remain explicit analysis obligations.
-/

namespace LeanPhy.Fluid

abbrev ConservationCertificate {V E A : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [AddCommGroup A]
    (tail head : E → V) (current : E → A) (source : V → A) : Prop :=
  LeanPhy.Mathematics.FiniteDivergence.ConservationCertificate
    tail head current source

abbrev Vorticity {n : Nat} {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin n → LeanPhy.Mathematics.PhysicsDerivation R A)
    (velocity : LeanPhy.Mathematics.Form1 n A) :
    LeanPhy.Mathematics.Form2 n A :=
  LeanPhy.Classical.vorticity D velocity

theorem closed_total_source_zero {V E A : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [AddCommGroup A]
    {tail head : E → V} {current : E → A} {source : V → A}
    (h : ConservationCertificate tail head current source) :
    ∑ v, source v = 0 :=
  LeanPhy.Mathematics.FiniteDivergence.ConservationCertificate.total_source_zero h

end LeanPhy.Fluid
