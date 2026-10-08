import LeanPhy.Quantum.DrivenPulse
import LeanPhy.FieldTheory.HeavyFieldInterval
import LeanPhy.FieldTheory.FermionVacuumWick
import LeanPhy.FieldTheory.FermionUnitaryWick
import LeanPhy.StatMech.GibbsCertificate
import LeanPhy.FieldTheory.RedefinitionVariation
import LeanPhy.FieldTheory.EulerTransport
import LeanPhy.StatMech.FeedbackCertificate
import LeanPhy.StatMech.MeanFieldFunctional
import LeanPhy.FieldTheory.InteractingFermion
import LeanPhy.FieldTheory.FermionEmbedding
import LeanPhy.FieldTheory.IntervalAction
import LeanPhy.Quantum.CertifiedResolvent
import LeanPhy.Quantum.ThermalPerturbation
import LeanPhy.FieldTheory.FiniteFermion
import LeanPhy.FieldTheory.FermionicQuasiFree
import LeanPhy.FieldTheory.FermionVacuum
import LeanPhy.FieldTheory.FermionBasis
import LeanPhy.FieldTheory.PhysicalMajorana
import LeanPhy.Condensed.ComplexPairing
import LeanPhy.Mathematics.FormalBlockElimination
import LeanPhy.Mathematics.EliminationError
import LeanPhy.Quantum.EffectiveHamiltonian
import LeanPhy.Quantum.FiniteThermalState
import LeanPhy.StatMech.GibbsResponse
import LeanPhy.StatMech.ResponseBound
import LeanPhy.FieldTheory.PolynomialAction
import LeanPhy.FieldTheory.VariationalResidual
import LeanPhy.Minimal
import LeanPhy.Condensed.Lattice
import LeanPhy.Condensed.Fermion
import LeanPhy.Condensed.Hubbard
import LeanPhy.Condensed.Majorana
import LeanPhy.Condensed.BCS
import LeanPhy.Condensed.Topological
import LeanPhy.Condensed.Berry
import LeanPhy.Condensed.JordanWigner

/-! Condensed-matter entry point.

Finite lattice, fermion, BdG, Berry and Jordan--Wigner interfaces are exposed
as ordinary Lean modules; thermodynamic and continuum limits remain explicit. -/
