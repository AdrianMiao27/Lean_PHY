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
import LeanPhy.Mathematics.CertifiedElimination
import LeanPhy.Quantum.DynamicalResponse
import LeanPhy.FieldTheory.FiniteFermion
import LeanPhy.FieldTheory.FermionBasis
import LeanPhy.FieldTheory.PhysicalMajorana
import LeanPhy.FieldTheory.HeavyFieldElimination
import LeanPhy.FieldTheory.FiniteActionResponse
import LeanPhy.FieldTheory.FiniteSourceResponse
import LeanPhy.FieldTheory.PolynomialAction
import LeanPhy.FieldTheory.VariationalResidual
import LeanPhy.Minimal
import LeanPhy.FieldTheory.CCR
import LeanPhy.FieldTheory.Fock
import LeanPhy.FieldTheory.MultiMode
import LeanPhy.FieldTheory.MultiCAR
import LeanPhy.FieldTheory.Wick
import LeanPhy.FieldTheory.FermionicWick
import LeanPhy.FieldTheory.FermionicQuasiFree
import LeanPhy.FieldTheory.FermionVacuum
import LeanPhy.FieldTheory.Pairing
import LeanPhy.FieldTheory.MultiWick

/-! Finite-mode quantum field theory entry point.

This profile exposes CCR/CAR, constructed finite fermion occupation spaces,
abstract bosonic ladder algebra and Wick contraction kernels while keeping the
continuum distributional and renormalisation layers explicit. -/
