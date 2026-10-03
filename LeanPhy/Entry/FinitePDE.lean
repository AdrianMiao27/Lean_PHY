import LeanPhy.Minimal
import LeanPhy.Mathematics.CertifiedResidual
import LeanPhy.Mathematics.ConservationResidual
import LeanPhy.Mathematics.FiniteDivergence
import LeanPhy.Mathematics.FiniteEvolution
import LeanPhy.Mathematics.FiniteEnergy
import LeanPhy.Mathematics.FiniteParabolic
import LeanPhy.Mathematics.FiniteDrivenParabolic
import LeanPhy.Mathematics.FiniteElliptic
import LeanPhy.Mathematics.FiniteFourier
import LeanPhy.Mathematics.ApproximationBridge
import LeanPhy.Mathematics.AdditiveLeftInverseCertificate

/-! Finite PDE and numerical-certificate entry point.

Residual, stability, energy and approximation contracts are available for
finite-difference/finite-element adapters.  Mesh convergence and continuum
well-posedness remain explicit obligations. -/
