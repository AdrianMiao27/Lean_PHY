import LeanPhy.Minimal
import LeanPhy.Quantum.Basic
import LeanPhy.Quantum.Pauli
import LeanPhy.Quantum.Density
import LeanPhy.Quantum.FiniteDensity
import LeanPhy.Quantum.Unitary
import LeanPhy.Quantum.HamiltonianFlow
import LeanPhy.Quantum.PartialTrace
import LeanPhy.QuantumInfo.Channel
import LeanPhy.QuantumInfo.KrausBundle
import LeanPhy.QuantumInfo.CPTP
import LeanPhy.QuantumInfo.Model
import LeanPhy.QuantumInfo.Measurement
import LeanPhy.QuantumInfo.POVM
import LeanPhy.Mathematics.Hilbert

/-! Quantum mechanics entry point.  It includes finite matrix objects and the
bounded Hilbert-space bridge; unbounded domains and continuous spectra remain
explicit analytic obligations. -/
