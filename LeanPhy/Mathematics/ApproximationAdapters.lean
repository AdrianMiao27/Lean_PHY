import LeanPhy.Mathematics.ApproximationBridge

/-!
# Domain names for the shared approximation certificate

The certificate itself is deliberately domain neutral.  These aliases make
the same checked object discoverable from the vocabulary used in different
subfields.  They carry no hidden convergence theorem: each exact/surrogate
pair still has to provide an explicit bound.
-/

namespace LeanPhy

namespace Quantum

abbrev FiniteOperatorLeftInverse {X Y : Type} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] (A : X →+ Y) :=
  Mathematics.AdditiveLeftInverseCertificate A

abbrev StateTruncation {X : Type} [PseudoMetricSpace X]
    (exact surrogate : X) (ε : ℝ) : Prop :=
  Mathematics.FiniteApproximation exact surrogate ε

abbrev OperatorTruncation {X : Type} [PseudoMetricSpace X]
    (exact surrogate : X) (ε : ℝ) : Prop :=
  Mathematics.FiniteApproximation exact surrogate ε

end Quantum

namespace FieldTheory

abbrev FiniteModeLeftInverse {X Y : Type} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] (A : X →+ Y) :=
  Mathematics.AdditiveLeftInverseCertificate A

abbrev ModeTruncation {X : Type} [PseudoMetricSpace X]
    (exact surrogate : X) (ε : ℝ) : Prop :=
  Mathematics.FiniteApproximation exact surrogate ε

abbrev WickResidual {R : Type} [PseudoMetricSpace R] [Zero R]
    (residual : R) (ε : ℝ) : Prop :=
  Mathematics.ErrorCertificate.ResidualCertificate residual ε

end FieldTheory

namespace GaugeTheory

abbrev FiniteLatticeLeftInverse {X Y : Type} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] (A : X →+ Y) :=
  Mathematics.AdditiveLeftInverseCertificate A

abbrev LatticeDiscretization {X : Type} [PseudoMetricSpace X]
    (exact surrogate : X) (ε : ℝ) : Prop :=
  Mathematics.FiniteApproximation exact surrogate ε

abbrev GaugeResidual {R : Type} [PseudoMetricSpace R] [Zero R]
    (residual : R) (ε : ℝ) : Prop :=
  Mathematics.ErrorCertificate.ResidualCertificate residual ε

end GaugeTheory

namespace Condensed

abbrev FiniteBandLeftInverse {X Y : Type} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] (A : X →+ Y) :=
  Mathematics.AdditiveLeftInverseCertificate A

abbrev BandTruncation {X : Type} [PseudoMetricSpace X]
    (exact surrogate : X) (ε : ℝ) : Prop :=
  Mathematics.FiniteApproximation exact surrogate ε

abbrev FiniteLatticeApproximation {X : Type} [PseudoMetricSpace X]
    (exact surrogate : X) (ε : ℝ) : Prop :=
  Mathematics.FiniteApproximation exact surrogate ε

end Condensed

namespace StatMech

abbrev FiniteTransferLeftInverse {X Y : Type} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] (A : X →+ Y) :=
  Mathematics.AdditiveLeftInverseCertificate A

abbrev FiniteVolumeApproximation {X : Type} [PseudoMetricSpace X]
    (exact surrogate : X) (ε : ℝ) : Prop :=
  Mathematics.FiniteApproximation exact surrogate ε

abbrev ThermodynamicResidual {R : Type} [PseudoMetricSpace R] [Zero R]
    (residual : R) (ε : ℝ) : Prop :=
  Mathematics.ErrorCertificate.ResidualCertificate residual ε

end StatMech

namespace Classical

abbrev FiniteDynamicsLeftInverse {X Y : Type} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] (A : X →+ Y) :=
  Mathematics.AdditiveLeftInverseCertificate A

abbrev DiscretizationCertificate {X : Type} [PseudoMetricSpace X]
    (exact surrogate : X) (ε : ℝ) : Prop :=
  Mathematics.FiniteApproximation exact surrogate ε

abbrev ODEResidual {R : Type} [PseudoMetricSpace R] [Zero R]
    (residual : R) (ε : ℝ) : Prop :=
  Mathematics.ErrorCertificate.ResidualCertificate residual ε

end Classical

end LeanPhy
