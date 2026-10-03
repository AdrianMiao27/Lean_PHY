import LeanPhy.Mathematics.Approximation

/-!
# Cross-space approximation bridges

Finite calculations and continuum statements usually live in different types:
a lattice state is a finite vector, while its reconstruction is a function,
measure or operator in a larger space.  `FiniteApproximation` deliberately
does not coerce those types implicitly.  This module supplies the explicit
bridge that a numerical or analytic adapter must provide.

The bridge is still conditional: a user supplies `decode : Y → X` and proves
the metric error after reconstruction.  The kernel then transports that error
through Lipschitz observables and composes several reconstruction stages.  No
convergence theorem is inferred from a resolution parameter or from a runtime
number.
-/

namespace LeanPhy.Mathematics

universe u v w

/-! A certificate whose surrogate has a different representation type. -/

structure CrossSpaceApproximation
    {X : Type u} {Y : Type v}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (decode : Y → X) (exact : X) (surrogate : Y) (ε : ℝ) : Prop where
  nonneg : 0 ≤ ε
  bound : dist exact (decode surrogate) ≤ ε

namespace CrossSpaceApproximation

variable {X : Type u} {Y : Type v}
  [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem toFiniteApproximation {decode : Y → X} {exact : X} {surrogate : Y}
    {ε : ℝ} (C : CrossSpaceApproximation decode exact surrogate ε) :
    FiniteApproximation exact (decode surrogate) ε :=
  ⟨C.nonneg, C.bound⟩

theorem weaken {decode : Y → X} {exact : X} {surrogate : Y}
    {ε δ : ℝ} (C : CrossSpaceApproximation decode exact surrogate ε)
    (hεδ : ε ≤ δ) :
    CrossSpaceApproximation decode exact surrogate δ :=
  ⟨C.nonneg.trans hεδ, C.bound.trans hεδ⟩

theorem symmetric {decode : Y → X} {exact : X} {surrogate : Y}
    {ε : ℝ} (C : CrossSpaceApproximation decode exact surrogate ε) :
    ErrorCertificate (decode surrogate) exact ε := by
  exact ⟨C.nonneg, by simpa [dist_comm] using C.bound⟩

/-! Applying a stable observable after reconstruction. -/

theorem map {Z : Type w} [PseudoMetricSpace Z]
    {decode : Y → X} {exact : X} {surrogate : Y}
    {f : X → Z} {L ε : ℝ}
    (hf : ErrorCertificate.LipschitzCertificate f L)
    (C : CrossSpaceApproximation decode exact surrogate ε) :
    ErrorCertificate (f exact) (f (decode surrogate)) (L * ε) := by
  exact ErrorCertificate.map hf C.toFiniteApproximation.certificate

/-! Compose two different representations.  The first decoder maps `Y` to
    `X`; the second maps `Z` to `Y`.  A Lipschitz bound for the first decoder
    is required explicitly, so a discretisation chain cannot hide a stability
    assumption. -/

theorem compose
    {Z : Type w} [PseudoMetricSpace Z]
    {decodeXY : Y → X} {decodeYZ : Z → Y}
    {exact : X} {middle : Y} {surrogate : Z}
    {ε δ L : ℝ}
    (first : CrossSpaceApproximation decodeXY exact middle ε)
    (second : CrossSpaceApproximation decodeYZ middle surrogate δ)
    (stable : ErrorCertificate.LipschitzCertificate decodeXY L) :
    CrossSpaceApproximation (decodeXY ∘ decodeYZ) exact surrogate
      (ε + L * δ) := by
  have mapped : ErrorCertificate (decodeXY middle)
      (decodeXY (decodeYZ surrogate)) (L * δ) :=
    ErrorCertificate.map stable second.toFiniteApproximation.certificate
  refine ⟨add_nonneg first.nonneg (mul_nonneg stable.nonneg second.nonneg), ?_⟩
  change dist exact (decodeXY (decodeYZ surrogate)) ≤ ε + L * δ
  exact (ErrorCertificate.trans first.toFiniteApproximation.certificate mapped).bound

end CrossSpaceApproximation

/-! A reconstruction/encoding pair gives a radius-zero bridge for exact data.
    This is useful when a finite object is embedded into a larger space before
    an independent truncation or discretisation certificate is applied. -/

structure ReconstructionBridge
    (X : Type u) (Y : Type v)
    [PseudoMetricSpace X] [PseudoMetricSpace Y] where
  encode : X → Y
  decode : Y → X
  roundtrip : ∀ x, decode (encode x) = x

namespace ReconstructionBridge

variable {X : Type u} {Y : Type v}
  [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem exact (B : ReconstructionBridge X Y) (x : X) :
    CrossSpaceApproximation B.decode x (B.encode x) 0 := by
  refine ⟨le_rfl, ?_⟩
  simp [B.roundtrip]

theorem decode_encode (B : ReconstructionBridge X Y) (x : X) :
    B.decode (B.encode x) = x := B.roundtrip x

end ReconstructionBridge

/-! Domain vocabulary aliases.  These are all the same checked contract; the
    aliases make adapters discoverable without duplicating theorem statements. -/

namespace Quantum
abbrev TruncationBridge {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (decode : Y → X) (exact : X) (surrogate : Y) (ε : ℝ) : Prop :=
  CrossSpaceApproximation decode exact surrogate ε
end Quantum

namespace FieldTheory
abbrev ContinuumReconstruction {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (decode : Y → X) (exact : X) (surrogate : Y) (ε : ℝ) : Prop :=
  CrossSpaceApproximation decode exact surrogate ε
end FieldTheory

namespace Condensed
abbrev LatticeBandBridge {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (decode : Y → X) (exact : X) (surrogate : Y) (ε : ℝ) : Prop :=
  CrossSpaceApproximation decode exact surrogate ε
end Condensed

namespace GaugeTheory
abbrev LatticeContinuumBridge {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (decode : Y → X) (exact : X) (surrogate : Y) (ε : ℝ) : Prop :=
  CrossSpaceApproximation decode exact surrogate ε
end GaugeTheory

namespace StatMech
abbrev ThermodynamicBridge {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (decode : Y → X) (exact : X) (surrogate : Y) (ε : ℝ) : Prop :=
  CrossSpaceApproximation decode exact surrogate ε
end StatMech

namespace Classical
abbrev DiscretizationBridge {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (decode : Y → X) (exact : X) (surrogate : Y) (ε : ℝ) : Prop :=
  CrossSpaceApproximation decode exact surrogate ε
end Classical

end LeanPhy.Mathematics
