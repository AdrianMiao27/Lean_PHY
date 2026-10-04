import LeanPhy.Dimensions
import LeanPhy.Indices
import LeanPhy.Surface.DiracNotation
import LeanPhy.Surface.Einstein
import LeanPhy.Surface.IndexCalculus
import LeanPhy.Surface.TypedTensor
import LeanPhy.Surface.Variance
import LeanPhy.Surface.GenericTensor
import LeanPhy.Mathematics.Approximation
import LeanPhy.Mathematics.FiniteProcess
import LeanPhy.Mathematics.SymmetryReduction
import LeanPhy.Mathematics.Model
import LeanPhy.Mathematics.ApproximateModel
import LeanPhy.Mathematics.ParametricModel
import LeanPhy.Mathematics.FiniteGroupAverage
import LeanPhy.Mathematics.ExternalCertificate
import LeanPhy.Mathematics.CertifiedResidual
import LeanPhy.Tactics

/-!
# LeanPhy minimal entry point

This import is the small shared layer for a new physics development.  It
contains dimensions, typed indices/tensors, Dirac and Einstein surface
helpers, the reusable approximation/error contracts, proof-producing external
certificates, and the physics tactic facade.  It deliberately does not import
every domain adapter or the default research-package catalogue.

Use a domain entry point (for example `LeanPhy.Entry.Quantum`) when a project
needs concrete finite quantum objects; use `LeanPhy.Workflow` only when it
wants the full package/reporting adapters.
-/

namespace LeanPhy

/- A stable marker for tools that want to report the selected import profile. -/
def minimalProfile : String :=
  "dimensions + surface + models + parametric-models + approximation + symmetry-reduction + certificates + tactics"

end LeanPhy
