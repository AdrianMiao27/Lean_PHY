import LeanPhy.Mathematics.Approximation

/-!
# Public import for additive left-inverse certificates

The implementation lives in `Mathematics.Approximation` because it shares the
same error algebra.  This thin module gives the concept a stable import path
for numerical, PDE, band and finite-mode adapters.
-/

namespace LeanPhy.Mathematics

/- The declaration is intentionally re-exported by importing the implementation
   module; no second certificate type is introduced. -/

end LeanPhy.Mathematics
