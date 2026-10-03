import LeanPhy.Entry.Quantum
import LeanPhy.Workflow
import LeanPhy.CLI

/-!
# Strict downstream-client regression

This executable is intentionally tiny: it has one actual theorem and no open
research obligation.  The regression proves that a downstream project can use
the public CLI as a publication gate, not only as a report generator.
-/

namespace StrictClient

open LeanPhy.Workflow

theorem checked : (1 : Nat) = 1 := rfl

def package : TheoryPackage :=
  (TheoryPackage.empty "strict client package" "finite algebra")
    |>.addAssumptionText "finite-model" "the claim is stated in a finite model" "regression"
    |>.addTheoremWithAssumptions "identity" "1 = 1" "StrictClientMain.lean"
      ["finite-model"] checked

def project : ResearchProject :=
  (ResearchProject.empty "strict client project").addPackage package

def manifest : ResearchManifest :=
  (ResearchManifest.ofProject "strict client manifest" project)
    |>.withProfiles ["LeanPhy.Entry.Quantum"]
    |>.withSources ["StrictClientMain.lean", "lakefile.toml"]

end StrictClient

def main (args : List String) : IO Unit :=
  LeanPhy.CLI.run StrictClient.manifest args
