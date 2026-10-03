import LeanPhy.Entry.Physics
import LeanPhy.CLI

/-!
# Downstream client regression

This file intentionally behaves like a separate research repository: it only
imports the public physics umbrella and the reusable CLI, defines its own
package/project/manifest, and exposes an ordinary `main` suitable for a
`lake exe` target.  Keeping this small client in the tree prevents the public
workflow from silently depending on the built-in catalogue in `Check.lean`.
-/

namespace LeanPhy.Examples.ClientProject

open LeanPhy.Workflow

def pauliClaim : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions
    "Pauli XY product"
    "σx σy = i σz"
    "LeanPhy.Quantum.pauliX_pauliY"
    ["finite operators"]
    LeanPhy.Quantum.pauliX_pauliY

def package : TheoryPackage :=
  (TheoryPackage.ofModel
      "client Pauli model"
      "finite quantum algebra"
      [{ name := "finite operators"
         statement := "the model is represented by explicit 2 × 2 matrices"
         source := "client model declaration" }]
      [{ label := "continuum lift"
         explanation := "the finite matrix identity does not establish an infinite-dimensional result" }])
    |>.addClaim pauliClaim
    |>.addObligationText
      "operator-domain bridge"
      "supply domain and self-adjointness arguments before interpreting the matrix identity as an unbounded-operator statement"
      "client analysis"

def derivedPackage : TheoryPackage :=
  TheoryPackage.ofModel
    "client derived algebra"
    "finite quantum algebra"
    [{ name := "finite operators"
       statement := "the target package uses the same explicit matrix model"
       source := "client model declaration" }]
    []

theorem deriveCommutator
    (h : LeanPhy.Quantum.pauliX * LeanPhy.Quantum.pauliY =
      Complex.I • LeanPhy.Quantum.pauliZ) :
    LeanPhy.Quantum.commutator LeanPhy.Quantum.pauliX LeanPhy.Quantum.pauliY =
      (2 * Complex.I) • LeanPhy.Quantum.pauliZ := by
  rw [LeanPhy.Quantum.commutator, h, LeanPhy.Quantum.pauliY_pauliX]
  rw [show (2 : ℂ) * Complex.I = Complex.I + Complex.I by ring,
    add_smul, neg_smul, sub_neg_eq_add]

def baseProject : ResearchProject :=
  ResearchProject.empty "client project"
    |>.addPackage package
    |>.addPackage derivedPackage

def project : ResearchProject :=
  ResearchProject.addDerivedTheorem baseProject
    "client Pauli model" pauliClaim derivedPackage
    "Pauli commutator derived from XY product"
    "ClientProject.lean:deriveCommutator statement"
    "ClientProject.lean:deriveCommutator"
    ["finite operators"]
    deriveCommutator

def manifest : ResearchManifest :=
  ResearchManifest.ofProject "client reproducibility manifest" project
    |>.withProfiles ["LeanPhy.Entry.Physics"]
    |>.withSources ["ClientProject.lean", "lakefile.toml", "lean-toolchain"]
    |>.withExternalTools ["Lean kernel", "mathlib", "lake"]

/- An archived client may record the toolchain that produced an older proof
   bundle explicitly.  This is metadata for reproducibility; it does not
   bypass the compiler currently checking this file. -/
def archivedManifest : ResearchManifest :=
  manifest.withToolchain
    { lean := "v4.33.0", mathlib := "v4.33.0", leanPhy := "0.1.0" }

/- A local package can opt into elaboration-time model guards.  The ordinary
   string API remains useful when importing a package assembled elsewhere, but
   this form makes a typo in a same-file model reference a Lean error before
   the CLI is run. -/
def guardedPackage : TheoryPackage :=
  let base :=
    (TheoryPackage.empty "guarded client model" "finite quantum algebra")
      |>.addModelText "guarded-pauli" "finite operator model"
        "unit" "Matrix (Fin 2) (Fin 2) ℂ" "Matrix (Fin 2) (Fin 2) ℂ" "identity"
        []
  base.addTheoremForModelRegistered "guarded-pauli"
    (by simp [base, TheoryPackage.modelNames, TheoryPackage.addModelText,
      TheoryPackage.addModel, ModelRegistration.text, TheoryPackage.empty])
    "guarded identity" "the registered model has a reflexive identity" "ClientProject.lean"
    [] (by rfl : (1 : Nat) = 1)

example : guardedPackage.status = "VERIFIED-CONDITIONAL" := rfl
example : guardedPackage.missingModelReferenceCount = 0 := by decide
example : guardedPackage.diagnosticCount = 0 := by decide

def guardedAssumptionPackage : TheoryPackage :=
  let base :=
    (TheoryPackage.empty "guarded assumption model" "finite algebra")
      |>.addAssumptionText "finite-state" "the state space is finite" "ClientProject.lean"
  base.addModelTextRegistered "finite-model" "finite" "unit" "Finite state"
    "scalar observable" "one step" ["finite-state"]
    (by
      intro assumption h
      simp only [List.mem_cons, List.not_mem_nil] at h
      rcases h with rfl | h
      · simp [base, TheoryPackage.addAssumptionText,
          TheoryPackage.addAssumption, TheoryPackage.empty]
      · exact False.elim h)

example : guardedAssumptionPackage.missingModelAssumptionReferenceCount = 0 := by decide
example : guardedAssumptionPackage.diagnosticCount = 0 := by decide

/- A downstream `Main.lean` can use exactly this definition as its executable
   entry point; no catalogue-specific code is required. -/
def main (args : List String) : IO Unit :=
  LeanPhy.CLI.run manifest args

def targetDependencies (packages : List TheoryPackage) : List String :=
  (packages.drop 1).flatMap (fun target =>
    (target.claims.take 1).flatMap (fun claim => claim.dependencies))

example : package.status = "VERIFIED-CONDITIONAL" := rfl
example : project.packageCount = 2 := rfl
example : project.claimCount = 2 := rfl
example : manifest.claimCount = 2 := rfl
example : manifest.obligationCount = 1 := rfl
example : package.stableId = "leanphy.package:client Pauli model" := rfl
example : pauliClaim.stableId = "leanphy.claim:Pauli XY product" := rfl
example : ResearchProject.qualifiedClaimId "client Pauli model" "Pauli XY product" =
    "leanphy.claim:client Pauli model::Pauli XY product" := rfl
example : archivedManifest.toolchain.lean = "v4.33.0" := rfl
example : project.diagnosticCount = 0 := by decide
example : targetDependencies project.packages =
    ["client Pauli model::Pauli XY product"] := rfl

end LeanPhy.Examples.ClientProject
