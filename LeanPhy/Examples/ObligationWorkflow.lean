import LeanPhy.Workflow.Core
import Lean.Elab.AssertExists

/-! Regression for registered goals, evidence, resolution history and package
composition. This client imports no built-in domain-package catalogue. -/
assert_not_exists LeanPhy.Workflow.QuantumTheoryPackage
assert_not_exists LeanPhy.Condensed.bdg

namespace LeanPhy.Examples.ObligationWorkflow

open LeanPhy.Workflow LeanPhy.Mathematics

def residualGoal (x : ℝ) : ExternalObligationWitness where
  metadata :=
    { name := "residual bound"
      statement := "the exact state has zero residual"
      source := "model declaration" }
  proposition := ErrorCertificate x x 0

def base : TheoryPackage := TheoryPackage.empty "residual research" "approximation"

def pending (x : ℝ) : TheoryPackage := base.addObligationWitness (residualGoal x)

def closed (x : ℝ) : TheoryPackage :=
  (pending x).resolveObligation (base.addedObligationRef (residualGoal x))
    "zero residual checked" "the exact state has zero residual" "ErrorCertificate.of_eq"
    [] [] (ErrorCertificate.of_eq rfl)

example (x : ℝ) : (closed x).obligationCount = 0 := rfl
example (x : ℝ) : (closed x).resolvedObligations.length = 1 := rfl
example (x : ℝ) : ((closed x).resolvedObligations[0]'(by change 0 < 1; decide)).obligation.Goal := by
  -- Use a proof-bearing history entry directly, without trusting a status label.
  exact ((closed x).resolvedObligations[0]'(by change 0 < 1; decide)).proof

/-- Identical names cannot make one proof remove a different goal. -/
def duplicateName : TheoryPackage :=
  (pending 0).addObligation
    { name := "residual bound"
      statement := "a second, unproved target"
      source := "separate assumption"
      target := some False }

def duplicateRef : ObligationRef duplicateName := ⟨⟨0, by decide⟩⟩

def oneClosed : TheoryPackage :=
  duplicateName.resolveObligation duplicateRef "first checked" "zero residual" "model"
    [] [] (ErrorCertificate.of_eq rfl)

example : oneClosed.obligationCount = 1 := rfl
example : oneClosed.obligations[0].Goal = False := rfl
example : duplicateName.hasErrors = true := by decide

def continuum : TheoryPackage :=
  base.addObligationText "continuum limit" "establish convergence" "analysis"

def continuumRef : ObligationRef continuum := ⟨⟨0, by decide⟩⟩

def withEvidence : TheoryPackage :=
  continuum.addObligationEvidence continuumRef "finite residual" "finite evidence only"
    "model" [] [] (ErrorCertificate.of_eq (x := (0 : ℝ)) rfl)

example : withEvidence.obligationCount = 1 := rfl
example : withEvidence.resolvedObligations.length = 0 := rfl
example : ((closed 0).append continuum).obligationCount = 1 := rfl
example : ((closed 0).append continuum).resolvedObligations.length = 1 := rfl

end LeanPhy.Examples.ObligationWorkflow
