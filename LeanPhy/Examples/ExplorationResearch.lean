import LeanPhy.Workflow.Exploration
import LeanPhy.Condensed.ComplexPairing
import LeanPhy.FieldTheory.HeavyFieldElimination

set_option autoImplicit false

/-!
# Exploratory physics with conditional results, counterexamples and revisions

The pairing question tests a real-order-parameter ansatz on complex data. The
auxiliary-field question tests elimination through a singular mass coefficient.
Both reuse public physics operations. The notebook layer does not manufacture
new physics from its labels or from an unsuccessful proof search.
-/

namespace LeanPhy.Examples.ExplorationResearch

open LeanPhy.Workflow LeanPhy.Workflow.Exploration LeanPhy.Condensed
open LeanPhy.FieldTheory.HeavyFieldElimination
open scoped Matrix

/-- The parameter contains the actual energy and pairing amplitude. -/
def pairingQuestion : Question (ℝ × ℂ) where
  name := "pairing ansatz"
  revision := "real-form-v1"
  statement := "the real pairing ansatz equals the Hermitian pairing block"
  domainDescription := "all real energies and complex pairing amplitudes"
  source := "ComplexPairing.real_pairing"
  domain := fun _ => True
  target := fun p => ComplexPairing.block p.1 p.2 = bdg (p.1 : ℂ) p.2

def realPairing : Condition (ℝ × ℂ) :=
  ⟨"real order parameter", "Delta is the embedding of a real number",
    fun p => ∃ d : ℝ, p.2 = (d : ℂ)⟩

def realBranch : Branch pairingQuestion :=
  (Branch.root pairingQuestion).refine "real pairing" realPairing

theorem real_pairing_branch : realBranch.Goal := by
  intro p _ hc
  obtain ⟨d, hd⟩ := hc realPairing (by simp [realBranch, Branch.refine])
  change ComplexPairing.block p.1 p.2 = bdg (p.1 : ℂ) p.2
  rw [hd]
  exact ComplexPairing.real_pairing p.1 d

def phaseCounterexample : Counterexample (Branch.root pairingQuestion) where
  input := (0, Complex.I)
  inDomain := trivial
  inBranch := Condition.holds_nil _
  violates := by
    intro h
    have he := congrArg (fun M => M 1 0) h
    norm_num [pairingQuestion, ComplexPairing.block, bdg] at he
    have hi := congrArg Complex.im he
    norm_num at hi

/-- One failed approach and one actual counterexample have different outcomes. -/
def pairingNotebook : Notebook pairingQuestion :=
  ⟨[(Candidate.propose realBranch).prove real_pairing_branch,
    ((Candidate.propose (Branch.root pairingQuestion)).fail
      "A real-coefficient ansatz did not cover the imaginary pairing phase.").refute
      phaseCounterexample], []⟩

def pairingOpen : TheoryPackage := pairingNotebook.toPackage "pairing exploration" "condensed matter"

/-- The revised target refers to the corrected physical operator. -/
def correctedPairing : Question (ℝ × ℂ) :=
  { pairingQuestion with
    revision := "hermitian-v2"
    statement := "the Hermitian block square depends on the modulus of the pairing"
    source := "ComplexPairing.square"
    target := fun p => ComplexPairing.block p.1 p.2 * ComplexPairing.block p.1 p.2 =
      ((p.1 ^ 2 + Complex.normSq p.2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) }

def revisedPairing : Notebook correctedPairing := pairingNotebook.revise correctedPairing

theorem corrected_pairing_answer : correctedPairing.Answer :=
  fun p _ => ComplexPairing.square p.1 p.2

def pairingClosed : TheoryPackage :=
  revisedPairing.complete "corrected pairing exploration" "condensed matter" corrected_pairing_answer

/-- A scalar auxiliary coefficient and a nonzero constant source expose the
singular domain in the existing polynomial heavy-field operation. -/
def massQuestion : Question ℝ where
  name := "auxiliary field elimination"
  revision := "all-masses-v1"
  statement := "substitution solves the heavy Euler equation"
  domainDescription := "all real quadratic coefficients, including zero"
  source := "HeavyFieldElimination.eliminated_heavy_equation"
  domain := fun _ => True
  target := fun m => eliminate m (1 : MvPolynomial Unit ℝ)
    (MvPolynomial.pderiv none (action m 0 1)) = 0

def nonzeroMass : Condition ℝ :=
  ⟨"invertible heavy coefficient", "m is nonzero", fun m => m ≠ 0⟩

def massiveBranch : Branch massQuestion :=
  (Branch.root massQuestion).refine "invertible coefficient" nonzeroMass

theorem massive_branch : massiveBranch.Goal := by
  intro m _ hc
  exact eliminated_heavy_equation m
    (hc nonzeroMass (by simp [massiveBranch, Branch.refine])) 0 1

def massCounterexample : Counterexample (Branch.root massQuestion) where
  input := 0
  inDomain := trivial
  inBranch := Condition.holds_nil _
  violates := by
    simp [massQuestion, heavy_equation]

def massNotebook : Notebook massQuestion :=
  ⟨[(Candidate.propose massiveBranch).prove massive_branch,
    (Candidate.propose (Branch.root massQuestion)).refute massCounterexample], []⟩

def massOpen : TheoryPackage :=
  massNotebook.toPackage "singular elimination exploration" "high energy / auxiliary fields"

def invertibleMassQuestion : Question ℝ :=
  { massQuestion with
    revision := "invertible-v2"
    domainDescription := "nonzero quadratic coefficient; no stability or large-mass limit claimed"
    domain := fun m => m ≠ 0 }

/-- Reuse the old theorem after proving the new domain supplies its condition. -/
theorem invertible_mass_answer : invertibleMassQuestion.Answer := by
  let B := massiveBranch.withQuestion invertibleMassQuestion
  have hB : B.Goal := massiveBranch.transport invertibleMassQuestion
    (fun _ _ => trivial) (fun _ _ _ h => h) massive_branch
  apply B.discharge hB
  intro m hm
  simp only [B, Branch.withQuestion, massiveBranch, Branch.refine,
    Condition.holds_cons, Branch.root, Condition.holds_nil, and_true]
  exact hm

def massClosed : TheoryPackage :=
  (massNotebook.revise invertibleMassQuestion).complete
    "invertible elimination exploration" "high energy / auxiliary fields" invertible_mass_answer

/-- A second research question demonstrates exhaustive hypothesis splitting.
The singular branch may only be closed with an actual zero-source condition. -/
def regularizedQuestion : Question ℝ :=
  { massQuestion with
    name := "source regularized elimination"
    revision := "v1"
    statement := "elimination solves the heavy equation when the source vanishes at m = 0"
    target := fun m => eliminate m (MvPolynomial.C m : MvPolynomial Unit ℝ)
      (MvPolynomial.pderiv none (action m 0 (MvPolynomial.C m))) = 0 }

theorem regularized_nonzero :
    ((Branch.root regularizedQuestion).refine "nonzero" nonzeroMass).Goal := by
  intro m _ hc
  exact eliminated_heavy_equation m
    (hc nonzeroMass (by simp [Branch.refine])) 0 (MvPolynomial.C m)

theorem regularized_zero :
    ((Branch.root regularizedQuestion).refine "zero" nonzeroMass.negate).Goal := by
  intro m _ hc
  have hm : m = 0 := not_not.mp (hc nonzeroMass.negate (by simp [Branch.refine]))
  subst m
  simp [regularizedQuestion, heavy_equation]

theorem regularized_answer : regularizedQuestion.Answer :=
  (Branch.root_goal regularizedQuestion).mp
    ((Branch.root regularizedQuestion).joinSplit nonzeroMass "nonzero" "zero"
      regularized_nonzero regularized_zero)

def coveredPackage : TheoryPackage :=
  (Notebook.start regularizedQuestion).complete "covered elimination exploration"
    "high energy / auxiliary fields" regularized_answer

/-- Indexed updates preserve both the earlier failed attempt and its target. -/
def recordedPairing : Notebook pairingQuestion :=
  let n := Notebook.start pairingQuestion
  n.record ⟨⟨0, by decide⟩⟩ (.failed "No proof of the universal real ansatz was found.")

example : pairingOpen.obligationCount = 1 := rfl
example : pairingClosed.obligationCount = 0 := rfl
example : massOpen.obligationCount = 1 := rfl
example : massClosed.obligationCount = 0 := rfl
example : coveredPackage.resolvedObligations.length = 1 := rfl
example : revisedPairing.candidates.length = 1 := rfl
example : recordedPairing.records.length = 2 := rfl
example : realBranch.Feasible :=
  ⟨(0, 0), trivial, by
    simp only [realBranch, Branch.refine, Condition.holds_cons, Branch.root,
      Condition.holds_nil, and_true]
    exact ⟨0, by simp⟩⟩

end LeanPhy.Examples.ExplorationResearch
