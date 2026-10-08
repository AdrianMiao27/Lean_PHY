import LeanPhy.Entry.Gauge
import LeanPhy.CLI

/-!
# A reproducible finite ghost calculation

Run `lake exe leanphy_ghost_research --project-json` to inspect the proof-bearing
ledger. The calculation distinguishes a Koszul contraction from a quadratic
ghost differential, includes a nontriviality theorem and records the missing
general gauge-cochain and physical interpretations as open obligations.
-/

namespace LeanPhy.Examples.GhostResearch

open LeanPhy.Mathematics LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial
open LeanPhy.Workflow

abbrev Ghosts := GhostPolynomial ℚ 3

noncomputable def c (i : Fin 3) : Ghosts := generator i

theorem left_derivative : derivative 0 (c 0 * c 1) = c 1 := by
  have h := derivative_generator_mul (R := ℚ) (0 : Fin 3) 0 (c 1)
  simpa [c] using h

theorem right_derivative_sign : derivative 1 (c 0 * c 1) = -c 0 :=
  derivative_pair 0 1 (by decide)

theorem car_on_polynomials (x : Ghosts) :
    derivative 1 (c 1 * x) + c 1 * derivative 1 x = x := by
  simpa [c] using derivative_generator_mul (R := ℚ) (1 : Fin 3) 1 x

noncomputable def s : GradedBRSTDifferential (grading (R := ℚ) (n := 3)) :=
  quadraticBRST 0 1 (by decide)

theorem s_on_generators : s (c 0) = 0 ∧ s (c 1) = c 0 * c 1 ∧ s (c 2) = 0 := by
  change quadratic 0 1 (c 0) = 0 ∧ quadratic 0 1 (c 1) = c 0 * c 1 ∧
    quadratic 0 1 (c 2) = 0
  simp [c]

theorem s_nilpotent (x : Ghosts) : s (s x) = 0 := s.nilpotent_apply x

theorem s_nonzero : s (c 1) ≠ 0 := quadratic_nonzero 0 1 (by decide)

theorem s_leibniz (x y : Ghosts) : s (x * y) = s x * y + parityInvolution x * s y :=
  quadratic_mul 0 1 x y

theorem inner_charge_degenerate (x : Ghosts) :
    innerDifferential (c 0) (generator_isOdd 0) (generator_sq 0) x = 0 :=
  innerDifferential_eq_zero _ _ _ x

theorem koszul_exact (x : Ghosts) (hx : (koszul (LinearMap.proj 0)).IsClosed x) :
    (koszul (LinearMap.proj 0)).IsExact x :=
  exact_of_closed_of_pairing_one _ (Pi.single 0 1) (by simp) hx

theorem zero_constraints_not_exact :
    ¬(koszul (0 : Module.Dual ℚ (Fin 3 → ℚ))).IsExact (1 : Ghosts) := by
  rw [koszul_zero_exact_iff]
  exact one_ne_zero

/-- Constraints may be actual polynomial observables, not just scalar constants. -/
abbrev Observables := MvPolynomial (Fin 2) ℚ

noncomputable def constraints : Fin 2 → Observables := MvPolynomial.X

noncomputable def constraintD := koszulOfConstraints constraints

theorem constraint_generator : constraintD (generator 0) =
    algebraMap Observables (GhostPolynomial Observables 2) (MvPolynomial.X 0) :=
  koszulOfConstraints_generator constraints 0

theorem constraint_syzygy : constraintD (generator 0 * generator 1) =
    (MvPolynomial.X 0 : Observables) • generator (R := Observables) (1 : Fin 2) -
    (MvPolynomial.X 1 : Observables) • generator (R := Observables) (0 : Fin 2) :=
  koszulOfConstraints_pair constraints 0 1

theorem constraint_syzygy_closed : constraintD
    ((MvPolynomial.X 0 : Observables) • generator (R := Observables) (1 : Fin 2) -
      (MvPolynomial.X 1 : Observables) • generator (R := Observables) (0 : Fin 2)) = 0 := by
  rw [← constraint_syzygy]
  exact constraintD.nilpotent_apply _

def package : TheoryPackage :=
  TheoryPackage.empty "finite ghost research" "finite Grassmann algebra"
    |>.addAssumptionText "finite algebra" "three Grassmann generators over rational scalars"
      "LeanPhy.Examples.GhostResearch.Ghosts"
    |>.addTheoremWithAssumptions "left Grassmann derivative" "partial_0(c_0 c_1) = c_1"
      "LeanPhy.Examples.GhostResearch.left_derivative" ["finite algebra"] left_derivative
    |>.addTheoremWithAssumptions "right Grassmann sign" "partial_1(c_0 c_1) = -c_0"
      "LeanPhy.Examples.GhostResearch.right_derivative_sign" ["finite algebra"]
      right_derivative_sign
    |>.addTheoremWithAssumptions "ghost CAR" "partial_i c_i + c_i partial_i = identity"
      "LeanPhy.Examples.GhostResearch.car_on_polynomials" ["finite algebra"] car_on_polynomials
    |>.addTheoremWithAssumptions "quadratic ghost nilpotency" "s(s(x)) = 0 for every polynomial"
      "LeanPhy.Examples.GhostResearch.s_nilpotent" ["finite algebra"] s_nilpotent
    |>.addTheoremWithAssumptions "quadratic ghost nontriviality" "s(c_1) is not zero"
      "LeanPhy.Examples.GhostResearch.s_nonzero" ["finite algebra"] s_nonzero
    |>.addTheoremWithAssumptions "quadratic signed product rule" "s(xy) = s(x)y + parity(x)s(y)"
      "LeanPhy.Examples.GhostResearch.s_leibniz" ["finite algebra"] s_leibniz
    |>.addTheoremWithAssumptions "inner ghost charge degeneracy" "pure exterior inner charge is zero"
      "LeanPhy.Examples.GhostResearch.inner_charge_degenerate" ["finite algebra"]
      inner_charge_degenerate
    |>.addTheoremWithAssumptions "Koszul contraction" "closed implies exact under unit pairing"
      "LeanPhy.Examples.GhostResearch.koszul_exact" ["finite algebra"] koszul_exact
    |>.addTheoremWithAssumptions "zero constraint obstruction" "one is not exact for zero constraints"
      "LeanPhy.Examples.GhostResearch.zero_constraints_not_exact" ["finite algebra"]
      zero_constraints_not_exact
    |>.addAssumptionText "polynomial constraints" "two coordinate constraints in Q[x_0,x_1]"
      "LeanPhy.Examples.GhostResearch.constraints"
    |>.addTheoremWithAssumptions "constraint syzygy boundary" "d(c_0 c_1) = x_0 c_1 - x_1 c_0"
      "LeanPhy.Examples.GhostResearch.constraint_syzygy" ["polynomial constraints"] constraint_syzygy
    |>.addTheoremWithAssumptions "constraint syzygy closedness" "d(x_0 c_1 - x_1 c_0) = 0"
      "LeanPhy.Examples.GhostResearch.constraint_syzygy_closed" ["polynomial constraints"]
      constraint_syzygy_closed
    |>.addBoundaryText "parity only" "integer ghost degree and a full gauge BRST/BV complex are not constructed"
    |>.addObligationText "gauge cochain identification"
      "identify this polynomial model with the supplied Lie-cochain representation and conventions"
      "research model"
    |>.addObligationText "physical interpretation"
      "supply matter content, constraints and the map to physical observables; continuum claims need analysis"
      "research model"

def project : ResearchProject := ResearchProject.ofPackages "finite ghost research" [package]

def manifest : ResearchManifest :=
  ResearchManifest.ofProject "finite ghost research manifest" project
    |>.withProfiles ["LeanPhy.Entry.Gauge"]
    |>.withSources ["LeanPhy.Examples.GhostResearch", "lakefile.toml", "lean-toolchain"]

example : project.claimCount = 11 := rfl
example : project.obligationCount = 2 := rfl
example : project.diagnosticCount = 0 := by decide

def main (args : List String) : IO Unit := LeanPhy.CLI.run manifest args

end LeanPhy.Examples.GhostResearch
