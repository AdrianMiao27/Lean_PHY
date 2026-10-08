import LeanPhy.FieldTheory.PolynomialAction
import LeanPhy.FieldTheory.VariationalResidual
import LeanPhy.Classical.VariationalBridge
import LeanPhy.Workflow.Core

/-!
# Regression chains for coupled actions and local currents

These parameterized tests exercise common research operations, including the
cross-component term missed by the old three-slot Euler residual. The package
reports actual action-level theorems and leaves boundary flux/integration and
smooth solutions open. It does not promote a formal current to a conserved
integrated physical charge.
-/

namespace LeanPhy.Examples.VariationalResearch

open LeanPhy.FieldTheory
open LeanPhy.FieldTheory.FirstOrderLagrangian
open LeanPhy.FieldTheory.JetPolynomial
open LeanPhy.Workflow
open scoped BigOperators

abbrev MechanicalAction := FirstOrderLagrangian ℝ (Fin 2) Unit

noncomputable def kineticMixing (g : ℝ) : MechanicalAction :=
  MvPolynomial.C g * gradient 0 () * gradient 1 ()

/-- The equation for the first field contains the acceleration of the second. -/
theorem kineticMixing_first (g : ℝ) :
    eulerLagrange (kineticMixing g) 0 =
      -MvPolynomial.C g * jet 1 (Finsupp.single () 2) := by
  simp [eulerLagrange, fieldPartial, momentum, kineticMixing, gradient,
    lift, jetIndex, JetPolynomial.totalDerivative, jet, Derivation.leibniz,
    smul_eq_mul, ← Finsupp.single_add]

theorem kineticMixing_second (g : ℝ) :
    eulerLagrange (kineticMixing g) 1 =
      -MvPolynomial.C g * jet 0 (Finsupp.single () 2) := by
  simp [eulerLagrange, fieldPartial, momentum, kineticMixing, gradient,
    lift, jetIndex, JetPolynomial.totalDerivative, jet, Derivation.leibniz,
    smul_eq_mul, ← Finsupp.single_add]

/-- Regression through the original mechanical API, not just the new action type. -/
theorem legacy_cross_acceleration (g : ℝ) :
    LeanPhy.Classical.fieldEulerLagrangeResidual (0 : Fin 2)
      (MvPolynomial.C g * LeanPhy.Classical.fieldJetVar 0 1 *
        LeanPhy.Classical.fieldJetVar 1 1) =
      -MvPolynomial.C g * LeanPhy.Classical.fieldJetVar 1 2 := by
  simp [LeanPhy.Classical.fieldEulerLagrangeResidual,
    LeanPhy.Classical.fieldTimeDerivative, LeanPhy.Classical.fieldJetVar,
    Derivation.leibniz, smul_eq_mul]

/-- Explicitly check the representation bridge for the same mixed action. -/
theorem kineticMixing_bridge (g : ℝ) :
    toFieldJets (eulerLagrange (kineticMixing g) 0) =
      LeanPhy.Classical.fieldEulerLagrangeResidual 0 (toMechanical (kineticMixing g)) :=
  eulerLagrange_toMechanical _ _

/-- A coordinate-dependent kinetic coefficient must itself be differentiated. -/
noncomputable def derivativeCoupling : MechanicalAction :=
  field 0 * gradient 0 () * gradient 1 ()

theorem derivativeCoupling_first :
    eulerLagrange derivativeCoupling 0 =
      -(jet 0 0 * jet 1 (Finsupp.single () 2)) := by
  simp [eulerLagrange, fieldPartial, momentum, derivativeCoupling, field, gradient,
    lift, jetIndex, JetPolynomial.totalDerivative, jet, Derivation.leibniz,
    smul_eq_mul, ← Finsupp.single_add]

/-- Relabeling the components transports the derived equation itself. -/
theorem kineticMixing_relabel (g : ℝ) (e : Fin 2 ≃ Fin 2) (a : Fin 2) :
    eulerLagrange (FirstOrderLagrangian.renameFields e (kineticMixing g)) (e a) =
      JetPolynomial.renameFields e (eulerLagrange (kineticMixing g) a) :=
  eulerLagrange_renameFields e e.injective _ a

/-- An interaction depending only on a difference preserves the common shift. -/
noncomputable def relativePotential (coupling : ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C coupling * (MvPolynomial.X 0 - MvPolynomial.X 1) ^ 4

theorem relativePotential_shift
    (K : (Fin 2 × Unit) → (Fin 2 × Unit) → ℝ) (coupling : ℝ) :
    firstVariation (quadraticAction K (relativePotential coupling)) (fun _ => 1) = 0 := by
  have h := firstVariation_quadraticAction_shift K (relativePotential coupling) (fun _ => 1)
  simp only [map_one] at h
  rw [h]
  simp [relativePotential, Fin.sum_univ_two, Derivation.leibniz,
    smul_eq_mul]

/-- The diagonal shift current is conserved locally when the derived Euler
residuals vanish, for every kinetic mixing tensor and quartic coupling. -/
theorem relativePotential_current
    (K : (Fin 2 × Unit) → (Fin 2 × Unit) → ℝ) (coupling : ℝ)
    (ev : JetPolynomial ℝ (Fin 2) Unit →+* ℝ)
    (hE : ∀ a, ev (eulerLagrange (quadraticAction K (relativePotential coupling)) a) = 0) :
    ev (divergence (noetherCurrent (quadraticAction K (relativePotential coupling))
      (fun _ => 1) (fun _ => 0))) = 0 := by
  apply noether_on_shell _ _ _ _ ev hE
  simpa [divergence] using relativePotential_shift K coupling

/-- Time and space signatures are supplied by the kinetic tensor. In this
1+1-dimensional scalar action the spatial kinetic coefficient is negative. -/
noncomputable def scalarDensity (m2 coupling : ℝ) : FirstOrderLagrangian ℝ Unit (Fin 2) :=
  (1 / 2 : ℝ) • (gradient () 0 ^ 2 - gradient () 1 ^ 2) -
    MvPolynomial.C (m2 / 2) * field () ^ 2 -
    MvPolynomial.C (coupling / 4) * field () ^ 4

theorem scalarDensity_equation (m2 coupling : ℝ) :
    eulerLagrange (scalarDensity m2 coupling) () =
      -jet () (Finsupp.single 0 2) + jet () (Finsupp.single 1 2) -
        MvPolynomial.C m2 * jet () 0 - MvPolynomial.C coupling * jet () 0 ^ 3 := by
  have htwo (D : LeanPhy.Mathematics.PhysicsDerivation ℝ
      (JetPolynomial ℝ Unit (Fin 2))) : D 2 = 0 := by
    simpa using D.map_natCast 2
  simp [eulerLagrange, fieldPartial, momentum, scalarDensity, field, gradient,
    lift, jetIndex, JetPolynomial.totalDerivative, jet, Derivation.leibniz,
    smul_eq_mul, Fin.sum_univ_two, ← Finsupp.single_add, map_ofNat, htwo]
  simp only [← MvPolynomial.smul_eq_C_mul, ← smul_mul_assoc]
  simp only [smul_mul_assoc, show (4 : JetPolynomial ℝ Unit (Fin 2)) = 2 + 2 by norm_num,
    add_mul, two_mul, smul_add]
  module

/-- The local stress identity reuses the general proof for every parameter value. -/
theorem scalarDensity_stress (m2 coupling : ℝ) (ν : Fin 2) :
    divergence (fun μ => canonicalStressTensor (scalarDensity m2 coupling) μ ν) =
      -(eulerLagrange (scalarDensity m2 coupling) () * jet () (Finsupp.single ν 1)) := by
  simpa using canonicalStressTensor_off_shell (scalarDensity m2 coupling) ν

/-- A concrete off-shell jet assignment: fields and all their formal
 derivatives evaluate to one. It is not assumed to describe a solution. -/
noncomputable def candidateJets : JetPolynomial ℝ (Fin 2) Unit →+* ℝ :=
  MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun _ => 1)

private theorem candidate_equation_residual (a : Fin 2) :
    candidateJets (eulerLagrange (kineticMixing 1) a) = -1 := by
  fin_cases a
  · change candidateJets (eulerLagrange (kineticMixing 1) 0) = -1
    rw [kineticMixing_first]
    simp [candidateJets, jet]
  · change candidateJets (eulerLagrange (kineticMixing 1) 1) = -1
    rw [kineticMixing_second]
    simp [candidateJets, jet]

/-- A nonzero-residual candidate receives a quantitative current budget. -/
theorem candidate_current_budget :
    LeanPhy.Mathematics.ErrorCertificate
      (candidateJets (divergence (noetherCurrent (kineticMixing 1)
        (fun _ => 1) (fun _ => 0)))) 0 2 := by
  have hSym : firstVariation (kineticMixing 1) (fun _ => 1) =
      divergence (fun _ => 0) := by
    simp [firstVariation, fieldPartial, kineticMixing, gradient, divergence]
  have hE (a : Fin 2) : LeanPhy.Mathematics.ErrorCertificate
      (candidateJets (eulerLagrange (kineticMixing 1) a)) 0 1 := by
    rw [candidate_equation_residual]
    exact ⟨by norm_num, by norm_num [Real.dist_eq]⟩
  have hη (a : Fin 2) : |candidateJets (1 : JetPolynomial ℝ (Fin 2) Unit)| ≤ (1 : ℝ) := by
    simp
  simpa using noether_residual_of_symmetry (kineticMixing 1) (fun _ => 1) (fun _ => 0)
    hSym candidateJets (fun _ => 1) (fun _ => 1) hE hη

/-- The same candidate has a nonzero current divergence, so its budget
cannot be relabelled as an exact conservation statement. -/
theorem candidate_current_defect :
    candidateJets (divergence (noetherCurrent (kineticMixing 1)
      (fun _ => 1) (fun _ => 0))) = 2 := by
  have hSym : firstVariation (kineticMixing 1) (fun _ => 1) =
      divergence (fun _ => 0) := by
    simp [firstVariation, fieldPartial, kineticMixing, gradient, divergence]
  rw [noether_off_shell _ _ _ hSym]
  norm_num [candidate_equation_residual]

def package : TheoryPackage :=
  TheoryPackage.empty "coupled polynomial actions" "classical and field theory"
    |>.addTheorem "coupled momentum" "mixed velocities produce cross accelerations"
      "kineticMixing_first" kineticMixing_first
    |>.addTheorem "parameterized scalar equation" "derived scalar equation for arbitrary couplings"
      "scalarDensity_equation" scalarDensity_equation
    |>.addTheorem "translation current" "off-shell stress identity for all couplings and directions"
      "scalarDensity_stress" scalarDensity_stress
    |>.addTheorem "off-shell candidate budget" "nonzero equation residuals give a local current-error certificate"
      "candidate_current_budget" candidate_current_budget
    |>.addObligationText "smooth solutions" "realize the formal jets as derivatives of a solution"
      "analytic field model"
    |>.addObligationText "integrated charge" "prove spacetime integrability and the boundary flux condition"
      "boundary analysis"

example : package.claimCount = 4 := rfl
example : package.obligationCount = 2 := rfl
example : package.hasErrors = false := by decide

end LeanPhy.Examples.VariationalResearch
