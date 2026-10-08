import LeanPhy.FieldTheory.Variational

/-!
# Translation variation and the canonical energy-momentum tensor

For a first-order density with no explicit coordinate dependence, the field
variation `δφ_a = ∂_ν φ_a` is its total coordinate derivative. This is proved
from the polynomial action, rather than supplied as a symmetry certificate.
The resulting canonical tensor satisfies its off-shell divergence identity
and a local conservation equation on every assignment satisfying the Euler
residuals. No nondegeneracy of the kinetic term is needed.

The first tensor slot is the divergence/current direction and the second is
the translation direction. No metric raising/lowering is implicit. This is
the canonical tensor: symmetry, gauge invariance, improvements, integrated
charges, and boundary flux conditions are not asserted here.
-/

namespace LeanPhy.FieldTheory.FirstOrderLagrangian

open JetPolynomial
open scoped BigOperators

variable {R Field Direction : Type*} [CommRing R]
variable [Fintype Field] [Fintype Direction]

noncomputable def translationVariation (ν : Direction) (a : Field) :
    JetPolynomial R Field Direction := jet a (Finsupp.single ν 1)

/-- The action-level translation symmetry follows from the actual chain rule
on polynomial generators and the proved product rule for first variation. -/
theorem firstVariation_translation (L : FirstOrderLagrangian R Field Direction)
    (ν : Direction) :
    firstVariation L (translationVariation ν) = totalDerivative ν (lift L) := by
  have hX (j : Field × Option Direction) :
      firstVariation (MvPolynomial.X j : FirstOrderLagrangian R Field Direction)
        (translationVariation ν) = totalDerivative ν (lift (MvPolynomial.X j)) := by
    rcases j with ⟨a, μ⟩
    cases μ with
    | none =>
        change firstVariation (field a) (translationVariation ν) =
          totalDerivative ν (lift (field a))
        simp [translationVariation]
    | some μ =>
        change firstVariation (gradient a μ) (translationVariation ν) =
          totalDerivative ν (lift (gradient a μ))
        simp [translationVariation, add_comm]
  induction L using MvPolynomial.induction_on with
  | C r => simp [firstVariation, fieldPartial, momentum, lift]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      simp only [firstVariation_mul, map_mul, Derivation.leibniz, smul_eq_mul, hp, hX]

noncomputable def translationBoundary (L : FirstOrderLagrangian R Field Direction)
    (ν μ : Direction) : JetPolynomial R Field Direction := by
  classical
  exact if μ = ν then lift L else 0

omit [Fintype Field] in
@[simp] theorem divergence_translationBoundary
    (L : FirstOrderLagrangian R Field Direction) (ν : Direction) :
    divergence (translationBoundary L ν) = totalDerivative ν (lift L) := by
  classical
  simp [divergence, translationBoundary, apply_ite]

/-- `T^μ_ν = Σ_a π_a^μ ∂_ν φ_a - δ^μ_ν L` with the slot convention explicit. -/
noncomputable def canonicalStressTensor (L : FirstOrderLagrangian R Field Direction)
    (μ ν : Direction) : JetPolynomial R Field Direction :=
  boundaryCurrent L (translationVariation ν) μ - translationBoundary L ν μ

/-- The divergence is derived for arbitrary first-order polynomial interactions,
including derivative couplings. It is not an input field of a certificate. -/
theorem canonicalStressTensor_off_shell
    (L : FirstOrderLagrangian R Field Direction) (ν : Direction) :
    divergence (fun μ => canonicalStressTensor L μ ν) =
      -(∑ a, eulerLagrange L a * jet a (Finsupp.single ν 1)) := by
  have hSym : firstVariation L (translationVariation ν) = divergence (translationBoundary L ν) := by
    rw [firstVariation_translation, divergence_translationBoundary]
  exact noether_off_shell L (translationVariation ν) (translationBoundary L ν) hSym

theorem canonicalStressTensor_on_shell {S : Type*} [CommRing S]
    (L : FirstOrderLagrangian R Field Direction) (ν : Direction)
    (ev : JetPolynomial R Field Direction →+* S)
    (hEquations : ∀ a, ev (eulerLagrange L a) = 0) :
    ev (divergence (fun μ => canonicalStressTensor L μ ν)) = 0 := by
  rw [canonicalStressTensor_off_shell]
  simp [hEquations]

end LeanPhy.FieldTheory.FirstOrderLagrangian
