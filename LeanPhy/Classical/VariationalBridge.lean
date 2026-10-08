import LeanPhy.Classical.Lagrangian
import LeanPhy.FieldTheory.Variational

/-!
# Bridge from first-order time actions to the existing mechanical jet interface

The new first-order action type maps to the existing `(q,v,a)` polynomials.
The derived Euler residuals agree, including cross-component momentum terms.
The auxiliary projection of unrestricted jets sets orders three and above to
zero. This is a formal quotient, not a physical approximation or a statement
that the jerk vanishes. A first-order time action's Euler residual uses only
orders zero, one and two; the comparison theorem operates on that input type.
-/

namespace LeanPhy.FieldTheory.FirstOrderLagrangian

open JetPolynomial

variable {Field : Type}

/-- Project a time-derivative order to the three-slot polynomial algebra.
Orders above two map to zero; this is a formal projection, not a physical bound. -/
noncomputable def mechanicalJet (a : Field) : ℕ → Classical.FieldJetPolynomial Field
  | 0 => MvPolynomial.X (a, 0)
  | 1 => MvPolynomial.X (a, 1)
  | 2 => MvPolynomial.X (a, 2)
  | _ => 0

private theorem mechanicalJet_next (a : Field) (n : ℕ) :
    mechanicalJet a (n + 1) = Classical.fieldTimeDerivative (mechanicalJet a n) := by
  rcases n with _ | (_ | (_ | n)) <;>
    simp [mechanicalJet, Classical.fieldTimeDerivative]

/-- Formal projection onto the three-slot jet algebra; high derivatives are
set to zero. Use `eulerLagrange_toMechanical` for a first-order-action bridge. -/
noncomputable def toFieldJets : JetPolynomial ℝ Field Unit →ₐ[ℝ]
    Classical.FieldJetPolynomial Field :=
  MvPolynomial.aeval (fun p => mechanicalJet p.1 (p.2 ()))

@[simp] theorem toFieldJets_jet (a : Field) (α : Unit →₀ ℕ) :
    toFieldJets (jet a α) = mechanicalJet a (α ()) := by
  simp [toFieldJets, jet]

/-- The truncated differential algebra is a quotient of the full jet algebra.
This algebraic fact alone does not justify truncating a physical solution. -/
theorem toFieldJets_totalDerivative (P : JetPolynomial ℝ Field Unit) :
    toFieldJets (totalDerivative () P) = Classical.fieldTimeDerivative (toFieldJets P) := by
  have hx (j : Field × (Unit →₀ ℕ)) :
      toFieldJets (totalDerivative () (MvPolynomial.X j)) =
        Classical.fieldTimeDerivative (toFieldJets (MvPolynomial.X j)) := by
    rcases j with ⟨a, α⟩
    change toFieldJets (totalDerivative () (jet a α)) =
      Classical.fieldTimeDerivative (toFieldJets (jet a α))
    simp [mechanicalJet_next]
  induction P using MvPolynomial.induction_on with
  | C r => simp [toFieldJets]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hx]

private def mechanicalIndex (p : Field × Option Unit) : Field × Fin 3 :=
  (p.1, p.2.elim 0 (fun _ => 1))

private theorem mechanicalIndex_injective :
    Function.Injective (mechanicalIndex (Field := Field)) := by
  rintro ⟨a, μ⟩ ⟨b, ν⟩ h
  have hab : a = b := congrArg Prod.fst h
  subst b
  cases μ with
  | none => cases ν with
    | none => rfl
    | some ν => simp [mechanicalIndex] at h
  | some μ => cases ν with
    | none => simp [mechanicalIndex] at h
    | some ν => cases μ; cases ν; rfl

/-- Translate the typed first-order time density into the existing polynomial
interface, retaining every field component. -/
noncomputable def toMechanical : FirstOrderLagrangian ℝ Field Unit →ₐ[ℝ]
    Classical.FieldJetPolynomial Field := MvPolynomial.rename mechanicalIndex

@[simp] theorem toFieldJets_lift (L : FirstOrderLagrangian ℝ Field Unit) :
    toFieldJets (lift L) = toMechanical L := by
  induction L using MvPolynomial.induction_on with
  | C r => simp [toFieldJets, lift, toMechanical]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, hp]
      congr 1
      rcases j with ⟨a, μ⟩
      cases μ with
      | none => simp [lift, jetIndex, toFieldJets, mechanicalJet, toMechanical, mechanicalIndex]
      | some μ => cases μ; simp [lift, jetIndex, toFieldJets, mechanicalJet, toMechanical, mechanicalIndex]

/-- For every first-order time action, both APIs derive the same coupled
Euler--Lagrange equations after the explicit representation conversion. -/
theorem eulerLagrange_toMechanical [DecidableEq Field]
    (L : FirstOrderLagrangian ℝ Field Unit) (a : Field) :
    toFieldJets (eulerLagrange L a) =
      Classical.fieldEulerLagrangeResidual a (toMechanical L) := by
  have hq : MvPolynomial.pderiv (a, 0) (toMechanical L) =
      toMechanical (MvPolynomial.pderiv (a, none) L) :=
    MvPolynomial.pderiv_rename mechanicalIndex_injective (a, none) L
  have hv : MvPolynomial.pderiv (a, 1) (toMechanical L) =
      toMechanical (MvPolynomial.pderiv (a, some ()) L) :=
    MvPolynomial.pderiv_rename mechanicalIndex_injective (a, some ()) L
  simp [eulerLagrange, fieldPartial, momentum, Classical.fieldEulerLagrangeResidual,
    toFieldJets_totalDerivative, hq, hv]

end LeanPhy.FieldTheory.FirstOrderLagrangian
