import LeanPhy.FieldTheory.Jet

/-!
# First-order polynomial actions, boundary terms and Noether currents

`FirstOrderLagrangian R Field Direction` separates field values from their
first derivatives in its type. Its lift into the unbounded jet algebra permits
spacetime differentiation without setting higher derivatives to zero.

The residual convention is `E_a = ∂L/∂φ_a - D_μ(∂L/∂(∂_μ φ_a))`.
`first_variation` proves the local integration-by-parts identity with its full
boundary current. `noether_off_shell` derives the divergence of the Noether
current from a proved symmetry variation; evaluating on jets that satisfy the
Euler equations gives a checked local conservation equation.

All identities are local polynomial identities for commuting fields in flat
coordinates. No spacetime integral, boundary condition, existence of a smooth
solution, gauge fixing, or charge conservation after integration is inferred.
There is no explicit coordinate dependence: scalar coefficients are constant
under spacetime differentiation. Background profiles must be included as
fields with their own jets, not silently treated as scalar coefficients.
-/

namespace LeanPhy.FieldTheory

abbrev FirstOrderLagrangian (R : Type*) [CommRing R] (Field : Type*) (Direction : Type*) :=
  MvPolynomial (Field × Option Direction) R

namespace FirstOrderLagrangian

open JetPolynomial
open scoped BigOperators

variable {R Field Direction : Type*} [CommRing R]

/-- `none` labels a field value; `some μ` labels its first derivative. -/
noncomputable def jetIndex (p : Field × Option Direction) : Field × (Direction →₀ ℕ) :=
  (p.1, p.2.elim 0 (fun μ => Finsupp.single μ 1))

noncomputable def lift : FirstOrderLagrangian R Field Direction →ₐ[R]
    JetPolynomial R Field Direction := MvPolynomial.rename jetIndex

noncomputable def field (a : Field) : FirstOrderLagrangian R Field Direction :=
  MvPolynomial.X (a, none)

noncomputable def gradient (a : Field) (μ : Direction) :
    FirstOrderLagrangian R Field Direction := MvPolynomial.X (a, some μ)

@[simp] theorem lift_field (a : Field) :
    lift (field a : FirstOrderLagrangian R Field Direction) = jet a 0 := by
  simp [lift, field, jetIndex, jet]

@[simp] theorem lift_gradient (a : Field) (μ : Direction) :
    lift (gradient a μ : FirstOrderLagrangian R Field Direction) =
      jet a (Finsupp.single μ 1) := by
  simp [lift, gradient, jetIndex, jet]

noncomputable def fieldPartial (L : FirstOrderLagrangian R Field Direction) (a : Field) :
    JetPolynomial R Field Direction := lift (MvPolynomial.pderiv (a, none) L)

/-- The momentum density conjugate to `∂_μ φ_a`. -/
noncomputable def momentum (L : FirstOrderLagrangian R Field Direction)
    (a : Field) (μ : Direction) : JetPolynomial R Field Direction :=
  lift (MvPolynomial.pderiv (a, some μ) L)

variable [Fintype Field] [Fintype Direction]

/-- All field components participate in the total derivative, even in the
Euler equation of a single selected component. -/
noncomputable def eulerLagrange (L : FirstOrderLagrangian R Field Direction) (a : Field) :
    JetPolynomial R Field Direction :=
  fieldPartial L a - ∑ μ, totalDerivative μ (momentum L a μ)

/-- The local directional variation with `δφ_a = η_a` and
`δ(∂_μ φ_a) = D_μ η_a`. -/
noncomputable def firstVariation (L : FirstOrderLagrangian R Field Direction)
    (η : Field → JetPolynomial R Field Direction) : JetPolynomial R Field Direction :=
  (∑ a, fieldPartial L a * η a) +
    ∑ a, ∑ μ, momentum L a μ * totalDerivative μ (η a)

noncomputable def boundaryCurrent (L : FirstOrderLagrangian R Field Direction)
    (η : Field → JetPolynomial R Field Direction) (μ : Direction) :
    JetPolynomial R Field Direction := ∑ a, momentum L a μ * η a

noncomputable def divergence (J : Direction → JetPolynomial R Field Direction) :
    JetPolynomial R Field Direction := ∑ μ, totalDerivative μ (J μ)

/-- Local first-variation identity, with the boundary term retained. -/
theorem first_variation (L : FirstOrderLagrangian R Field Direction)
    (η : Field → JetPolynomial R Field Direction) :
    firstVariation L η = (∑ a, eulerLagrange L a * η a) +
      divergence (boundaryCurrent L η) := by
  unfold firstVariation eulerLagrange divergence boundaryCurrent
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib,
    sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun μ a => momentum L a μ * totalDerivative μ (η a)),
    Finset.sum_comm (f := fun μ a => η a * totalDerivative μ (momentum L a μ))]
  simp only [mul_comm (η _) _, ← Finset.sum_mul]
  ring

omit [Fintype Field] in
@[simp] theorem eulerLagrange_add (L K : FirstOrderLagrangian R Field Direction) (a : Field) :
    eulerLagrange (L + K) a = eulerLagrange L a + eulerLagrange K a := by
  simp [eulerLagrange, fieldPartial, momentum, Finset.sum_add_distrib]
  ring

omit [Fintype Field] in
@[simp] theorem eulerLagrange_smul (c : R)
    (L : FirstOrderLagrangian R Field Direction) (a : Field) :
    eulerLagrange (c • L) a = c • eulerLagrange L a := by
  simp [eulerLagrange, fieldPartial, momentum, map_smul, Finset.smul_sum, smul_sub]

@[simp] theorem firstVariation_add (L K : FirstOrderLagrangian R Field Direction)
    (η : Field → JetPolynomial R Field Direction) :
    firstVariation (L + K) η = firstVariation L η + firstVariation K η := by
  simp [firstVariation, fieldPartial, momentum, add_mul, Finset.sum_add_distrib]
  ring

@[simp] theorem firstVariation_field (a : Field)
    (η : Field → JetPolynomial R Field Direction) :
    firstVariation (field a) η = η a := by
  classical
  simp [firstVariation, fieldPartial, momentum, field, MvPolynomial.pderiv_X, Pi.single_apply, apply_ite, ite_mul]

@[simp] theorem firstVariation_gradient (a : Field) (μ : Direction)
    (η : Field → JetPolynomial R Field Direction) :
    firstVariation (gradient a μ) η = totalDerivative μ (η a) := by
  classical
  simp [firstVariation, fieldPartial, momentum, gradient, MvPolynomial.pderiv_X, Pi.single_apply, apply_ite, ite_mul, ite_and]

/-- The constructed variation obeys the product rule for arbitrary densities. -/
theorem firstVariation_mul (L K : FirstOrderLagrangian R Field Direction)
    (η : Field → JetPolynomial R Field Direction) :
    firstVariation (L * K) η = lift L * firstVariation K η +
      lift K * firstVariation L η := by
  simp only [firstVariation, fieldPartial, momentum, Derivation.leibniz,
    smul_eq_mul, map_add, map_mul, add_mul, Finset.sum_add_distrib]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

/-- The symmetry may change the density by a divergence `D_μ B^μ`. -/
noncomputable def noetherCurrent (L : FirstOrderLagrangian R Field Direction)
    (η : Field → JetPolynomial R Field Direction)
    (B : Direction → JetPolynomial R Field Direction) (μ : Direction) :
    JetPolynomial R Field Direction := boundaryCurrent L η μ - B μ

/-- A symmetry yields the full off-shell identity; equations of motion are
not assumed until the evaluation theorem below. -/
theorem noether_off_shell (L : FirstOrderLagrangian R Field Direction)
    (η : Field → JetPolynomial R Field Direction)
    (B : Direction → JetPolynomial R Field Direction)
    (hSymmetry : firstVariation L η = divergence B) :
    divergence (noetherCurrent L η B) = -(∑ a, eulerLagrange L a * η a) := by
  have h := first_variation L η
  rw [hSymmetry] at h
  simp only [divergence, noetherCurrent, map_sub, Finset.sum_sub_distrib]
  unfold divergence at h
  linear_combination -h

/-- Evaluation on any assignment satisfying the Euler equations gives a
vanishing local current divergence. Interpreting an assignment as derivatives
of a smooth solution is a separate analytic obligation. -/
theorem noether_on_shell {S : Type*} [CommRing S]
    (L : FirstOrderLagrangian R Field Direction)
    (η : Field → JetPolynomial R Field Direction)
    (B : Direction → JetPolynomial R Field Direction)
    (hSymmetry : firstVariation L η = divergence B)
    (ev : JetPolynomial R Field Direction →+* S)
    (hEquations : ∀ a, ev (eulerLagrange L a) = 0) :
    ev (divergence (noetherCurrent L η B)) = 0 := by
  rw [noether_off_shell L η B hSymmetry]
  simp [hEquations]

/-! ## Field-label and mode-order conversions -/

noncomputable def renameFields {OtherField : Type*} (f : Field → OtherField) :
    FirstOrderLagrangian R Field Direction →ₐ[R]
      FirstOrderLagrangian R OtherField Direction :=
  MvPolynomial.rename (fun p => (f p.1, p.2))

omit [Fintype Field] [Fintype Direction] in
theorem lift_renameFields {OtherField : Type*} (f : Field → OtherField)
    (L : FirstOrderLagrangian R Field Direction) :
    lift (renameFields f L) = JetPolynomial.renameFields f (lift L) := by
  simp only [lift, renameFields, JetPolynomial.renameFields, MvPolynomial.rename_rename]
  rfl

omit [Fintype Field] [Fintype Direction] in
private theorem fieldIndex_injective {OtherField : Type*} {f : Field → OtherField}
    (hf : Function.Injective f) :
    Function.Injective (fun p : Field × Option Direction => (f p.1, p.2)) := by
  rintro ⟨a, μ⟩ ⟨b, ν⟩ h
  exact Prod.ext (hf (Prod.mk.inj h).1) (Prod.mk.inj h).2

omit [Fintype Field] [Fintype Direction] in
theorem fieldPartial_renameFields {OtherField : Type*} (f : Field → OtherField)
    (hf : Function.Injective f) (L : FirstOrderLagrangian R Field Direction) (a : Field) :
    fieldPartial (renameFields f L) (f a) =
      JetPolynomial.renameFields f (fieldPartial L a) := by
  unfold fieldPartial
  have h := MvPolynomial.pderiv_rename (fieldIndex_injective (Direction := Direction) hf)
    (a, none) L
  exact (congrArg lift h).trans (lift_renameFields f _)

omit [Fintype Field] [Fintype Direction] in
theorem momentum_renameFields {OtherField : Type*} (f : Field → OtherField)
    (hf : Function.Injective f) (L : FirstOrderLagrangian R Field Direction)
    (a : Field) (μ : Direction) :
    momentum (renameFields f L) (f a) μ =
      JetPolynomial.renameFields f (momentum L a μ) := by
  unfold momentum
  have h := MvPolynomial.pderiv_rename (fieldIndex_injective (Direction := Direction) hf)
    (a, some μ) L
  exact (congrArg lift h).trans (lift_renameFields f _)

omit [Fintype Field] in
/-- Injective field relabeling preserves the derived equations. Merging two
field labels is not a change of convention and needs a separate reduction. -/
theorem eulerLagrange_renameFields {OtherField : Type*} (f : Field → OtherField)
    (hf : Function.Injective f) (L : FirstOrderLagrangian R Field Direction) (a : Field) :
    eulerLagrange (renameFields f L) (f a) =
      JetPolynomial.renameFields f (eulerLagrange L a) := by
  simp [eulerLagrange, fieldPartial_renameFields f hf, momentum_renameFields f hf,
    JetPolynomial.renameFields_totalDerivative]

end FirstOrderLagrangian
end LeanPhy.FieldTheory
