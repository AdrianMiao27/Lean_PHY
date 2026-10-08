import LeanPhy.FieldTheory.Variational

/-!
# Interacting polynomial actions with kinetic mixing

The input is an arbitrary finite set of real commuting fields, an arbitrary
finite set of coordinate directions, a constant kinetic tensor on their
product, and an arbitrary polynomial potential. The tensor explicitly carries
all spacetime-sign and component-mixing choices. Symmetry is required only for
the usual simplified equation; no positivity, invertibility, or solution
existence is inferred from a formal action.

This supplies a reusable action-to-equation operation for coupled scalar field
models, anisotropic effective actions and finite-mode/lattice mechanical
models. Complex scalar fields can be expressed as real components. This is
not a fermionic action or a spacetime-integrated existence theorem.
-/

namespace LeanPhy.FieldTheory.FirstOrderLagrangian

open JetPolynomial
open scoped BigOperators

variable {R Field Direction : Type*} [CommRing R]

/-- Insert a field-only interaction potential into a first-order density. -/
noncomputable def potential : MvPolynomial Field R →ₐ[R]
    FirstOrderLagrangian R Field Direction :=
  MvPolynomial.rename (fun a => (a, none))

@[simp] theorem fieldPartial_potential (V : MvPolynomial Field R) (a : Field) :
    fieldPartial (potential V : FirstOrderLagrangian R Field Direction) a =
      lift (potential (MvPolynomial.pderiv a V)) := by
  unfold fieldPartial potential
  exact congrArg lift (MvPolynomial.pderiv_rename
    (f := fun b : Field => (b, (none : Option Direction)))
    (fun _ _ h => congrArg Prod.fst h) a V)

@[simp] theorem momentum_potential (V : MvPolynomial Field R) (a : Field) (μ : Direction) :
    momentum (potential V : FirstOrderLagrangian R Field Direction) a μ = 0 := by
  have h : MvPolynomial.pderiv (a, some μ)
      (potential V : FirstOrderLagrangian R Field Direction) = 0 := by
    induction V using MvPolynomial.induction_on with
    | C r => simp [potential]
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp =>
        simp only [map_mul, Derivation.leibniz, smul_eq_mul, hp, mul_zero, add_zero]
        simp [potential]
  simp [momentum, h]

variable [Fintype Field] [Fintype Direction]

omit [Fintype Field] in
@[simp] theorem eulerLagrange_potential (V : MvPolynomial Field R) (a : Field) :
    eulerLagrange (potential V : FirstOrderLagrangian R Field Direction) a =
      lift (potential (MvPolynomial.pderiv a V)) := by
  simp [eulerLagrange]

/-- The constant-coefficient density `1/2 K_(aμ,bν) ∂_μ φ_a ∂_ν φ_b`.
Symmetry is not built into the definition, so nonsymmetric input stays visible. -/
noncomputable def quadraticKinetic
    (K : (Field × Direction) → (Field × Direction) → ℝ) :
    FirstOrderLagrangian ℝ Field Direction :=
  (1 / 2 : ℝ) • ∑ i, ∑ j,
    MvPolynomial.C (K i j) * gradient i.1 i.2 * gradient j.1 j.2

noncomputable def quadraticAction
    (K : (Field × Direction) → (Field × Direction) → ℝ) (V : MvPolynomial Field ℝ) :
    FirstOrderLagrangian ℝ Field Direction := quadraticKinetic K - potential V

omit [Fintype Field] [Fintype Direction] in
private theorem pderiv_gradient_pair [DecidableEq Field] [DecidableEq Direction]
    (i j : Field × Direction) :
    MvPolynomial.pderiv (i.1, some i.2)
      (gradient j.1 j.2 : FirstOrderLagrangian ℝ Field Direction) =
        if j = i then 1 else 0 := by
  classical
  change _ = if (j.1, j.2) = (i.1, i.2) then _ else _
  simp [gradient, MvPolynomial.pderiv_X, Pi.single_apply, Prod.ext_iff]

@[simp] theorem fieldPartial_quadraticKinetic
    (K : (Field × Direction) → (Field × Direction) → ℝ) (a : Field) :
    fieldPartial (quadraticKinetic K) a = 0 := by
  classical
  simp [fieldPartial, quadraticKinetic, gradient, Derivation.leibniz,
    smul_eq_mul, MvPolynomial.pderiv_X]

/-- Without symmetry, both index orderings of the kinetic tensor contribute. -/
theorem momentum_quadraticKinetic
    (K : (Field × Direction) → (Field × Direction) → ℝ) (a : Field) (μ : Direction) :
    momentum (quadraticKinetic K) a μ = (1 / 2 : ℝ) •
      ((∑ j, MvPolynomial.C (K (a, μ) j) * jet j.1 (Finsupp.single j.2 1)) +
       (∑ j, MvPolynomial.C (K j (a, μ)) * jet j.1 (Finsupp.single j.2 1))) := by
  classical
  have hself : MvPolynomial.pderiv (a, some μ)
      (gradient a μ : FirstOrderLagrangian ℝ Field Direction) = 1 := by simp [gradient]
  have hterm (i j : Field × Direction) :
      MvPolynomial.pderiv (a, some μ)
        (MvPolynomial.C (K i j) * gradient i.1 i.2 * gradient j.1 j.2 :
          FirstOrderLagrangian ℝ Field Direction) =
        (if i = (a, μ) then MvPolynomial.C (K i j) * gradient j.1 j.2 else 0) +
        (if j = (a, μ) then MvPolynomial.C (K i j) * gradient i.1 i.2 else 0) := by
    by_cases hi : i = (a, μ) <;> by_cases hj : j = (a, μ) <;>
      simp [pderiv_gradient_pair (a, μ), hi, hj, hself] <;> ring
  simp only [momentum, quadraticKinetic, Derivation.map_smul, map_sum, hterm,
    Finset.sum_add_distrib, Finset.sum_ite_irrel]
  simp [lift_gradient]

/-- The standard momentum formula needs a symmetric kinetic tensor. -/
theorem momentum_quadraticKinetic_of_symmetric
    (K : (Field × Direction) → (Field × Direction) → ℝ)
    (hK : ∀ i j, K i j = K j i) (a : Field) (μ : Direction) :
    momentum (quadraticKinetic K) a μ =
      ∑ j, MvPolynomial.C (K (a, μ) j) * jet j.1 (Finsupp.single j.2 1) := by
  rw [momentum_quadraticKinetic]
  simp_rw [hK _ (a, μ)]
  module

/-- Derived coupled Euler equations for any polynomial interaction potential.
The Hessian jet contains both coordinate directions; no diagonal or
single-component approximation is made. -/
theorem eulerLagrange_quadraticAction
    (K : (Field × Direction) → (Field × Direction) → ℝ)
    (hK : ∀ i j, K i j = K j i) (V : MvPolynomial Field ℝ) (a : Field) :
    eulerLagrange (quadraticAction K V) a =
      -lift (potential (MvPolynomial.pderiv a V)) -
        ∑ μ, ∑ j, MvPolynomial.C (K (a, μ) j) *
          jet j.1 (Finsupp.single j.2 1 + Finsupp.single μ 1) := by
  have hfield : fieldPartial (quadraticAction K V) a =
      -lift (potential (MvPolynomial.pderiv a V)) := by
    simp only [quadraticAction, fieldPartial, map_sub]
    change fieldPartial (quadraticKinetic K) a - fieldPartial (potential V) a = _
    simp
  have hm (μ : Direction) : momentum (quadraticAction K V) a μ =
      ∑ j, MvPolynomial.C (K (a, μ) j) * jet j.1 (Finsupp.single j.2 1) := by
    simp only [quadraticAction, momentum, map_sub]
    change momentum (quadraticKinetic K) a μ - momentum (potential V) a μ = _
    simp [momentum_quadraticKinetic_of_symmetric K hK]
  simp [eulerLagrange, hfield, hm, Derivation.leibniz, smul_eq_mul]

/-- A constant shift varies only the interaction potential. This checks the
symmetry condition before any current-conservation claim is used. -/
theorem firstVariation_quadraticAction_shift
    (K : (Field × Direction) → (Field × Direction) → ℝ)
    (V : MvPolynomial Field ℝ) (c : Field → ℝ) :
    firstVariation (quadraticAction K V) (fun a => MvPolynomial.C (c a)) =
      -(∑ a, lift (potential (MvPolynomial.pderiv a V)) * MvPolynomial.C (c a)) := by
  unfold firstVariation
  simp only [MvPolynomial.derivation_C, mul_zero, Finset.sum_const_zero, add_zero]
  have hfield (a : Field) : fieldPartial (quadraticAction K V) a =
      -lift (potential (MvPolynomial.pderiv a V)) := by
    simp only [quadraticAction, fieldPartial, map_sub]
    change fieldPartial (quadraticKinetic K) a - fieldPartial (potential V) a = _
    simp
  simp [hfield, Finset.sum_neg_distrib]

end LeanPhy.FieldTheory.FirstOrderLagrangian
