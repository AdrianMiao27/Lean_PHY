import LeanPhy.FieldTheory.PropagatingHeavy

set_option autoImplicit false

/-!
# Tree-level matching of quadratic propagating heavy sectors

Mass and derivative couplings may mix arbitrarily many heavy components.
Derivative coefficients and sources are elements of a differential algebra,
so polynomial light-field jets are valid inputs. The kinetic tensor is symmetric
under simultaneous exchange of component and direction. Its sign is explicit;
neither positivity nor a spacetime signature is inferred.

Finite elimination retains the equation residual, total divergence, transformed
source and induced readouts. It is a classical quadratic-heavy-sector operation,
not a determinant, functional measure, loop matching or interacting-heavy-field
solver. Actual interval integrals are supplied in `HeavyFieldInterval`.
-/

namespace LeanPhy.FieldTheory.PropagatingHeavy

open scoped BigOperators

variable {R H Direction : Type*} [CommRing R] [Algebra ℝ R]
  [Fintype H] [DecidableEq H] [Fintype Direction]

def pair (χ ψ : H → R) : R := ∑ i, χ i * ψ i

omit [Algebra ℝ R] [DecidableEq H] in
theorem pair_comm (χ ψ : H → R) : pair χ ψ = pair ψ χ := by
  simp only [pair, mul_comm]

omit [Algebra ℝ R] [DecidableEq H] in
@[simp] theorem pair_add_left (χ ψ η : H → R) :
    pair (χ + ψ) η = pair χ η + pair ψ η := by
  simp [pair, add_mul, Finset.sum_add_distrib]

omit [Algebra ℝ R] [DecidableEq H] in
@[simp] theorem pair_add_right (χ ψ η : H → R) :
    pair χ (ψ + η) = pair χ ψ + pair χ η := by
  simp [pair, mul_add, Finset.sum_add_distrib]

omit [DecidableEq H] in
@[simp] theorem pair_smul_left (s : ℝ) (χ ψ : H → R) :
    pair (s • χ) ψ = s • pair χ ψ := by simp [pair, Finset.smul_sum]

omit [DecidableEq H] in
@[simp] theorem pair_smul_right (s : ℝ) (χ ψ : H → R) :
    pair χ (s • ψ) = s • pair χ ψ := by simp [pair, Finset.smul_sum]

omit [Algebra ℝ R] [DecidableEq H] in
@[simp] theorem pair_sub_right (χ ψ η : H → R) :
    pair χ (ψ - η) = pair χ ψ - pair χ η := by
  simp [pair, mul_sub, Finset.sum_sub_distrib]

/-- Symmetry is required so the quadratic action produces the stated heavy equation. -/
structure Model (R H Direction : Type*) [CommRing R] [Algebra ℝ R]
    [Fintype H] [DecidableEq H] where
  derivative : Direction → Derivation ℝ R R
  mass : (Matrix H H ℝ)ˣ
  mass_symmetric : ∀ i j, (mass : Matrix H H ℝ) i j = (mass : Matrix H H ℝ) j i
  coupling : H → H → Direction → Direction → R
  coupling_symmetric : ∀ i j μ ν, coupling i j μ ν = coupling j i ν μ

namespace Model

variable (M : Model R H Direction)

def massOperator : (Module.End ℝ (H → R))ˣ := massUnit M.mass
def kineticOperator : Module.End ℝ (H → R) := kinetic M.derivative M.coupling

def field (ε : ℝ) (N : ℕ) (J : H → R) : H → R :=
  reconstruct M.massOperator M.kineticOperator ε N J

def residual (ε : ℝ) (J χ : H → R) : H → R :=
  equation M.massOperator M.kineticOperator ε J χ

def gradientPair (χ ψ : H → R) : R :=
  ∑ i, ∑ μ, M.derivative μ (χ i) * gradientFlux M.derivative M.coupling ψ i μ

@[simp] theorem gradientPair_add_left (χ ψ η : H → R) :
    M.gradientPair (χ + ψ) η = M.gradientPair χ η + M.gradientPair ψ η := by
  simp [gradientPair, add_mul, Finset.sum_add_distrib]

@[simp] theorem gradientPair_add_right (χ ψ η : H → R) :
    M.gradientPair χ (ψ + η) = M.gradientPair χ ψ + M.gradientPair χ η := by
  simp [gradientPair, gradientFlux, mul_add, Finset.sum_add_distrib]

@[simp] theorem gradientPair_smul_left (s : ℝ) (χ ψ : H → R) :
    M.gradientPair (s • χ) ψ = s • M.gradientPair χ ψ := by
  simp [gradientPair, Finset.smul_sum]

@[simp] theorem gradientPair_smul_right (s : ℝ) (χ ψ : H → R) :
    M.gradientPair χ (s • ψ) = s • M.gradientPair χ ψ := by
  simp [gradientPair, gradientFlux, Finset.smul_sum, Finset.mul_sum]

def flux (χ ψ : H → R) (μ : Direction) : R :=
  ∑ i, χ i * gradientFlux M.derivative M.coupling ψ i μ

def divergence (B : Direction → R) : R := ∑ μ, M.derivative μ (B μ)

/-- Local density with an explicit ε coefficient on the derivative energy. -/
noncomputable def density (ε : ℝ) (V : R) (J χ : H → R) : R :=
  V + (1 / 2 : ℝ) • (pair χ ((M.massOperator : Module.End ℝ (H → R)) χ) +
    ε • M.gradientPair χ χ) + pair χ J

noncomputable def effective (ε : ℝ) (N : ℕ) (V : R) (J : H → R) : R :=
  V + (1 / 2 : ℝ) • pair (M.field ε N J) J

def readout (ε : ℝ) (N : ℕ) (O : R) (Q J : H → R) : R :=
  O + pair Q (M.field ε N J)

omit [Fintype Direction] in
theorem mass_pair_symmetric (χ ψ : H → R) :
    pair χ ((M.massOperator : Module.End ℝ (H → R)) ψ) =
      pair ψ ((M.massOperator : Module.End ℝ (H → R)) χ) := by
  simp only [pair, massOperator, massUnit_val, massMap_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [M.mass_symmetric j i]
  simp [Algebra.smul_def, mul_comm, mul_left_comm]

theorem gradientPair_symmetric (χ ψ : H → R) :
    M.gradientPair χ ψ = M.gradientPair ψ χ := by
  simp only [gradientPair, gradientFlux, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro μ _
  rw [M.coupling_symmetric]
  ring

/-- Local integration by parts retains the derivative of variable coefficients. -/
theorem green_identity (χ ψ : H → R) :
    M.divergence (M.flux χ ψ) = M.gradientPair χ ψ + pair χ (M.kineticOperator ψ) := by
  simp only [divergence, flux, map_sum, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib, gradientPair, pair, kineticOperator, kinetic_apply,
    Finset.mul_sum]
  rw [add_comm]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro μ _
    ring
  · rw [Finset.sum_comm]

theorem residual_field (ε : ℝ) (N : ℕ) (J : H → R) :
    M.residual ε J (M.field ε N J) =
      ε ^ N • (((M.massOperator : Module.End ℝ (H → R)) *
        ((↑(M.massOperator⁻¹) : Module.End ℝ (H → R)) * M.kineticOperator) ^ N *
          ↑(M.massOperator⁻¹)) J) :=
  equation_reconstruct_order M.massOperator M.kineticOperator ε N J

/-- The stated residual is derived from the quadratic density's heavy-field
variation. The source and light-background coefficients are held fixed. -/
theorem density_perturb (ε s : ℝ) (V : R) (J χ η : H → R) :
    M.density ε V J (χ + s • η) = M.density ε V J χ +
      s • (pair η (M.residual ε J χ) + ε • M.divergence (M.flux η χ)) +
      (s ^ 2 / 2) • (pair η ((M.massOperator : Module.End ℝ (H → R)) η) +
        ε • M.gradientPair η η) := by
  rw [M.green_identity]
  simp only [density, residual, equation, operator, LinearMap.sub_apply,
    LinearMap.smul_apply, map_add, map_smul, pair_add_left, pair_add_right,
    pair_sub_right, pair_smul_left, pair_smul_right, gradientPair_add_left,
    gradientPair_add_right, gradientPair_smul_left, gradientPair_smul_right]
  rw [M.mass_pair_symmetric χ η, M.gradientPair_symmetric χ η]
  module

/-- The density relation is exact, with both the finite-order residual and
the total divergence retained. Symmetry alone cannot remove endpoint flux. -/
theorem density_matching (ε : ℝ) (N : ℕ) (V : R) (J : H → R) :
    M.density ε V J (M.field ε N J) = M.effective ε N V J +
      (1 / 2 : ℝ) • pair (M.field ε N J) (M.residual ε J (M.field ε N J)) +
      (ε / 2) • M.divergence (M.flux (M.field ε N J) (M.field ε N J)) := by
  rw [M.green_identity]
  simp only [density, effective, residual, equation, operator, LinearMap.sub_apply,
    LinearMap.smul_apply, pair_add_right, pair_sub_right, pair_smul_right]
  module

/-- Both mixed source terms and the quadratic contact contribution are kept. -/
theorem effective_source_shift (ε s : ℝ) (N : ℕ) (V : R) (J Q : H → R) :
    M.effective ε N V (J + s • Q) = M.effective ε N V J +
      (s / 2) • (pair (M.field ε N J) Q + pair (M.field ε N Q) J) +
      (s ^ 2 / 2) • pair (M.field ε N Q) Q := by
  simp only [effective, field, reconstruct_source_shift, pair_add_left,
    pair_add_right, pair_smul_left, pair_smul_right]
  module

theorem readout_source_shift (ε s : ℝ) (N : ℕ) (O : R) (Q J S : H → R) :
    M.readout ε N O Q (J + s • S) =
      M.readout ε N O Q J + s • pair Q (M.field ε N S) := by
  simp only [readout, field, reconstruct_source_shift, pair_add_right, pair_smul_right]
  abel

end Model

/-- Polynomial-jet construction supplies actual total derivatives, with no
additional derivative algebra or kinetic-equation proof required of the caller. -/
noncomputable def jetModel {Field : Type*} (M : (Matrix H H ℝ)ˣ)
    (hM : ∀ i j, (M : Matrix H H ℝ) i j = (M : Matrix H H ℝ) j i)
    (Z : H → H → Direction → Direction → JetPolynomial ℝ Field Direction)
    (hZ : ∀ i j μ ν, Z i j μ ν = Z j i ν μ) :
    Model (JetPolynomial ℝ Field Direction) H Direction where
  derivative := JetPolynomial.totalDerivative
  mass := M
  mass_symmetric := hM
  coupling := Z
  coupling_symmetric := hZ

end LeanPhy.FieldTheory.PropagatingHeavy
