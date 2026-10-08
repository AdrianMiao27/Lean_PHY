import LeanPhy.FieldTheory.Jet
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Matrix.Basic

set_option autoImplicit false

/-!
# Finite derivative expansion for coupled propagating heavy fields

The leading mass operator is an actual unit. Kinetic insertions retain their
order even when masses, mixing and background-dependent coefficients do not
commute. Every finite truncation has an exact equation residual; no Green
operator, boundary condition, small-gradient bound or convergence is inferred.

The differential operator below acts on existing polynomial jets (or any real
differential algebra). Thus kinetic insertions actually differentiate both
profiles and their variable coefficients, rather than being scalar placeholders.
-/

namespace LeanPhy.FieldTheory.PropagatingHeavy

open scoped BigOperators

section Expansion

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- `D = M - ε L`, with Euclidean `L = div Z grad` in the differential adapter. -/
def operator (M : (Module.End ℝ V)ˣ) (L : Module.End ℝ V) (ε : ℝ) : Module.End ℝ V :=
  (M : Module.End ℝ V) - ε • L

/-- N kinetic insertions, i.e. orders 0 through N-1, with ordered mass inverses. -/
def inverseApprox (M : (Module.End ℝ V)ˣ) (L : Module.End ℝ V) (ε : ℝ) (N : ℕ) :
    Module.End ℝ V :=
  (∑ k ∈ Finset.range N, (ε • ((↑(M⁻¹) : Module.End ℝ V) * L)) ^ k) * ↑(M⁻¹)

def reconstruct (M : (Module.End ℝ V)ˣ) (L : Module.End ℝ V) (ε : ℝ) (N : ℕ)
    (J : V) : V := -(inverseApprox M L ε N J)

def equation (M : (Module.End ℝ V)ˣ) (L : Module.End ℝ V) (ε : ℝ)
    (J χ : V) : V := operator M L ε χ + J

theorem operator_factor (M : (Module.End ℝ V)ˣ) (L : Module.End ℝ V) (ε : ℝ) :
    operator M L ε = (M : Module.End ℝ V) *
      (1 - ε • ((↑(M⁻¹) : Module.End ℝ V) * L)) := by
  simp [operator, mul_sub, ← mul_assoc]

/-- A finite sum is not silently promoted to an exact inverse. -/
theorem inverse_residual (M : (Module.End ℝ V)ˣ) (L : Module.End ℝ V)
    (ε : ℝ) (N : ℕ) :
    1 - operator M L ε * inverseApprox M L ε N =
      (M : Module.End ℝ V) * (ε • ((↑(M⁻¹) : Module.End ℝ V) * L)) ^ N * ↑(M⁻¹) := by
  rw [operator_factor, inverseApprox]
  rw [show (M : Module.End ℝ V) * (1 - ε • ((↑(M⁻¹) : Module.End ℝ V) * L)) *
      ((∑ k ∈ Finset.range N, (ε • ((↑(M⁻¹) : Module.End ℝ V) * L)) ^ k) * ↑(M⁻¹)) =
      (M : Module.End ℝ V) * ((1 - ε • ((↑(M⁻¹) : Module.End ℝ V) * L)) *
        (∑ k ∈ Finset.range N, (ε • ((↑(M⁻¹) : Module.End ℝ V) * L)) ^ k)) * ↑(M⁻¹) by
    simp only [mul_assoc]]
  rw [mul_neg_geom_sum]
  simp [mul_sub, sub_mul]

/-- Exact residual at the reconstructed field, valid including the zero-term cutoff. -/
theorem equation_reconstruct (M : (Module.End ℝ V)ˣ) (L : Module.End ℝ V)
    (ε : ℝ) (N : ℕ) (J : V) :
    equation M L ε J (reconstruct M L ε N J) =
      ((M : Module.End ℝ V) * (ε • ((↑(M⁻¹) : Module.End ℝ V) * L)) ^ N * ↑(M⁻¹)) J := by
  have h := congrArg (fun A : Module.End ℝ V => A J) (inverse_residual M L ε N)
  simpa [equation, reconstruct, Module.End.mul_apply, sub_eq_add_neg, add_comm] using h

/-- The remainder carries ε^N explicitly. This is an order statement, not a norm bound. -/
theorem equation_reconstruct_order (M : (Module.End ℝ V)ˣ) (L : Module.End ℝ V)
    (ε : ℝ) (N : ℕ) (J : V) :
    equation M L ε J (reconstruct M L ε N J) =
      ε ^ N • (((M : Module.End ℝ V) * ((↑(M⁻¹) : Module.End ℝ V) * L) ^ N * ↑(M⁻¹)) J) := by
  rw [equation_reconstruct, smul_pow, mul_smul_comm, smul_mul_assoc]
  rfl

theorem reconstruct_source_shift (M : (Module.End ℝ V)ˣ) (L : Module.End ℝ V)
    (ε s : ℝ) (N : ℕ) (J Q : V) :
    reconstruct M L ε N (J + s • Q) =
      reconstruct M L ε N J + s • reconstruct M L ε N Q := by
  simp [reconstruct, neg_add_rev, add_comm]

end Expansion

section Differential

variable {R H Direction : Type*} [CommRing R] [Algebra ℝ R]
  [Fintype H] [DecidableEq H] [Fintype Direction]

/-- Constant, potentially mixed, mass matrices act on all heavy components. -/
def massMap (M : Matrix H H ℝ) : Module.End ℝ (H → R) where
  toFun χ i := ∑ j, M i j • χ j
  map_add' χ ψ := by ext i; simp [smul_add, Finset.sum_add_distrib]
  map_smul' s χ := by
    funext i
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl (fun j _ => smul_comm (M i j) s (χ j))

omit [DecidableEq H] in
@[simp] theorem massMap_apply (M : Matrix H H ℝ) (χ : H → R) (i : H) :
    massMap M χ i = ∑ j, M i j • χ j := rfl

def massHom : Matrix H H ℝ →+* Module.End ℝ (H → R) where
  toFun := massMap
  map_zero' := by ext χ i; simp
  map_add' M N := by ext χ i; simp [add_smul, Finset.sum_add_distrib]
  map_one' := by ext χ i; simp [Matrix.one_apply]
  map_mul' M N := by
    apply LinearMap.ext
    intro χ
    funext i
    change (∑ j, (∑ k, M i k * N k j) • χ j) =
      ∑ k, M i k • (∑ j, N k j • χ j)
    simp only [Finset.sum_smul, mul_smul, Finset.smul_sum]
    rw [Finset.sum_comm]

/-- A proved invertible real mass matrix supplies the unit used by the expansion. -/
def massUnit (M : (Matrix H H ℝ)ˣ) : (Module.End ℝ (H → R))ˣ :=
  Units.map (massHom (R := R)).toMonoidHom M

@[simp] theorem massUnit_val (M : (Matrix H H ℝ)ˣ) :
    (massUnit (R := R) M : Module.End ℝ (H → R)) = massMap (M : Matrix H H ℝ) := rfl

/-- Matrix- and direction-valued derivative couplings may depend on light jets. -/
def gradientFlux (δ : Direction → Derivation ℝ R R)
    (Z : H → H → Direction → Direction → R) (χ : H → R) (i : H) (μ : Direction) : R :=
  ∑ j, ∑ ν, Z i j μ ν * δ ν (χ j)

def kinetic (δ : Direction → Derivation ℝ R R)
    (Z : H → H → Direction → Direction → R) : Module.End ℝ (H → R) where
  toFun χ i := ∑ μ, δ μ (gradientFlux δ Z χ i μ)
  map_add' χ ψ := by
    ext i
    simp [gradientFlux, map_add, mul_add, Finset.sum_add_distrib]
  map_smul' s χ := by
    ext i
    simp [gradientFlux, Finset.smul_sum]

omit [DecidableEq H] in
@[simp] theorem kinetic_apply (δ : Direction → Derivation ℝ R R)
    (Z : H → H → Direction → Direction → R) (χ : H → R) (i : H) :
    kinetic δ Z χ i = ∑ μ, δ μ (gradientFlux δ Z χ i μ) := rfl

end Differential
end LeanPhy.FieldTheory.PropagatingHeavy
