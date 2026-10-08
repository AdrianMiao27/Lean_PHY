import LeanPhy.Mathematics.CentralExtension

/-!
# First-order Lie deformations and changes of generators

The pair `(x,u)` represents `x + εu`, with `ε² = 0`. An adjoint
two-cochain changes the first-order bracket. Its Jacobi identity is equivalent
to the CE cocycle equation. Equivalences fixing the reduction and tangent
inclusion are classified by the actual adjoint `H2` quotient.

This is a first-order statement over a commutative ring, with no convergence,
integration to Lie groups, or automatic extension to higher orders.
-/

namespace LeanPhy.Mathematics.LieDeformation

open LieCohomology

universe u v
variable {R : Type u} {V : Type v} [CommRing R] [AddCommGroup V] [Module R V]
variable {L : LieAlgebra R V}

abbrev Cochain (L : LieAlgebra R V) := LieCochain2 L (adjointLieModule L)

/-- The coefficient of the first power of the deformation parameter in Jacobi. -/
def linearJacobi (ω : Cochain L) (x y z : V) : V :=
  L.bracket x (ω y z) + L.bracket y (ω z x) + L.bracket z (ω x y) +
    ω x (L.bracket y z) + ω y (L.bracket z x) + ω z (L.bracket x y)

theorem linearJacobi_eq_differential2 (ω : Cochain L) (x y z : V) :
    linearJacobi ω x y z = differential2 (adjointLieModule L) ω x y z := by
  rw [differential2_apply]
  simp only [linearJacobi, adjointLieModule]
  rw [ω.skew z x, L.bracket_neg_right, ω.skew x (L.bracket y z),
    ω.skew y (L.bracket z x), ω.skew z (L.bracket x y),
    L.antisymm z x, LieCochain2.neg_left]
  abel

/-- The bracket on first-order jets. No Jacobi premise is hidden here. -/
def bracket (ω : Cochain L) (x y : V × V) : V × V :=
  (L.bracket x.1 y.1, L.bracket x.1 y.2 + L.bracket x.2 y.1 + ω x.1 y.1)

theorem jacobi_snd (ω : Cochain L) (x y z : V × V) :
    (bracket ω x (bracket ω y z) + bracket ω y (bracket ω z x) +
      bracket ω z (bracket ω x y)).2 =
        differential2 (adjointLieModule L) ω x.1 y.1 z.1 := by
  rw [← linearJacobi_eq_differential2]
  simp only [bracket, Prod.snd_add, LieAlgebra.bracket_add_right]
  calc
    _ = (L.bracket x.1 (L.bracket y.1 z.2) + L.bracket y.1 (L.bracket z.2 x.1) +
            L.bracket z.2 (L.bracket x.1 y.1)) +
        (L.bracket x.1 (L.bracket y.2 z.1) + L.bracket y.2 (L.bracket z.1 x.1) +
            L.bracket z.1 (L.bracket x.1 y.2)) +
        (L.bracket x.2 (L.bracket y.1 z.1) + L.bracket y.1 (L.bracket z.1 x.2) +
            L.bracket z.1 (L.bracket x.2 y.1)) + linearJacobi ω x.1 y.1 z.1 := by
      dsimp [linearJacobi]; abel
    _ = _ := by rw [L.jacobi, L.jacobi, L.jacobi]; simp

/-- Full Jacobi on jets holds exactly for adjoint cocycles. -/
theorem jacobi_iff_cocycle (ω : Cochain L) :
    (∀ x y z, bracket ω x (bracket ω y z) + bracket ω y (bracket ω z x) +
      bracket ω z (bracket ω x y) = 0) ↔ IsTwoCocycle (adjointLieModule L) ω := by
  rw [isTwoCocycle_iff]
  constructor
  · intro h x y z
    have hh := congrArg Prod.snd (h (x,0) (y,0) (z,0))
    simpa only [jacobi_snd, Prod.snd_zero] using hh
  · intro h x y z
    apply Prod.ext
    · exact L.jacobi x.1 y.1 z.1
    · rw [jacobi_snd]; exact h x.1 y.1 z.1

/-- An actual Lie algebra over the original scalar ring on the jet carrier. -/
def algebra (ω : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω) :
    LieAlgebra R (V × V) where
  bracket := bracket ω
  add_left := by
    intros; apply Prod.ext <;> simp [bracket]
    abel
  add_right := by
    intros; apply Prod.ext <;> simp [bracket]
    abel
  smul_left := by intros; apply Prod.ext <;> simp [bracket, smul_add]
  smul_right := by intros; apply Prod.ext <;> simp [bracket, smul_add]
  zero_left := by intros; apply Prod.ext <;> simp [bracket]
  alternating := by
    intro x; apply Prod.ext
    · exact L.alternating x.1
    · simp only [bracket, LieCochain2.alternating, add_zero]
      rw [L.antisymm x.2 x.1]; exact add_neg_cancel _
  antisymm := by
    intro x y; apply Prod.ext
    · exact L.antisymm x.1 y.1
    · simp only [bracket, Prod.snd_neg]
      rw [L.antisymm x.1 y.2, L.antisymm x.2 y.1, ω.skew x.1 y.1]; abel
  jacobi := (jacobi_iff_cocycle ω).mpr hω

theorem algebra_exists_iff (ω : Cochain L) :
    (∃ D : LieAlgebra R (V × V), D.bracket = bracket ω) ↔
      IsTwoCocycle (adjointLieModule L) ω := by
  constructor
  · rintro ⟨D,hD⟩
    apply (jacobi_iff_cocycle ω).mp
    rw [← hD]
    exact D.jacobi
  · intro h; exact ⟨algebra ω h,rfl⟩

/-- Multiplication by the formal parameter, explicitly square-zero. -/
def epsilon : (V × V) →ₗ[R] (V × V) :=
  (LinearMap.inr R V V).comp (LinearMap.fst R V V)

@[simp] theorem epsilon_apply (x : V × V) : epsilon (R := R) x = (0,x.1) := rfl

@[simp] theorem epsilon_square (x : V × V) :
    epsilon (R := R) (epsilon (R := R) x) = 0 := rfl

theorem bracket_epsilon_left (ω : Cochain L) (x y : V × V) :
    bracket ω (epsilon (R := R) x) y = epsilon (R := R) (bracket ω x y) := by
  apply Prod.ext <;> simp [bracket]

theorem bracket_epsilon_right (ω : Cochain L) (x y : V × V) :
    bracket ω x (epsilon (R := R) y) = epsilon (R := R) (bracket ω x y) := by
  apply Prod.ext <;> simp [bracket]

/-- Fix both the original generators modulo ε and the tangent inclusion. -/
structure Equivalence (ω η : Cochain L) where
  source_cocycle : IsTwoCocycle (adjointLieModule L) ω
  target_cocycle : IsTwoCocycle (adjointLieModule L) η
  linearEquiv : (V × V) ≃ₗ[R] (V × V)
  map_bracket : ∀ x y, linearEquiv (bracket ω x y) =
    bracket η (linearEquiv x) (linearEquiv y)
  map_reduction : ∀ x, (linearEquiv x).1 = x.1
  map_tangent : ∀ u, linearEquiv (0,u) = (0,u)

/-- Change generators by `x ↦ x + ε φ(x)`. The inverse subtracts `φ`. -/
abbrev gauge (φ : V →ₗ[R] V) : (V × V) ≃ₗ[R] (V × V) := CentralExtension.shear φ

theorem gauge_bracket_iff (ω η : Cochain L) (φ : V →ₗ[R] V) :
    (∀ x y, gauge φ (bracket ω x y) = bracket η (gauge φ x) (gauge φ y)) ↔
      differential1 (adjointLieModule L) φ = ω - η := by
  constructor
  · intro h
    ext x y
    have hh := congrArg Prod.snd (h (x,0) (y,0))
    simp [gauge, CentralExtension.shear, bracket] at hh
    simp only [differential1, adjointLieModule, LieCochain2.sub_apply]
    rw [L.antisymm (φ x) y] at hh
    rw [← sub_eq_zero] at hh ⊢
    calc
      _ = -(ω x y + φ (L.bracket x y) -
          (L.bracket x (φ y) + -L.bracket y (φ x) + η x y)) := by abel
      _ = 0 := by rw [hh, neg_zero]
  · intro h x y
    apply Prod.ext
    · rfl
    have hh := congrArg (fun a : Cochain L => a x.1 y.1) h
    simp only [differential1, adjointLieModule, LieCochain2.sub_apply] at hh
    change L.bracket x.1 y.2 + L.bracket x.2 y.1 + ω x.1 y.1 + φ (L.bracket x.1 y.1) =
      L.bracket x.1 (y.2 + φ y.1) + L.bracket (x.2 + φ x.1) y.1 + η x.1 y.1
    rw [L.add_right, L.add_left, L.antisymm (φ x.1) y.1]
    calc
      _ = L.bracket x.1 y.2 + L.bracket x.2 y.1 + (ω x.1 y.1 - η x.1 y.1) +
          φ (L.bracket x.1 y.1) + η x.1 y.1 := by abel
      _ = _ := by rw [← hh]; abel

def equivalenceOfCoboundary (ω η : Cochain L) (φ : V →ₗ[R] V)
    (hφ : differential1 (adjointLieModule L) φ = ω - η)
    (hω : IsTwoCocycle (adjointLieModule L) ω) : Equivalence ω η where
  source_cocycle := hω
  target_cocycle := cocycle_of_cohomologous _ hω ⟨φ,hφ⟩
  linearEquiv := gauge φ
  map_bracket := (gauge_bracket_iff ω η φ).mpr hφ
  map_reduction := by intros; rfl
  map_tangent := by intro u; change (0,u + φ 0) = (0,u); simp

namespace Equivalence

variable {ω η : Cochain L}

def generatorChange (E : Equivalence ω η) : V →ₗ[R] V :=
  (LinearMap.snd R V V).comp (E.linearEquiv.toLinearMap.comp (LinearMap.inl R V V))

theorem apply_eq_gauge (E : Equivalence ω η) (x : V × V) :
    E.linearEquiv x = gauge E.generatorChange x := by
  apply Prod.ext
  · exact E.map_reduction x
  · have hx : x = (x.1,0) + (0,x.2) := by ext <;> simp
    conv_lhs => rw [hx, map_add, E.map_tangent]
    change (E.linearEquiv (x.1,0)).2 + x.2 = x.2 + (E.linearEquiv (x.1,0)).2
    exact add_comm _ _

theorem coboundary_generatorChange (E : Equivalence ω η) :
    differential1 (adjointLieModule L) E.generatorChange = ω - η := by
  apply (gauge_bracket_iff ω η E.generatorChange).mp
  intro x y
  simpa only [E.apply_eq_gauge] using E.map_bracket x y

theorem commutes_epsilon (E : Equivalence ω η) (x : V × V) :
    E.linearEquiv (epsilon (R := R) x) = epsilon (R := R) (E.linearEquiv x) := by
  simp only [epsilon_apply, E.map_tangent, E.map_reduction]

end Equivalence

/-- Actual adjoint H² class equality is precisely first-order equivalence. -/
theorem class_eq_iff_nonempty_equivalence (ω η : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hη : IsTwoCocycle (adjointLieModule L) η) :
    classOf (adjointLieModule L) ω hω = classOf (adjointLieModule L) η hη ↔
      Nonempty (Equivalence ω η) := by
  rw [classOf_eq_iff]
  constructor
  · rintro ⟨φ,hφ⟩; exact ⟨equivalenceOfCoboundary ω η φ hφ hω⟩
  · rintro ⟨E⟩; exact ⟨E.generatorChange,E.coboundary_generatorChange⟩

theorem nonempty_equivalence_zero_iff (ω : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) :
    Nonempty (Equivalence ω 0) ↔ IsTwoCoboundary (adjointLieModule L) ω := by
  constructor
  · rintro ⟨E⟩; exact ⟨E.generatorChange, by simpa using E.coboundary_generatorChange⟩
  · rintro ⟨φ,hφ⟩
    exact ⟨equivalenceOfCoboundary ω 0 φ (by simpa using hφ) hω⟩

/-- Vanishing of the actual H² quotient gives first-order triviality only. -/
theorem firstOrder_trivial_of_subsingleton_h2 [Subsingleton (H2 (adjointLieModule L))]
    (ω : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω) :
    Nonempty (Equivalence ω 0) := by
  apply (nonempty_equivalence_zero_iff ω hω).mpr
  exact (classOf_eq_zero_iff _ ω hω).mp (Subsingleton.elim _ _)

/-- The quadratic Jacobi obstruction, without division by two. -/
def obstruction (ω : Cochain L) (x y z : V) : V :=
  ω x (ω y z) + ω y (ω z x) + ω z (ω x y)

/-- Jets through order two, with coefficients of ε³ and higher discarded. -/
def secondBracket (ω ν : Cochain L) (x y : V × V × V) : V × V × V :=
  (L.bracket x.1 y.1,
   L.bracket x.1 y.2.1 + L.bracket x.2.1 y.1 + ω x.1 y.1,
   L.bracket x.1 y.2.2 + L.bracket x.2.1 y.2.1 + L.bracket x.2.2 y.1 +
     ω x.1 y.2.1 + ω x.2.1 y.1 + ν x.1 y.1)

theorem secondJacobi_top (ω ν : Cochain L) (x y z : V × V × V) :
    (secondBracket ω ν x (secondBracket ω ν y z) +
     secondBracket ω ν y (secondBracket ω ν z x) +
     secondBracket ω ν z (secondBracket ω ν x y)).2.2 =
      differential2 (adjointLieModule L) ν x.1 y.1 z.1 + obstruction ω x.1 y.1 z.1 +
      differential2 (adjointLieModule L) ω x.1 y.1 z.2.1 +
      differential2 (adjointLieModule L) ω x.1 y.2.1 z.1 +
      differential2 (adjointLieModule L) ω x.2.1 y.1 z.1 := by
  let J (a b c : V) := L.bracket a (L.bracket b c) +
    L.bracket b (L.bracket c a) + L.bracket c (L.bracket a b)
  have hJ (a b c : V) : J a b c = 0 := L.jacobi a b c
  calc
    _ = J x.1 y.1 z.2.2 + J x.1 y.2.1 z.2.1 + J x.1 y.2.2 z.1 +
        J x.2.1 y.1 z.2.1 + J x.2.1 y.2.1 z.1 + J x.2.2 y.1 z.1 +
        linearJacobi ν x.1 y.1 z.1 + obstruction ω x.1 y.1 z.1 +
        linearJacobi ω x.1 y.1 z.2.1 + linearJacobi ω x.1 y.2.1 z.1 +
        linearJacobi ω x.2.1 y.1 z.1 := by
      simp only [secondBracket, Prod.snd_add,
        LieAlgebra.bracket_add_right, LieCochain2.map_add_right,
        J, linearJacobi, obstruction]
      abel
    _ = _ := by simp only [hJ, zero_add, linearJacobi_eq_differential2]

/-- The second-order Jacobi coefficient on original generators is computed,
not stipulated as the definition of a valid deformation. -/
theorem secondJacobi_on_constants (ω ν : Cochain L) (x y z : V) :
    (secondBracket ω ν (x,0,0) (secondBracket ω ν (y,0,0) (z,0,0)) +
     secondBracket ω ν (y,0,0) (secondBracket ω ν (z,0,0) (x,0,0)) +
     secondBracket ω ν (z,0,0) (secondBracket ω ν (x,0,0) (y,0,0))).2.2 =
      differential2 (adjointLieModule L) ν x y z + obstruction ω x y z := by
  rw [← linearJacobi_eq_differential2]
  simp [secondBracket, linearJacobi, obstruction]
  abel

/-- Every actual Lie algebra with this second-order bracket must cancel the
quadratic obstruction with the differential of its second-order correction. -/
theorem obstruction_of_secondOrder_model (ω ν : Cochain L)
    (D : LieAlgebra R (V × V × V)) (hD : D.bracket = secondBracket ω ν) (x y z : V) :
    differential2 (adjointLieModule L) ν x y z + obstruction ω x y z = 0 := by
  have h := congrArg (fun a : V × V × V => a.2.2) (D.jacobi (x,0,0) (y,0,0) (z,0,0))
  rw [hD, secondJacobi_on_constants] at h
  exact h

/-- These are exactly the two equations needed for full second-order Jacobi. -/
theorem secondJacobi_iff (ω ν : Cochain L) :
    (∀ x y z, secondBracket ω ν x (secondBracket ω ν y z) +
      secondBracket ω ν y (secondBracket ω ν z x) +
      secondBracket ω ν z (secondBracket ω ν x y) = 0) ↔
    IsTwoCocycle (adjointLieModule L) ω ∧
      ∀ x y z, differential2 (adjointLieModule L) ν x y z + obstruction ω x y z = 0 := by
  constructor
  · intro h
    constructor
    · rw [isTwoCocycle_iff]
      intro x y z
      have hh := congrArg (fun a : V × V × V => a.2.1) (h (x,0,0) (y,0,0) (z,0,0))
      have heq := jacobi_snd ω (x,0) (y,0) (z,0)
      exact heq ▸ hh
    · intro x y z
      simpa only [secondJacobi_on_constants, Prod.snd_zero] using
        congrArg (fun a : V × V × V => a.2.2) (h (x,0,0) (y,0,0) (z,0,0))
  · rintro ⟨hω,hν⟩ x y z
    apply Prod.ext
    · exact L.jacobi x.1 y.1 z.1
    · apply Prod.ext
      · exact congrArg Prod.snd ((jacobi_iff_cocycle ω).mpr hω
          (x.1,x.2.1) (y.1,y.2.1) (z.1,z.2.1))
      · rw [secondJacobi_top, hν]
        simp only [(isTwoCocycle_iff _ _).mp hω, add_zero, Prod.snd_zero]

/-- Construct a genuine Lie algebra through order two from a checked correction. -/
def secondAlgebra (ω ν : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω)
    (hν : ∀ x y z, differential2 (adjointLieModule L) ν x y z + obstruction ω x y z = 0) :
    LieAlgebra R (V × V × V) where
  bracket := secondBracket ω ν
  add_left := by
    intros; apply Prod.ext; · simp [secondBracket]
    apply Prod.ext <;> simp [secondBracket] <;> abel
  add_right := by
    intros; apply Prod.ext; · simp [secondBracket]
    apply Prod.ext <;> simp [secondBracket] <;> abel
  smul_left := by
    intros; apply Prod.ext; · simp [secondBracket]
    apply Prod.ext <;> simp [secondBracket, smul_add]
  smul_right := by
    intros; apply Prod.ext; · simp [secondBracket]
    apply Prod.ext <;> simp [secondBracket, smul_add]
  zero_left := by
    intros; apply Prod.ext; · simp [secondBracket]
    apply Prod.ext <;> simp [secondBracket]
  alternating := by
    intro x; apply Prod.ext; · exact L.alternating x.1
    apply Prod.ext
    · change L.bracket x.1 x.2.1 + L.bracket x.2.1 x.1 + ω x.1 x.1 = 0
      rw [L.antisymm x.2.1 x.1, ω.alternating]; abel
    · simp only [secondBracket, LieAlgebra.bracket_self, LieCochain2.alternating, Prod.snd_zero]
      rw [L.antisymm x.2.2 x.1, ω.skew x.2.1 x.1]; abel
  antisymm := by
    intro x y; apply Prod.ext; · exact L.antisymm x.1 y.1
    apply Prod.ext
    · simp only [secondBracket, Prod.snd_neg, Prod.fst_neg]
      rw [L.antisymm x.1 y.2.1, L.antisymm x.2.1 y.1, ω.skew x.1 y.1]; abel
    · simp only [secondBracket, Prod.snd_neg]
      rw [L.antisymm x.1 y.2.2, L.antisymm x.2.1 y.2.1, L.antisymm x.2.2 y.1,
        ω.skew x.1 y.2.1, ω.skew x.2.1 y.1, ν.skew x.1 y.1]; abel
  jacobi := (secondJacobi_iff ω ν).mpr ⟨hω,hν⟩

theorem secondAlgebra_exists_iff (ω ν : Cochain L) :
    (∃ D : LieAlgebra R (V × V × V), D.bracket = secondBracket ω ν) ↔
    IsTwoCocycle (adjointLieModule L) ω ∧
      ∀ x y z, differential2 (adjointLieModule L) ν x y z + obstruction ω x y z = 0 := by
  constructor
  · rintro ⟨D,hD⟩
    apply (secondJacobi_iff ω ν).mp
    rw [← hD]; exact D.jacobi
  · rintro ⟨hω,hν⟩; exact ⟨secondAlgebra ω ν hω hν,rfl⟩

end LeanPhy.Mathematics.LieDeformation
