import LeanPhy.Mathematics.LieDeformationSecondOrder

/-!
# Changes of generators through second order

The map `1 + εφ + ε²ψ` has inverse `1 - εφ + ε²(φ² - ψ)`.
It transports actual second-jet Lie brackets and their correction terms.
Consequently first-order equivalence and computed H² normalization preserve
second-order extendability. No all-orders equivalence or convergence is asserted.
-/

namespace LeanPhy.Mathematics.LieDeformation

open LieCohomology
set_option maxSynthPendingDepth 5

universe u v w
variable {R : Type u} {V : Type v} [CommRing R] [AddCommGroup V] [Module R V]
variable {L : LieAlgebra R V}

/-- Multiplication by the formal parameter on second jets. -/
def secondEpsilon : (V × V × V) →ₗ[R] (V × V × V) where
  toFun x := (0,x.1,x.2.1)
  map_add' := by intros; ext <;> simp
  map_smul' := by intros; ext <;> simp

/-- A change of generators through order two, with its actual inverse. -/
def secondGauge (φ ψ : V →ₗ[R] V) : (V × V × V) ≃ₗ[R] (V × V × V) where
  toFun x := (x.1,x.2.1 + φ x.1,x.2.2 + φ x.2.1 + ψ x.1)
  invFun x := (x.1,x.2.1 - φ x.1,x.2.2 - φ x.2.1 + φ (φ x.1) - ψ x.1)
  left_inv := by
    intro x
    apply Prod.ext; · rfl
    apply Prod.ext <;> simp only [map_add] <;> abel
  right_inv := by
    intro x
    apply Prod.ext; · rfl
    apply Prod.ext <;> simp only [map_sub] <;> abel
  map_add' := by
    intros
    apply Prod.ext; · rfl
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add] <;> abel
  map_smul' := by
    intros
    apply Prod.ext; · rfl
    apply Prod.ext <;> simp [smul_add]

@[simp] theorem secondGauge_apply (φ ψ : V →ₗ[R] V) (x : V × V × V) :
    secondGauge φ ψ x = (x.1,x.2.1 + φ x.1,x.2.2 + φ x.2.1 + ψ x.1) := rfl

@[simp] theorem secondGauge_symm_apply (φ ψ : V →ₗ[R] V) (x : V × V × V) :
    (secondGauge φ ψ).symm x =
      (x.1,x.2.1 - φ x.1,x.2.2 - φ x.2.1 + φ (φ x.1) - ψ x.1) := rfl

theorem secondGauge_commutes_epsilon (φ ψ : V →ₗ[R] V) (x : V × V × V) :
    secondGauge φ ψ (secondEpsilon (R := R) x) = secondEpsilon (R := R) (secondGauge φ ψ x) := by
  simp [secondEpsilon]

theorem secondGauge_truncation (φ ψ : V →ₗ[R] V) (x : V × V × V) :
    ((secondGauge φ ψ x).1,(secondGauge φ ψ x).2.1) = gauge φ (x.1,x.2.1) := rfl

/-- Composition includes a quadratic cross term even when ψ and ξ vanish. -/
theorem secondGauge_comp_apply (φ ψ χ ξ : V →ₗ[R] V) (x : V × V × V) :
    secondGauge χ ξ (secondGauge φ ψ x) =
      secondGauge (φ + χ) (ψ + ξ + χ.comp φ) x := by
  simp only [secondGauge_apply, map_add, LinearMap.add_apply, LinearMap.comp_apply]
  apply Prod.ext; · rfl
  apply Prod.ext <;> abel_nf

theorem secondGauge_inverse_parameters (φ ψ : V →ₗ[R] V) :
    (secondGauge φ ψ).symm = secondGauge (-φ) (φ.comp φ - ψ) := by
  apply LinearEquiv.ext
  intro x
  simp only [secondGauge_symm_apply, secondGauge_apply, LinearMap.neg_apply,
    LinearMap.sub_apply, LinearMap.comp_apply]
  apply Prod.ext; · rfl
  apply Prod.ext <;> abel_nf

/-- Exact correction transformation for a specified first-order generator change.
The premise relating ω and η is checked by `secondGauge_map_bracket`. -/
def transportCorrection (ω η : Cochain L) (φ ψ : V →ₗ[R] V) (ν : Cochain L) : Cochain L where
  eval x y := ν x y + φ (ω x y) - η (φ x) y - η x (φ y) -
    L.bracket (φ x) (φ y) - differential1 (adjointLieModule L) ψ x y
  map_add_left' := by
    intros
    simp only [LieCochain2.map_add_left, map_add, LieAlgebra.bracket_add_left]
    abel
  map_add_right' := by
    intros
    simp only [LieCochain2.map_add_right, map_add, LieAlgebra.bracket_add_right]
    abel
  map_smul_left' := by intros; simp [smul_add, smul_sub]
  map_smul_right' := by intros; simp [smul_add, smul_sub]
  alternating' := by
    intro x
    simp only [LieCochain2.alternating, map_zero, zero_add, LieAlgebra.bracket_self, sub_zero]
    rw [η.skew (φ x) x]
    abel

theorem direction_change_apply (ω η : Cochain L) (φ : V →ₗ[R] V)
    (hφ : differential1 (adjointLieModule L) φ = ω - η) (x y : V) :
    ω x y = L.bracket x (φ y) + L.bracket (φ x) y + η x y - φ (L.bracket x y) := by
  have h := congrArg (fun c : Cochain L => c x y) hφ
  simp only [differential1, adjointLieModule, LieCochain2.sub_apply] at h
  rw [L.antisymm (φ x) y]
  calc
    _ = (ω x y - η x y) + η x y := by abel
    _ = _ := by rw [← h]; abel

/-- The correction formula preserves the full bracket on arbitrary jets. -/
theorem secondGauge_map_bracket (ω η ν : Cochain L) (φ ψ : V →ₗ[R] V)
    (hφ : differential1 (adjointLieModule L) φ = ω - η) (x y : V × V × V) :
    secondGauge φ ψ (secondBracket ω ν x y) =
      secondBracket η (transportCorrection ω η φ ψ ν)
        (secondGauge φ ψ x) (secondGauge φ ψ y) := by
  apply Prod.ext; · rfl
  apply Prod.ext
  · exact congrArg Prod.snd ((gauge_bracket_iff ω η φ).mpr hφ (x.1,x.2.1) (y.1,y.2.1))
  · simp only [secondGauge_apply, secondBracket, transportCorrection, differential1,
      adjointLieModule, LieAlgebra.bracket_add_left, LieAlgebra.bracket_add_right,
      LieCochain2.map_add_left, LieCochain2.map_add_right, map_add]
    rw [direction_change_apply ω η φ hφ x.1 y.2.1,
      direction_change_apply ω η φ hφ x.2.1 y.1, L.antisymm (ψ x.1) y.1]
    abel

/-- Jacobi transforms as a vector under the proved bracket equivalence. -/
theorem secondGauge_jacobi (ω η ν : Cochain L) (φ ψ : V →ₗ[R] V)
    (hφ : differential1 (adjointLieModule L) φ = ω - η) (x y z : V × V × V) :
    secondGauge φ ψ (secondBracket ω ν x (secondBracket ω ν y z) +
      secondBracket ω ν y (secondBracket ω ν z x) +
      secondBracket ω ν z (secondBracket ω ν x y)) =
    secondBracket η (transportCorrection ω η φ ψ ν) (secondGauge φ ψ x)
      (secondBracket η (transportCorrection ω η φ ψ ν) (secondGauge φ ψ y) (secondGauge φ ψ z)) +
    secondBracket η (transportCorrection ω η φ ψ ν) (secondGauge φ ψ y)
      (secondBracket η (transportCorrection ω η φ ψ ν) (secondGauge φ ψ z) (secondGauge φ ψ x)) +
    secondBracket η (transportCorrection ω η φ ψ ν) (secondGauge φ ψ z)
      (secondBracket η (transportCorrection ω η φ ψ ν) (secondGauge φ ψ x) (secondGauge φ ψ y)) := by
  simp only [map_add, secondGauge_map_bracket ω η ν φ ψ hφ]

/-- For a closed first-order direction, the full second-order residual is
unchanged by the correction transformation. No validity of ν is assumed. -/
theorem transportCorrection_residual (ω η ν : Cochain L) (φ ψ : V →ₗ[R] V)
    (hφ : differential1 (adjointLieModule L) φ = ω - η)
    (hω : IsTwoCocycle (adjointLieModule L) ω) :
    secondResidual η (transportCorrection ω η φ ψ ν) = secondResidual ω ν := by
  have hη := cocycle_of_cohomologous (adjointLieModule L) hω ⟨φ,hφ⟩
  apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
  let J := secondBracket ω ν (x,0,0) (secondBracket ω ν (y,0,0) (z,0,0)) +
    secondBracket ω ν (y,0,0) (secondBracket ω ν (z,0,0) (x,0,0)) +
    secondBracket ω ν (z,0,0) (secondBracket ω ν (x,0,0) (y,0,0))
  have hJ₀ : J.1 = 0 := L.jacobi x y z
  have hJ₁ : J.2.1 = 0 := by
    have hh := jacobi_snd ω (x,0) (y,0) (z,0)
    exact hh.trans ((isTwoCocycle_iff _ _).mp hω x y z)
  have ht := congrArg (fun a : V × V × V => a.2.2)
    (secondGauge_jacobi ω η ν φ ψ hφ (x,0,0) (y,0,0) (z,0,0))
  change J.2.2 + φ J.2.1 + ψ J.1 = _ at ht
  rw [hJ₀,hJ₁,map_zero,map_zero,add_zero,add_zero] at ht
  rw [show J.2.2 = secondResidual ω ν x y z from secondJacobi_on_constants ω ν x y z] at ht
  rw [secondJacobi_top] at ht
  simpa only [secondGauge_apply,
    (isTwoCocycle_iff _ _).mp hη,add_zero,secondResidual_apply] using ht.symm

/-- An equivalence of actual second-order Lie models, fixing the original
generators modulo ε and commuting with multiplication by ε. -/
structure SecondEquivalence (ω ν η μ : Cochain L) where
  source_cocycle : IsTwoCocycle (adjointLieModule L) ω
  target_cocycle : IsTwoCocycle (adjointLieModule L) η
  source_residual : secondResidual ω ν = 0
  target_residual : secondResidual η μ = 0
  linearEquiv : (V × V × V) ≃ₗ[R] (V × V × V)
  map_bracket : ∀ x y, linearEquiv (secondBracket ω ν x y) =
    secondBracket η μ (linearEquiv x) (linearEquiv y)
  map_reduction : ∀ x, (linearEquiv x).1 = x.1
  map_epsilon : ∀ x, linearEquiv (secondEpsilon (R := R) x) =
    secondEpsilon (R := R) (linearEquiv x)

namespace SecondEquivalence
variable {ω ν η μ : Cochain L}

def sourceModel (E : SecondEquivalence ω ν η μ) : LieAlgebra R (V × V × V) :=
  secondAlgebra ω ν E.source_cocycle ((secondResidual_eq_zero_iff _ _).mp E.source_residual)

def targetModel (E : SecondEquivalence ω ν η μ) : LieAlgebra R (V × V × V) :=
  secondAlgebra η μ E.target_cocycle ((secondResidual_eq_zero_iff _ _).mp E.target_residual)

def symm (E : SecondEquivalence ω ν η μ) : SecondEquivalence η μ ω ν where
  source_cocycle := E.target_cocycle
  target_cocycle := E.source_cocycle
  source_residual := E.target_residual
  target_residual := E.source_residual
  linearEquiv := E.linearEquiv.symm
  map_bracket := by
    intro x y
    apply E.linearEquiv.injective
    rw [E.linearEquiv.apply_symm_apply,E.map_bracket,
      E.linearEquiv.apply_symm_apply,E.linearEquiv.apply_symm_apply]
  map_reduction := by
    intro x
    have h := E.map_reduction (E.linearEquiv.symm x)
    rw [E.linearEquiv.apply_symm_apply] at h
    exact h.symm
  map_epsilon := by
    intro x
    apply E.linearEquiv.injective
    rw [E.linearEquiv.apply_symm_apply,E.map_epsilon,E.linearEquiv.apply_symm_apply]

end SecondEquivalence

/-- Existence quantifies over all corrections and actual second-jet Lie algebras. -/
def SecondExtendable (ω : Cochain L) : Prop :=
  ∃ ν : Cochain L, ∃ D : LieAlgebra R (V × V × V), D.bracket = secondBracket ω ν

namespace Equivalence
variable {ω η : Cochain L}

def symm (E : Equivalence ω η) : Equivalence η ω where
  source_cocycle := E.target_cocycle
  target_cocycle := E.source_cocycle
  linearEquiv := E.linearEquiv.symm
  map_bracket := by
    intro x y
    apply E.linearEquiv.injective
    rw [E.linearEquiv.apply_symm_apply,E.map_bracket,
      E.linearEquiv.apply_symm_apply,E.linearEquiv.apply_symm_apply]
  map_reduction := by
    intro x
    have h := E.map_reduction (E.linearEquiv.symm x)
    rw [E.linearEquiv.apply_symm_apply] at h
    exact h.symm
  map_tangent := by
    intro x
    apply E.linearEquiv.injective
    rw [E.linearEquiv.apply_symm_apply,E.map_tangent]

theorem symm_generatorChange (E : Equivalence ω η) : E.symm.generatorChange = -E.generatorChange := by
  apply LinearMap.ext
  intro x
  have h := congrArg Prod.snd (E.apply_eq_gauge (E.linearEquiv.symm (x,0)))
  rw [E.linearEquiv.apply_symm_apply] at h
  have hr := E.map_reduction (E.linearEquiv.symm (x,0))
  rw [E.linearEquiv.apply_symm_apply] at hr
  change (0 : V) = (E.linearEquiv.symm (x,0)).2 +
    E.generatorChange (E.linearEquiv.symm (x,0)).1 at h
  rw [← hr] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The explicit correction associated to the recovered first-order change. -/
def secondCorrection (E : Equivalence ω η) (ψ : V →ₗ[R] V) (ν : Cochain L) : Cochain L :=
  transportCorrection ω η E.generatorChange ψ ν

theorem secondCorrection_residual (E : Equivalence ω η) (ψ : V →ₗ[R] V) (ν : Cochain L) :
    secondResidual η (E.secondCorrection ψ ν) = secondResidual ω ν :=
  transportCorrection_residual ω η ν E.generatorChange ψ E.coboundary_generatorChange E.source_cocycle

/-- Lift any first-order equivalence and supplied valid correction to an actual
second-order equivalence. The additional quadratic generator change is explicit. -/
def liftSecond (E : Equivalence ω η) (ψ : V →ₗ[R] V) (ν : Cochain L)
    (hν : secondResidual ω ν = 0) : SecondEquivalence ω ν η (E.secondCorrection ψ ν) where
  source_cocycle := E.source_cocycle
  target_cocycle := E.target_cocycle
  source_residual := hν
  target_residual := (E.secondCorrection_residual ψ ν).trans hν
  linearEquiv := secondGauge E.generatorChange ψ
  map_bracket := secondGauge_map_bracket ω η ν E.generatorChange ψ E.coboundary_generatorChange
  map_reduction := by intros; rfl
  map_epsilon := secondGauge_commutes_epsilon E.generatorChange ψ

theorem liftSecond_truncates (E : Equivalence ω η) (ψ : V →ₗ[R] V) (ν : Cochain L)
    (hν : secondResidual ω ν = 0) (x : V × V × V) :
    (((E.liftSecond ψ ν hν).linearEquiv x).1,((E.liftSecond ψ ν hν).linearEquiv x).2.1) =
      E.linearEquiv (x.1,x.2.1) := (E.apply_eq_gauge (x.1,x.2.1)).symm

theorem transports_extension (E : Equivalence ω η) (h : SecondExtendable ω) : SecondExtendable η := by
  rcases h with ⟨ν,D,hD⟩
  have hν := (secondResidual_eq_zero_iff ω ν).mpr ((secondAlgebra_exists_iff ω ν).mp ⟨D,hD⟩).2
  exact ⟨E.secondCorrection 0 ν,(E.liftSecond 0 ν hν).targetModel,rfl⟩

theorem secondExtendable_iff (E : Equivalence ω η) : SecondExtendable ω ↔ SecondExtendable η :=
  ⟨E.transports_extension,E.symm.transports_extension⟩

end Equivalence

/-- Second-order extendability is a property of the actual H² class. -/
theorem secondExtendable_of_class_eq (ω η : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hη : IsTwoCocycle (adjointLieModule L) η)
    (h : classOf (adjointLieModule L) ω hω = classOf (adjointLieModule L) η hη) :
    SecondExtendable ω ↔ SecondExtendable η := by
  obtain ⟨E⟩ := (class_eq_iff_nonempty_equivalence ω η hω hη).mp h
  exact E.secondExtendable_iff

theorem secondExtendable_zero : SecondExtendable (0 : Cochain L) := by
  have hω : IsTwoCocycle (adjointLieModule L) (0 : Cochain L) :=
    map_zero (differential2Linear (adjointLieModule L))
  have hν : secondResidual (0 : Cochain L) 0 = 0 := by
    rw [secondResidual, hω]
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
    simp [obstructionTrilinear, obstruction]
  exact ⟨0,secondAlgebra 0 0 hω ((secondResidual_eq_zero_iff _ _).mp hν),rfl⟩

/-- A first-order boundary always admits a second-order extension. -/
theorem secondExtendable_of_boundary (ω : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hb : IsTwoCoboundary (adjointLieModule L) ω) :
    SecondExtendable ω := by
  obtain ⟨E⟩ := (nonempty_equivalence_zero_iff ω hω).mpr hb
  exact E.secondExtendable_iff.mpr secondExtendable_zero

/-- Vanishing H² implies extension of every closed direction through order two. -/
theorem secondExtendable_of_subsingleton_h2 [Subsingleton (H2 (adjointLieModule L))]
    (ω : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω) : SecondExtendable ω := by
  obtain ⟨E⟩ := firstOrder_trivial_of_subsingleton_h2 ω hω
  exact E.secondExtendable_iff.mpr secondExtendable_zero

namespace SecondOrderSolver
variable {A B O : Type*} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup O] [Module R O]
variable (T : SecondOrderSolver L A B O)

theorem extendable_iff (ω : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω) :
    SecondExtendable ω ↔ T.obstructionCoordinates ω = 0 := by
  change (∃ ν : Cochain L, ∃ D : LieAlgebra R (V × V × V),
    D.bracket = secondBracket ω ν) ↔ _
  rw [T.model_exists_iff, and_iff_right hω]

/-- The actual projected obstruction coordinates agree, not only their zero loci. -/
theorem obstructionCoordinates_equivalence {ω η : Cochain L} (E : Equivalence ω η) :
    T.obstructionCoordinates ω = T.obstructionCoordinates η := by
  have h := congrArg (fun t => T.project (T.readThird t)) (E.secondCorrection_residual 0 0)
  have hh : T.obstructionCoordinates η = T.obstructionCoordinates ω := by
    simpa only [secondResidual,map_add,← T.bridge,T.boundary,zero_add,obstructionCoordinates] using h
  exact hh.symm

end SecondOrderSolver

namespace Reduction
variable {H : Type w} [AddCommGroup H] [Module R H]
variable (S : LieCohomology.Reduction (adjointLieModule L) H)

theorem normalize_generatorChange (ω : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω) :
    (normalize S ω hω).generatorChange = S.primitive ω := by
  apply LinearMap.ext
  intro x
  change 0 + S.primitive ω x = S.primitive ω x
  exact zero_add _

/-- Normalization into the complete representative space preserves extension. -/
theorem secondExtendable_normalize (ω : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω) :
    SecondExtendable ω ↔ SecondExtendable (S.represent (S.project ω)) :=
  (normalize S ω hω).secondExtendable_iff

variable {A B O : Type*} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup O] [Module R O]
variable (T : SecondOrderSolver L A B O)

theorem obstructionCoordinates_normalize (ω : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) :
    T.obstructionCoordinates ω = T.obstructionCoordinates (S.represent (S.project ω)) :=
  T.obstructionCoordinates_equivalence (normalize S ω hω)

/-- The complete extension test can be performed solely on H² representatives. -/
theorem secondExtendable_iff_representative_obstruction (ω : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) :
    SecondExtendable ω ↔ T.obstructionCoordinates (S.represent (S.project ω)) = 0 := by
  rw [secondExtendable_normalize S ω hω]
  exact T.extendable_iff _ (S.represent_closed _)

/-- Solve on the smaller representative space, then transport the correction
back to the original generators using the inverse first-order equivalence. -/
noncomputable def correctionFromRepresentative (ω : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) : Cochain L :=
  (normalize S ω hω).symm.secondCorrection 0 (T.correction (S.represent (S.project ω)))

theorem correctionFromRepresentative_eq (ω : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) :
    correctionFromRepresentative S T ω hω = transportCorrection (S.represent (S.project ω)) ω
      (-S.primitive ω) 0 (T.correction (S.represent (S.project ω))) := by
  unfold correctionFromRepresentative Equivalence.secondCorrection
  rw [Equivalence.symm_generatorChange, normalize_generatorChange]

theorem correctionFromRepresentative_cancels (ω : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω)
    (h : T.obstructionCoordinates (S.represent (S.project ω)) = 0) :
    secondResidual ω (correctionFromRepresentative S T ω hω) = 0 := by
  exact ((normalize S ω hω).symm.secondCorrection_residual 0 _).trans (T.correction_cancels _ h)

/-- An actual equivalence relates the representative solution to the original
generators; its inverse supplies the normalization of the resulting model. -/
noncomputable def equivalenceFromRepresentative (ω : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω)
    (h : T.obstructionCoordinates (S.represent (S.project ω)) = 0) :
    SecondEquivalence (S.represent (S.project ω)) (T.correction (S.represent (S.project ω)))
      ω (correctionFromRepresentative S T ω hω) :=
  (normalize S ω hω).symm.liftSecond 0 _ (T.correction_cancels _ h)

noncomputable def modelFromRepresentative (ω : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω)
    (h : T.obstructionCoordinates (S.represent (S.project ω)) = 0) : LieAlgebra R (V × V × V) :=
  secondAlgebra ω (correctionFromRepresentative S T ω hω) hω
    ((secondResidual_eq_zero_iff _ _).mp (correctionFromRepresentative_cancels S T ω hω h))

end Reduction

end LeanPhy.Mathematics.LieDeformation
