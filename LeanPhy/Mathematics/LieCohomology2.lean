import LeanPhy.Mathematics.LieCohomology
import Mathlib.Algebra.Lie.Cochain
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Degree-two Lie cohomology and a native mathlib bridge

The explicit LeanPhy Lie algebra and module structures are adapted to mathlib
without installing global Lie instances on the user's carrier. Two-cochains
are identified with mathlib's alternating bilinear maps. Their module
structure, the next coboundary map and the quotient of cocycles by boundaries
can therefore be used with ordinary Lean linear algebra.

The action, representation law and sign convention remain explicit. This is
algebraic cohomology, with no topology, Lie-group integration or identification
of a cocycle with a physical anomaly. Constructing the quotient does not
compute its dimension or classify its elements.
-/

namespace LeanPhy.Mathematics

universe u v w

variable {R : Type u} {V : Type v} {M : Type w}
variable [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup M] [Module R M]

/-- An explicit adapter, deliberately not a global instance. -/
@[instance_reducible] def LieAlgebra.toMathlibLieRing (L : LieAlgebra R V) : LieRing V where
  __ := (inferInstance : AddCommGroup V)
  bracket := L.bracket
  add_lie := L.add_left
  lie_add := L.add_right
  lie_self := L.alternating
  leibniz_lie x y z := by
    have h := (adjointLieModule L).bracket_act x y z
    change L.bracket (L.bracket x y) z =
      L.bracket x (L.bracket y z) - L.bracket y (L.bracket x z) at h
    rw [h]
    abel

@[instance_reducible] def LieAlgebra.toMathlibLieAlgebra (L : LieAlgebra R V) :
    letI := L.toMathlibLieRing
    _root_.LieAlgebra R V := by
  letI := L.toMathlibLieRing
  exact { (inferInstance : Module R V) with lie_smul := L.smul_right }

@[instance_reducible] def LieModule.toMathlibLieRingModule {L : LieAlgebra R V}
    (𝒨 : LieModule L M) :
    letI := L.toMathlibLieRing
    LieRingModule V M := by
  letI := L.toMathlibLieRing
  exact {
    bracket := 𝒨.act
    add_lie := 𝒨.act_add_left
    lie_add := 𝒨.act_add_right
    leibniz_lie := by
      intro x y m
      change 𝒨.act x (𝒨.act y m) = 𝒨.act (L.bracket x y) m + 𝒨.act y (𝒨.act x m)
      rw [𝒨.bracket_act, sub_add_cancel]
  }

theorem LieModule.toMathlibLieModule {L : LieAlgebra R V}
    (𝒨 : LieModule L M) :
    letI := L.toMathlibLieRing
    letI := L.toMathlibLieAlgebra
    letI := 𝒨.toMathlibLieRingModule
    _root_.LieModule R V M := by
  let := L.toMathlibLieRing
  let := L.toMathlibLieAlgebra
  let := 𝒨.toMathlibLieRingModule
  exact { smul_lie := 𝒨.act_smul_left, lie_smul := fun r x m => 𝒨.act_smul_right x r m }

namespace LieCochain2

variable {L : LieAlgebra R V} {𝒨 : LieModule L M}

@[ext] theorem ext {ω η : LieCochain2 L 𝒨} (h : ∀ x y, ω x y = η x y) : ω = η := by
  cases ω
  cases η
  congr
  funext x y
  exact h x y

/-- The native cochain space using the explicitly supplied bracket. -/
abbrev Native (L : LieAlgebra R V) (M : Type w) [AddCommGroup M] [Module R M] :=
  letI := L.toMathlibLieRing
  letI := L.toMathlibLieAlgebra
  _root_.LieModule.Cohomology.twoCochain R V M

def toNative (ω : LieCochain2 L 𝒨) : Native L M :=
  ⟨{ toFun := fun x => {
       toFun := ω x
       map_add' := ω.map_add_right x
       map_smul' := ω.map_smul_right x }
     map_add' := by intro x y; ext z; exact ω.map_add_left x y z
     map_smul' := by intro r x; ext y; exact ω.map_smul_left r x y }, ω.alternating⟩

def ofNative (ω : Native L M) : LieCochain2 L 𝒨 where
  eval x y := ω.val x y
  map_add_left' := by intro x y z; simp
  map_smul_left' := by intro r x y; simp
  map_add_right' := by intro x y z; simp
  map_smul_right' := by intro x r y; simp
  alternating' := ω.property

def nativeEquiv : LieCochain2 L 𝒨 ≃ Native L M where
  toFun := toNative
  invFun := ofNative
  left_inv := by intro ω; rfl
  right_inv := by intro ω; rfl

instance : AddCommGroup (LieCochain2 L 𝒨) := nativeEquiv.addCommGroup

def nativeAddEquiv : LieCochain2 L 𝒨 ≃+ Native L M where
  __ := nativeEquiv
  map_add' := by intro ω η; rfl

instance : Module R (LieCochain2 L 𝒨) := nativeAddEquiv.module R

def nativeLinearEquiv : LieCochain2 L 𝒨 ≃ₗ[R] Native L M := nativeAddEquiv.linearEquiv R

@[simp] theorem zero_apply (x y : V) : (0 : LieCochain2 L 𝒨) x y = 0 := rfl
@[simp] theorem add_apply (ω η : LieCochain2 L 𝒨) (x y : V) :
    (ω + η) x y = ω x y + η x y := rfl
@[simp] theorem neg_apply (ω : LieCochain2 L 𝒨) (x y : V) : (-ω) x y = -ω x y := rfl
@[simp] theorem sub_apply (ω η : LieCochain2 L 𝒨) (x y : V) :
    (ω - η) x y = ω x y - η x y := rfl
@[simp] theorem smul_apply (r : R) (ω : LieCochain2 L 𝒨) (x y : V) :
    (r • ω) x y = r • ω x y := rfl

@[simp] theorem zero_left (ω : LieCochain2 L 𝒨) (y : V) : ω 0 y = 0 := by
  simpa using ω.map_smul_left (0 : R) 0 y
@[simp] theorem zero_right (ω : LieCochain2 L 𝒨) (x : V) : ω x 0 = 0 := by
  simpa using ω.map_smul_right x (0 : R) 0

theorem skew (ω : LieCochain2 L 𝒨) (x y : V) : ω x y = -ω y x := by
  have h := ω.alternating (x + y)
  rw [map_add_left, map_add_right, map_add_right, alternating, alternating,
    zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

end LieCochain2

namespace LieCohomology

variable {L : LieAlgebra R V} (𝒨 : LieModule L M)

/-- The existing degree-one differential, bundled as a linear map. -/
def differential1Linear : LieCochain1 L 𝒨 →ₗ[R] LieCochain2 L 𝒨 where
  toFun := differential1 𝒨
  map_add' := by intro φ ψ; ext x y; simp [differential1]; abel
  map_smul' := by intro r φ; ext x y; simp [differential1, smul_sub]

/-- The next differential as a trilinear map, with mathlib's sign convention. -/
def differential2 (ω : LieCochain2 L 𝒨) : V →ₗ[R] V →ₗ[R] V →ₗ[R] M := by
  letI := L.toMathlibLieRing
  letI := L.toMathlibLieAlgebra
  letI := 𝒨.toMathlibLieRingModule
  letI := 𝒨.toMathlibLieModule
  exact _root_.LieModule.Cohomology.d₂₃ R V M ω.toNative

@[simp] theorem differential2_apply (ω : LieCochain2 L 𝒨) (x y z : V) :
    differential2 𝒨 ω x y z =
      𝒨.act x (ω y z) - 𝒨.act y (ω x z) + 𝒨.act z (ω x y) -
        ω (L.bracket x y) z + ω (L.bracket x z) y - ω (L.bracket y z) x := rfl

/-- Native and explicit degree-one differentials agree, including the sign. -/
theorem differential1_toNative (φ : LieCochain1 L 𝒨) :
    letI := L.toMathlibLieRing
    letI := L.toMathlibLieAlgebra
    letI := 𝒨.toMathlibLieRingModule
    letI := 𝒨.toMathlibLieModule
    (differential1 𝒨 φ).toNative = _root_.LieModule.Cohomology.d₁₂ R V M φ := rfl

theorem differential2_differential1 (φ : LieCochain1 L 𝒨) :
    differential2 𝒨 (differential1 𝒨 φ) = 0 := by
  let := L.toMathlibLieRing
  let := L.toMathlibLieAlgebra
  let := 𝒨.toMathlibLieRingModule
  let := 𝒨.toMathlibLieModule
  exact LinearMap.congr_fun (_root_.LieModule.Cohomology.d₂₃_comp_d₁₂ R V M) φ

def differential2Linear : LieCochain2 L 𝒨 →ₗ[R] V →ₗ[R] V →ₗ[R] V →ₗ[R] M where
  toFun := differential2 𝒨
  map_add' := by intro ω η; ext x y z; simp [differential2_apply]; abel
  map_smul' := by intro r ω; ext x y z; simp [differential2_apply, smul_sub, smul_add]

/-- The cocycle condition is a trilinear equality, not a metadata flag. -/
def IsTwoCocycle (ω : LieCochain2 L 𝒨) : Prop := differential2 𝒨 ω = 0

theorem isTwoCocycle_iff (ω : LieCochain2 L 𝒨) :
    IsTwoCocycle 𝒨 ω ↔ ∀ x y z, differential2 𝒨 ω x y z = 0 := by
  constructor
  · intro h x y z; rw [h]; rfl
  · intro h; ext x y z; exact h x y z

def IsTwoCoboundary (ω : LieCochain2 L 𝒨) : Prop :=
  ∃ φ : LieCochain1 L 𝒨, differential1 𝒨 φ = ω

theorem two_coboundary_is_cocycle {ω : LieCochain2 L 𝒨}
    (hω : IsTwoCoboundary 𝒨 ω) : IsTwoCocycle 𝒨 ω := by
  rcases hω with ⟨φ, rfl⟩
  exact differential2_differential1 𝒨 φ

def Cohomologous2 (ω η : LieCochain2 L 𝒨) : Prop := IsTwoCoboundary 𝒨 (ω - η)

def twoCocycles : Submodule R (LieCochain2 L 𝒨) := LinearMap.ker (differential2Linear 𝒨)

def twoCoboundaries : Submodule R (LieCochain2 L 𝒨) := LinearMap.range (differential1Linear 𝒨)

@[simp] theorem mem_twoCocycles (ω : LieCochain2 L 𝒨) :
    ω ∈ twoCocycles 𝒨 ↔ IsTwoCocycle 𝒨 ω := Iff.rfl

@[simp] theorem mem_twoCoboundaries (ω : LieCochain2 L 𝒨) :
    ω ∈ twoCoboundaries 𝒨 ↔ IsTwoCoboundary 𝒨 ω := Iff.rfl

theorem twoCoboundaries_le_twoCocycles : twoCoboundaries 𝒨 ≤ twoCocycles 𝒨 := by
  intro ω hω
  exact two_coboundary_is_cocycle 𝒨 hω

/-- Boundaries considered inside the cocycle module. -/
def twoBoundariesInCycles : Submodule R (twoCocycles 𝒨) :=
  (twoCoboundaries 𝒨).comap (twoCocycles 𝒨).subtype

/-- The actual degree-two quotient module. No basis or dimension is assumed. -/
abbrev H2 := (twoCocycles 𝒨) ⧸ twoBoundariesInCycles 𝒨

def classOf (ω : LieCochain2 L 𝒨) (hω : IsTwoCocycle 𝒨 ω) : H2 𝒨 :=
  Submodule.Quotient.mk ⟨ω, hω⟩

theorem classOf_eq_iff (ω η : LieCochain2 L 𝒨)
    (hω : IsTwoCocycle 𝒨 ω) (hη : IsTwoCocycle 𝒨 η) :
    classOf 𝒨 ω hω = classOf 𝒨 η hη ↔ Cohomologous2 𝒨 ω η := by
  exact Submodule.Quotient.eq (twoBoundariesInCycles 𝒨)

theorem classOf_eq_zero_iff (ω : LieCochain2 L 𝒨) (hω : IsTwoCocycle 𝒨 ω) :
    classOf 𝒨 ω hω = 0 ↔ IsTwoCoboundary 𝒨 ω := by
  exact Submodule.Quotient.mk_eq_zero (twoBoundariesInCycles 𝒨)

theorem cohomologous2_refl (ω : LieCochain2 L 𝒨) : Cohomologous2 𝒨 ω ω := by
  change ω - ω ∈ twoCoboundaries 𝒨
  simp

theorem cohomologous2_symm {ω η : LieCochain2 L 𝒨}
    (h : Cohomologous2 𝒨 ω η) : Cohomologous2 𝒨 η ω := by
  change η - ω ∈ twoCoboundaries 𝒨
  simpa only [neg_sub] using (twoCoboundaries 𝒨).neg_mem h

theorem cohomologous2_trans {ω η θ : LieCochain2 L 𝒨}
    (h₁ : Cohomologous2 𝒨 ω η) (h₂ : Cohomologous2 𝒨 η θ) :
    Cohomologous2 𝒨 ω θ := by
  change ω - θ ∈ twoCoboundaries 𝒨
  simpa only [sub_add_sub_cancel] using (twoCoboundaries 𝒨).add_mem h₁ h₂

theorem cocycle_of_cohomologous {ω η : LieCochain2 L 𝒨}
    (hω : IsTwoCocycle 𝒨 ω) (h : Cohomologous2 𝒨 ω η) : IsTwoCocycle 𝒨 η := by
  have hd := two_coboundary_is_cocycle 𝒨 h
  change η ∈ twoCocycles 𝒨
  simpa only [sub_sub_cancel] using (twoCocycles 𝒨).sub_mem hω hd

end LieCohomology

end LeanPhy.Mathematics
