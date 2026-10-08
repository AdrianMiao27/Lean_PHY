import LeanPhy.Mathematics.LieRepresentation

/-!
# Low-degree Lie-algebra cohomology

This file provides the finite algebraic part of the first steps of the
Chevalley--Eilenberg complex.  A `LieModule` records an action and its
representation law; degree-zero cochains produce degree-one coboundaries, and
the degree-one differential produces an explicit alternating bilinear
cochain.  The kernel checks `d₁ d₀ = 0` from the declared representation law.

This file keeps the low-degree witnesses explicit. `LieCohomology2` builds
on it with the next differential, native mathlib adapters and the quotient
module `H2`; `CentralExtension` connects that quotient to supplied extensions.
General higher-degree cohomology, anomalies, Lie-group integration and the
identification with physical observables remain separate obligations. The
same API can be reused by gauge, representation and BRST developments.
-/

namespace LeanPhy.Mathematics

universe u v w

variable {R : Type u} {V : Type v} {M : Type w}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [AddCommGroup M] [Module R M]

/-! ## Lie modules -/

/-/ A module for the declared Lie algebra action.  The action is kept as a
plain function so that importing this interface never installs a potentially
ambiguous global `SMul V M` instance. -/
structure LieModule (L : LieAlgebra R V) (M : Type w)
    [AddCommGroup M] [Module R M] where
  act : V → M → M
  act_add_left' : ∀ x y m, act (x + y) m = act x m + act y m
  act_smul_left' : ∀ (r : R) x m, act (r • x) m = r • act x m
  act_add_right' : ∀ x m n, act x (m + n) = act x m + act x n
  act_smul_right' : ∀ x (r : R) m, act x (r • m) = r • act x m
  bracket_act' : ∀ x y m,
    act (L.bracket x y) m = act x (act y m) - act y (act x m)

namespace LieAlgebra

variable (L : LieAlgebra R V)

@[simp] theorem bracket_add_left (x y z : V) :
    L.bracket (x + y) z = L.bracket x z + L.bracket y z :=
  L.add_left x y z

@[simp] theorem bracket_add_right (x y z : V) :
    L.bracket x (y + z) = L.bracket x y + L.bracket x z :=
  L.add_right x y z

@[simp] theorem bracket_smul_left (r : R) (x y : V) :
    L.bracket (r • x) y = r • L.bracket x y :=
  L.smul_left r x y

@[simp] theorem bracket_smul_right (r : R) (x y : V) :
    L.bracket x (r • y) = r • L.bracket x y :=
  L.smul_right r x y

end LieAlgebra

namespace LieModule

variable {L : LieAlgebra R V} (𝒨 : LieModule L M)

@[simp] theorem act_add_left (x y : V) (m : M) :
    𝒨.act (x + y) m = 𝒨.act x m + 𝒨.act y m :=
  𝒨.act_add_left' x y m

@[simp] theorem act_smul_left (r : R) (x : V) (m : M) :
    𝒨.act (r • x) m = r • 𝒨.act x m :=
  𝒨.act_smul_left' r x m

@[simp] theorem act_add_right (x : V) (m n : M) :
    𝒨.act x (m + n) = 𝒨.act x m + 𝒨.act x n :=
  𝒨.act_add_right' x m n

@[simp] theorem act_smul_right (x : V) (r : R) (m : M) :
    𝒨.act x (r • m) = r • 𝒨.act x m :=
  𝒨.act_smul_right' x r m

@[simp] theorem act_zero_right (x : V) : 𝒨.act x 0 = 0 := by
  simpa using 𝒨.act_smul_right' x (0 : R) (0 : M)

@[simp] theorem act_neg_right (x : V) (m : M) :
    𝒨.act x (-m) = -𝒨.act x m := by
  simpa using 𝒨.act_smul_right' x (-1 : R) m

theorem bracket_act (x y : V) (m : M) :
    𝒨.act (L.bracket x y) m = 𝒨.act x (𝒨.act y m) - 𝒨.act y (𝒨.act x m) :=
  𝒨.bracket_act' x y m

end LieModule

/-! ## Canonical actions -/

/-/ The adjoint action of a Lie algebra on its own carrier. -/
def adjointLieModule (L : LieAlgebra R V) : LieModule L V where
  act := L.bracket
  act_add_left' := L.add_left
  act_smul_left' := L.smul_left
  act_add_right' := L.add_right
  act_smul_right' := by
    intro x r m
    exact L.smul_right r x m
  bracket_act' := by
    intro x y m
    have h := L.jacobi x y m
    rw [L.antisymm m (L.bracket x y)] at h
    rw [L.antisymm m x] at h
    have h' :
        L.bracket x (L.bracket y m) - L.bracket y (L.bracket x m) -
            L.bracket (L.bracket x y) m = 0 := by
      simpa [LieAlgebra.bracket_neg_right, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm] using h
    exact (sub_eq_zero.mp h').symm

/-/ The commutator action induced by a concrete associative representation. -/
def representationLieModule {A : Type w} [Ring A] [Algebra R A]
    {L : LieAlgebra R V} (ρ : Representation L A) : LieModule L A where
  act := fun x a => ringCommutator (ρ x) a
  act_add_left' := by
    intro x y a
    rw [ρ.map_add]
    exact ringCommutator_add_left (ρ x) (ρ y) a
  act_smul_left' := by
    intro r x a
    rw [ρ.map_smul]
    exact ringCommutator_smul_left r (ρ x) a
  act_add_right' := by
    intro x a b
    exact ringCommutator_add_right (ρ x) a b
  act_smul_right' := by
    intro x r a
    exact ringCommutator_smul_right r (ρ x) a
  bracket_act' := by
    intro x y a
    rw [← ρ.commutator_map x y]
    simp [ringCommutator]
    noncomm_ring

/-! ## Low-degree cochains -/

abbrev LieCochain0 (L : LieAlgebra R V) (_𝒨 : LieModule L M) := M

abbrev LieCochain1 (L : LieAlgebra R V) (_𝒨 : LieModule L M) := V →ₗ[R] M

/-/ A degree-two cochain with linearity in each slot and the alternating
condition.  A full `AlternatingMap` can be introduced later without changing
the degree-zero and degree-one theorems below. -/
structure LieCochain2 (L : LieAlgebra R V) (𝒨 : LieModule L M) where
  eval : V → V → M
  map_add_left' : ∀ x y z, eval (x + y) z = eval x z + eval y z
  map_smul_left' : ∀ (r : R) x y, eval (r • x) y = r • eval x y
  map_add_right' : ∀ x y z, eval x (y + z) = eval x y + eval x z
  map_smul_right' : ∀ x (r : R) y, eval x (r • y) = r • eval x y
  alternating' : ∀ x, eval x x = 0

namespace LieCochain2

variable {L : LieAlgebra R V} {𝒨 : LieModule L M}

instance : CoeFun (LieCochain2 L 𝒨) (fun _ => V → V → M) := ⟨LieCochain2.eval⟩

@[simp] theorem map_add_left (ω : LieCochain2 L 𝒨) (x y z : V) :
    ω (x + y) z = ω x z + ω y z :=
  ω.map_add_left' x y z

@[simp] theorem map_smul_left (ω : LieCochain2 L 𝒨) (r : R) (x y : V) :
    ω (r • x) y = r • ω x y :=
  ω.map_smul_left' r x y

@[simp] theorem map_add_right (ω : LieCochain2 L 𝒨) (x y z : V) :
    ω x (y + z) = ω x y + ω x z :=
  ω.map_add_right' x y z

@[simp] theorem map_smul_right (ω : LieCochain2 L 𝒨) (x : V) (r : R) (y : V) :
    ω x (r • y) = r • ω x y :=
  ω.map_smul_right' x r y

@[simp] theorem alternating (ω : LieCochain2 L 𝒨) (x : V) : ω x x = 0 :=
  ω.alternating' x

end LieCochain2

/-! ## The Chevalley--Eilenberg maps `d₀` and `d₁` -/

namespace LieCohomology

variable {L : LieAlgebra R V} (𝒨 : LieModule L M)

/-/ `d₀ m (x) = x • m`. -/
def differential0 (m : LieCochain0 L 𝒨) : LieCochain1 L 𝒨 where
  toFun := fun x => 𝒨.act x m
  map_add' := by
    intro x y
    exact 𝒨.act_add_left' x y m
  map_smul' := by
    intro r x
    exact 𝒨.act_smul_left' r x m

/-/ `d₁ φ (x,y) = x • φ(y) - y • φ(x) - φ([x,y])`. -/
def differential1 (φ : LieCochain1 L 𝒨) : LieCochain2 L 𝒨 where
  eval := fun x y =>
    𝒨.act x (φ y) - 𝒨.act y (φ x) - φ (L.bracket x y)
  map_add_left' := by
    intro x y z
    simp only [LieAlgebra.bracket_add_left, LieModule.act_add_left,
      LieModule.act_add_right, LinearMap.map_add]
    abel
  map_smul_left' := by
    intro r x y
    simp only [LieAlgebra.bracket_smul_left, LieModule.act_smul_left,
      LieModule.act_smul_right, LinearMap.map_smul]
    rw [smul_sub, smul_sub]
  map_add_right' := by
    intro x y z
    simp only [LieAlgebra.bracket_add_right, LieModule.act_add_left,
      LieModule.act_add_right, LinearMap.map_add]
    abel
  map_smul_right' := by
    intro x r y
    simp only [LieAlgebra.bracket_smul_right, LieModule.act_smul_left,
      LieModule.act_smul_right, LinearMap.map_smul]
    rw [smul_sub, smul_sub]
  alternating' := by
    intro x
    simp [LieAlgebra.bracket_self]

theorem differential1_differential0 (m : LieCochain0 L 𝒨) (x y : V) :
    differential1 𝒨 (differential0 𝒨 m) x y = 0 := by
  change 𝒨.act x (𝒨.act y m) - 𝒨.act y (𝒨.act x m) -
      𝒨.act (L.bracket x y) m = 0
  rw [𝒨.bracket_act]
  abel

/-/ A one-cocycle is a degree-one cochain killed by `d₁`. -/
def IsOneCocycle (φ : LieCochain1 L 𝒨) : Prop :=
  ∀ x y, differential1 𝒨 φ x y = 0

/-/ A one-coboundary is a degree-one cochain in the image of `d₀`. -/
def IsOneCoboundary (φ : LieCochain1 L 𝒨) : Prop :=
  ∃ m : LieCochain0 L 𝒨, φ = differential0 𝒨 m

theorem coboundary_is_cocycle {φ : LieCochain1 L 𝒨}
    (hφ : IsOneCoboundary 𝒨 φ) : IsOneCocycle 𝒨 φ := by
  rcases hφ with ⟨m, rfl⟩
  intro x y
  exact differential1_differential0 𝒨 m x y

/-/ Two one-cochains are cohomologous when their difference is a
degree-one coboundary.  This keeps the witness instead of quotienting by it. -/
def Cohomologous1 (φ ψ : LieCochain1 L 𝒨) : Prop :=
  ∃ m : LieCochain0 L 𝒨, φ - ψ = differential0 𝒨 m

theorem cohomologous1_refl (φ : LieCochain1 L 𝒨) : Cohomologous1 𝒨 φ φ := by
  refine ⟨0, ?_⟩
  ext x
  simp [differential0]

theorem cohomologous1_symm {φ ψ : LieCochain1 L 𝒨}
    (h : Cohomologous1 𝒨 φ ψ) : Cohomologous1 𝒨 ψ φ := by
  rcases h with ⟨m, hm⟩
  refine ⟨-m, ?_⟩
  calc
    ψ - φ = -(φ - ψ) := by abel
    _ = -(differential0 𝒨 m) := by rw [hm]
    _ = differential0 𝒨 (-m) := by
      ext x
      simp [differential0]

theorem cohomologous1_trans {φ ψ χ : LieCochain1 L 𝒨}
    (h₁ : Cohomologous1 𝒨 φ ψ) (h₂ : Cohomologous1 𝒨 ψ χ) :
    Cohomologous1 𝒨 φ χ := by
  rcases h₁ with ⟨m, hm⟩
  rcases h₂ with ⟨n, hn⟩
  refine ⟨m + n, ?_⟩
  calc
    φ - χ = (φ - ψ) + (ψ - χ) := by
      ext x
      simp [sub_eq_add_neg, add_assoc, add_left_comm]
    _ = differential0 𝒨 m + differential0 𝒨 n := by rw [hm, hn]
    _ = differential0 𝒨 (m + n) := by
      ext x
      simp [differential0]

end LieCohomology

end LeanPhy.Mathematics
