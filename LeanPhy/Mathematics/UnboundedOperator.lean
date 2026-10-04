import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

/-!
# Dense-domain operators and unbounded resolvent certificates

Hamiltonians, momentum operators and field generators are generally
unbounded.  Treating them as bounded maps silently drops their domains, so
this module uses a dense submodule as an explicit domain.  The resolvent
certificate records both equations for an inverse whose codomain is the
domain; uniqueness is proved algebraically.  Self-adjointness, closability,
essential self-adjointness and existence of a resolvent remain hypotheses to
be discharged by a concrete model.
-/

namespace LeanPhy.Mathematics

open scoped InnerProductSpace
open scoped LinearPMap

universe u v

structure DenseDomainOperator
    {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace E] where
  domain : Submodule 𝕜 E
  dense : Dense (domain : Set E)
  operator : domain →ₗ[𝕜] E

namespace DenseDomainOperator

variable {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace E]

def apply (T : DenseDomainOperator (𝕜 := 𝕜) (E := E))
    (x : T.domain) : E := T.operator x

theorem apply_eq (T : DenseDomainOperator (𝕜 := 𝕜) (E := E))
    (x : T.domain) : T.apply x = T.operator x := rfl

end DenseDomainOperator

/-! Symmetry is stated on the declared domain and therefore cannot be applied
to vectors for which the unbounded operator is undefined. -/

structure SymmetricDomainCertificate
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [TopologicalSpace E]
    (T : DenseDomainOperator (𝕜 := 𝕜) (E := E)) : Prop where
  inner_eq : ∀ x y : T.domain,
    ⟪T.operator x, (y : E)⟫_𝕜 = ⟪(x : E), T.operator y⟫_𝕜

/-! A two-sided inverse of `z - T` with range in the domain. -/

structure DomainResolventCertificate
    {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace E]
    (T : DenseDomainOperator (𝕜 := 𝕜) (E := E)) (z : 𝕜) where
  inverse : E →ₗ[𝕜] T.domain
  right_inverse : ∀ y : E,
    z • (inverse y : E) - T.operator (inverse y) = y
  left_inverse : ∀ x : T.domain,
    inverse (z • (x : E) - T.operator x) = x

namespace DomainResolventCertificate

variable {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace E]
  {T : DenseDomainOperator (𝕜 := 𝕜) (E := E)} {z : 𝕜}

theorem inverse_unique
    (h₁ h₂ : DomainResolventCertificate T z) : h₁.inverse = h₂.inverse := by
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  calc
    ((h₁.inverse y : T.domain) : E) =
        ((h₁.inverse (z • (h₂.inverse y : E) -
          T.operator (h₂.inverse y)) : T.domain) : E) := by
      rw [h₂.right_inverse]
    _ = ((h₂.inverse y : T.domain) : E) := by
      rw [h₁.left_inverse]

theorem right_inverse_eq
    (h : DomainResolventCertificate T z) (y : E) :
    z • (h.inverse y : E) - T.operator (h.inverse y) = y :=
  h.right_inverse y

end DomainResolventCertificate

/-! ## Mathlib `LinearPMap` bridge

`DenseDomainOperator` is intentionally a small physics-facing record.  The
mathlib theory of partially defined operators uses `LinearPMap`, which already
provides graphs, closures, cores and formal adjoints.  The following adapter
keeps the convenient record while making those theorems available without
erasing the declared domain.
-/

namespace DenseDomainOperator

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The same operator represented as mathlib's partially defined linear map. -/
def asPMap (T : DenseDomainOperator (𝕜 := 𝕜) (E := E)) : E →ₗ.[𝕜] E where
  domain := T.domain
  toFun := T.operator

@[simp] theorem asPMap_domain (T : DenseDomainOperator (𝕜 := 𝕜) (E := E)) :
    T.asPMap.domain = T.domain := rfl

@[simp] theorem asPMap_apply (T : DenseDomainOperator (𝕜 := 𝕜) (E := E))
    (x : T.domain) : T.asPMap x = T.operator x := rfl

theorem symmetric_formalAdjoint
    (T : DenseDomainOperator (𝕜 := 𝕜) (E := E))
    (hT : SymmetricDomainCertificate T) :
    T.asPMap.IsFormalAdjoint T.asPMap := by
  exact hT.inner_eq

theorem formalAdjoint_isClosed
    (T : DenseDomainOperator (𝕜 := 𝕜) (E := E)) :
    T.asPMap†.IsClosed := by
  exact LinearPMap.adjoint_isClosed T.dense

theorem formalAdjoint_maximal
    (T S : DenseDomainOperator (𝕜 := 𝕜) (E := E))
    (hS : T.asPMap.IsFormalAdjoint S.asPMap) :
    S.asPMap ≤ T.asPMap† := by
  exact LinearPMap.IsFormalAdjoint.le_adjoint T.dense hS

end DenseDomainOperator

/-! ## Closedness, closability and self-adjointness contracts

These predicates are not inferred from a name such as `Hamiltonian`.  A model
must supply the corresponding `LinearPMap` equality or graph certificate.
Once supplied, the standard consequences are available to downstream proofs.
-/

namespace DenseDomainOperator

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  [ContinuousAdd E] [TopologicalSpace 𝕜] [ContinuousSMul 𝕜 E]

structure ClosedCertificate (T : DenseDomainOperator (𝕜 := 𝕜) (E := E)) : Prop where
  graph_closed : T.asPMap.IsClosed

structure ClosableCertificate (T : DenseDomainOperator (𝕜 := 𝕜) (E := E)) : Prop where
  graph_closable : T.asPMap.IsClosable

structure SelfAdjointCertificate (T : DenseDomainOperator (𝕜 := 𝕜) (E := E)) : Prop where
  adjoint_eq : IsSelfAdjoint T.asPMap

theorem ClosedCertificate.isClosable
    {T : DenseDomainOperator (𝕜 := 𝕜) (E := E)}
    (hT : ClosedCertificate T) : ClosableCertificate T :=
  ⟨hT.graph_closed.isClosable⟩

theorem ClosableCertificate.closure
    {T : DenseDomainOperator (𝕜 := 𝕜) (E := E)}
    (hT : ClosableCertificate T) :
    T.asPMap.closure.IsClosed :=
  hT.graph_closable.closure_isClosed

theorem SelfAdjointCertificate.dense
    {T : DenseDomainOperator (𝕜 := 𝕜) (E := E)}
    (hT : SelfAdjointCertificate T) : Dense (T.asPMap.domain : Set E) :=
  hT.adjoint_eq.dense_domain

theorem SelfAdjointCertificate.isClosed
    {T : DenseDomainOperator (𝕜 := 𝕜) (E := E)}
    (hT : SelfAdjointCertificate T) : T.asPMap.IsClosed :=
  hT.adjoint_eq.isClosed

theorem SelfAdjointCertificate.isClosable
    {T : DenseDomainOperator (𝕜 := 𝕜) (E := E)}
    (hT : SelfAdjointCertificate T) : ClosableCertificate T :=
  ⟨hT.isClosed.isClosable⟩

theorem SelfAdjointCertificate.formalAdjoint
    {T : DenseDomainOperator (𝕜 := 𝕜) (E := E)}
    (hT : SelfAdjointCertificate T) :
    LinearPMap.adjoint T.asPMap = T.asPMap :=
  hT.adjoint_eq

end DenseDomainOperator

/-! ## Graph norms and relative bounds

Relative bounds are a practical interface for perturbation theory.  They
express that an interaction term is controlled by the graph norm of a declared
operator, without pretending that the interaction is bounded on the ambient
Hilbert space.
-/

namespace DenseDomainOperator

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

def graphNorm (T : DenseDomainOperator (𝕜 := 𝕜) (E := E))
    (x : T.domain) : ℝ := ‖(x : E)‖ + ‖T.operator x‖

@[simp] theorem graphNorm_zero (T : DenseDomainOperator (𝕜 := 𝕜) (E := E)) :
    T.graphNorm 0 = 0 := by
  simp [graphNorm]

theorem norm_le_graphNorm (T : DenseDomainOperator (𝕜 := 𝕜) (E := E))
    (x : T.domain) : ‖(x : E)‖ ≤ T.graphNorm x := by
  exact le_add_of_nonneg_right (norm_nonneg _)

theorem operator_norm_le_graphNorm (T : DenseDomainOperator (𝕜 := 𝕜) (E := E))
    (x : T.domain) : ‖T.operator x‖ ≤ T.graphNorm x := by
  exact le_add_of_nonneg_left (norm_nonneg _)

structure GraphBoundCertificate {F : Type v}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : DenseDomainOperator (𝕜 := 𝕜) (E := E))
    (S : T.domain →ₗ[𝕜] F) (a b : ℝ) : Prop where
  a_nonneg : 0 ≤ a
  b_nonneg : 0 ≤ b
  bound : ∀ x, ‖S x‖ ≤ a * ‖(x : E)‖ + b * ‖T.operator x‖

namespace GraphBoundCertificate

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {T : DenseDomainOperator (𝕜 := 𝕜) (E := E)}
  {S : T.domain →ₗ[𝕜] F} {a b : ℝ}

theorem by_graphNorm (h : GraphBoundCertificate T S a b) :
    ∀ x, ‖S x‖ ≤ max a b * T.graphNorm x := by
  intro x
  calc
    ‖S x‖ ≤ a * ‖(x : E)‖ + b * ‖T.operator x‖ := h.bound x
    _ ≤ max a b * ‖(x : E)‖ + max a b * ‖T.operator x‖ := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = max a b * T.graphNorm x := by
      rw [DenseDomainOperator.graphNorm]
      ring

theorem widen (h : GraphBoundCertificate T S a b)
    {a' b' : ℝ} (ha : a ≤ a') (hb : b ≤ b')
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') :
    GraphBoundCertificate T S a' b' := by
  refine ⟨ha', hb', ?_⟩
  intro x
  exact (h.bound x).trans (add_le_add
    (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _)))

theorem add {G : Type v} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {S R : T.domain →ₗ[𝕜] G} {a b c d : ℝ}
    (hS : GraphBoundCertificate T S a b)
    (hR : GraphBoundCertificate T R c d) :
    GraphBoundCertificate T (S + R) (a + c) (b + d) := by
  refine ⟨add_nonneg hS.a_nonneg hR.a_nonneg,
    add_nonneg hS.b_nonneg hR.b_nonneg, ?_⟩
  intro x
  calc
    ‖(S + R) x‖ ≤ ‖S x‖ + ‖R x‖ := norm_add_le _ _
    _ ≤ (a * ‖(x : E)‖ + b * ‖T.operator x‖) +
        (c * ‖(x : E)‖ + d * ‖T.operator x‖) :=
      add_le_add (hS.bound x) (hR.bound x)
    _ = (a + c) * ‖(x : E)‖ + (b + d) * ‖T.operator x‖ := by ring

end GraphBoundCertificate

end DenseDomainOperator

/-! ## Operators that preserve a declared domain

Bounded maps such as symmetries, projections and regularising resolvents often
act on an unbounded Hamiltonian only after a domain-preservation proof.  This
adapter turns that proof into an honest operator on the domain, so compositions
cannot silently apply an operator outside its definition domain.
-/

namespace DenseDomainOperator

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

structure DomainPreserving (T : DenseDomainOperator (𝕜 := 𝕜) (E := E)) where
  bounded : E →L[𝕜] E
  maps_domain : ∀ x : T.domain, bounded (x : E) ∈ T.domain

namespace DomainPreserving

variable {T : DenseDomainOperator (𝕜 := 𝕜) (E := E)}

def onDomain (B : DomainPreserving T) : T.domain →ₗ[𝕜] T.domain :=
  (B.bounded.toLinearMap.domRestrict T.domain).codRestrict T.domain B.maps_domain

@[simp] theorem onDomain_apply (B : DomainPreserving T) (x : T.domain) :
    B.onDomain x = ⟨B.bounded (x : E), B.maps_domain x⟩ := by
  apply Subtype.ext
  rfl

@[simp] theorem onDomain_coe (B : DomainPreserving T) (x : T.domain) :
    (B.onDomain x : E) = B.bounded (x : E) := by
  rfl

def identity : DomainPreserving T where
  bounded := ContinuousLinearMap.id 𝕜 E
  maps_domain := by intro x; exact x.property

theorem identity_onDomain (x : T.domain) :
    (DomainPreserving.identity (T := T)).onDomain x = x := by
  apply Subtype.ext
  simp [identity, onDomain]

def compose (B C : DomainPreserving T) : DomainPreserving T where
  bounded := B.bounded.comp C.bounded
  maps_domain := by
    intro x
    exact B.maps_domain ⟨C.bounded (x : E), C.maps_domain x⟩

theorem compose_onDomain_apply (B C : DomainPreserving T) (x : T.domain) :
    ((B.compose C).onDomain x : E) = B.bounded (C.bounded (x : E)) := by
  simp [compose, onDomain]

end DomainPreserving

end DenseDomainOperator

end LeanPhy.Mathematics
