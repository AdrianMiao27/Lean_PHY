import Mathlib.Analysis.InnerProductSpace.Basic
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

end LeanPhy.Mathematics
