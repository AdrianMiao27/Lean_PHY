import LeanPhy.Mathematics.LieDeformation
import LeanPhy.Mathematics.LieCohomologyReduction

/-!
# Computed normal forms for infinitesimal Lie deformations

A complete reduction of the adjoint CE complex computes equivalence classes
of first-order deformations. Its primitive supplies the actual generator
change, and its representatives construct actual jet Lie algebras. All
conclusions retain the cocycle hypothesis; no higher-order extension is inferred.
-/

namespace LeanPhy.Mathematics.LieDeformation

open LieCohomology

set_option maxSynthPendingDepth 5

universe u v w
variable {R : Type u} {V : Type v} {H : Type w}
variable [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup H] [Module R H]
variable {L : LieAlgebra R V}

namespace Reduction

variable (S : LieCohomology.Reduction (adjointLieModule L) H)

/-- Equality of computed coordinates exactly decides first-order equivalence. -/
theorem equivalent_iff (ω η : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hη : IsTwoCocycle (adjointLieModule L) η) :
    Nonempty (Equivalence ω η) ↔ S.project ω = S.project η := by
  rw [← class_eq_iff_nonempty_equivalence ω η hω hη, classOf_eq_iff]
  exact S.cohomologous_iff ω η hω hη

/-- The reduction primitive is an explicit change of generators. -/
noncomputable def equivalenceOfCoordinates (ω η : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) (hη : IsTwoCocycle (adjointLieModule L) η)
    (h : S.project ω = S.project η) : Equivalence ω η :=
  equivalenceOfCoboundary ω η (S.primitive (ω - η)) (by
    have hc : differential2 (adjointLieModule L) (ω - η) = 0 := by
      change differential2Linear (adjointLieModule L) (ω - η) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr ((show differential2Linear (adjointLieModule L) ω = 0 from hω).trans
        (show differential2Linear (adjointLieModule L) η = 0 from hη).symm)
    have hn := S.normal_form (ω - η) hc
    have hp : S.project (ω - η) = 0 := by rw [map_sub,h,sub_self]
    change differential1Linear (adjointLieModule L) (S.primitive (ω - η)) = ω - η
    simpa only [hp, map_zero, add_zero] using hn) hω

/-- Every closed direction is equivalent to its computed representative. -/
noncomputable def normalize (ω : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω) :
    Equivalence ω (S.represent (S.project ω)) :=
  equivalenceOfCoboundary ω (S.represent (S.project ω)) (S.primitive ω)
    ((eq_sub_iff_add_eq).mpr (S.normal_form ω hω)) hω

/-- Each coordinate tuple produces an actual first-order Lie model. -/
noncomputable def deformation (h : H) : LieAlgebra R (V × V) :=
  algebra (S.represent h) (S.represent_closed h)

theorem representatives_equivalent_iff (h k : H) :
    Nonempty (Equivalence (S.represent h) (S.represent k)) ↔ h = k := by
  rw [equivalent_iff S _ _ (S.represent_closed h) (S.represent_closed k),
    S.project_represent, S.project_represent]

/-- Vanishing computed coordinates provide a concrete trivializing map. -/
noncomputable def trivialize (ω : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω)
    (h : S.project ω = 0) : Equivalence ω 0 :=
  equivalenceOfCoordinates S ω 0 hω (by
    change differential2Linear (adjointLieModule L) 0 = 0
    exact map_zero _) (by simpa using h)

theorem removable_iff (ω : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω) :
    Nonempty (Equivalence ω 0) ↔ S.project ω = 0 := by
  rw [nonempty_equivalence_zero_iff ω hω]
  exact S.exact_iff ω hω

include S in
/-- A zero computed parameter space proves first-order rigidity. -/
theorem all_removable [Subsingleton H] (ω : Cochain L)
    (hω : IsTwoCocycle (adjointLieModule L) ω) : Nonempty (Equivalence ω 0) :=
  ⟨trivialize S ω hω (Subsingleton.elim _ _)⟩

end Reduction
end LeanPhy.Mathematics.LieDeformation
