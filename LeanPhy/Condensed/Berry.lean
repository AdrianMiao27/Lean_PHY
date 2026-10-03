import LeanPhy.Quantum.Pauli
import LeanPhy.Mathematics.Holonomy
import LeanPhy.Mathematics.DiscreteCochain
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# Berry curvature of a two-level system

A qubit Hamiltonian `H(d) = d . sigma` is a Bloch vector.  When the Bloch
vector is swept by two angles `(theta, phi)` on the unit sphere, the Berry
curvature density (the integrand of the first Chern number, the solid-angle
two-form) is the scalar triple product of the Bloch vector with the two angle
tangents,

    F = dhat . (d_theta dhat x d_phi dhat).

For the standard spherical parametrisation

    dhat(theta, phi) = (sin t cos p, sin t sin p, cos t)

the kernel checks the two defining facts: the Bloch vector is a unit vector
(`dhat_unit`), and the curvature density is exactly `sin theta` (`berry_density`),
the monopole field of a charge-one Dirac point.  The two tangents are also
proved orthogonal to `dhat` and to one another, and `dTheta` is a unit
vector while `dPhi` has squared norm `sin theta ^ 2`.  In the spherical
frame the curvature density is the Jacobian `sin theta` of the area element, so the
flux through the whole sphere is `4 pi`, the charge of the monopole.

Everything here is real trigonometric ring algebra over `ℝ`, closed with
the Pythagorean identity `sin^2 + cos^2 = 1` as the only input, so it is kernel-verified
with no analysis.  The topological invariant itself - the integral of `F` over the
Brillouin zone, the `N = 1` Chern number of a Dirac monopole - needs the surface
integral on top and is out of scope, in keeping with the conditional semantics
of the library.
-/

namespace LeanPhy.Condensed

open scoped BigOperators

/-- The Euclidean dot product on `Fin 3` vectors with real entries. -/
noncomputable def dot3 (u v : Fin 3 → ℝ) : ℝ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- The Euclidean cross product on `Fin 3` vectors. -/
noncomputable def cross3 (u v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- The unit Bloch vector in spherical coordinates,
`dhat theta phi = (sin theta cos phi, sin theta sin phi, cos theta)`. -/
noncomputable def dhat (theta phi : ℝ) : Fin 3 → ℝ :=
  ![Real.sin theta * Real.cos phi, Real.sin theta * Real.sin phi, Real.cos theta]

/-- The theta tangent of the Bloch vector. -/
noncomputable def dTheta (theta phi : ℝ) : Fin 3 → ℝ :=
  ![Real.cos theta * Real.cos phi, Real.cos theta * Real.sin phi, -Real.sin theta]

/-- The phi tangent of the Bloch vector. -/
noncomputable def dPhi (theta phi : ℝ) : Fin 3 → ℝ :=
  ![-Real.sin theta * Real.sin phi, Real.sin theta * Real.cos phi, 0]

/-- **Unit norm**: the Bloch vector lies on the unit sphere. -/
theorem dhat_unit (theta phi : ℝ) : dot3 (dhat theta phi) (dhat theta phi) = 1 := by
  have hphi := Real.sin_sq_add_cos_sq phi
  have htheta := Real.sin_sq_add_cos_sq theta
  simp [dot3, dhat]
  nlinarith [hphi, htheta]

/-- The theta tangent is orthogonal to the Bloch vector. -/
theorem dhat_dTheta (theta phi : ℝ) : dot3 (dhat theta phi) (dTheta theta phi) = 0 := by
  have hphi := Real.sin_sq_add_cos_sq phi
  simp [dot3, dhat, dTheta]
  ring_nf
  linear_combination (Real.sin theta * Real.cos theta) * hphi

/-- The phi tangent is orthogonal to the Bloch vector. -/
theorem dhat_dPhi (theta phi : ℝ) : dot3 (dhat theta phi) (dPhi theta phi) = 0 := by
  simp [dot3, dhat, dPhi]
  ring

/-- **Berry curvature density**: the triple product of the Bloch vector with the
two angle tangents equals `sin theta`, the monopole field of a charge-one
Dirac point.  This is the integrand of the first Chern number. -/
theorem berry_density (theta phi : ℝ) :
    dot3 (dhat theta phi) (cross3 (dTheta theta phi) (dPhi theta phi)) = Real.sin theta := by
  have hphi := Real.sin_sq_add_cos_sq phi
  have htheta := Real.sin_sq_add_cos_sq theta
  simp [dot3, cross3, dhat, dTheta, dPhi]
  ring_nf
  linear_combination
    (Real.sin theta * Real.cos theta ^ 2 + Real.sin theta ^ 3) * hphi
    + Real.sin theta * htheta

/-- The theta tangent is a unit vector. -/
theorem dTheta_unit (theta phi : ℝ) : dot3 (dTheta theta phi) (dTheta theta phi) = 1 := by
  have hphi := Real.sin_sq_add_cos_sq phi
  have htheta := Real.sin_sq_add_cos_sq theta
  simp [dot3, dTheta]
  nlinarith [hphi, htheta]

/-- The phi tangent has squared norm `sin theta ^ 2`. -/
theorem dPhi_norm (theta phi : ℝ) :
    dot3 (dPhi theta phi) (dPhi theta phi) = Real.sin theta ^ 2 := by
  have hphi := Real.sin_sq_add_cos_sq phi
  simp [dot3, dPhi]
  ring_nf
  linear_combination (Real.sin theta ^ 2) * hphi

/-- The two tangents are orthogonal. -/
theorem dTheta_dPhi (theta phi : ℝ) : dot3 (dTheta theta phi) (dPhi theta phi) = 0 := by
  simp [dot3, dTheta, dPhi]
  ring

/-! ## Discrete Berry-phase adapter

For a finite mesh, a Berry link is a phase-valued edge variable.  The phase
group is deliberately abstract: a caller may choose a finite cyclic group, a
unit-circle subgroup, or a symbolic phase group.  The shared finite-path
theorem then proves gauge invariance of a closed product.  Smooth eigenvector
patches, connection one-forms and the Chern-number integral remain outside
this algebraic adapter.
-/

def discreteBerryHolonomy {V G : Type} [CommGroup G]
    (phase : V → V → G) {x : V}
    (p : LeanPhy.Mathematics.FinitePath V x x) : G :=
  LeanPhy.Mathematics.FinitePath.transport phase p

theorem discreteBerryHolonomy_gauge_invariant {V G : Type} [CommGroup G]
    (g : V → G) (phase : V → V → G) {x : V}
    (p : LeanPhy.Mathematics.FinitePath V x x) :
    discreteBerryHolonomy
        (LeanPhy.Mathematics.FinitePath.gaugeLink g phase) p =
      discreteBerryHolonomy phase p := by
  exact LeanPhy.Mathematics.FinitePath.abelian_transport_invariant g phase p

/-! Additive finite-mesh curvature is the oriented phase sum on a triangle.
The phase convention (for example a lifted angle or a finite cyclic group) is
left to the caller; no branch of a logarithm is silently chosen. -/

def discreteBerryCurvature {V A : Type} [AddCommGroup A]
    (phase : LeanPhy.Mathematics.DiscreteCochain.Cochain1 V A)
    (x y z : V) : A :=
  LeanPhy.Mathematics.DiscreteCochain.d1 phase x y z

theorem discreteBerryCurvature_gauge_invariant {V A : Type} [AddCommGroup A]
    (phase : LeanPhy.Mathematics.DiscreteCochain.Cochain1 V A)
    (gauge : LeanPhy.Mathematics.DiscreteCochain.Cochain0 V A)
    (x y z : V) :
    discreteBerryCurvature
      (LeanPhy.Mathematics.DiscreteCochain.gaugeShift phase gauge) x y z =
      discreteBerryCurvature phase x y z := by
  exact LeanPhy.Mathematics.DiscreteCochain.d1_gaugeShift phase gauge x y z

end LeanPhy.Condensed
