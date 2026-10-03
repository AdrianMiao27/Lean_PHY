import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-!
# The continuum gauge field strength and the Bianchi identity

On the lattice the curvature of a gauge field is the plaquette holonomy
(`LeanPhy.GaugeTheory`).  In the continuum it is the commutator of covariant
derivatives,

    F_{mu nu} = [D_mu, D_nu],

which is antisymmetric, and whose derivatives satisfy the Bianchi identity.
Both statements are pure ring identities in the covariant-derivative algebra,
so they are kernel-checked in an abstract (noncommutative) ring with no
representation assumed.  This is the algebraic skeleton a nonabelian gauge
calculation rests on; the fields themselves are whatever ring elements the
user supplies, consistent with the conditional semantics of the library.
-/

namespace LeanPhy.GaugeTheory

/-- A `2 x 2` witness for the non-vacuity check of the field strength. -/
noncomputable def witnessD0 : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;0,0]

/-- A `2 x 2` witness for the non-vacuity check of the field strength. -/
noncomputable def witnessD1 : Matrix (Fin 2) (Fin 2) ℂ := !![0,0;0,1]



/-- The commutator of two covariant derivatives, i.e. the field strength
`F_{mu nu} = [D_mu, D_nu]`. -/
def fieldStrength {A : Type} [Ring A] (D : Fin 4 → A) (mu nu : Fin 4) : A :=
  D mu * D nu - D nu * D mu

/-- The field strength is antisymmetric in its indices. -/
theorem fieldStrength_antisym {A : Type} [Ring A] (D : Fin 4 → A) (mu nu : Fin 4) :
    fieldStrength D mu nu = -fieldStrength D nu mu := by
  simp only [fieldStrength]; noncomm_ring

/-- On the diagonal the field strength vanishes. -/
theorem fieldStrength_self {A : Type} [Ring A] (D : Fin 4 → A) (mu : Fin 4) :
    fieldStrength D mu mu = 0 := by
  simp only [fieldStrength]; noncomm_ring

/-- **Algebraic Bianchi identity.**  The cyclic sum of commutators
`[F_{mu nu}, D_rho] + [F_{nu rho}, D_mu] + [F_{rho mu}, D_nu] = 0`,
equivalently the statement that the covariant curl of the field strength
vanishes.  It is the Jacobi identity for the covariant derivatives, and it
holds in any ring. -/
theorem bianchi {A : Type} [Ring A] (D : Fin 4 → A) (mu nu rho : Fin 4) :
    fieldStrength D mu nu * D rho + fieldStrength D nu rho * D mu
        + fieldStrength D rho mu * D nu
      = D rho * fieldStrength D mu nu + D mu * fieldStrength D nu rho
        + D nu * fieldStrength D rho mu := by
  simp only [fieldStrength]; noncomm_ring

/-- The abelian case is forced: commuting covariant derivatives have no field
strength, so `F = 0` for a `U(1)`-type (commuting) derivative. -/
theorem fieldStrength_abelian {A : Type} [CommRing A] (D : Fin 4 → A) (mu nu : Fin 4) :
    fieldStrength D mu nu = 0 := by
  simp only [fieldStrength]
  rw [mul_comm (D mu) (D nu)]
  simp

/-- A concrete matrix witness: the field strength is not identically zero, so
this module is not vacuous.  With `D_0 = !![0,1;0,0]` and `D_1 = !![0,0;0,1]` on
`2 x 2` complex matrices, the (0,1) entry of `F_01` is 1, so `F_01` is nonzero.
Evaluated entrywise by the kernel. -/
theorem fieldStrength_matrix_witness :
    fieldStrength (fun i : Fin 4 => if i = 0 then witnessD0 else if i = 1 then witnessD1 else witnessD0)
      0 1 ≠ 0 := by
  intro h
  have h01 :
      fieldStrength (fun i : Fin 4 => if i = 0 then witnessD0 else if i = 1 then witnessD1 else witnessD0)
          0 1 0 1 = 1 := by
    simp [fieldStrength, witnessD0, witnessD1, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.sub_apply, Fin.isValue, Fin.zero_eta, reduceIte]
  rw [h] at h01
  simp at h01

end LeanPhy.GaugeTheory
