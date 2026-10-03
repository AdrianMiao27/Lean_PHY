import LeanPhy.HighEnergy.DiracBilinear
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The Ward identity: gauge invariance of the photon vertex

The Ward identity says that the longitudinal part of a photon polarisation
couples to nothing.  In the textbook derivation one replaces the polarisation
`eps_mu` by the photon momentum `q_mu = p'_mu - p_mu` in the amplitude, uses the
on-shell Dirac equations for the two electron legs, and gets zero.  This is the
identity that keeps a QED amplitude gauge invariant, and it is exactly the step
where a dropped spinor equation or a sign slip quietly breaks the result, so it
is worth having the kernel confirm it.

The file is pure algebra on the explicit chiral gamma matrices:

- `bilinear ub M u` is the spinor sandwich `ubar M u`;
- `slash` and its linearity, so `slash (p' - p) = slash p' - slash p`;
- `vertexAmplitude eps ub u = sum_mu eps_mu * (ubar gamma^mu u)`, which is the
  slash sandwich `ubar slash(eps) u`, and is linear in `eps`;
- `ward_identity`: the on-shell conditions `slash p u = 0` and
  `ubar slash p' = 0` are explicit hypotheses, and they imply that the
  amplitude with `eps = p' - p` vanishes;
- `gauge_invariance`: consequently `eps -> eps + lambda (p' - p)` leaves the
  amplitude unchanged, which is the physics content of gauge invariance.

The on-shell spinor equations are arguments of the theorems (structures are not
needed and no axiom is introduced): the module proves "if the legs are on shell,
the longitudinal polarisation decouples", which is exactly what a derivation
uses.
-/

namespace LeanPhy.HighEnergy

open LeanPhy.Quantum
open scoped BigOperators

local notation "M4" => Matrix (Fin 4) (Fin 4) ℂ

/-- A Dirac spinor: four complex amplitudes. -/
abbrev Spinor := Fin 4 → ℂ

/-- The row vector `ubar M`, the co-spinor `ubar` acted on by `M`. -/
noncomputable def rowMul (ub : Spinor) (M : M4) : Spinor := fun j => ∑ i, ub i * M i j

/-- The spinor sandwich `ubar M u`, the bilinear a scattering amplitude is
built from. -/
noncomputable def bilinear (ub : Spinor) (M : M4) (u : Spinor) : ℂ :=
  ub ⬝ᵥ (M.mulVec u)

/-- The photon vertex `sum_mu eps_mu (ubar gamma^mu u)`: the electron-photon
coupling with polarisation `eps`. -/
noncomputable def vertexAmplitude (eps : Fin 4 → ℂ) (ub : Spinor) (u : Spinor) : ℂ :=
  ∑ μ : Fin 4, eps μ * bilinear ub (gammaFin μ) u

/-- `rowMul` really is mathlib's `Matrix.vecMul`, so the two pairings agree by
`Matrix.dotProduct_mulVec`. -/
theorem rowMul_eq_vecMul (ub : Spinor) (M : M4) :
    rowMul ub M = Matrix.vecMul ub M := rfl

/-- The bar acts on the left: `ubar M u` can be read as `(ubar M) u`. -/
theorem rowMul_dotProduct (ub : Spinor) (M : M4) (u : Spinor) :
    rowMul ub M ⬝ᵥ u = bilinear ub M u := by
  rw [bilinear, rowMul_eq_vecMul, Matrix.dotProduct_mulVec]

/-! ## The Feynman slash is linear -/

theorem slash_add (a b : Fin 4 → ℂ) : slash (a + b) = slash a + slash b := by
  simp only [slash, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem slash_sub (a b : Fin 4 → ℂ) : slash (a - b) = slash a - slash b := by
  simp only [slash, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem slash_smul (c : ℂ) (a : Fin 4 → ℂ) : slash (c • a) = c • slash a := by
  simp only [slash, Pi.smul_apply, smul_assoc, Finset.smul_sum]

@[simp] theorem slash_zero : slash (0 : Fin 4 → ℂ) = 0 := by
  simp only [slash, Pi.zero_apply, zero_smul, Finset.sum_const_zero]

@[simp] theorem slash_neg (a : Fin 4 → ℂ) : slash (-a) = -slash a := by
  simpa using slash_smul (-1) a

/-! ## The vertex is the slash sandwich -/

/-- Gathering the polarisation into a slash leaves the amplitude unchanged: the
index form and the slash form are the same object. -/
theorem vertexAmplitude_eq_slash (eps : Fin 4 → ℂ) (ub u : Spinor) :
    vertexAmplitude eps ub u = bilinear ub (slash eps) u := by
  simp only [vertexAmplitude, slash, bilinear, Matrix.sum_mulVec, dotProduct_sum,
    Matrix.smul_mulVec, dotProduct_smul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

theorem vertexAmplitude_add (eps₁ eps₂ : Fin 4 → ℂ) (ub u : Spinor) :
    vertexAmplitude (eps₁ + eps₂) ub u =
      vertexAmplitude eps₁ ub u + vertexAmplitude eps₂ ub u := by
  simp only [vertexAmplitude, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem vertexAmplitude_smul (c : ℂ) (eps : Fin 4 → ℂ) (ub u : Spinor) :
    vertexAmplitude (c • eps) ub u = c * vertexAmplitude eps ub u := by
  simp only [vertexAmplitude, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

/-! ## The Ward identity -/

/-- **Ward identity.**  If the incoming electron is on shell (`slash p u = 0`)
and the outgoing co-spinor is on shell (`ubar slash p' = 0`), then the photon
vertex with polarisation equal to the photon momentum `p' - p` vanishes. -/
theorem ward_identity (p p' : Fin 4 → ℂ) (ub u : Spinor)
    (hu : (slash p).mulVec u = 0) (hub : rowMul ub (slash p') = 0) :
    vertexAmplitude (p' - p) ub u = 0 := by
  rw [vertexAmplitude_eq_slash, bilinear, slash_sub, Matrix.sub_mulVec, hu, sub_zero]
  rw [Matrix.dotProduct_mulVec,
    show Matrix.vecMul ub (slash p') = rowMul ub (slash p') from rfl, hub]
  simp

/-- **Gauge invariance.**  Shifting the polarisation by any multiple of the
photon momentum leaves the on-shell amplitude unchanged.  This is the physics
content of the Ward identity. -/
theorem gauge_invariance (eps p p' : Fin 4 → ℂ) (lam : ℂ) (ub u : Spinor)
    (hu : (slash p).mulVec u = 0) (hub : rowMul ub (slash p') = 0) :
    vertexAmplitude (eps + lam • (p' - p)) ub u = vertexAmplitude eps ub u := by
  rw [vertexAmplitude_add, vertexAmplitude_smul,
    ward_identity p p' ub u hu hub, mul_zero, add_zero]

/-! ## A concrete on-shell witness (the hypotheses are satisfiable)

The Ward identity has explicit on-shell hypotheses.  To show they are not
vacuous, here is an explicit on-shell spinor configuration, with both equations
and the resulting vanishing amplitude proved on the explicit gamma matrices. -/

/-- A concrete lightlike momentum. -/
def wardP : Fin 4 → ℂ := ![1, 0, 0, 1]

/-- A concrete spinor that solves `slash wardP u = 0`. -/
def wardU : Spinor := ![0, 0, 0, 1]

/-- A concrete co-spinor that solves `ubar slash wardP = 0`. -/
def wardUb : Spinor := ![0, 1, 0, 0]

/-- The incoming electron leg is on shell. -/
theorem wardP_onshell_u : (slash wardP).mulVec wardU = 0 := by
  funext i; fin_cases i <;>
    simp [slash, gammaFin, gamma0, gamma1, gamma2, gamma3, wardP, wardU,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The outgoing co-spinor leg is on shell. -/
theorem wardP_onshell_ub : rowMul wardUb (slash wardP) = 0 := by
  funext j; fin_cases j <;>
    simp [rowMul, slash, gammaFin, gamma0, gamma1, gamma2, gamma3, wardP, wardUb,
      Fin.sum_univ_four]

/-- The Ward identity applies to this configuration on the explicit matrices. -/
theorem ward_identity_witness : vertexAmplitude (wardP - wardP) wardUb wardU = 0 :=
  ward_identity wardP wardP wardUb wardU wardP_onshell_u wardP_onshell_ub

end LeanPhy.HighEnergy
