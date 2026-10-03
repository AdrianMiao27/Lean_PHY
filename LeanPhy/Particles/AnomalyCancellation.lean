import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-!
# Standard Model anomaly cancellation

A chiral gauge theory is consistent only if its gauge anomalies cancel.  For the
Standard Model the fermions of one generation have the quantum numbers
`(colour, isospin, hypercharge)`

    Q = (3, 2, 1/6),  U = (3, 1, -2/3),  D = (3, 1, 1/3),
    L = (1, 2, -1/2),  E = (1, 1, 1),

and the four anomaly coefficients that must vanish are

    gravity-`U(1)`:      sum  (colour) (isospin) Y,
    `SU(3)^2 U(1)`:      sum  ((colour-1)/2) (isospin) Y,
    `SU(2)^2 U(1)`:      sum  (isospin-1) (colour) Y,
    `U(1)^3`:            sum  (colour) (isospin) Y^3,

where each sum runs over the Weyl fermions of a generation.  This module sets up
that arithmetic exactly over `Q` and proves, by kernel evaluation, that all four
coefficients of the Standard Model content vanish, for any number `n` of
generations.

Two consequences beyond the evaluation are included because they are what make
the statement useful rather than a coincidence: shifting every hypercharge by a
constant is a one-parameter family, and the `U(1)^3` and gravity conditions cut
that family back to zero, so the hypercharge assignment is rigid.  The
coefficients are functions of the fermion content, which is the input: this is
conditional correctness, the Standard Model content being the hypothesis.
-/

namespace LeanPhy.Particles

open scoped BigOperators

/-- The gauge quantum numbers of one Weyl fermion: the dimension of the colour
representation, the dimension of the isospin representation, and the
hypercharge.  A colour-singlet has `su3 = 1`, an isospin-singlet has `su2 = 1`. -/
structure FermionContent where
  su3 : ℚ
  su2 : ℚ
  hyper : ℚ

namespace FermionContent

/-- The antiparticle content: conjugate representations and opposite
hypercharge. -/
def neg (f : FermionContent) : FermionContent := ⟨f.su3, f.su2, -f.hyper⟩

end FermionContent

/-- The mixed gravitational-`U(1)` anomaly coefficient
`sum (colour) (isospin) Y`.  It weights the fermion by its total multiplicity in
the ways the graviton couples. -/
def accGrav {ι : Type} [Fintype ι] (c : ι → FermionContent) : ℚ :=
  ∑ i, (c i).su3 * (c i).su2 * (c i).hyper

/-- The `SU(3)^2 U(1)` anomaly coefficient
`sum ((colour-1)/2) (isospin) Y`; the factor `(colour-1)/2` is the second
Casimir `T(R)` of the colour representation. -/
def accSU3U1 {ι : Type} [Fintype ι] (c : ι → FermionContent) : ℚ :=
  ∑ i, ((c i).su3 - 1) / 2 * (c i).su2 * (c i).hyper

/-- The `SU(2)^2 U(1)` anomaly coefficient
`sum (isospin-1) (colour) Y`, the analogous second-Casimir weight for isospin. -/
def accSU2U1 {ι : Type} [Fintype ι] (c : ι → FermionContent) : ℚ :=
  ∑ i, ((c i).su2 - 1) * (c i).su3 * (c i).hyper

/-- The `U(1)^3` anomaly coefficient `sum (colour) (isospin) Y^3`. -/
def accU1cubed {ι : Type} [Fintype ι] (c : ι → FermionContent) : ℚ :=
  ∑ i, (c i).su3 * (c i).su2 * (c i).hyper ^ 3

/-- A fermion content is anomaly free when all four coefficients vanish. -/
structure AnomalyFree {ι : Type} [Fintype ι] (c : ι → FermionContent) : Prop where
  grav : accGrav c = 0
  su3u1 : accSU3U1 c = 0
  su2u1 : accSU2U1 c = 0
  u1cubed : accU1cubed c = 0

/-- The five Weyl fermions of one Standard Model generation, indexed by
`Fin 5`: `Q, U, D, L, E`. -/
def smGen : Fin 5 → FermionContent
  | 0 => ⟨3, 2, 1/6⟩
  | 1 => ⟨3, 1, -2/3⟩
  | 2 => ⟨3, 1, 1/3⟩
  | 3 => ⟨1, 2, -1/2⟩
  | 4 => ⟨1, 1, 1⟩

/-- `n` identical generations. -/
def smContent (n : ℕ) : (Fin n × Fin 5) → FermionContent := fun p => smGen p.2

/-- **The Standard Model content is anomaly free.**  All four anomaly
coefficients vanish for one generation, evaluated by the kernel over `Q`. -/
theorem smGen_anomalyFree : AnomalyFree smGen where
  grav := by simp only [accGrav, smGen, Fin.sum_univ_five]; norm_num
  su3u1 := by simp only [accSU3U1, smGen, Fin.sum_univ_five]; norm_num
  su2u1 := by simp only [accSU2U1, smGen, Fin.sum_univ_five]; norm_num
  u1cubed := by simp only [accU1cubed, smGen, Fin.sum_univ_five]; norm_num

/-- Anomaly freedom is inherited by any number `n` of identical generations:
each generation contributes zero, so the sum is zero. -/
theorem smContent_anomalyFree (n : ℕ) : AnomalyFree (smContent n) where
  grav := by
    simp only [accGrav, smContent, Fintype.sum_prod_type, smGen, Fin.sum_univ_five]
    norm_num
  su3u1 := by
    simp only [accSU3U1, smContent, Fintype.sum_prod_type, smGen, Fin.sum_univ_five]
    norm_num
  su2u1 := by
    simp only [accSU2U1, smContent, Fintype.sum_prod_type, smGen, Fin.sum_univ_five]
    norm_num
  u1cubed := by
    simp only [accU1cubed, smContent, Fintype.sum_prod_type, smGen, Fin.sum_univ_five]
    norm_num

/-- A uniform shift of every hypercharge by `eps`, the one-parameter family of
hypercharge normalisations. -/
def hyperShift {ι : Type} (c : ι → FermionContent) (eps : ℚ) : ι → FermionContent :=
  fun i => ⟨(c i).su3, (c i).su2, (c i).hyper + eps⟩

/-- The mixed gravitational anomaly under a uniform shift is affine in `eps`,
with slope the total multiplicity `sum (colour)(isospin)`. -/
theorem accGrav_hyperShift {ι : Type} [Fintype ι] (c : ι → FermionContent) (eps : ℚ) :
    accGrav (hyperShift c eps)
      = accGrav c + eps * ∑ i, (c i).su3 * (c i).su2 := by
  simp only [accGrav, hyperShift]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The `U(1)^3` anomaly under a uniform shift is a cubic polynomial in `eps`:
it changes by `eps` times the `SU(2)^2 U(1)`-weighted multiplicity at first
order and by terms fixed by the lower moments. -/
theorem accU1cubed_hyperShift {ι : Type} [Fintype ι] (c : ι → FermionContent) (eps : ℚ) :
    accU1cubed (hyperShift c eps)
      = accU1cubed c
        + 3 * eps * ∑ i, (c i).su3 * (c i).su2 * (c i).hyper ^ 2
        + 3 * eps ^ 2 * ∑ i, (c i).su3 * (c i).su2 * (c i).hyper
        + eps ^ 3 * ∑ i, (c i).su3 * (c i).su2 := by
  simp only [accU1cubed, hyperShift]
  rw [show (∑ i, (c i).su3 * (c i).su2 * ((c i).hyper + eps) ^ 3)
        = ∑ i, ((c i).su3 * (c i).su2 * (c i).hyper ^ 3
            + (3 * eps * ((c i).su3 * (c i).su2 * (c i).hyper ^ 2)
              + (3 * eps ^ 2 * ((c i).su3 * (c i).su2 * (c i).hyper)
                + eps ^ 3 * ((c i).su3 * (c i).su2)))) from by
    apply Finset.sum_congr rfl; intro i _; ring]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **Hypercharge rigidity (cubic mixed anomaly).**  For the Standard Model
content the `U(1)^3` anomaly, as a function of a uniform hypercharge shift
`eps`, equals `15 eps^3 + 10 eps`; the only rational shift that keeps it zero is
`eps = 0`.  This is the algebraic statement that the hypercharge normalisation
is fixed by the SM content. -/
theorem smGen_accU1cubed_shift (eps : ℚ) :
    accU1cubed (hyperShift smGen eps) = 15 * eps ^ 3 + 10 * eps := by
  simp only [accU1cubed, hyperShift, smGen, Fin.sum_univ_five]
  ring

theorem smGen_shift_rigid (eps : ℚ) (h : accU1cubed (hyperShift smGen eps) = 0) :
    eps = 0 := by
  rw [smGen_accU1cubed_shift] at h
  have hf : eps * (5 * (3 * eps ^ 2 + 2)) = 0 := by
    have : 15 * eps ^ 3 + 10 * eps = eps * (5 * (3 * eps ^ 2 + 2)) := by ring
    rw [this] at h; exact h
  rcases mul_eq_zero.mp hf with h1 | h2
  · exact h1
  · exfalso; nlinarith [sq_nonneg eps]

/-- The gravitational anomaly under a uniform shift is `15 eps` for the SM
content, so it too forbids a shift: the hypercharge is not a free parameter. -/
theorem smGen_accGrav_shift (eps : ℚ) :
    accGrav (hyperShift smGen eps) = 15 * eps := by
  rw [accGrav_hyperShift]
  have h : (∑ i, (smGen i).su3 * (smGen i).su2 : ℚ) = 15 := by
    simp only [smGen, Fin.sum_univ_five]; norm_num
  have h0 : accGrav smGen = 0 := smGen_anomalyFree.grav
  rw [h0, h]; ring

theorem smGen_grav_shift_rigid (eps : ℚ) (h : accGrav (hyperShift smGen eps) = 0) :
    eps = 0 := by
  rw [smGen_accGrav_shift] at h
  linarith

end LeanPhy.Particles

