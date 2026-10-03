import Mathlib.Tactic

/-!
# A finite fermionic Wick/Pfaffian kernel

For a free fermion, the four-point contraction is the Pfaffian of the
antisymmetric two-point matrix:

`C₁₂ C₃₄ - C₁₃ C₂₄ + C₁₄ C₂₃`.

This file isolates that sign-sensitive algebra so that finite CAR, lattice
fermions, BdG calculations and truncated QFT models can share one theorem.
It does not define Grassmann integration, time ordering, distribution products,
renormalisation or a continuum Fock representation.  An actual model supplies
the antisymmetric contraction kernel as an explicit hypothesis or a proved
finite matrix calculation.
-/

namespace LeanPhy.FieldTheory

universe u v

namespace FermionicWick

variable {I : Type u} {A : Type v} [CommRing A]

/-- The sign-correct four-point fermionic contraction. -/
def fourPoint (C : I → I → A) (i j k l : I) : A :=
  C i j * C k l - C i k * C j l + C i l * C j k

@[simp] theorem fourPoint_apply (C : I → I → A) (i j k l : I) :
    fourPoint C i j k l = C i j * C k l - C i k * C j l + C i l * C j k := rfl

/-- Swapping two neighbouring fermionic slots changes the sign when the
corresponding contraction is antisymmetric. -/
theorem fourPoint_swap12 (C : I → I → A)
    (hanti : ∀ a b, C b a = -C a b) (i j k l : I) :
    fourPoint C j i k l = -fourPoint C i j k l := by
  unfold fourPoint
  rw [hanti i j]
  ring

theorem fourPoint_swap23 (C : I → I → A)
    (hanti : ∀ a b, C b a = -C a b) (i j k l : I) :
    fourPoint C i k j l = -fourPoint C i j k l := by
  unfold fourPoint
  rw [hanti j k]
  ring

theorem fourPoint_swap34 (C : I → I → A)
    (hanti : ∀ a b, C b a = -C a b) (i j k l : I) :
    fourPoint C i j l k = -fourPoint C i j k l := by
  unfold fourPoint
  rw [hanti k l]
  ring

/-- A repeated fermionic slot vanishes when the diagonal contraction is zero.
This is the finite algebraic form of the Pauli exclusion sign check. -/
theorem fourPoint_repeat12 (C : I → I → A)
    (hdiag : ∀ i, C i i = 0) (i k l : I) :
    fourPoint C i i k l = 0 := by
  unfold fourPoint
  rw [hdiag i]
  ring

theorem fourPoint_repeat23 (C : I → I → A)
    (hdiag : ∀ i, C i i = 0) (i j l : I) :
    fourPoint C i j j l = 0 := by
  unfold fourPoint
  rw [hdiag j]
  ring

theorem fourPoint_repeat34 (C : I → I → A)
    (hdiag : ∀ i, C i i = 0) (i j k : I) :
    fourPoint C i j k k = 0 := by
  unfold fourPoint
  rw [hdiag k]
  ring

/-! A concrete four-slot Pfaffian name.  The matrix form is convenient when a
BdG or lattice calculation already stores its contraction as a finite matrix. -/

def pfaffian4 (K : Matrix (Fin 4) (Fin 4) A) : A :=
  K 0 1 * K 2 3 - K 0 2 * K 1 3 + K 0 3 * K 1 2

theorem pfaffian4_eq_fourPoint (K : Matrix (Fin 4) (Fin 4) A) :
    pfaffian4 K = fourPoint (fun i j => K i j) 0 1 2 3 := by
  rfl

theorem pfaffian4_swap12 (K : Matrix (Fin 4) (Fin 4) A)
    (hanti : ∀ i j, K j i = -K i j) :
    fourPoint (fun i j => K i j) 1 0 2 3 = -pfaffian4 K := by
  rw [pfaffian4_eq_fourPoint]
  exact fourPoint_swap12 (fun i j => K i j) hanti 0 1 2 3

end FermionicWick

/-! Domain vocabulary for the same finite sign-sensitive kernel. -/

abbrev FermionicContraction4 {I A : Type*} [CommRing A] :=
  FermionicWick.fourPoint (I := I) (A := A)

namespace Condensed
abbrev BdGFermionicContraction {I A : Type*} [CommRing A] :=
  FermionicWick.fourPoint (I := I) (A := A)
end Condensed

namespace Particles
abbrev QFTFermionicContraction {I A : Type*} [CommRing A] :=
  FermionicWick.fourPoint (I := I) (A := A)
end Particles

end LeanPhy.FieldTheory
