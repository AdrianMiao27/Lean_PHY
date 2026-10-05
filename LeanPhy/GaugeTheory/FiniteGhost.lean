import LeanPhy.Mathematics.GradedBRST

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-!
# Finite CAR ghost–antighost adapter

This module gives the graded BRST interface one concrete, executable model.  The
underlying algebra is the finite matrix ring `Matrix (Fin 2) (Fin 2) R`; `ghost`
and `antighost` satisfy the two-generator CAR identities, and
`finiteGhostDifferential` is a square-zero odd derivation on the declared even/
odd matrix subspaces.

The adapter is deliberately finite.  It is a reusable algebraic witness for
signs, grading, nilpotency, closedness, and exactness.  It is not a construction
of the full ghost polynomial algebra, a BV antibracket, gauge fixing, a path
integral measure, an anomaly cancellation theorem, or a continuum/infinite-
dimensional field representation.  Those claims remain explicit model inputs
or open research obligations.
-/

namespace LeanPhy.GaugeTheory

open LeanPhy.Mathematics
open scoped Matrix

/-! ## The finite CAR pair -/

/-- The finite matrix algebra used by this adapter. -/
abbrev FiniteGhost (R : Type*) := Matrix (Fin 2) (Fin 2) R

/-- The square-zero ghost generator `c`. -/
noncomputable def ghost [Zero R] [One R] : FiniteGhost R := !![0, 1; 0, 0]
/-- The square-zero antighost generator `c†`. -/
noncomputable def antighost [Zero R] [One R] : FiniteGhost R := !![0, 0; 1, 0]

@[simp] theorem ghost_sq [CommRing R] : ghost (R := R) * ghost = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ghost, Fin.sum_univ_two]

@[simp] theorem antighost_sq [CommRing R] : antighost (R := R) * antighost = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antighost, Fin.sum_univ_two]

@[simp] theorem ghost_antighost [CommRing R] :
    ghost (R := R) * antighost + antighost * ghost = (1 : FiniteGhost R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ghost, antighost, Fin.sum_univ_two]

/-- A matrix is even when it is diagonal. -/
def isEven [Zero R] (X : FiniteGhost R) : Prop :=
  X 0 1 = 0 ∧ X 1 0 = 0

/-- A matrix is odd when it is off-diagonal. -/
def isOdd [Zero R] (X : FiniteGhost R) : Prop :=
  X 0 0 = 0 ∧ X 1 1 = 0

noncomputable def finiteGhostHomogeneous [Zero R] (g : Parity) : Set (FiniteGhost R) :=
  match g with | .even => {X | isEven X} | .odd => {X | isOdd X}

theorem even_mul_even [CommRing R] {x y : FiniteGhost R}
    (hx : isEven x) (hy : isEven y) : isEven (x * y) := by
  rcases hx with ⟨hx₁, hx₂⟩
  rcases hy with ⟨hy₁, hy₂⟩
  constructor <;> simp [isEven, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hx₁, hx₂, hy₁, hy₂] <;> ring

theorem even_mul_odd [CommRing R] {x y : FiniteGhost R}
    (hx : isEven x) (hy : isOdd y) : isOdd (x * y) := by
  rcases hx with ⟨hx₁, hx₂⟩
  rcases hy with ⟨hy₁, hy₂⟩
  constructor <;> simp [isOdd, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hx₁, hx₂, hy₁, hy₂] <;> ring

theorem odd_mul_even [CommRing R] {x y : FiniteGhost R}
    (hx : isOdd x) (hy : isEven y) : isOdd (x * y) := by
  rcases hx with ⟨hx₁, hx₂⟩
  rcases hy with ⟨hy₁, hy₂⟩
  constructor <;> simp [isOdd, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hx₁, hx₂, hy₁, hy₂] <;> ring

theorem odd_mul_odd [CommRing R] {x y : FiniteGhost R}
    (hx : isOdd x) (hy : isOdd y) : isEven (x * y) := by
  rcases hx with ⟨hx₁, hx₂⟩
  rcases hy with ⟨hy₁, hy₂⟩
  constructor <;> simp [isEven, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hx₁, hx₂, hy₁, hy₂] <;> ring

/-- The diagonal/off-diagonal `Parity` grading of the finite matrix algebra. -/
noncomputable def finiteGhostGrading [CommRing R] : GradedRing Parity (FiniteGhost R) where
  homogeneous := finiteGhostHomogeneous
  zero_mem := by
    intro g
    cases g <;> simp [finiteGhostHomogeneous, isEven, isOdd]
  add_mem := by
    intro g x y hx hy
    cases g
    · rcases hx with ⟨hx₁, hx₂⟩
      rcases hy with ⟨hy₁, hy₂⟩
      exact ⟨by simp [isEven, Matrix.add_apply, hx₁, hy₁],
        by simp [isEven, Matrix.add_apply, hx₂, hy₂]⟩
    · rcases hx with ⟨hx₁, hx₂⟩
      rcases hy with ⟨hy₁, hy₂⟩
      exact ⟨by simp [isOdd, Matrix.add_apply, hx₁, hy₁],
        by simp [isOdd, Matrix.add_apply, hx₂, hy₂]⟩
  neg_mem := by
    intro g x hx
    cases g
    · rcases hx with ⟨hx₁, hx₂⟩
      exact ⟨by simp [isEven, Matrix.neg_apply, hx₁],
        by simp [isEven, Matrix.neg_apply, hx₂]⟩
    · rcases hx with ⟨hx₁, hx₂⟩
      exact ⟨by simp [isOdd, Matrix.neg_apply, hx₁],
        by simp [isOdd, Matrix.neg_apply, hx₂]⟩
  one_mem := by
    constructor <;> simp [finiteGhostHomogeneous, isEven]
  mul_mem := by
    intro g h x y hx hy
    cases g <;> cases h
    · exact even_mul_even hx hy
    · exact even_mul_odd hx hy
    · exact odd_mul_even hx hy
    · exact odd_mul_odd hx hy
  parity := id
  parity_add := by intro g h; rfl
  differential_degree := .odd
  differential_is_odd := rfl

/-- The odd differential of the finite adapter, written entrywise. -/
noncomputable def finiteGhostDifferential [CommRing R] (X : FiniteGhost R) : FiniteGhost R :=
  !![X 1 0, X 1 1 - X 0 0; 0, X 1 0]

@[simp] theorem finiteGhostDifferential_zero [CommRing R] : finiteGhostDifferential (R := R) 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [finiteGhostDifferential]

@[simp] theorem finiteGhostDifferential_add [CommRing R] (X Y : FiniteGhost R) :
    finiteGhostDifferential (X + Y) = finiteGhostDifferential X + finiteGhostDifferential Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [finiteGhostDifferential] <;> ring

@[simp] theorem finiteGhostDifferential_neg [CommRing R] (X : FiniteGhost R) :
    finiteGhostDifferential (-X) = -finiteGhostDifferential X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [finiteGhostDifferential, sub_eq_add_neg, add_comm]

@[simp] theorem finiteGhostDifferential_sq [CommRing R] (X : FiniteGhost R) :
    finiteGhostDifferential (finiteGhostDifferential X) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [finiteGhostDifferential]

@[simp] theorem finiteGhostDifferential_ghost [CommRing R] :
    finiteGhostDifferential (ghost (R := R)) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [finiteGhostDifferential, ghost]

@[simp] theorem finiteGhostDifferential_antighost [CommRing R] :
    finiteGhostDifferential (antighost (R := R)) = (1 : FiniteGhost R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [finiteGhostDifferential, antighost]

theorem ghost_isOdd [CommRing R] : isOdd (ghost (R := R)) := by
  constructor <;> simp [isOdd, ghost]

theorem antighost_isOdd [CommRing R] : isOdd (antighost (R := R)) := by
  constructor <;> simp [isOdd, antighost]

theorem one_isEven [CommRing R] : isEven (1 : FiniteGhost R) := by
  constructor <;> simp [isEven]

theorem finiteGhost_maps_grade [CommRing R] {g : Parity} {X : FiniteGhost R}
    (hX : (finiteGhostGrading (R := R)).IsHomogeneous g X) :
    (finiteGhostGrading (R := R)).IsHomogeneous (g + Parity.odd) (finiteGhostDifferential X) := by
  cases g
  · change isOdd (finiteGhostDifferential X)
    rcases hX with ⟨h01, h10⟩
    constructor <;> simp [isOdd, finiteGhostDifferential, h10]
  · change isEven (finiteGhostDifferential X)
    rcases hX with ⟨h00, h11⟩
    constructor <;> simp [isEven, finiteGhostDifferential, h00, h11]

theorem finiteGhost_leibniz [CommRing R] {g h : Parity} {x y : FiniteGhost R}
    (hx : (finiteGhostGrading (R := R)).IsHomogeneous g x)
    (hy : (finiteGhostGrading (R := R)).IsHomogeneous h y) :
    finiteGhostDifferential (x * y) = finiteGhostDifferential x * y +
      Parity.sign ((finiteGhostGrading (R := R)).parity g) (x * finiteGhostDifferential y) := by
  cases g <;> cases h
  · rcases hx with ⟨hx01, hx10⟩
    rcases hy with ⟨hy01, hy10⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [finiteGhostDifferential, finiteGhostGrading, isEven, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        hx01, hx10, hy01, hy10] <;> ring
  · rcases hx with ⟨hx01, hx10⟩
    rcases hy with ⟨hy00, hy11⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [finiteGhostDifferential, finiteGhostGrading, isEven, isOdd, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        hx01, hx10, hy00, hy11, Parity.sign] <;> ring
  · rcases hx with ⟨hx00, hx11⟩
    rcases hy with ⟨hy01, hy10⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [finiteGhostDifferential, finiteGhostGrading, isEven, isOdd, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        hx00, hx11, hy01, hy10, Parity.sign] <;> ring
  · rcases hx with ⟨hx00, hx11⟩
    rcases hy with ⟨hy00, hy11⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [finiteGhostDifferential, finiteGhostGrading, isEven, isOdd, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        hx00, hx11, hy00, hy11, Parity.sign] <;> ring

/-- The concrete finite graded BRST differential. -/
noncomputable def finiteGhostBRST [CommRing R] :
    GradedBRSTDifferential (finiteGhostGrading (R := R)) where
  toGradedDerivation := {
    differential := finiteGhostDifferential
    map_zero' := finiteGhostDifferential_zero
    map_add' := finiteGhostDifferential_add
    map_neg' := finiteGhostDifferential_neg
    maps_grade' := by
      intro g x hx
      exact finiteGhost_maps_grade hx
    leibniz' := by
      intro g h x y hx hy
      exact finiteGhost_leibniz hx hy
  }
  nilpotent := finiteGhostDifferential_sq

theorem ghost_closed [CommRing R] :
    (finiteGhostBRST (R := R)).IsClosed (ghost (R := R)) := by
  change finiteGhostDifferential (ghost (R := R)) = 0
  exact finiteGhostDifferential_ghost

theorem one_exact [CommRing R] :
    (finiteGhostBRST (R := R)).IsExact (1 : FiniteGhost R) := by
  refine ⟨antighost (R := R), ?_⟩
  change finiteGhostDifferential (antighost (R := R)) = (1 : FiniteGhost R)
  exact finiteGhostDifferential_antighost

end LeanPhy.GaugeTheory
