import LeanPhy.GaugeTheory.LieGhostComplex
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Actual homogeneous ghost degrees

Homogeneous pieces are the exterior powers, not eigenspaces of the parity
involution. Thus the degree remains meaningful over rings of characteristic
two. Negative integer pieces are zero for this pure ghost algebra.
-/

namespace LeanPhy.GaugeTheory.GhostPolynomial

open LeanPhy.Mathematics

variable {R : Type*} [CommRing R] {n : Nat}

/-- The genuine natural-degree piece of the exterior algebra. -/
abbrev natDegree (k : Nat) : Submodule R (GhostPolynomial R n) :=
  ExteriorAlgebra.exteriorPower R k (Fin n → R)

theorem scalar_mem_natDegree (r : R) :
    algebraMap R (GhostPolynomial R n) r ∈ natDegree 0 := by
  change algebraMap R _ r ∈ (1 : Submodule R (GhostPolynomial R n))
  exact Submodule.algebraMap_mem _

theorem ι_mem_natDegree (v : Fin n → R) :
    ExteriorAlgebra.ι R v ∈ natDegree 1 := by
  change ExteriorAlgebra.ι R v ∈ LinearMap.range (ExteriorAlgebra.ι R) ^ 1
  simp

theorem generator_mem_natDegree (i : Fin n) : generator (R := R) i ∈ natDegree 1 :=
  ι_mem_natDegree _

theorem mul_mem_natDegree {k l : Nat} {x y : GhostPolynomial R n}
    (hx : x ∈ natDegree k) (hy : y ∈ natDegree l) : x * y ∈ natDegree (k + l) := by
  change x * y ∈ LinearMap.range (ExteriorAlgebra.ι R) ^ (k + l)
  rw [pow_add]
  exact Submodule.mul_mem_mul hx hy

theorem parity_natDegree {k : Nat} {x : GhostPolynomial R n} (hx : x ∈ natDegree k) :
    parityInvolution x = (-1 : R) ^ k • x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y k hx hy ihx ihy => simp only [map_add, ihx, ihy, smul_add]
  | mem_mul v hv k x hx ih =>
      obtain ⟨v, rfl⟩ := hv
      rw [map_mul, parityInvolution_ι, ih]
      simp [pow_succ]

theorem contract_mem_natDegree (f : Module.Dual R (Fin n → R))
    {k : Nat} {x : GhostPolynomial R n} (hx : x ∈ natDegree k) :
    contract f x ∈ natDegree (k - 1) ∧ (k = 0 → contract f x = 0) := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [contract_scalar]
  | add x y k hx hy ihx ihy =>
      rw [map_add]
      exact ⟨(natDegree _).add_mem ihx.1 ihy.1, fun h => by rw [ihx.2 h, ihy.2 h, add_zero]⟩
  | mem_mul v hv k x hx ih =>
      obtain ⟨v, rfl⟩ := hv
      rw [contract_ι_mul]
      constructor
      · simp only [Nat.succ_sub_one]
        refine (natDegree (R := R) (n := n) k).sub_mem ?_ ?_
        · exact (natDegree k).smul_mem (f v) hx
        · cases k with
          | zero => simp [ih.2 rfl]
          | succ k => simpa [Nat.add_comm] using mul_mem_natDegree (ι_mem_natDegree v) ih.1
      · omega

theorem derivative_mem_natDegree (i : Fin n) {k : Nat} {x : GhostPolynomial R n}
    (hx : x ∈ natDegree k) : derivative i x ∈ natDegree (k - 1) :=
  (contract_mem_natDegree _ hx).1

theorem lieImages_mem_natDegree (L : LieAlgebra R (Fin n → R)) (i : Fin n) :
    lieImages L i ∈ natDegree 2 := by
  rw [lieImages_formula]
  apply Submodule.sum_mem; intro j _
  apply Submodule.sum_mem; intro k _
  split_ifs
  · exact (natDegree 2).smul_mem _ (mul_mem_natDegree (generator_mem_natDegree j) (generator_mem_natDegree k))
  · exact (natDegree 2).zero_mem

theorem lieDifferential_mem_natDegree (L : LieAlgebra R (Fin n → R))
    {k : Nat} {x : GhostPolynomial R n} (hx : x ∈ natDegree k) :
    lieDifferential L x ∈ natDegree (k + 1) := by
  change (∑ i, lieImages L i * derivative i x) ∈ natDegree (k + 1)
  apply Submodule.sum_mem; intro i _
  cases k with
  | zero => simp [derivative, (contract_mem_natDegree (LinearMap.proj i) hx).2 rfl]
  | succ k => simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using
      mul_mem_natDegree (lieImages_mem_natDegree L i) (derivative_mem_natDegree i hx)

/-- Natural homogeneous components provide an actual finite-support decomposition. -/
noncomputable def degreeProjection (k : Nat) : GhostPolynomial R n →ₗ[R] GhostPolynomial R n :=
  _root_.GradedAlgebra.proj (fun k => natDegree (R := R) (n := n) k) k

theorem degreeProjection_mem (k : Nat) (x : GhostPolynomial R n) :
    degreeProjection k x ∈ natDegree k :=
  (DirectSum.decompose (fun k => natDegree (R := R) (n := n) k) x k).property

theorem degreeProjection_of_mem {k : Nat} {x : GhostPolynomial R n} (hx : x ∈ natDegree k) :
    degreeProjection k x = x := DirectSum.decompose_of_mem_same _ hx

theorem degreeProjection_of_ne {k l : Nat} {x : GhostPolynomial R n}
    (hx : x ∈ natDegree k) (hkl : k ≠ l) : degreeProjection l x = 0 :=
  DirectSum.decompose_of_mem_ne _ hx hkl

theorem natDegree_unique {k l : Nat} {x : GhostPolynomial R n}
    (hx : x ∈ natDegree k) (hy : x ∈ natDegree l) (hne : x ≠ 0) : k = l :=
  DirectSum.degree_eq_of_mem_mem (fun k => natDegree (R := R) (n := n) k) hx hy hne

/-- Every polynomial is the sum of finitely many actual homogeneous components. -/
theorem exists_degree_decomposition (x : GhostPolynomial R n) :
    ∃ s : Finset Nat, ∑ k ∈ s, degreeProjection k x = x := by
  classical
  exact ⟨(DirectSum.decompose (fun k => natDegree (R := R) (n := n) k) x).support,
    DirectSum.sum_support_decompose _ x⟩

/-- Integer ghost degree, zero in negative degrees for the pure exterior sector. -/
def degree (d : Int) : Submodule R (GhostPolynomial R n) :=
  if 0 ≤ d then natDegree d.toNat else ⊥

@[simp] theorem degree_nat (k : Nat) : degree (R := R) (n := n) (k : Int) = natDegree k := by
  simp [degree]

@[simp] theorem degree_negative {d : Int} (hd : d < 0) :
    degree (R := R) (n := n) d = ⊥ := by simp [degree, not_le.mpr hd]

theorem generator_mem_degree (i : Fin n) : generator (R := R) i ∈ degree 1 :=
  generator_mem_natDegree i

theorem scalar_mem_degree (r : R) : algebraMap R (GhostPolynomial R n) r ∈ degree 0 :=
  scalar_mem_natDegree r

theorem mul_mem_degree {d e : Int} {x y : GhostPolynomial R n}
    (hx : x ∈ degree d) (hy : y ∈ degree e) : x * y ∈ degree (d + e) := by
  by_cases hd : 0 ≤ d
  · by_cases he : 0 ≤ e
    · have hde : 0 ≤ d + e := add_nonneg hd he
      simpa only [degree, ite_eq_left hd, ite_eq_left he, ite_eq_left hde, Int.toNat_add hd he] using
        mul_mem_natDegree (show x ∈ natDegree d.toNat by simpa [degree, hd] using hx)
          (show y ∈ natDegree e.toNat by simpa [degree, he] using hy)
    · have hz : y = 0 := by simpa [degree, he] using hy
      simp [hz]
  · have hz : x = 0 := by simpa [degree, hd] using hx
    simp [hz]

theorem degree_unique {d e : Int} {x : GhostPolynomial R n}
    (hx : x ∈ degree d) (hy : x ∈ degree e) (hne : x ≠ 0) : d = e := by
  have hd : 0 ≤ d := by by_contra h; exact hne (by simpa [degree, h] using hx)
  have he : 0 ≤ e := by by_contra h; exact hne (by simpa [degree, h] using hy)
  have h := natDegree_unique (show x ∈ natDegree d.toNat by simpa [degree, hd] using hx)
    (show x ∈ natDegree e.toNat by simpa [degree, he] using hy) hne
  omega

theorem contract_mem_degree (f : Module.Dual R (Fin n → R))
    {d : Int} {x : GhostPolynomial R n} (hx : x ∈ degree d) : contract f x ∈ degree (d - 1) := by
  by_cases hd : 0 ≤ d
  · lift d to Nat using hd
    rw [degree_nat] at hx
    cases d with
    | zero => simp [(contract_mem_natDegree f hx).2 rfl]
    | succ k => simpa using (contract_mem_natDegree f hx).1
  · have hz : x = 0 := by simpa [degree, hd] using hx
    simp [hz]

theorem lieDifferential_mem_degree (L : LieAlgebra R (Fin n → R))
    {d : Int} {x : GhostPolynomial R n} (hx : x ∈ degree d) :
    lieDifferential L x ∈ degree (d + 1) := by
  by_cases hd : 0 ≤ d
  · lift d to Nat using hd
    rw [degree_nat] at hx
    have hd : (0 : Int) ≤ d + 1 := by omega
    simpa [degree, hd] using lieDifferential_mem_natDegree L hx
  · have hz : x = 0 := by simpa [degree, hd] using hx
    simp [hz]

/-- Integer parity; unlike degree, this forgets all information modulo two. -/
def integerParity (d : Int) : Parity := if Even d then .even else .odd

theorem integerParity_add (d e : Int) :
    integerParity (d + e) = Parity.add (integerParity d) (integerParity e) := by
  by_cases hd : Even d <;> by_cases he : Even e <;>
    simp [integerParity, Int.even_add, hd, he, Parity.add]

theorem parity_degree {d : Int} {x : GhostPolynomial R n} (hx : x ∈ degree d) :
    parityInvolution x = Parity.sign (integerParity d) x := by
  by_cases hd : 0 ≤ d
  · lift d to Nat using hd
    rw [degree_nat] at hx
    rw [parity_natDegree hx, neg_one_pow_eq_ite]
    by_cases h : Even d <;> simp [integerParity, h, Parity.sign]
  · have hz : x = 0 := by simpa [degree, hd] using hx
    simp [hz]

/-- The genuine integer grading with a specified odd differential shift. -/
def integerGrading (shift : Int) (hshift : integerParity shift = .odd) :
    GradedRing Int (GhostPolynomial R n) where
  homogeneous d := (degree (R := R) (n := n) d : Set (GhostPolynomial R n))
  zero_mem d := (degree (R := R) (n := n) d).zero_mem
  add_mem d := (degree (R := R) (n := n) d).add_mem
  neg_mem d := (degree (R := R) (n := n) d).neg_mem
  one_mem := by simpa using scalar_mem_degree (R := R) (n := n) 1
  mul_mem := mul_mem_degree
  parity := integerParity
  parity_add := integerParity_add
  differential_degree := shift
  differential_is_odd := hshift

/-- CE/BRST differential: ghost degree +1. -/
def lieDegreeGrading : GradedRing Int (GhostPolynomial R n) := integerGrading 1 (by decide)

/-- Koszul contraction: ghost degree -1 on the same homogeneous submodules. -/
def koszulDegreeGrading : GradedRing Int (GhostPolynomial R n) := integerGrading (-1) (by decide)

private theorem sign_mul (p : Parity) (x y : GhostPolynomial R n) :
    Parity.sign p x * y = Parity.sign p (x * y) := by cases p <;> simp [Parity.sign]

/-- The canonical Lie ghost differential now carries integer degree, not just parity. -/
noncomputable def integerLieBRST (L : LieAlgebra R (Fin n → R)) :
    GradedBRSTDifferential (lieDegreeGrading (R := R) (n := n)) where
  differential := lieDifferential L
  map_zero' := map_zero _
  map_add' := map_add _
  map_neg' := map_neg _
  maps_grade' := lieDifferential_mem_degree L
  leibniz' := by
    intro d e x y hx _
    rw [lieDifferential_mul, parity_degree hx, sign_mul]
    rfl
  nilpotent := lieDifferential_sq L

/-- Covector contraction with its actual descending integer degree. -/
noncomputable def integerKoszul (f : Module.Dual R (Fin n → R)) :
    GradedBRSTDifferential (koszulDegreeGrading (R := R) (n := n)) where
  differential := contract f
  map_zero' := map_zero _
  map_add' := map_add _
  map_neg' := map_neg _
  maps_grade' := by intro d x hx; exact contract_mem_degree f hx
  leibniz' := by
    intro d e x y hx _
    rw [contract_mul, parity_degree hx, sign_mul]
    rfl
  nilpotent := contract_sq f

@[simp] theorem integerLieBRST_apply (L : LieAlgebra R (Fin n → R)) (x : GhostPolynomial R n) :
    integerLieBRST L x = lieDifferential L x := rfl

@[simp] theorem integerKoszul_apply (f : Module.Dual R (Fin n → R)) (x : GhostPolynomial R n) :
    integerKoszul f x = contract f x := rfl

/-- Taking a homogeneous component commutes with the Lie differential's degree shift. -/
theorem degreeProjection_lieDifferential (L : LieAlgebra R (Fin n → R)) (k : Nat)
    (x : GhostPolynomial R n) :
    degreeProjection (k + 1) (lieDifferential L x) = lieDifferential L (degreeProjection k x) := by
  induction x using DirectSum.Decomposition.inductionOn (fun k => natDegree (R := R) (n := n) k) with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | @homogeneous j x =>
      have hj := x.property
      by_cases h : j = k
      · subst j
        rw [degreeProjection_of_mem hj, degreeProjection_of_mem (lieDifferential_mem_natDegree L hj)]
      · rw [degreeProjection_of_ne hj h, map_zero,
          degreeProjection_of_ne (lieDifferential_mem_natDegree L hj) (by omega)]

/-- A closed inhomogeneous polynomial has closed components of every degree. -/
theorem closed_degreeProjection (L : LieAlgebra R (Fin n → R)) {x : GhostPolynomial R n}
    (hx : lieDifferential L x = 0) (k : Nat) : lieDifferential L (degreeProjection k x) = 0 := by
  rw [← degreeProjection_lieDifferential, hx, map_zero]

/-- The image of the Lie differential has no degree-zero component. -/
theorem degreeProjection_zero_lieDifferential (L : LieAlgebra R (Fin n → R))
    (x : GhostPolynomial R n) : degreeProjection 0 (lieDifferential L x) = 0 := by
  induction x using DirectSum.Decomposition.inductionOn (fun k => natDegree (R := R) (n := n) k) with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | @homogeneous j x => exact degreeProjection_of_ne (lieDifferential_mem_natDegree L x.property) (by omega)

/-- A homogeneous boundary has a primitive of exactly the preceding degree. -/
theorem homogeneous_exact_iff (L : LieAlgebra R (Fin n → R))
    {k : Nat} {x : GhostPolynomial R n} (hx : x ∈ natDegree (k + 1)) :
    (∃ y, lieDifferential L y = x) ↔ ∃ y ∈ natDegree k, lieDifferential L y = x := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨degreeProjection k y, degreeProjection_mem k y, ?_⟩
    rw [← degreeProjection_lieDifferential, hy, degreeProjection_of_mem hx]
  · rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩

/-- In the pure Lie ghost complex, a scalar is exact precisely when it is zero. -/
theorem scalar_exact_iff (L : LieAlgebra R (Fin n → R)) (r : R) :
    (∃ y, lieDifferential L y = algebraMap R (GhostPolynomial R n) r) ↔ r = 0 := by
  constructor
  · rintro ⟨y, hy⟩
    have h := degreeProjection_zero_lieDifferential L y
    rw [hy, degreeProjection_of_mem (scalar_mem_natDegree r)] at h
    simpa using congrArg ExteriorAlgebra.algebraMapInv h
  · intro h; exact ⟨0, by simp [h]⟩

theorem natDegree_eq_bot_of_lt {k : Nat} (hk : n < k) :
    natDegree (R := R) (n := n) k = ⊥ := by
  let := exteriorPower.subsingleton_of_span_eq_top_of_card_lt
    (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin n)).span_eq k (by simpa using hk)
  apply bot_unique
  intro x hx
  change x = 0
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : natDegree (R := R) (n := n) k) 0)

/-- Top-degree pure ghosts are closed, without a statement about exactness. -/
theorem top_degree_closed (L : LieAlgebra R (Fin n → R)) {x : GhostPolynomial R n}
    (hx : x ∈ natDegree n) : lieDifferential L x = 0 := by
  have h := lieDifferential_mem_natDegree L hx
  simpa only [natDegree_eq_bot_of_lt (Nat.lt_succ_self n), Submodule.mem_bot] using h

theorem ghostOne_mem_natDegree (φ : Module.Dual R (Fin n → R)) :
    ghostOne φ ∈ natDegree 1 := by
  change (∑ i, φ (Pi.single i 1) • generator i) ∈ natDegree 1
  apply Submodule.sum_mem; intro i _
  exact (natDegree 1).smul_mem _ (generator_mem_natDegree i)

theorem ghostTwo_mem_natDegree (L : LieAlgebra R (Fin n → R))
    (ω : LieCochain2 L (trivialLieModule L : LieModule L R)) : ghostTwo L ω ∈ natDegree 2 := by
  change (∑ i, ∑ j, if i < j then ω (Pi.single i 1) (Pi.single j 1) •
    (generator i * generator j) else 0) ∈ natDegree 2
  apply Submodule.sum_mem; intro i _
  apply Submodule.sum_mem; intro j _
  split_ifs
  · exact (natDegree 2).smul_mem _ (mul_mem_natDegree (generator_mem_natDegree i) (generator_mem_natDegree j))
  · exact (natDegree 2).zero_mem

theorem ghostThree_mem_natDegree (L : LieAlgebra R (Fin n → R))
    (t : LieCochain3 L (trivialLieModule L : LieModule L R)) : ghostThree L t ∈ natDegree 3 := by
  change (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
    t (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) •
      (generator i * (generator j * generator k)) else 0) ∈ natDegree 3
  apply Submodule.sum_mem; intro i _
  apply Submodule.sum_mem; intro j _
  apply Submodule.sum_mem; intro k _
  split_ifs
  · exact (natDegree 3).smul_mem _ (mul_mem_natDegree (generator_mem_natDegree i)
      (mul_mem_natDegree (generator_mem_natDegree j) (generator_mem_natDegree k)))
  · exact (natDegree 3).zero_mem

end LeanPhy.GaugeTheory.GhostPolynomial
