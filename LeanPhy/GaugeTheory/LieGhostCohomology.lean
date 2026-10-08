import LeanPhy.GaugeTheory.GhostDegree

/-!
# Low-degree cohomology of the pure Lie ghost complex

Ordered contractions recover scalar cochains from their ghost coordinates.
The actual degree decomposition controls arbitrary polynomial primitives.
-/

namespace LeanPhy.GaugeTheory.GhostPolynomial

open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology

set_option maxSynthPendingDepth 7

variable {R : Type*} [CommRing R] {n : Nat}

noncomputable def pairCoefficient (i j : Fin n) : GhostPolynomial R n →ₗ[R] R :=
  ExteriorAlgebra.algebraMapInv.toLinearMap ∘ₗ derivative j ∘ₗ derivative i

noncomputable def tripleCoefficient (i j k : Fin n) : GhostPolynomial R n →ₗ[R] R :=
  ExteriorAlgebra.algebraMapInv.toLinearMap ∘ₗ derivative k ∘ₗ derivative j ∘ₗ derivative i

theorem pairCoefficient_generators (i j a b : Fin n) :
    pairCoefficient (R := R) i j (generator a * generator b) =
      (if i = a ∧ j = b then 1 else 0) - (if i = b ∧ j = a then 1 else 0) := by
  simp [pairCoefficient, derivative, contract_mul, generator, Pi.single_apply]
  split_ifs <;> simp_all

theorem pairCoefficient_ghostTwo (L : LieAlgebra R (Fin n → R))
    (ω : LieCochain2 L (trivialLieModule L : LieModule L R))
    (i j : Fin n) (hij : i < j) :
    pairCoefficient i j (ghostTwo L ω) = ω (Pi.single i 1) (Pi.single j 1) := by
  change pairCoefficient i j (∑ a, ∑ b, if a < b then
    ω (Pi.single a 1) (Pi.single b 1) • (generator a * generator b) else 0) = _
  simp only [map_sum, apply_ite, map_smul, map_zero]
  have term (a b : Fin n) :
      (if a < b then ω (Pi.single a 1) (Pi.single b 1) •
        pairCoefficient i j (generator a * generator b) else 0) =
      if a = i then if b = j then ω (Pi.single i 1) (Pi.single j 1) else 0 else 0 := by
    rw [pairCoefficient_generators]
    split_ifs <;> (try omega) <;> subst_vars <;> simp_all only [smul_eq_mul, mul_one, mul_zero, sub_zero, sub_self]
  simp_rw [term]
  simp

theorem ghostTwo_injective (L : LieAlgebra R (Fin n → R)) : Function.Injective (ghostTwo L) := by
  intro ω η h
  have ordered (i j : Fin n) (hij : i < j) : ω (Pi.single i 1) (Pi.single j 1) =
      η (Pi.single i 1) (Pi.single j 1) := by
    simpa only [pairCoefficient_ghostTwo L _ i j hij] using congrArg (pairCoefficient i j) h
  apply LieCochainCoordinates.ext_basis
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact ordered i j hij
  · simp [LieCochainCoordinates.e]
  · rw [ω.skew, η.skew]; exact congrArg Neg.neg (ordered j i hji)

private theorem derivative_triple (i a b c : Fin n) :
    derivative (R := R) i (generator a * (generator b * generator c)) =
      (if i = a then generator b * generator c else 0) -
      (if i = b then generator a * generator c else 0) +
      (if i = c then generator a * generator b else 0) := by
  simp [derivative, contract_mul, generator, Pi.single_apply]
  split_ifs <;> simp_all

theorem tripleCoefficient_generators (i j k a b c : Fin n) :
    tripleCoefficient (R := R) i j k (generator a * (generator b * generator c)) =
      (if i = a then pairCoefficient j k (generator b * generator c) else 0) -
      (if i = b then pairCoefficient j k (generator a * generator c) else 0) +
      (if i = c then pairCoefficient j k (generator a * generator b) else 0) := by
  change pairCoefficient j k (derivative i _) = _
  rw [derivative_triple]
  split_ifs <;> simp only [map_add, map_sub, map_zero]

private theorem tripleCoefficient_ordered (i j k a b c : Fin n)
    (hij : i < j) (hjk : j < k) (hab : a < b) (hbc : b < c) :
    tripleCoefficient (R := R) i j k (generator a * (generator b * generator c)) =
      if a = i then if b = j then if c = k then 1 else 0 else 0 else 0 := by
  rw [tripleCoefficient_generators]
  simp only [pairCoefficient_generators]
  by_cases ha : a = i
  · subst a
    have hib : i ≠ b := ne_of_lt hab
    have hic : i ≠ c := ne_of_lt (hab.trans hbc)
    simp only [ite_true, eq_self, hib, hic, ite_false, sub_zero, add_zero]
    split_ifs <;> (try omega) <;> norm_num
  · by_cases hb : b = i
    · subst b
      have hia : i ≠ a := ne_of_gt hab
      have hic : i ≠ c := ne_of_lt hbc
      have hja : j ≠ a := by omega
      have hka : k ≠ a := by omega
      simp [ha, hia, hic, hja, hka]
    · by_cases hc : c = i
      · subst c
        have hia : i ≠ a := by omega
        have hib : i ≠ b := ne_of_gt hbc
        have hja : j ≠ a := by omega
        have hjb : j ≠ b := by omega
        simp [ha, hia, hib, hja, hjb]
      · simp [ha, Ne.symm ha, Ne.symm hb, Ne.symm hc]

theorem tripleCoefficient_ghostThree (L : LieAlgebra R (Fin n → R))
    (t : LieCochain3 L (trivialLieModule L : LieModule L R))
    (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    tripleCoefficient i j k (ghostThree L t) =
      t (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) := by
  change tripleCoefficient i j k (∑ a, ∑ b, ∑ c, if a < b ∧ b < c then
    t (Pi.single a 1) (Pi.single b 1) (Pi.single c 1) •
      (generator a * (generator b * generator c)) else 0) = _
  simp only [map_sum, apply_ite, map_smul, map_zero]
  have term (a b c : Fin n) :
      (if a < b ∧ b < c then t (Pi.single a 1) (Pi.single b 1) (Pi.single c 1) •
        tripleCoefficient i j k (generator a * (generator b * generator c)) else 0) =
      if a = i then if b = j then if c = k then
        t (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) else 0 else 0 else 0 := by
    by_cases h : a < b ∧ b < c
    · rw [ite_eq_left h, tripleCoefficient_ordered i j k a b c hij hjk h.1 h.2]
      split_ifs <;> subst_vars <;> simp only [smul_eq_mul, mul_one, mul_zero]
    · rw [ite_eq_right h]
      split_ifs <;> (try omega) <;> rfl
  simp_rw [term]
  simp

/-- Coordinate alternating two-form, defined without division by two. -/
def coordinateTwo (L : LieAlgebra R (Fin n → R)) (i j : Fin n) :
    LieCochain2 L (trivialLieModule L : LieModule L R) where
  eval v w := v i * w j - v j * w i
  map_add_left' := by intros; simp; ring
  map_add_right' := by intros; simp; ring
  map_smul_left' := by intros; simp; ring
  map_smul_right' := by intros; simp; ring
  alternating' := by intros; ring

theorem ghostTwo_coordinateTwo (L : LieAlgebra R (Fin n → R))
    (i j : Fin n) (hij : i < j) :
    ghostTwo L (coordinateTwo L i j) = generator i * generator j := by
  change (∑ a, ∑ b, if a < b then
    ((Pi.single a (1 : R) : Fin n → R) i * (Pi.single b (1 : R) : Fin n → R) j -
      (Pi.single a (1 : R) : Fin n → R) j * (Pi.single b (1 : R) : Fin n → R) i) • (generator (R := R) a * generator b) else 0) = _
  have term (a b : Fin n) :
      (if a < b then ((Pi.single a (1 : R) : Fin n → R) i * (Pi.single b (1 : R) : Fin n → R) j -
        (Pi.single a (1 : R) : Fin n → R) j * (Pi.single b (1 : R) : Fin n → R) i) • (generator (R := R) a * generator b) else 0) =
      if a = i then if b = j then generator (R := R) i * generator j else 0 else 0 := by
    simp only [Pi.single_apply]
    split_ifs <;> (try omega) <;> subst_vars <;>
      simp only [mul_one, mul_zero, sub_self, sub_zero, zero_smul, one_smul]
  simp_rw [term]
  simp

/-- All exterior degree-two elements, not only an ansatz, have cochain coordinates. -/
theorem natDegree_two_le_range (L : LieAlgebra R (Fin n → R)) :
    natDegree (R := R) (n := n) 2 ≤ LinearMap.range (ghostTwo L) := by
  have pair (i j : Fin n) : generator (R := R) i * generator j ∈ LinearMap.range (ghostTwo L) := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact ⟨coordinateTwo L i j, ghostTwo_coordinateTwo L i j hij⟩
    · simp
    · have h := (LinearMap.range (ghostTwo L)).neg_mem
        (show generator j * generator i ∈ LinearMap.range (ghostTwo L) from
          ⟨coordinateTwo L j i, ghostTwo_coordinateTwo L j i hji⟩)
      simpa only [generator_swap j i, neg_neg] using h
  change LinearMap.range (ExteriorAlgebra.ι R) ^ 2 ≤ _
  rw [pow_two]
  apply Submodule.mul_le.mpr
  rintro x ⟨v, rfl⟩ y ⟨w, rfl⟩
  rw [ι_eq_sum_generators, ι_eq_sum_generators, Finset.sum_mul]
  apply Submodule.sum_mem; intro i _
  rw [Finset.mul_sum]
  apply Submodule.sum_mem; intro j _
  simpa only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm] using
    (LinearMap.range (ghostTwo L)).smul_mem (v i * w j) (pair i j)

noncomputable def ghostTwoHomogeneous (L : LieAlgebra R (Fin n → R)) :
    LieCochain2 L (trivialLieModule L : LieModule L R) →ₗ[R] natDegree (R := R) (n := n) 2 :=
  (ghostTwo L).codRestrict _ (ghostTwo_mem_natDegree L)

noncomputable def ghostTwoEquiv (L : LieAlgebra R (Fin n → R)) :
    LieCochain2 L (trivialLieModule L : LieModule L R) ≃ₗ[R] natDegree (R := R) (n := n) 2 :=
  LinearEquiv.ofBijective (ghostTwoHomogeneous L) ⟨
    fun _ _ h => ghostTwo_injective L (congrArg Subtype.val h), by
      intro x
      obtain ⟨ω, hω⟩ := natDegree_two_le_range L x.property
      exact ⟨ω, Subtype.ext hω⟩⟩

@[simp] theorem ghostTwoEquiv_val (L : LieAlgebra R (Fin n → R))
    (ω : LieCochain2 L (trivialLieModule L : LieModule L R)) :
    (ghostTwoEquiv L ω).val = ghostTwo L ω := rfl

/-- Every degree-one ghost polynomial comes from an actual scalar one-cochain. -/
theorem exists_ghostOne {x : GhostPolynomial R n} (hx : x ∈ natDegree 1) :
    ∃ φ : Module.Dual R (Fin n → R), ghostOne φ = x := by
  change x ∈ LinearMap.range (ExteriorAlgebra.ι R) ^ 1 at hx
  rw [pow_one] at hx
  obtain ⟨v, rfl⟩ := hx
  refine ⟨(LieCochainCoordinates.oneEquiv n).symm v, ?_⟩
  rw [ι_eq_sum_generators]
  change (∑ i, ((LieCochainCoordinates.oneEquiv n).symm v) (Pi.single i 1) • generator i) = _
  have h := (LieCochainCoordinates.oneEquiv (R := R) n).apply_symm_apply v
  apply Finset.sum_congr rfl; intro i _
  exact congrArg (fun r : R => r • generator i) (congrFun h i)

/-- The closedness bridge is an equivalence, not only a forward implication. -/
theorem ghostTwo_closed_iff (L : LieAlgebra R (Fin n → R))
    (ω : LieCochain2 L (trivialLieModule L : LieModule L R)) :
    lieDifferential L (ghostTwo L ω) = 0 ↔ IsTwoCocycle (trivialLieModule L) ω := by
  rw [lieDifferential_ghostTwo]
  constructor
  · intro h
    apply LieCochainCoordinates.differential2_eq_zero_of_increasing
    intro i j k hij hjk
    have hc := congrArg (tripleCoefficient i j k) h
    simpa only [tripleCoefficient_ghostThree L _ i j k hij hjk, map_zero,
      differential2Cochain_apply, LieCochainCoordinates.e] using hc
  · intro h
    have ht : differential2Cochain (trivialLieModule L) ω = 0 := Subtype.ext h
    rw [ht, map_zero]

/-- Exactness allows arbitrary polynomial primitives and reflects CE boundaries. -/
theorem ghostTwo_exact_iff (L : LieAlgebra R (Fin n → R))
    (ω : LieCochain2 L (trivialLieModule L : LieModule L R)) :
    (∃ y, lieDifferential L y = ghostTwo L ω) ↔ IsTwoCoboundary (trivialLieModule L) ω := by
  rw [homogeneous_exact_iff L (show ghostTwo L ω ∈ natDegree (1 + 1) from ghostTwo_mem_natDegree L ω)]
  constructor
  · rintro ⟨y, hy, h⟩
    obtain ⟨φ, rfl⟩ := exists_ghostOne hy
    exact ⟨φ, ghostTwo_injective L (by rwa [lieDifferential_ghostOne] at h)⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨ghostOne φ, ghostOne_mem_natDegree φ, lieDifferential_ghostOne L φ⟩

theorem ghostTwo_cohomologous_iff (L : LieAlgebra R (Fin n → R))
    (ω η : LieCochain2 L (trivialLieModule L : LieModule L R)) :
    (integerLieBRST L).Cohomologous (ghostTwo L ω) (ghostTwo L η) ↔
      Cohomologous2 (trivialLieModule L) ω η := by
  change (∃ y, lieDifferential L y = ghostTwo L ω - ghostTwo L η) ↔ _
  rw [← map_sub]
  exact ghostTwo_exact_iff L (ω - η)

/-- A supplied reduction gives a complete ghost exactness test on closed cochains. -/
theorem ghostTwo_exact_iff_coordinates (L : LieAlgebra R (Fin n → R))
    {H : Type*} [AddCommGroup H] [Module R H]
    (S : Reduction (trivialLieModule L : LieModule L R) H)
    (ω : LieCochain2 L (trivialLieModule L : LieModule L R))
    (hω : IsTwoCocycle (trivialLieModule L) ω) :
    (∃ y, lieDifferential L y = ghostTwo L ω) ↔ S.project ω = 0 := by
  rw [ghostTwo_exact_iff]
  exact S.exact_iff ω hω

/-- Computed CE representatives and primitives become a ghost polynomial normal form. -/
theorem ghostTwo_normal_form (L : LieAlgebra R (Fin n → R))
    {H : Type*} [AddCommGroup H] [Module R H]
    (S : Reduction (trivialLieModule L : LieModule L R) H)
    (ω : LieCochain2 L (trivialLieModule L : LieModule L R))
    (hω : IsTwoCocycle (trivialLieModule L) ω) :
    lieDifferential L (ghostOne (S.primitive ω)) + ghostTwo L (S.represent (S.project ω)) =
      ghostTwo L ω := by
  rw [lieDifferential_ghostOne, ← map_add]
  exact congrArg (ghostTwo L) (S.normal_form ω hω)

/-- Actual closed homogeneous polynomials of ghost degree two. -/
noncomputable def twoGhostCycles (L : LieAlgebra R (Fin n → R)) : Submodule R (GhostPolynomial R n) :=
  natDegree 2 ⊓ LinearMap.ker (lieDifferential L)

/-- Boundaries are images of arbitrary polynomials, pulled back to degree-two cycles. -/
noncomputable def twoGhostBoundaries (L : LieAlgebra R (Fin n → R)) : Submodule R (twoGhostCycles L) :=
  (LinearMap.range (lieDifferential L)).comap (twoGhostCycles L).subtype

/-- The actual degree-two pure ghost cohomology module. -/
abbrev GhostH2 (L : LieAlgebra R (Fin n → R)) := (twoGhostCycles L) ⧸ twoGhostBoundaries L

noncomputable def twoGhostClass (L : LieAlgebra R (Fin n → R)) (x : GhostPolynomial R n)
    (hx : x ∈ natDegree 2) (hd : lieDifferential L x = 0) : GhostH2 L :=
  Submodule.Quotient.mk ⟨x, hx, hd⟩

theorem twoGhostClass_eq_zero_iff (L : LieAlgebra R (Fin n → R)) (x : GhostPolynomial R n)
    (hx : x ∈ natDegree 2) (hd : lieDifferential L x = 0) :
    twoGhostClass L x hx hd = 0 ↔ ∃ y, lieDifferential L y = x :=
  Submodule.Quotient.mk_eq_zero (twoGhostBoundaries L)

theorem twoGhostClass_eq_iff (L : LieAlgebra R (Fin n → R)) (x y : GhostPolynomial R n)
    (hx : x ∈ natDegree 2) (hy : y ∈ natDegree 2)
    (hdx : lieDifferential L x = 0) (hdy : lieDifferential L y = 0) :
    twoGhostClass L x hx hdx = twoGhostClass L y hy hdy ↔
      ∃ z, lieDifferential L z = x - y :=
  Submodule.Quotient.eq (twoGhostBoundaries L)

noncomputable def twoGhostCycleMap (L : LieAlgebra R (Fin n → R)) :
    twoCocycles (trivialLieModule L : LieModule L R) →ₗ[R] twoGhostCycles L :=
  ((ghostTwo L).comp (twoCocycles (trivialLieModule L)).subtype).codRestrict _
    (fun ω => ⟨ghostTwo_mem_natDegree L ω.val, (ghostTwo_closed_iff L ω.val).mpr ω.property⟩)

noncomputable def twoGhostCycleEquiv (L : LieAlgebra R (Fin n → R)) :
    twoCocycles (trivialLieModule L : LieModule L R) ≃ₗ[R] twoGhostCycles L :=
  LinearEquiv.ofBijective (twoGhostCycleMap L) ⟨by
    intro ω η h
    exact Subtype.ext (ghostTwo_injective L (congrArg Subtype.val h)), by
    intro x
    obtain ⟨ω, hω⟩ := natDegree_two_le_range L x.property.1
    refine ⟨⟨ω, (ghostTwo_closed_iff L ω).mp ?_⟩, Subtype.ext hω⟩
    rw [hω]; exact x.property.2⟩

@[simp] theorem twoGhostCycleEquiv_val (L : LieAlgebra R (Fin n → R))
    (ω : twoCocycles (trivialLieModule L : LieModule L R)) :
    (twoGhostCycleEquiv L ω).val = ghostTwo L ω.val := rfl

theorem twoGhostCycleEquiv_boundaries (L : LieAlgebra R (Fin n → R)) :
    (twoBoundariesInCycles (trivialLieModule L : LieModule L R)).map
      (twoGhostCycleEquiv L).toLinearMap = twoGhostBoundaries L := by
  ext x
  constructor
  · rintro ⟨ω, hω, rfl⟩
    change ∃ y, lieDifferential L y = ghostTwo L ω.val
    exact (ghostTwo_exact_iff L ω.val).mpr hω
  · intro hx
    let ω := (twoGhostCycleEquiv L).symm x
    refine ⟨ω, ?_, (twoGhostCycleEquiv L).apply_symm_apply x⟩
    change IsTwoCoboundary (trivialLieModule L) ω.val
    apply (ghostTwo_exact_iff L ω.val).mp
    have h : ghostTwo L ω.val = x.val :=
      congrArg Subtype.val ((twoGhostCycleEquiv L).apply_symm_apply x)
    rw [h]
    exact hx

/-- CE H² and the actual homogeneous ghost H² are linearly equivalent over any commutative ring. -/
noncomputable def h2GhostEquiv (L : LieAlgebra R (Fin n → R)) :
    H2 (trivialLieModule L : LieModule L R) ≃ₗ[R] GhostH2 L :=
  Submodule.Quotient.equiv _ _ (twoGhostCycleEquiv L) (twoGhostCycleEquiv_boundaries L)

@[simp] theorem h2GhostEquiv_classOf (L : LieAlgebra R (Fin n → R))
    (ω : LieCochain2 L (trivialLieModule L : LieModule L R))
    (hω : IsTwoCocycle (trivialLieModule L) ω) :
    h2GhostEquiv L (classOf (trivialLieModule L) ω hω) =
      twoGhostClass L (ghostTwo L ω) (ghostTwo_mem_natDegree L ω) ((ghostTwo_closed_iff L ω).mpr hω) := rfl

/-- A certified CE reduction now computes the actual degree-two ghost quotient. -/
noncomputable def ghostH2ReductionEquiv (L : LieAlgebra R (Fin n → R))
    {H : Type*} [AddCommGroup H] [Module R H]
    (S : Reduction (trivialLieModule L : LieModule L R) H) : GhostH2 L ≃ₗ[R] H :=
  (h2GhostEquiv L).symm.trans (S.h2Equiv (trivialLieModule L))

@[simp] theorem ghostH2ReductionEquiv_classOf (L : LieAlgebra R (Fin n → R))
    {H : Type*} [AddCommGroup H] [Module R H]
    (S : Reduction (trivialLieModule L : LieModule L R) H)
    (ω : LieCochain2 L (trivialLieModule L : LieModule L R))
    (hω : IsTwoCocycle (trivialLieModule L) ω) :
    ghostH2ReductionEquiv L S
      (twoGhostClass L (ghostTwo L ω) (ghostTwo_mem_natDegree L ω) ((ghostTwo_closed_iff L ω).mpr hω)) =
      S.project ω := by
  rw [← h2GhostEquiv_classOf L ω hω]
  simp only [ghostH2ReductionEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    Reduction.h2Equiv_classOf]

end LeanPhy.GaugeTheory.GhostPolynomial
