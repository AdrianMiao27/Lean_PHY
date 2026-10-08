import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Certified reduction of a cochain complex

A reduction supplies representatives, class coordinates, a boundary primitive
and a correction for nonclosed cochains. Five linear identities certify the
entire middle cohomology, including completeness of the representatives.
The matrix version can be produced by an untrusted exact-arithmetic solver;
Lean checks every identity and constructs an actual quotient equivalence.
-/

namespace LeanPhy.Mathematics

universe u v w x y

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w} {C : Type x} {H : Type y}
variable [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
variable [AddCommGroup C] [Module R C] [AddCommGroup H] [Module R H]

/-- A complete, split reduction of the middle cohomology of `A → B → C`.
Over general rings such a certificate need not exist. -/
structure CohomologyReduction (d₁ : A →ₗ[R] B) (d₂ : B →ₗ[R] C) (H : Type y)
    [AddCommGroup H] [Module R H] where
  project : B →ₗ[R] H
  represent : H →ₗ[R] B
  primitive : B →ₗ[R] A
  correction : C →ₗ[R] B
  chain : d₂.comp d₁ = 0
  closed : d₂.comp represent = 0
  boundary : project.comp d₁ = 0
  retract : project.comp represent = LinearMap.id
  decompose : d₁.comp primitive + represent.comp project + correction.comp d₂ = LinearMap.id

namespace CohomologyReduction

variable {d₁ : A →ₗ[R] B} {d₂ : B →ₗ[R] C} (S : CohomologyReduction d₁ d₂ H)

@[simp] theorem project_boundary (a : A) : S.project (d₁ a) = 0 :=
  LinearMap.congr_fun S.boundary a

@[simp] theorem represent_closed (h : H) : d₂ (S.represent h) = 0 :=
  LinearMap.congr_fun S.closed h

@[simp] theorem project_represent (h : H) : S.project (S.represent h) = h :=
  LinearMap.congr_fun S.retract h

/-- Every closed cochain has a computed representative and an explicit primitive. -/
theorem normal_form (b : B) (hb : d₂ b = 0) :
    d₁ (S.primitive b) + S.represent (S.project b) = b := by
  have h := LinearMap.congr_fun S.decompose b
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, hb,
    map_zero, add_zero] using h

/-- Exactness is decided by the vanishing of the computed coordinates. -/
theorem exact_iff (b : B) (hb : d₂ b = 0) :
    (∃ a, d₁ a = b) ↔ S.project b = 0 := by
  constructor
  · rintro ⟨a, rfl⟩; exact S.project_boundary a
  · intro h
    refine ⟨S.primitive b, ?_⟩
    simpa only [h, map_zero, add_zero] using S.normal_form b hb

theorem cohomologous_iff (b c : B) (hb : d₂ b = 0) (hc : d₂ c = 0) :
    (∃ a, d₁ a = b - c) ↔ S.project b = S.project c := by
  rw [S.exact_iff (b - c) (by simp [hb, hc]), map_sub, sub_eq_zero]

/-- Boundary submodule pulled back to the closed cochains. -/
def boundariesInCycles (d₁ : A →ₗ[R] B) (d₂ : B →ₗ[R] C) :
    Submodule R (LinearMap.ker d₂) :=
  (LinearMap.range d₁).comap (LinearMap.ker d₂).subtype

abbrev Cohomology (d₁ : A →ₗ[R] B) (d₂ : B →ₗ[R] C) :=
  (LinearMap.ker d₂) ⧸ boundariesInCycles d₁ d₂

def classOf (b : B) (hb : d₂ b = 0) : Cohomology d₁ d₂ :=
  Submodule.Quotient.mk ⟨b, hb⟩

/-- The projection descends through the quotient because boundaries map to zero. -/
def quotientProject : Cohomology d₁ d₂ →ₗ[R] H :=
  (boundariesInCycles d₁ d₂).liftQ (S.project.comp (LinearMap.ker d₂).subtype) (by
    rintro b ⟨a, ha⟩
    change S.project b.val = 0
    change d₁ a = b.val at ha
    rw [← ha, S.project_boundary])

def cycleInclude : H →ₗ[R] LinearMap.ker d₂ :=
  S.represent.codRestrict (LinearMap.ker d₂) (fun h => S.represent_closed h)

def quotientInclude : H →ₗ[R] Cohomology d₁ d₂ :=
  (boundariesInCycles d₁ d₂).mkQ.comp S.cycleInclude

@[simp] theorem quotientProject_classOf (b : B) (hb : d₂ b = 0) :
    S.quotientProject (classOf b hb) = S.project b := rfl

/-- A linear equivalence, not only a list of independent candidate classes. -/
def quotientEquiv : Cohomology d₁ d₂ ≃ₗ[R] H where
  __ := S.quotientProject
  invFun := S.quotientInclude
  left_inv := by
    intro q
    obtain ⟨b, rfl⟩ := (boundariesInCycles d₁ d₂).mkQ_surjective q
    apply (Submodule.Quotient.eq (boundariesInCycles d₁ d₂)).mpr
    change ∃ a, d₁ a = S.represent (S.project b.val) - b.val
    refine ⟨-S.primitive b.val, ?_⟩
    have h := S.normal_form b.val b.property
    rw [map_neg]
    calc
      _ = S.represent (S.project b.val) -
          (d₁ (S.primitive b.val) + S.represent (S.project b.val)) := by abel
      _ = _ := congrArg (fun x => S.represent (S.project b.val) - x) h
  right_inv := by
    intro h
    change S.project (S.represent h) = h
    exact S.project_represent h

@[simp] theorem quotientEquiv_classOf (b : B) (hb : d₂ b = 0) :
    S.quotientEquiv (classOf b hb) = S.project b := rfl

/-- Transfer a matrix reduction through cochain coordinates. The next map
may be sampled into a smaller space, provided zero is reflected on its image. -/
noncomputable def transport
    {A' B' C' : Type*} [AddCommGroup A'] [Module R A']
    [AddCommGroup B'] [Module R B'] [AddCommGroup C'] [Module R C']
    {f : A' →ₗ[R] B'} {g : B' →ₗ[R] C'} (T : CohomologyReduction f g H)
    (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (readNext : C →ₗ[R] C')
    (hf : ∀ a, eB (d₁ a) = f (eA a))
    (hg : ∀ b, g (eB b) = readNext (d₂ b))
    (detect : ∀ b, readNext (d₂ b) = 0 → d₂ b = 0) :
    CohomologyReduction d₁ d₂ H where
  project := T.project.comp eB.toLinearMap
  represent := eB.symm.toLinearMap.comp T.represent
  primitive := eA.symm.toLinearMap.comp (T.primitive.comp eB.toLinearMap)
  correction := eB.symm.toLinearMap.comp (T.correction.comp readNext)
  chain := by
    ext a
    apply detect
    rw [← hg, hf]
    exact LinearMap.congr_fun T.chain (eA a)
  closed := by
    ext h
    apply detect
    rw [← hg]
    change g (eB (eB.symm (T.represent h))) = 0
    rw [eB.apply_symm_apply, T.represent_closed]
  boundary := by
    ext a
    change T.project (eB (d₁ a)) = 0
    rw [hf, T.project_boundary]
  retract := by
    ext h
    change T.project (eB (eB.symm (T.represent h))) = h
    rw [eB.apply_symm_apply, T.project_represent]
  decompose := by
    ext b
    apply eB.injective
    change eB (d₁ (eA.symm (T.primitive (eB b))) +
      eB.symm (T.represent (T.project (eB b))) +
      eB.symm (T.correction (readNext (d₂ b)))) = eB b
    simp only [map_add, eB.apply_symm_apply]
    rw [hf, eA.apply_symm_apply, ← hg]
    exact LinearMap.congr_fun T.decompose (eB b)

end CohomologyReduction

/-- A finite matrix certificate. All matrices are data; all five identities
are proof obligations. No rank estimate or solver output is trusted. -/
structure MatrixCohomologyReduction {a b c : Nat}
    (d₁ : Matrix (Fin b) (Fin a) R) (d₂ : Matrix (Fin c) (Fin b) R) (h : Nat) where
  project : Matrix (Fin h) (Fin b) R
  represent : Matrix (Fin b) (Fin h) R
  primitive : Matrix (Fin a) (Fin b) R
  correction : Matrix (Fin b) (Fin c) R
  chain : d₂ * d₁ = 0
  closed : d₂ * represent = 0
  boundary : project * d₁ = 0
  retract : project * represent = 1
  decompose : d₁ * primitive + represent * project + correction * d₂ = 1

namespace MatrixCohomologyReduction

variable {a b c h : Nat}
variable {d₁ : Matrix (Fin b) (Fin a) R} {d₂ : Matrix (Fin c) (Fin b) R}

noncomputable def toReduction (S : MatrixCohomologyReduction d₁ d₂ h) :
    CohomologyReduction d₁.toLin' d₂.toLin' (Fin h → R) where
  project := S.project.toLin'
  represent := S.represent.toLin'
  primitive := S.primitive.toLin'
  correction := S.correction.toLin'
  chain := by simpa only [Matrix.toLin'_mul, map_zero] using congrArg Matrix.toLin' S.chain
  closed := by simpa only [Matrix.toLin'_mul, map_zero] using congrArg Matrix.toLin' S.closed
  boundary := by simpa only [Matrix.toLin'_mul, map_zero] using congrArg Matrix.toLin' S.boundary
  retract := by simpa only [Matrix.toLin'_mul, Matrix.toLin'_one] using congrArg Matrix.toLin' S.retract
  decompose := by
    simpa only [map_add, Matrix.toLin'_mul, Matrix.toLin'_one] using congrArg Matrix.toLin' S.decompose

end MatrixCohomologyReduction

end LeanPhy.Mathematics
