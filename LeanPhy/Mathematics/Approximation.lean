import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-!
# Finite approximation and error certificates

Many physical calculations replace an infinite object by a finite basis, a
finite-volume lattice, a truncated Fock space, or a numerical surrogate.  It
is unsafe to record such a replacement as an equality: the missing tail and
the discretisation residual must be explicit assumptions.  This module gives
all of those situations one small interface.

`ErrorCertificate x y ε` means exactly `dist x y ≤ ε`, together with the
fact that the advertised radius is non-negative.  The kernel can therefore
compose certificates by the triangle inequality and transport them through a
supplied Lipschitz bound.  No convergence, continuum limit, or stability
claim is inferred without such a bound.
-/

namespace LeanPhy.Mathematics

universe u v w

/-! A checked quantitative statement, suitable for truncation and residuals. -/

structure ErrorCertificate {X : Type u} [PseudoMetricSpace X]
    (x y : X) (ε : ℝ) : Prop where
  nonneg : 0 ≤ ε
  bound : dist x y ≤ ε

namespace ErrorCertificate

variable {X : Type u} [PseudoMetricSpace X]

theorem of_eq {x y : X} (hxy : x = y) : ErrorCertificate x y 0 := by
  subst y
  exact ⟨le_rfl, by simp⟩

theorem symmetric {x y : X} {ε : ℝ}
    (h : ErrorCertificate x y ε) : ErrorCertificate y x ε := by
  exact ⟨h.nonneg, by simpa [dist_comm] using h.bound⟩

theorem weaken {x y : X} {ε δ : ℝ}
    (h : ErrorCertificate x y ε) (hεδ : ε ≤ δ) : ErrorCertificate x y δ := by
  exact ⟨h.nonneg.trans hεδ, h.bound.trans hεδ⟩

theorem trans {x y z : X} {ε δ : ℝ}
    (hxy : ErrorCertificate x y ε) (hyz : ErrorCertificate y z δ) :
    ErrorCertificate x z (ε + δ) := by
  refine ⟨add_nonneg hxy.nonneg hyz.nonneg, ?_⟩
  calc
    dist x z ≤ dist x y + dist y z := dist_triangle x y z
    _ ≤ ε + δ := add_le_add hxy.bound hyz.bound

theorem add {E : Type v} [SeminormedAddCommGroup E]
    {x₁ y₁ x₂ y₂ : E} {ε₁ ε₂ : ℝ}
    (h₁ : ErrorCertificate x₁ y₁ ε₁)
    (h₂ : ErrorCertificate x₂ y₂ ε₂) :
    ErrorCertificate (x₁ + x₂) (y₁ + y₂) (ε₁ + ε₂) := by
  refine ⟨add_nonneg h₁.nonneg h₂.nonneg, ?_⟩
  rw [dist_eq_norm]
  calc
    ‖(x₁ + x₂) - (y₁ + y₂)‖ = ‖(x₁ - y₁) + (x₂ - y₂)‖ := by
      congr 1
      abel
    _ ≤ ‖x₁ - y₁‖ + ‖x₂ - y₂‖ := norm_add_le _ _
    _ = dist x₁ y₁ + dist x₂ y₂ := by
      rw [dist_eq_norm, dist_eq_norm]
    _ ≤ ε₁ + ε₂ := add_le_add h₁.bound h₂.bound

/-! A Lipschitz estimate is itself a reusable, auditable certificate. -/

structure LipschitzCertificate {Y : Type v} [PseudoMetricSpace Y]
    (f : X → Y) (L : ℝ) : Prop where
  nonneg : 0 ≤ L
  bound : ∀ a b, dist (f a) (f b) ≤ L * dist a b

theorem map {Y : Type v} [PseudoMetricSpace Y]
    {f : X → Y} {L ε : ℝ} (hf : LipschitzCertificate f L)
    {x y : X} (hxy : ErrorCertificate x y ε) :
    ErrorCertificate (f x) (f y) (L * ε) := by
  refine ⟨mul_nonneg hf.nonneg hxy.nonneg, ?_⟩
  exact (hf.bound x y).trans (mul_le_mul_of_nonneg_left hxy.bound hf.nonneg)

theorem map_zero {Y : Type v} [PseudoMetricSpace Y]
    {f : X → Y} (hf : LipschitzCertificate f 0)
    {x y : X} (hxy : ErrorCertificate x y ε) :
    ErrorCertificate (f x) (f y) 0 := by
  simpa using map hf hxy

theorem compose {Y : Type v} {Z : Type w}
    [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    {f : X → Y} {g : Y → Z} {L M : ℝ}
    (hg : LipschitzCertificate g M) (hf : LipschitzCertificate f L) :
    LipschitzCertificate (g ∘ f) (M * L) := by
  refine ⟨mul_nonneg hg.nonneg hf.nonneg, ?_⟩
  intro x y
  calc
    dist ((g ∘ f) x) ((g ∘ f) y) ≤ M * dist (f x) (f y) := hg.bound _ _
    _ ≤ M * (L * dist x y) := mul_le_mul_of_nonneg_left (hf.bound x y) hg.nonneg
    _ = (M * L) * dist x y := by ring

/-! Equation residuals are just certificates against the exact zero. -/

def ResidualCertificate {R : Type v} [PseudoMetricSpace R] [Zero R]
    (residual : R) (ε : ℝ) : Prop := ErrorCertificate residual 0 ε

theorem residual_zero {R : Type v} [PseudoMetricSpace R] [Zero R]
    (residual : R) (h : residual = 0) : ResidualCertificate residual 0 :=
  of_eq h

theorem residual_trans {R : Type v} [PseudoMetricSpace R] [Zero R]
    {r s : R} {ε δ : ℝ} (hr : ResidualCertificate r ε)
    (hs : ErrorCertificate r s δ) : ResidualCertificate s (ε + δ) := by
  change ErrorCertificate s 0 (ε + δ)
  simpa [add_comm] using
    (ErrorCertificate.trans (ErrorCertificate.symmetric hs) hr)

end ErrorCertificate

/-! A finite approximation keeps the exact target and the computable surrogate
    together, so downstream APIs cannot silently forget which one is used. -/

structure FiniteApproximation {X : Type u} [PseudoMetricSpace X]
    (exact surrogate : X) (ε : ℝ) : Prop where
  certificate : ErrorCertificate exact surrogate ε

namespace FiniteApproximation

variable {X : Type u} [PseudoMetricSpace X]

theorem symmetric {x y : X} {ε : ℝ}
    (h : FiniteApproximation x y ε) : FiniteApproximation y x ε :=
  ⟨h.certificate.symmetric⟩

theorem compose {x y z : X} {ε δ : ℝ}
    (hxy : FiniteApproximation x y ε) (hyz : FiniteApproximation y z δ) :
    FiniteApproximation x z (ε + δ) :=
  ⟨hxy.certificate.trans hyz.certificate⟩

theorem map {Y : Type v} [PseudoMetricSpace Y]
    {f : X → Y} {L ε : ℝ} (hf : ErrorCertificate.LipschitzCertificate f L)
    {x y : X} (hxy : FiniteApproximation x y ε) :
    FiniteApproximation (f x) (f y) (L * ε) :=
  ⟨ErrorCertificate.map hf hxy.certificate⟩

end FiniteApproximation

/-! A left inverse is a useful way to make a stability estimate auditable.
The operator, inverse candidate and Lipschitz modulus are all inputs; the
kernel only derives the resulting residual-to-solution bound.  This contract
is deliberately domain-neutral so finite PDE, mode, band, transfer and
classical discretisation adapters can share it. -/

structure AdditiveLeftInverseCertificate
    {X : Type u} {Y : Type v}
    [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
    (A : X →+ Y) where
  solve : Y → X
  modulus : ℝ
  modulus_nonneg : 0 ≤ modulus
  left_inverse : ∀ x, solve (A x) = x
  lipschitz : ∀ r s, dist (solve r) (solve s) ≤ modulus * dist r s

namespace AdditiveLeftInverseCertificate

variable {X : Type u} {Y : Type v}
    [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]

/-- A left inverse turns an operator residual into a solution-distance bound. -/
theorem residual_stability {A : X →+ Y}
    (I : AdditiveLeftInverseCertificate A) (x y : X) :
    dist x y ≤ I.modulus * dist (A x) (A y) := by
  have hzero : I.solve 0 = 0 := by
    simpa using I.left_inverse 0
  have hleft : I.solve (A (x - y)) = x - y :=
    I.left_inverse (x - y)
  calc
    dist x y = dist (x - y) 0 := by simp [dist_eq_norm]
    _ = dist (I.solve (A (x - y))) (I.solve 0) := by rw [hleft, hzero]
    _ ≤ I.modulus * dist (A (x - y)) 0 := I.lipschitz _ _
    _ = I.modulus * dist (A x) (A y) := by
      rw [map_sub]
      simp [dist_eq_norm]

/-- An explicit operator residual certificate yields a finite approximation. -/
theorem approximate {A : X →+ Y}
    (I : AdditiveLeftInverseCertificate A) {x y : X} {ε : ℝ}
    (h : ErrorCertificate (A x) (A y) ε) :
    FiniteApproximation x y (I.modulus * ε) := by
  refine ⟨mul_nonneg I.modulus_nonneg h.nonneg, ?_⟩
  exact (I.residual_stability x y).trans
    (mul_le_mul_of_nonneg_left h.bound I.modulus_nonneg)

end AdditiveLeftInverseCertificate

end LeanPhy.Mathematics
