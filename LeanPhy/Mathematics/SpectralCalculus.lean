import LeanPhy.Mathematics.HilbertSpectrum
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Tactic

/-!
# Polynomial spectral calculus certificates

This module connects the bounded-operator spectrum layer with the finite and
Hilbert-space layers used by physics models.  The interface is deliberately
polynomial: it is already useful for Hamiltonian powers, resolvents, moments,
finite filters and lattice transfer operators, while it does not pretend that
an arbitrary measurable or unbounded functional calculus has been constructed.

Every analytic conclusion below is inherited from mathlib and every physical
bound remains an explicit hypothesis.  In particular, a spectral mapping
statement does not create a spectrum, and a finite-dimensional eigenbasis
certificate does not establish self-adjointness of an unbounded Hamiltonian.
-/

namespace LeanPhy.Mathematics

open Filter
open Module.End
open Polynomial
open scoped Topology

universe u v

/-! ## Bounded complex Banach-algebra bridge -/

/-- Polynomial spectral mapping for a bounded complex operator.

The operator polynomial uses mathlib's `aeval`; the image on the right uses
the ordinary scalar polynomial evaluation.  This is the exact theorem needed
to transport a certified spectral enclosure through a polynomial Hamiltonian
or transfer operator expression.
-/
theorem polynomial_spectrum_map {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Nontrivial E] (A : E →L[ℂ] E) (p : Polynomial ℂ) :
    spectrum ℂ (aeval A p) = (fun z => p.eval z) '' spectrum ℂ A := by
  exact spectrum.map_polynomial_aeval A p

/-! The spectral-radius limit is exposed beside the mapping theorem so that a
    Gelfand/numerical estimate can be recorded in one research package. -/

theorem spectral_radius_gelfand_limit {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Nontrivial E] (A : E →L[ℂ] E) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (‖A ^ n‖ ^ (1 / n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ A)) := by
  exact spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius A

/-! ## Polynomial action on an eigenvector -/

private theorem iterate_apply_eigenvector {𝕜 : Type u} {E : Type v}
    [CommRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (T : E →ₗ[𝕜] E) (v : E) (eigenvalue : 𝕜)
    (hT : T v = eigenvalue • v) :
    ∀ n : ℕ, (T ^ n) v = eigenvalue ^ n • v := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, hT, map_smul, ih]
      simp [smul_smul, pow_succ, mul_comm]

/-- A polynomial in an endomorphism acts on an eigenvector by evaluating the
polynomial at the corresponding eigenvalue. -/
theorem polynomial_aeval_apply_eigenvector {𝕜 : Type u} {E : Type v}
    [CommRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (T : E →ₗ[𝕜] E) (v : E) (eigenvalue : 𝕜)
    (hT : T v = eigenvalue • v) (p : Polynomial 𝕜) :
    (aeval T p) v = p.eval eigenvalue • v := by
  rw [Polynomial.aeval_endomorphism, Polynomial.eval_eq_sum]
  have hpow := iterate_apply_eigenvector T v eigenvalue hT
  simp_rw [hpow]
  rw [Polynomial.sum_def, Polynomial.sum_def, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro n hn
  simp [smul_smul, mul_comm]

/-! A named action keeps the conversion from a continuous operator to its
    underlying linear map explicit.  This avoids relying on definitional
    equality between the two operator algebras. -/

/-- Polynomial action of a bounded operator on its underlying linear map. -/
noncomputable def polynomialAction {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℂ] E) (p : Polynomial ℂ) : E →ₗ[ℂ] E :=
  aeval A.toLinearMap p

theorem polynomialAction_apply_eigenvector {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℂ] E) (v : E) (eigenvalue : ℂ)
    (hA : A v = eigenvalue • v) (p : Polynomial ℂ) :
    polynomialAction A p v = p.eval eigenvalue • v := by
  exact polynomial_aeval_apply_eigenvector A.toLinearMap v eigenvalue hA p

/-! ## Finite-dimensional self-adjoint spectral certificates -/

/-- The finite-dimensional assumptions needed by mathlib's self-adjoint
spectral theorem, collected as one reusable proof object. -/
structure FiniteSelfAdjointSpectrumCertificate {𝕜 : Type u} {E : Type v}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) (n : ℕ) : Prop where
  symmetric : T.IsSymmetric
  finrank_eq : Module.finrank 𝕜 E = n

namespace FiniteSelfAdjointSpectrumCertificate

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
  {T : E →ₗ[𝕜] E} {n : ℕ}

noncomputable def eigenvalues
    (h : FiniteSelfAdjointSpectrumCertificate T n) : Fin n → ℝ :=
  h.symmetric.eigenvalues h.finrank_eq

noncomputable def eigenvectorBasis
    (h : FiniteSelfAdjointSpectrumCertificate T n) : OrthonormalBasis (Fin n) 𝕜 E :=
  h.symmetric.eigenvectorBasis h.finrank_eq

theorem eigenvalue_is_real
    (h : FiniteSelfAdjointSpectrumCertificate T n) (i : Fin n) :
    HasEigenvalue T (h.eigenvalues i) := by
  exact h.symmetric.hasEigenvalue_eigenvalues h.finrank_eq i

theorem basis_apply
    (h : FiniteSelfAdjointSpectrumCertificate T n) (i : Fin n) :
    T (h.eigenvectorBasis i) = (h.eigenvalues i : 𝕜) • h.eigenvectorBasis i := by
  exact h.symmetric.apply_eigenvectorBasis h.finrank_eq i

theorem eigenvalues_antitone
    (h : FiniteSelfAdjointSpectrumCertificate T n) :
    Antitone h.eigenvalues := by
  exact h.symmetric.eigenvalues_antitone h.finrank_eq

theorem charpoly_eq
    (h : FiniteSelfAdjointSpectrumCertificate T n) :
    T.charpoly = ∏ i, (Polynomial.X - Polynomial.C (h.eigenvalues i : 𝕜)) := by
  exact h.symmetric.charpoly_eq h.finrank_eq

theorem det_eq_prod_eigenvalues
    (h : FiniteSelfAdjointSpectrumCertificate T n) :
    T.det = ∏ i, (h.eigenvalues i : 𝕜) := by
  exact h.symmetric.det_eq_prod_eigenvalues h.finrank_eq

end FiniteSelfAdjointSpectrumCertificate

/-! A finite interval is a useful physical certificate for a Hamiltonian or a
    covariance operator.  The theorem intentionally only propagates supplied
    pointwise bounds; it does not infer them from samples. -/

structure EigenvalueIntervalCertificate {𝕜 : Type u} {E : Type v}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} {n : ℕ}
    (h : FiniteSelfAdjointSpectrumCertificate T n) (lower upper : ℝ) : Prop where
  lower_le : ∀ i, lower ≤ h.eigenvalues i
  upper_le : ∀ i, h.eigenvalues i ≤ upper

theorem EigenvalueIntervalCertificate.mem_interval
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {T : E →ₗ[𝕜] E} {n : ℕ}
    {h : FiniteSelfAdjointSpectrumCertificate T n} {lower upper : ℝ}
    (bound : EigenvalueIntervalCertificate h lower upper) (i : Fin n) :
    h.eigenvalues i ∈ Set.Icc lower upper :=
  ⟨bound.lower_le i, bound.upper_le i⟩

/-! ## Continuous-to-linear self-adjoint bridge -/

theorem selfAdjoint_to_symmetric {E : Type v} {𝕜 : Type u}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) :
    A.toLinearMap.IsSymmetric :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hA

end LeanPhy.Mathematics
