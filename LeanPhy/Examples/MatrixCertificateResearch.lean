import LeanPhy.Examples.Generated.ComplexHeavyCertificate
import LeanPhy.Quantum.CertifiedResolvent
import LeanPhy.Workflow.Exploration

set_option autoImplicit false

/-! End-to-end certificate consumption by a complex finite Hamiltonian.
The certificate producer is untrusted; exact data inequalities are checked by
Lean, then bound a whole energy disk and feed rectangular block elimination.
Numerical input uncertainty, non-normal matrices and failure cases are covered
by the public interface and generator regressions, not assumed away by labels. -/

namespace LeanPhy.Examples.MatrixCertificateResearch

open LeanPhy.Mathematics LeanPhy.Mathematics.MatrixCertificate
open LeanPhy.Quantum LeanPhy.Workflow LeanPhy.Workflow.Exploration
open LeanPhy.Generated.MatrixCertificates.ComplexHeavy
open scoped Matrix Matrix.Norms.Operator

noncomputable def heavy : Matrix (Fin 2) (Fin 2) ℂ := nominal.realize

noncomputable def coupling : Matrix (Fin 1) (Fin 2) ℂ := !![1, Complex.I]

noncomputable def reverseCoupling : Matrix (Fin 2) (Fin 1) ℂ := couplingᴴ

theorem heavy_hermitian : heavy.IsHermitian := by
  ext i j
  apply Complex.ext <;> fin_cases i <;> fin_cases j <;>
    simp [heavy, nominal, RationalMatrix.realize, Matrix.conjTranspose_apply]

theorem nominal_center : nominal.realize = heavy - (0 : ℂ) • 1 := by simp [heavy]

/-- The exact inverse is constructed from the generated certificate. -/
theorem disk_excluded (z : ℂ) (hz : ‖z‖ ≤ 1) : z ∉ spectrum ℂ heavy := by
  exact CertifiedResolvent.excludes_spectrum nominal candidate accepted heavy 0 nominal_center z
    (by simpa [candidate] using hz)

noncomputable def model (z : ℂ) (hz : ‖z‖ ≤ 1) : EnergyElimination.Model (Fin 1) (Fin 2) :=
  CertifiedResolvent.model nominal candidate accepted heavy 0 nominal_center z
    (by simpa [candidate] using hz) 0 coupling reverseCoupling

theorem actual_equations (z : ℂ) (hz : ‖z‖ ≤ 1) (x : Fin 1 → ℂ) (y : Fin 2 → ℂ) :
    (model z hz).hamiltonian.mulVec (Sum.elim x y) = z • Sum.elim x y ↔
      (model z hz).effectiveHamiltonian.mulVec x = z • x ∧
        y = (model z hz).system.reconstruct x 0 :=
  (model z hz).eigen_equation_iff x y

theorem coupling_bound : ‖coupling‖ ≤ 2 := by
  apply RationalMatrix.norm_le_of_rows _ _ (by norm_num)
  intro i
  fin_cases i
  norm_num [coupling, Fin.sum_univ_two]

theorem reverse_bound : ‖reverseCoupling‖ ≤ 1 := by
  apply RationalMatrix.norm_le_of_rows _ _ (by norm_num)
  intro i
  fin_cases i <;> norm_num [reverseCoupling, coupling, Matrix.conjTranspose_apply]

theorem approximate_effective :
    (0 : Matrix (Fin 1) (Fin 1) ℂ) - coupling * candidate.inverse.realize * reverseCoupling =
      !![-(1 / 2 : ℂ)] := by
  ext i j
  fin_cases i; fin_cases j
  apply Complex.ext <;> norm_num [coupling, reverseCoupling, candidate, RationalMatrix.realize,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem effective_disk_error (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ErrorCertificate (model z hz).effectiveHamiltonian !![-(1 / 2 : ℂ)] (1 / 2) := by
  have h := CertifiedResolvent.effective_error nominal candidate accepted heavy 0 nominal_center
    z (by simpa [candidate] using hz) 0 coupling reverseCoupling
  rw [approximate_effective] at h
  apply h.weaken
  have he : (candidate.errorBound : ℝ) = 1 / 4 := by
    norm_num [Candidate.errorBound, Candidate.normBound, Candidate.totalResidual, candidate]
  rw [he]
  nlinarith [coupling_bound, reverse_bound, norm_nonneg coupling, norm_nonneg reverseCoupling]

/-- A condition branch can now consume the proved finite-data spectral domain. -/
def spectralQuestion : Question ℂ where
  name := "finite heavy resolvent domain"
  revision := "certified-disk-v1"
  statement := "the energy is outside the spectrum of the actual heavy block"
  domainDescription := "the closed complex unit disk"
  source := "CertifiedResolvent.excludes_spectrum / ComplexHeavy.accepted"
  domain := fun z => ‖z‖ ≤ 1
  target := fun z => z ∉ spectrum ℂ heavy

theorem spectral_answer : spectralQuestion.Answer := disk_excluded

def package : TheoryPackage :=
  (Notebook.start spectralQuestion).complete "certified effective Hamiltonian" "finite complex spectral domain"
    spectral_answer
  |>.addTheorem "rational data checked" "exact row inequalities pass the Lean checker"
      "Generated.MatrixCertificates.ComplexHeavy.accepted" accepted
  |>.addTheorem "certificate soundness" "all matrices in the declared norm ball have a bounded inverse"
      "MatrixCertificate.sound" valid
  |>.addTheorem "Hermitian physical block" "the certificate indexes the declared Hermitian heavy block"
      "MatrixCertificateResearch.heavy_hermitian" heavy_hermitian
  |>.addTheorem "full reduced equation equivalence" "constructed resolvents feed actual block eigen equations"
      "EnergyElimination.Model.eigen_equation_iff" actual_equations
  |>.addTheorem "effective Hamiltonian error" "uniform effective-operator error on the closed unit energy disk"
      "CertifiedResolvent.effective_error" effective_disk_error
  |>.addTheorem "heavy source error" "heavy-source insertions retain their certified approximation error"
      "CertifiedElimination.source_error" (@CertifiedElimination.source_error 1 2)
  |>.addTheorem "effective probe error" "rectangular linear probes are transformed with the same certificate"
      "CertifiedElimination.readout_error" (@CertifiedElimination.readout_error 1 2 1)
  |>.addTheorem "heavy reconstruction error" "heavy reconstruction retains sources and configuration dependence"
      "CertifiedElimination.reconstruction_error" (@CertifiedElimination.reconstruction_error 1 2)
  |>.addObligationText "physical model enclosure"
      "derive the numerical or analytic enclosure for a new measured or continuum model"
      "a rational nominal matrix alone does not supply this premise"
  |>.addObligationText "unitary low-energy dynamics"
      "derive a controlled energy-independent unitary reduction and its dynamical observables"
      "energy-dependent exact block elimination is available"
  |>.addObligationText "large-system and continuum validity"
      "verify sparse scaling, infinite-volume limits and unbounded-operator domains for the target model"
      "this client uses finite dense matrices"

end LeanPhy.Examples.MatrixCertificateResearch
