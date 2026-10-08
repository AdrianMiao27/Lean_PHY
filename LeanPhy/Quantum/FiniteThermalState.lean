import LeanPhy.Quantum.FiniteDensity
import LeanPhy.Quantum.HamiltonianFlow
import LeanPhy.StatMech.GibbsResponse
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false

/-!
# Finite thermal states and the classical/quantum expectation bridge

A real finite probability is an actual positive, trace-one matrix in a chosen
basis. Gibbs probabilities give `exp(-β H) / Tr(exp(-β H))`, proved using the
matrix exponential. Unitary basis changes transport the state and observables
together. The spectral theorem then constructs the thermal density for every
finite Hermitian Hamiltonian, including degenerate spectra.

Parameter-response theorems below hold in a fixed common basis for energy and
probe. They do not differentiate parameter-dependent eigenvectors or assert a
classical covariance formula for noncommuting perturbations. All energies use
dimensionless `β E`; no thermodynamic or continuum limit is taken.
-/

namespace LeanPhy.Quantum

open LeanPhy.StatMech
open scoped BigOperators Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real observable in the specified finite basis. -/
noncomputable def realDiagonal (O : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => (O i : ℂ))

omit [Fintype ι] in
theorem realDiagonal_isHermitian (O : ι → ℝ) : (realDiagonal O).IsHermitian := by
  rw [realDiagonal, Matrix.isHermitian_diagonal_iff]
  intro i
  rw [isSelfAdjoint_iff]
  simp

/-- The probability weights themselves supply positivity and normalization. -/
noncomputable def diagonalDensity (p : FiniteProbability ι) : FiniteDensity ι where
  rho := realDiagonal p.weight
  valid := by
    refine ⟨realDiagonal_isHermitian _, Matrix.PosSemidef.diagonal (fun i => ?_), ?_⟩
    · exact Complex.nonneg_iff.mpr ⟨p.nonneg i, by simp⟩
    · simp [realDiagonal, Matrix.trace_diagonal, ← Complex.ofReal_sum, p.normalised]

/-- For an arbitrary matrix probe, a diagonal state reads its diagonal entries. -/
theorem diagonalDensity_trace_mul (p : FiniteProbability ι) (O : Matrix ι ι ℂ) :
    Matrix.trace ((diagonalDensity p).rho * O) = ∑ i, (p.weight i : ℂ) * O i i := by
  simp [diagonalDensity, realDiagonal, Matrix.trace, Matrix.diagonal_mul]

@[simp] theorem diagonalDensity_expectation (p : FiniteProbability ι) (O : ι → ℝ) :
    Matrix.trace ((diagonalDensity p).rho * realDiagonal O) = (p.expectation O : ℂ) := by
  rw [diagonalDensity_trace_mul]
  simp [realDiagonal, FiniteProbability.expectation, Complex.ofReal_sum]

theorem diagonalDensity_connected (p : FiniteProbability ι) (O A : ι → ℝ) :
    Matrix.trace ((diagonalDensity p).rho * (realDiagonal O * realDiagonal A)) -
      Matrix.trace ((diagonalDensity p).rho * realDiagonal O) *
        Matrix.trace ((diagonalDensity p).rho * realDiagonal A) = (p.covariance O A : ℂ) := by
  have h : realDiagonal O * realDiagonal A = realDiagonal (fun i => O i * A i) := by
    simp [realDiagonal, Matrix.diagonal_mul_diagonal, Complex.ofReal_mul]
  rw [h, diagonalDensity_expectation, diagonalDensity_expectation, diagonalDensity_expectation]
  simp [FiniteProbability.covariance]

theorem FiniteUnitary.conjugate_mul (U : FiniteUnitary ι) (A B : Matrix ι ι ℂ) :
    U.conjugate A * U.conjugate B = U.conjugate (A * B) := by
  unfold FiniteUnitary.conjugate
  calc
    _ = U.op * A * (U.opᴴ * U.op) * B * U.opᴴ := by noncomm_ring
    _ = _ := by rw [U.unitary]; simp [Matrix.mul_assoc]

theorem FiniteUnitary.conjugate_smul (U : FiniteUnitary ι) (c : ℂ) (A : Matrix ι ι ℂ) :
    U.conjugate (c • A) = c • U.conjugate A := by
  simp [FiniteUnitary.conjugate]

theorem FiniteUnitary.conjugate_isHermitian (U : FiniteUnitary ι) (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) : (U.conjugate H).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose U.op hH

/-- Changing both state and probe preserves their trace pairing. -/
theorem FiniteUnitary.conjugate_expectation (U : FiniteUnitary ι) (rho O : Matrix ι ι ℂ) :
    Matrix.trace (U.conjugate rho * U.conjugate O) = Matrix.trace (rho * O) := by
  rw [U.conjugate_mul, U.conjugate_trace]

theorem FiniteUnitary.exp_conjugate (U : FiniteUnitary ι) (A : Matrix ι ι ℂ) :
    NormedSpace.exp (U.conjugate A) = U.conjugate (NormedSpace.exp A) := by
  let u : (Matrix ι ι ℂ)ˣ := ⟨U.op, U.opᴴ, U.right_unitary, U.unitary⟩
  exact Matrix.exp_units_conj u A

theorem exp_realDiagonal (β : ℝ) (E : ι → ℝ) :
    NormedSpace.exp ((-β : ℂ) • realDiagonal E) =
      realDiagonal (fun i => Real.exp (-β * E i)) := by
  rw [realDiagonal, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext i
  simp [Complex.ofReal_exp, Complex.ofReal_mul, Complex.exp_eq_exp_ℂ]

variable [Nonempty ι]

noncomputable def thermalStateInBasis (U : FiniteUnitary ι) (β : ℝ) (E : ι → ℝ) :
    FiniteDensity ι := U.evolveDensity (diagonalDensity (finiteGibbsProbability β E))

/-- Exact operator exponential in a supplied energy basis; no spectral gap is required. -/
theorem thermalStateInBasis_eq_exp (U : FiniteUnitary ι) (β : ℝ) (E : ι → ℝ) :
    (thermalStateInBasis U β E).rho = (finitePartitionFunction β E : ℂ)⁻¹ •
      NormedSpace.exp ((-β : ℂ) • U.conjugate (realDiagonal E)) := by
  rw [← U.conjugate_smul, U.exp_conjugate, exp_realDiagonal, ← U.conjugate_smul]
  apply congrArg U.conjugate
  ext i j
  simp [diagonalDensity, realDiagonal, finiteGibbsProbability, finiteGibbsWeight,
    Matrix.diagonal, div_eq_mul_inv, mul_comm]

omit [Nonempty ι] in
theorem thermalStateInBasis_partition (U : FiniteUnitary ι) (β : ℝ) (E : ι → ℝ) :
    Matrix.trace (NormedSpace.exp ((-β : ℂ) • U.conjugate (realDiagonal E))) =
      (finitePartitionFunction β E : ℂ) := by
  rw [← U.conjugate_smul, U.exp_conjugate, U.conjugate_trace, exp_realDiagonal]
  simp [realDiagonal, Matrix.trace_diagonal, finitePartitionFunction, Complex.ofReal_sum]

@[simp] theorem thermalStateInBasis_expectation (U : FiniteUnitary ι)
    (β : ℝ) (E O : ι → ℝ) :
    Matrix.trace ((thermalStateInBasis U β E).rho * U.conjugate (realDiagonal O)) =
      ((finiteGibbsProbability β E).expectation O : ℂ) := by
  rw [thermalStateInBasis, FiniteUnitary.evolveDensity_rho,
    U.conjugate_expectation, diagonalDensity_expectation]

theorem thermalStateInBasis_connected (U : FiniteUnitary ι) (β : ℝ) (E O A : ι → ℝ) :
    Matrix.trace ((thermalStateInBasis U β E).rho *
      (U.conjugate (realDiagonal O) * U.conjugate (realDiagonal A))) -
      Matrix.trace ((thermalStateInBasis U β E).rho * U.conjugate (realDiagonal O)) *
        Matrix.trace ((thermalStateInBasis U β E).rho * U.conjugate (realDiagonal A)) =
      ((finiteGibbsProbability β E).covariance O A : ℂ) := by
  change Matrix.trace (U.conjugate _ * (U.conjugate _ * U.conjugate _)) -
    Matrix.trace (U.conjugate _ * U.conjugate _) *
      Matrix.trace (U.conjugate _ * U.conjugate _) = _
  rw [U.conjugate_mul]
  simp only [U.conjugate_expectation]
  exact diagonalDensity_connected _ O A

/-- A fixed-basis energy source has the physical β factor in its trace response. -/
theorem hasDerivAt_thermalStateInBasis_energySource (U : FiniteUnitary ι)
    (β : ℝ) (E A O : ι → ℝ) (h : ℝ) :
    HasDerivAt (fun s => (Matrix.trace
      ((thermalStateInBasis U β (fun i => E i - s * A i)).rho *
        U.conjugate (realDiagonal O))).re)
      (β * (finiteGibbsProbability β (fun i => E i - h * A i)).covariance O A) h := by
  simp only [thermalStateInBasis_expectation, Complex.ofReal_re]
  exact hasDerivAt_finiteGibbs_energySource β E A O h

/-- The basis is fixed: a moving energy and moving diagonal probe retain the
explicit derivative of the probe and the thermal covariance term. -/
theorem hasDerivAt_thermalStateInBasis_parameter (U : FiniteUnitary ι) (β : ℝ)
    (E O : ℝ → ι → ℝ) (E' O' : ι → ℝ) (t : ℝ)
    (hE : ∀ i, HasDerivAt (fun s => E s i) (E' i) t)
    (hO : ∀ i, HasDerivAt (fun s => O s i) (O' i) t) :
    HasDerivAt (fun s => (Matrix.trace ((thermalStateInBasis U β (E s)).rho *
      U.conjugate (realDiagonal (O s)))).re)
      ((finiteGibbsProbability β (E t)).expectation O' -
        β * (finiteGibbsProbability β (E t)).covariance (O t) E') t := by
  simp only [thermalStateInBasis_expectation, Complex.ofReal_re]
  exact hasDerivAt_finiteGibbs_parameter β E O E' O' t hE hO

theorem thermalStateInBasis_conserved (U : FiniteUnitary ι) (β : ℝ) (E : ι → ℝ) :
    Conserved (U.conjugate (realDiagonal E)) (thermalStateInBasis U β E).rho := by
  apply sub_eq_zero.mpr
  change U.conjugate (realDiagonal E) * U.conjugate (realDiagonal _) =
    U.conjugate (realDiagonal _) * U.conjugate (realDiagonal E)
  rw [U.conjugate_mul, U.conjugate_mul]
  apply congrArg U.conjugate
  simp [realDiagonal, Matrix.diagonal_mul_diagonal, mul_comm]

/-- Adapt mathlib's actual spectral basis to the common unitary API. -/
noncomputable def hermitianEnergyBasis (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    FiniteUnitary ι where
  op := hH.eigenvectorUnitary
  unitary := Unitary.coe_star_mul_self hH.eigenvectorUnitary

omit [Nonempty ι] in
theorem hermitianEnergyBasis_diagonalizes (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (hermitianEnergyBasis H hH).conjugate (realDiagonal hH.eigenvalues) = H := by
  exact hH.spectral_theorem.symm

/-- A Gibbs density for every finite Hermitian Hamiltonian. Spectral positivity
and normalization are inherited from the finite Gibbs probability. -/
noncomputable def finiteThermalState (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (β : ℝ) : FiniteDensity ι :=
  thermalStateInBasis (hermitianEnergyBasis H hH) β hH.eigenvalues

theorem finiteThermalState_partition (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) :
    Matrix.trace (NormedSpace.exp ((-β : ℂ) • H)) =
      (finitePartitionFunction β hH.eigenvalues : ℂ) := by
  simpa only [hermitianEnergyBasis_diagonalizes] using
    thermalStateInBasis_partition (hermitianEnergyBasis H hH) β hH.eigenvalues

theorem finiteThermalState_partition_pos (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) :
    0 < (Matrix.trace (NormedSpace.exp ((-β : ℂ) • H))).re := by
  rw [finiteThermalState_partition, Complex.ofReal_re]
  exact finitePartitionFunction_pos β hH.eigenvalues

/-- The spectral construction agrees with the basis-independent operator formula. -/
theorem finiteThermalState_eq_exp (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) :
    (finiteThermalState H hH β).rho =
      (Matrix.trace (NormedSpace.exp ((-β : ℂ) • H)))⁻¹ •
        NormedSpace.exp ((-β : ℂ) • H) := by
  rw [finiteThermalState_partition]
  simpa only [finiteThermalState, hermitianEnergyBasis_diagonalizes] using
    thermalStateInBasis_eq_exp (hermitianEnergyBasis H hH) β hH.eigenvalues

/-- A supplied diagonalization yields the same density as the spectral construction. -/
theorem thermalStateInBasis_eq_finiteThermalState (U : FiniteUnitary ι)
    (β : ℝ) (E : ι → ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (hdiag : U.conjugate (realDiagonal E) = H) :
    (thermalStateInBasis U β E).rho = (finiteThermalState H hH β).rho := by
  rw [finiteThermalState_eq_exp, thermalStateInBasis_eq_exp, ← hdiag,
    thermalStateInBasis_partition]

/-- A unitary change of basis preserves the operator thermal construction. -/
theorem finiteThermalState_conjugate (U : FiniteUnitary ι) (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (β : ℝ) :
    (finiteThermalState (U.conjugate H)
      (U.conjugate_isHermitian H hH) β).rho =
      U.conjugate (finiteThermalState H hH β).rho := by
  rw [finiteThermalState_eq_exp, finiteThermalState_eq_exp,
    ← U.conjugate_smul, U.exp_conjugate, U.conjugate_trace, U.conjugate_smul]

theorem finiteThermalState_energy (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) :
    Matrix.trace ((finiteThermalState H hH β).rho * H) =
      ((finiteGibbsProbability β hH.eigenvalues).expectation hH.eigenvalues : ℂ) := by
  simpa only [finiteThermalState, hermitianEnergyBasis_diagonalizes] using
    thermalStateInBasis_expectation (hermitianEnergyBasis H hH) β hH.eigenvalues hH.eigenvalues

/-- Energy-temperature fluctuation identity for an arbitrary finite Hermitian
Hamiltonian. Its eigenbasis is fixed as β varies, including at degeneracies. -/
theorem hasDerivAt_finiteThermalState_energy_beta
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) :
    HasDerivAt (fun b => (Matrix.trace ((finiteThermalState H hH b).rho * H)).re)
      (-(finiteGibbsProbability β hH.eigenvalues).variance hH.eigenvalues) β := by
  simp only [finiteThermalState_energy, Complex.ofReal_re]
  exact hasDerivAt_finiteGibbs_beta hH.eigenvalues hH.eigenvalues β

theorem hasDerivAt_finiteThermalState_energy_temperature
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (T : ℝ) (hT : T ≠ 0) :
    HasDerivAt (fun t => (Matrix.trace ((finiteThermalState H hH t⁻¹).rho * H)).re)
      ((finiteGibbsProbability T⁻¹ hH.eigenvalues).variance hH.eigenvalues / T ^ 2) T := by
  simp only [finiteThermalState_energy, Complex.ofReal_re]
  exact hasDerivAt_finiteGibbs_temperature hH.eigenvalues T hT

theorem finiteThermalState_conserved (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) :
    Conserved H (finiteThermalState H hH β).rho := by
  simpa only [finiteThermalState, hermitianEnergyBasis_diagonalizes] using
    thermalStateInBasis_conserved (hermitianEnergyBasis H hH) β hH.eigenvalues

/-- Thermal states are stationary under the existing matrix-exponential flow. -/
theorem finiteThermalState_stationary (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β t : ℝ) :
    (finiteHamiltonianFlow H hH t).conjugate (finiteThermalState H hH β).rho =
      (finiteThermalState H hH β).rho :=
  finiteHamiltonianFlow_conjugate_of_conserved H hH t _ (finiteThermalState_conserved H hH β)

end LeanPhy.Quantum
