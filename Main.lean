import LeanPhy

/-!
# LeanPhy smoke test

This is the executable acceptance test for the physics-oriented layer.  Every
statement below is checked by the Lean kernel against mathlib; nothing here is
sorry-ed or axiomatized.  Running lake build therefore doubles as a
kernel-checked regression test for the algebraic core.
-/

open LeanPhy
open LeanPhy.Mathematics
open LeanPhy.Mathematics.Hilbert
open LeanPhy.Quantum
open LeanPhy.FieldTheory
open LeanPhy.IndexCalculus
open LeanPhy.Examples
open LeanPhy.Einstein
open LeanPhy.HighEnergy
open LeanPhy.FieldTheory.Pairing
open LeanPhy.QuantumInfo
open LeanPhy.Workflow
open LeanPhy.GaugeTheory
open LeanPhy.StatMech
open Filter
open Function
open MeasureTheory
open Polynomial
open scoped LeanPhy.Quantum
open scoped LeanPhy.Dirac
open scoped Interval
open scoped Matrix
open scoped ComplexOrder
open scoped Topology

/-! ## Continuous-analysis certificates

These are genuine Filter, Bochner-integral and tsum statements.  The
certificates are compositional proof records; they do not assert convergence
or integrability without the corresponding mathlib witness.
-/

example : LimitCertificate (𝓝 (0 : ℝ)) (fun _ : ℝ => (1 : ℝ)) 1 := by
  exact LimitCertificate.of_tendsto tendsto_const_nhds

example (μ : MeasureTheory.Measure ℝ) :
    IntegralCertificate μ (fun _ : ℝ => (0 : ℝ)) 0 := by
  exact IntegralCertificate.of_integral
    (MeasureTheory.integrable_zero ℝ ℝ μ) (by simp)

example : SeriesCertificate (fun _ : ℕ => (0 : ℝ)) 0 := by
  exact SeriesCertificate.of_summable summable_zero (by simp)

/-! ## Continuous path-integral certificates

The measure, integrability of the weight and non-zero partition function are
all explicit.  This is a finite-measure smoke test for the continuum-facing
API; it does not claim existence of an infinite-dimensional path measure.
-/

example : ContinuousPathIntegral (Unit) (MeasureTheory.Measure.dirac ()) := by
  refine {
    weight := fun _ => (1 : ℂ)
    weight_integrable := ?_
    partition := 1
    partition_eq := ?_
    partition_ne_zero := one_ne_zero
  }
  · simpa using (MeasureTheory.integrable_const (μ := MeasureTheory.Measure.dirac ())
      (c := (1 : ℂ)))
  · simp

example (P : ContinuousPathIntegral (Unit) (MeasureTheory.Measure.dirac ())) (c : ℂ) :
    P.expectation (fun _ => c) = c :=
  ContinuousPathIntegral.expectation_const P c

/-! ## Weak Hilbert-space PDE interface

The public analysis profile includes a direct Lax--Milgram adapter.  The
one-dimensional multiplication form is a concrete regression: it checks
coercivity, the weak variational identity, uniqueness and the homogeneous
zero-solution result through the same API used for elliptic forms on
infinite-dimensional spaces.
-/

noncomputable section WeakPDESmoke

abbrev scalarB : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ

def scalarLaxMilgram : LaxMilgramCertificate scalarB :=
  { coercive := by
      refine ⟨1, zero_lt_one, ?_⟩
      intro u
      simp [scalarB, Real.norm_eq_abs] }

example (f w : ℝ) :
    scalarB (scalarLaxMilgram.solution f) w = inner ℝ f w :=
  scalarLaxMilgram.solution_spec f w

example (f : ℝ) : scalarLaxMilgram.solution f = f := by
  apply (scalarLaxMilgram.solution_unique f f ?_).symm
  intro w
  simp [scalarB]
  exact mul_comm _ _

example {u : ℝ} (hu : ∀ w, scalarB u w = 0) : u = 0 :=
  scalarLaxMilgram.homogeneous_unique hu

end WeakPDESmoke

/-! ## Contraction and fixed-point certificates

The same analytic interface covers Picard iteration, dissipative evolution,
finite RG maps and stable nonlinear closures.  The smoke model is deliberately
small, but the certificate is stated for arbitrary complete metric spaces.
-/

noncomputable section ContractionSmoke

def halfMap : ℝ → ℝ := fun x => (1 / 2 : ℝ) * x

def halfMapCertificate : ContractionCertificate halfMap (1 / 2 : NNReal) := by
  refine ⟨by norm_num, ?_⟩
  unfold halfMap
  simpa [div_eq_mul_inv] using
    (lipschitzWith_smul (α := ℝ) (β := ℝ) (1 / 2 : ℝ))

def shiftedHalfMap : ℝ → ℝ := fun x => (1 / 2 : ℝ) * x + 1

def shiftedHalfMapCertificate : ContractionCertificate shiftedHalfMap (1 / 2 : NNReal) := by
  refine ⟨by norm_num, ?_⟩
  unfold shiftedHalfMap
  simpa [div_eq_mul_inv] using
    (lipschitzWith_smul (α := ℝ) (β := ℝ) (1 / 2 : ℝ)).add
      (LipschitzWith.const 1)

example : IsFixedPt halfMap halfMapCertificate.fixedPoint :=
  halfMapCertificate.fixedPoint_isFixedPt

example (x : ℝ) (n : ℕ) :
    dist (halfMap^[n] x) halfMapCertificate.fixedPoint ≤
      dist x (halfMap x) * ((1 / 2 : NNReal) : ℝ) ^ n /
        (1 - ((1 / 2 : NNReal) : ℝ)) :=
  halfMapCertificate.iterate_error_apriori x n

example :
    dist halfMapCertificate.fixedPoint shiftedHalfMapCertificate.fixedPoint ≤
      (1 : ℝ) / (1 - ((1 / 2 : NNReal) : ℝ)) := by
  apply halfMapCertificate.fixedPoint_stable_under_map_error
    shiftedHalfMapCertificate
  intro z
  simp [halfMap, shiftedHalfMap, dist_eq_norm]

end ContractionSmoke

/-! ## Bounded Hilbert-flow norm envelopes

The flow interface retains the semigroup law while a separate certificate
supplies the stability estimate needed by evolution and response arguments.
-/

namespace HilbertFlowBoundSmoke

noncomputable section

def identityFlow : Hilbert.Flow (𝕜 := ℂ) (E := ℂ) where
  op := fun _ => 1
  zero := rfl
  add := by intro t s; rfl

def identityFlowBound : FlowNormCertificate identityFlow (fun _ => (1 : ℝ)) where
  nonneg := by intro t; norm_num
  op_le := by
    intro t
    change ‖ContinuousLinearMap.id ℂ ℂ‖ ≤ 1
    rw [ContinuousLinearMap.norm_id]

example (t : ℝ) (x : ℂ) :
    ‖identityFlow.evolve t x‖ ≤ (1 : ℝ) * ‖x‖ :=
  identityFlowBound.evolve_norm_le t x

example (t s : ℝ) :
    ‖identityFlow.op (t + s)‖ ≤ (1 : ℝ) * 1 :=
  identityFlowBound.op_add_le t s

end

end HilbertFlowBoundSmoke

/-! ## Continuous-time Duhamel certificates

The endpoint identity is supplied by the modeler and the kernel checks its
interval integrability.  The norm theorem then propagates a certified source
majorant through the flow envelope; it does not construct a solution of an
ODE/PDE from a generator. -/

namespace ContinuousEvolutionSmoke

noncomputable section

def constantDuhamel (x c : ℂ) : VariationOfConstantsCertificate
    HilbertFlowBoundSmoke.identityFlow (fun _ => c)
      (fun t => x + (t : ℂ) * c) x := by
  refine { forcing_integrable := ?_, endpoint_eq := ?_ }
  · intro t
    simpa [HilbertFlowBoundSmoke.identityFlow] using
      (intervalIntegrable_const (a := (0 : ℝ)) (b := t) (c := c))
  · intro t
    simp [HilbertFlowBoundSmoke.identityFlow, Hilbert.Flow.evolve,
      intervalIntegral.integral_const]

def constantSourceBound (c : ℂ) : SourceNormCertificate (fun _ : ℝ => c)
    (fun _ => ‖c‖) := by
  refine { nonneg := ?_, pointwise := ?_ }
  · intro t
    exact norm_nonneg _
  · intro t
    simp

example (x c : ℂ) : (fun t => x + (t : ℂ) * c) 0 = x :=
  (constantDuhamel x c).initial

example (x c : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    ‖(x + (t : ℂ) * c) - HilbertFlowBoundSmoke.identityFlow.evolve t x‖ ≤
      ∫ s in (0 : ℝ)..t, (1 : ℝ) * ‖c‖ := by
  apply VariationOfConstantsCertificate.norm_error_le (constantDuhamel x c)
    HilbertFlowBoundSmoke.identityFlowBound (constantSourceBound c)
  intro t ht
  simpa using (intervalIntegrable_const (a := (0 : ℝ)) (b := t) (c := ‖c‖))
  exact ht

end

end ContinuousEvolutionSmoke

/-! The Neumann criterion is a real bounded-operator spectral smoke test. -/

example (A : ℂ →L[ℂ] ℂ) (hA : ‖A‖ < 1) :
    ResolventCertificate A 1 :=
  resolvent_of_neumann A hA

example (P : ContinuousPathIntegral (Unit) (MeasureTheory.Measure.dirac ()))
    (O Q : Unit → ℂ)
    (hO : MeasureTheory.Integrable (fun x => P.weight x * O x)
      (MeasureTheory.Measure.dirac ()))
    (hQ : MeasureTheory.Integrable (fun x => P.weight x * Q x)
      (MeasureTheory.Measure.dirac ())) :
    P.expectation (fun x => O x + Q x) = P.expectation O + P.expectation Q :=
  ContinuousPathIntegral.expectation_add P O Q hO hQ

/-! ## Dominated-convergence and regulated expectation limits

The following finite-measure regression is deliberately written through the
generic certificates.  It checks the same proof path used by a truncation or
regulator: both the weight and the inserted observable need domination, and
the limiting partition must be nonzero.
-/

namespace DominatedConvergenceSmoke

noncomputable section

abbrev μ : MeasureTheory.Measure Unit := MeasureTheory.Measure.dirac ()
def ws : ℕ → Unit → ℂ := fun _ _ => 1
def wl : Unit → ℂ := fun _ => 1
def O : Unit → ℂ := fun _ => 1

theorem weightDct : DominatedConvergenceCertificate μ ws wl (fun _ : Unit => (1 : ℝ)) := by
  refine { measurable := ?_, bound_integrable := ?_, dominated := ?_, pointwise_limit := ?_ }
  · intro n
    exact measurable_const.aestronglyMeasurable
  · simpa using (MeasureTheory.integrable_const (μ := μ) (1 : ℝ))
  · intro n
    filter_upwards [] with a
    simp [ws]
  · filter_upwards [] with a
    exact tendsto_const_nhds

theorem insertionDct :
    DominatedConvergenceCertificate μ (fun n a => ws n a * O a)
      (fun a => wl a * O a) (fun _ : Unit => (1 : ℝ)) := by
  refine { measurable := ?_, bound_integrable := ?_, dominated := ?_, pointwise_limit := ?_ }
  · intro n
    simpa [ws, O] using
      (measurable_const : Measurable (fun _ : Unit => (1 : ℂ))).aestronglyMeasurable
  · simpa using (MeasureTheory.integrable_const (μ := μ) (1 : ℝ))
  · intro n
    filter_upwards [] with a
    simp [ws, O]
  · filter_upwards [] with a
    simpa [ws, wl, O] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1))

theorem normalized :
    NormalizedObservableConvergenceCertificate μ ws wl O
      (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => (1 : ℝ)) := by
  refine { weight_certificate := weightDct, insertion_certificate := insertionDct, partition_limit_ne_zero := ?_ }
  simp [μ, wl]

example :
    Tendsto (fun n => (∫ a, ws n a * O a ∂μ) / (∫ a, ws n a ∂μ)) atTop
      (𝓝 ((∫ a, wl a * O a ∂μ) / (∫ a, wl a ∂μ))) :=
  normalized.expectation_tendsto

end
end DominatedConvergenceSmoke

/-! ## Infinite-dimensional Hilbert-space bridges

The theorem is stated for arbitrary complete inner-product spaces.  The smoke
case uses the identity on `ℂ` only to keep the regression executable; no finite
matrix representation is used by the certificate itself.
-/

example : MeanErgodicCertificate (1 : ℂ →L[ℂ] ℂ) := by
  refine ⟨?_⟩
  simp

example (x : ℂ) :
    Tendsto
      (fun n => MeanErgodicCertificate.average (1 : ℂ →L[ℂ] ℂ) n x) atTop
      (𝓝 (↑(((1 : ℂ →L[ℂ] ℂ).eqLocus (1 : ℂ →L[ℂ] ℂ)).orthogonalProjectionOnto x) : ℂ)) := by
  have h : MeanErgodicCertificate (1 : ℂ →L[ℂ] ℂ) := by
    refine ⟨?_⟩
    simp
  simpa using h.average_tendsto_projection x

example (x : ℂ) :
    Tendsto
      (fun n => (1 : ℂ →L[ℂ] ℂ)
        (MeanErgodicCertificate.average (1 : ℂ →L[ℂ] ℂ) n x)) atTop
      (𝓝 ((1 : ℂ →L[ℂ] ℂ)
        (↑(((1 : ℂ →L[ℂ] ℂ).eqLocus (1 : ℂ →L[ℂ] ℂ)).orthogonalProjectionOnto x) : ℂ))) := by
  have h : MeanErgodicCertificate (1 : ℂ →L[ℂ] ℂ) := by
    refine ⟨?_⟩
    simp
  exact h.observable_tendsto_projection (1 : ℂ →L[ℂ] ℂ) x

example :
    Tendsto (fun n : ℕ => ENNReal.ofReal
      (‖(1 : ℂ) ^ n‖ ^ (1 / (n : ℝ)))) atTop
      (𝓝 (spectralRadius ℂ (1 : ℂ))) := by
  exact spectral_radius_power_limit (1 : ℂ)

/-! ## Bounded-operator spectral certificates

The spectrum bridge uses actual continuous linear maps and checked inverse
equations.  It does not promote an unbounded operator or a numerical bound to
an analytic spectral theorem.
-/

example (A : ℂ →L[ℂ] ℂ) (z : ℂ)
    (h : ResolventCertificate A z) : z ∉ spectrum ℂ A :=
  ResolventCertificate.not_mem h

example : ResolventCertificate (0 : ℂ →L[ℂ] ℂ) 1 := by
  apply resolvent_of_norm_bound
  simp

example (A : ℂ →L[ℂ] ℂ) : IsClosed (spectrum ℂ A) :=
  spectrum_closed A

def scalarZeroResolvent : ResolventCertificate (0 : ℂ →L[ℂ] ℂ) 2 := by
  refine ⟨(1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ), ?_, ?_⟩ <;>
    ext x <;> simp [Algebra.algebraMap_eq_smul_one]

def scalarIdentityResolvent : ResolventCertificate (1 : ℂ →L[ℂ] ℂ) 2 := by
  refine ⟨(1 : ℂ →L[ℂ] ℂ), ?_, ?_⟩ <;>
    ext x <;> simp [Algebra.algebraMap_eq_smul_one] <;> norm_num

example :
    scalarZeroResolvent.inverse - scalarIdentityResolvent.inverse =
      scalarZeroResolvent.inverse *
        ((0 : ℂ →L[ℂ] ℂ) - (1 : ℂ →L[ℂ] ℂ)) *
        scalarIdentityResolvent.inverse :=
  resolvent_identity scalarZeroResolvent scalarIdentityResolvent

theorem scalarZeroResolvent_inverse :
    scalarZeroResolvent.inverse =
      (1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
  apply ResolventCertificate.inverse_eq_of_spec scalarZeroResolvent
  · ext x
    simp [Algebra.algebraMap_eq_smul_one]
  · ext x
    simp [Algebra.algebraMap_eq_smul_one]

theorem scalarIdentityResolvent_inverse :
    scalarIdentityResolvent.inverse = (1 : ℂ →L[ℂ] ℂ) := by
  apply ResolventCertificate.inverse_eq_of_spec scalarIdentityResolvent
  · ext x
    simp [Algebra.algebraMap_eq_smul_one]
    norm_num
  · ext x
    simp [Algebra.algebraMap_eq_smul_one]
    norm_num

example :
    ‖scalarZeroResolvent.inverse - scalarIdentityResolvent.inverse‖ ≤
      (1 / 2 : ℝ) * 1 * 1 := by
  apply resolvent_perturbation_bound scalarZeroResolvent scalarIdentityResolvent
  · rw [scalarZeroResolvent_inverse]
    norm_num
  · rw [scalarIdentityResolvent_inverse]
    norm_num
  · norm_num [scalarZeroResolvent, scalarIdentityResolvent,
      Algebra.algebraMap_eq_smul_one]

/-! ## Rayleigh and positivity certificates

These examples exercise the reusable bounded-Hilbert interface rather than a
single physics model.  The identity operator is a minimal regression for
Rayleigh intervals, norm bounds and the complex positive-spectrum bridge.
-/

example : RayleighIntervalCertificate (1 : ℂ →L[ℂ] ℂ) 1 1 := by
  refine ⟨IsSelfAdjoint.one _, ?_, ?_⟩
  · intro x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    simp only [one_apply_eq_self]
    rw [inner_self_eq_norm_sq]
    simp
  · intro x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    simp only [one_apply_eq_self]
    rw [inner_self_eq_norm_sq]
    simp

example : ‖(1 : ℂ →L[ℂ] ℂ)‖ ≤ (1 : ℝ) := by
  have h : RayleighIntervalCertificate (1 : ℂ →L[ℂ] ℂ) 1 1 := by
    refine ⟨IsSelfAdjoint.one _, ?_, ?_⟩
    · intro x
      rw [ContinuousLinearMap.reApplyInnerSelf_apply]
      simp only [one_apply_eq_self]
      rw [inner_self_eq_norm_sq]
      simp
    · intro x
      rw [ContinuousLinearMap.reApplyInnerSelf_apply]
      simp only [one_apply_eq_self]
      rw [inner_self_eq_norm_sq]
      simp
  simpa using h.norm_le

example : SpectrumRestricts (1 : ℂ →L[ℂ] ℂ) ContinuousMap.realToNNReal := by
  apply PositiveOperatorCertificate.spectrumRestricts_complex
  refine ⟨IsSelfAdjoint.one _, ?_⟩
  intro x
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  simp only [one_apply_eq_self]
  rw [inner_self_eq_norm_sq]
  simp

/-! ## Physics-facing tactics -/

-- commutator_nf: expand a commutator and close the ring identity
example {A : Type} [Ring A] (x y z : A) : commutator (x + y) z = commutator x z + commutator y z := by
  commutator_nf

-- dirac_unfold + a core lemma
example : (⟨(|0⟩ : Ket 2)|(|1⟩ : Ket 2)⟩ : ℂ) = 0 := by
  dirac_unfold
  simp [basisKet_orthonormal]

-- index_unfold
example (i j : Fin 3) : delta i j = if i = j then 1 else 0 := by
  index_unfold


/-! ## Dimensions: adding mismatched dimensions is a type error -/

-- dimension-respecting addition typechecks and the values add ...
example (x y : Length) : Length := x + y
example (x y : Length) : (x + y).val = x.val + y.val := rfl

-- Quotients, inverse powers and powers carry their derived SI exponents in the
-- result type.  These are common side conditions in mechanics, QFT and
-- condensed matter, so the bookkeeping is checked before algebraic tactics.
example (x : Length) (t : TimeQ) :
    (x / t : Quantity ({ length := 1, time := -1 } : Dimension) ℂ).val =
      x.val / t.val := rfl
example (x : Length) :
    (Quantity.inverse x : Quantity ({ length := -1 } : Dimension) ℂ).val =
      x.val⁻¹ := rfl
example (x : Length) :
    (Quantity.pow x 2 : Quantity ({ length := 2 } : Dimension) ℂ).val =
      x.val ^ 2 := rfl
example (p : Momentum) (v : Velocity) :
    (p * v : Quantity ({ length := 2, mass := 1, time := -2 } : Dimension) ℂ).val =
      p.val * v.val := rfl
example (e : Energy) (t : TimeQ) :
    (e * t : Quantity ({ length := 2, mass := 1, time := -1 } : Dimension) ℂ).val =
      e.val * t.val := rfl
example (c : ℂ) (e : Energy) : (c • e).val = c • e.val := rfl
example (e : Energy) : (Quantity.map Complex.re e).val = e.val.re := rfl
example (x : LengthOf ℝ) (t : TimeOf ℝ) :
    (x / t : Quantity ({ length := 1, time := -1 } : Dimension) ℝ).val =
      x.val / t.val := rfl
example (m n : Nat) (d : Dimension) :
    Dimension.dimensionScale (m + n) d =
      Dimension.dimensionScale m d + Dimension.dimensionScale n d :=
  Dimension.dimensionScale_add m n d

-- ... while adding a length to a time does not typecheck at all.
-- (Uncomment to see the elaborator reject it:
--  example (x : Length) (y : TimeQ) : Length := x + y )

/-! ## Finite-dimensional quantum mechanics -/

example : (pauliX : Operator 2) * pauliX = identity := pauliX_sq
example : (pauliY : Operator 2) * pauliY = identity := pauliY_sq
example : commutator pauliX pauliY = (2 * Complex.I) • pauliZ := pauliXY_commutator

/-! ## Finite unitary dynamics -/

def identityUnitary {n : Nat} : UnitaryOperator n where
  op := identity
  unitary := by simp [identity]

theorem pauliZHermitian : pauliZ.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ]

example (t s : ℝ) :
    (finiteHamiltonianFlow pauliZ pauliZHermitian (t + s)).op =
      (finiteHamiltonianFlow pauliZ pauliZHermitian t).op *
        (finiteHamiltonianFlow pauliZ pauliZHermitian s).op :=
  finiteHamiltonianFlow_add_op pauliZ pauliZHermitian t s

example :
    (finiteHamiltonianFlow pauliZ pauliZHermitian 0).op = identity := by
  exact finiteHamiltonianFlow_zero pauliZ pauliZHermitian

example (t : ℝ) (rho : State 2) (hrho : IsDensity rho) :
    IsDensity ((finiteHamiltonianFlow pauliZ pauliZHermitian t).conjugate rho) := by
  have hpos := finiteHamiltonianFlow_conjugate_posSemidef
    pauliZ pauliZHermitian t rho hrho.2.1
  refine ⟨hpos.isHermitian, hpos, ?_⟩
  exact (finiteHamiltonianFlow_conjugate_trace pauliZ pauliZHermitian t rho).trans hrho.2.2

example (t : ℝ) :
    (finiteHamiltonianFlow pauliZ pauliZHermitian t).conjugate pauliZ = pauliZ := by
  apply finiteHamiltonianFlow_conjugate_of_conserved pauliZ pauliZHermitian t pauliZ
  exact LeanPhy.Quantum.commutator_self pauliZ

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    (LeanPhy.Mathematics.FiniteMatrixFlow.exponential A).flow 0 = 1 := by
  exact LeanPhy.Mathematics.FiniteMatrixFlow.flow_zero
    (LeanPhy.Mathematics.FiniteMatrixFlow.exponential A)

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) :
    (LeanPhy.Mathematics.FiniteMatrixFlow.exponential A).evolve 0 v = v := by
  exact LeanPhy.Mathematics.FiniteMatrixFlow.evolve_zero
    (LeanPhy.Mathematics.FiniteMatrixFlow.exponential A) v

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (t s : ℝ) (v : ι → ℂ) :
    (LeanPhy.Mathematics.FiniteMatrixFlow.exponential A).evolve (t + s) v =
      (LeanPhy.Mathematics.FiniteMatrixFlow.exponential A).evolve t
        ((LeanPhy.Mathematics.FiniteMatrixFlow.exponential A).evolve s v) := by
  exact LeanPhy.Mathematics.FiniteMatrixFlow.evolve_add
    (LeanPhy.Mathematics.FiniteMatrixFlow.exponential A) t s v

/-! ## Cross-domain finite-flow invariants -/

-- The same commutation certificate gives a Heisenberg-style invariant for any
-- finite matrix exponential, independently of whether the matrix is called a
-- Hamiltonian, BdG block, transfer generator or a classical linear generator.
example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A O : Matrix ι ι ℂ) (hAO : Commute A O) (t : ℝ) :
    (LeanPhy.Mathematics.FiniteMatrixFlow.exponential A).conjugate t O = O :=
  LeanPhy.Mathematics.FiniteMatrixFlow.exponential_conjugate_of_commute A O hAO t

-- Quantum vocabulary is an alias of the same checked invariant contract.
example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A O : Matrix ι ι ℂ) (hAO : Commute A O) :
    LeanPhy.Quantum.FlowInvariant
      (LeanPhy.Mathematics.FiniteMatrixFlow.exponential A) O :=
  LeanPhy.Mathematics.FiniteMatrixFlow.exponential_isInvariant_of_commute A O hAO

-- Real classical systems use precisely the same theorem over an RCLike scalar.
example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A O : Matrix ι ι ℝ) (hAO : Commute A O) :
    LeanPhy.Classical.LinearFlowInvariant
      (LeanPhy.Mathematics.FiniteMatrixFlow.exponential A) O :=
  LeanPhy.Mathematics.FiniteMatrixFlow.exponential_isInvariant_of_commute A O hAO

-- Domain aliases for BdG, transfer and finite-mode field calculations carry
-- no extra proof obligations: the common flow invariant is the API boundary.
example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A O : Matrix ι ι ℂ) (hAO : Commute A O) :
    LeanPhy.Condensed.BdGFlowInvariant
      (LeanPhy.Mathematics.FiniteMatrixFlow.exponential A) O :=
  LeanPhy.Mathematics.FiniteMatrixFlow.exponential_isInvariant_of_commute A O hAO

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A O : Matrix ι ι ℝ) (hAO : Commute A O) :
    LeanPhy.StatMech.TransferFlowInvariant
      (LeanPhy.Mathematics.FiniteMatrixFlow.exponential A) O :=
  LeanPhy.Mathematics.FiniteMatrixFlow.exponential_isInvariant_of_commute A O hAO

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A O : Matrix ι ι ℂ) (hAO : Commute A O) :
    LeanPhy.FieldTheory.FiniteModeFlowInvariant
      (LeanPhy.Mathematics.FiniteMatrixFlow.exponential A) O :=
  LeanPhy.Mathematics.FiniteMatrixFlow.exponential_isInvariant_of_commute A O hAO

/-! The common proof-preserving process layer is itself algebraic: these facts
   exercise composition and finite-time iteration independently of the domain
   vocabulary attached to the adapter. -/

example {ι : Type} [Fintype ι] (K : FiniteKernel ι)
    (p : FiniteProbability ι) (m n : Nat) :
    Process.iterate K.toStateMap (m + n) p =
      Process.iterate K.toStateMap m (Process.iterate K.toStateMap n p) :=
  Process.iterate_add K.toStateMap m n p

example {ι : Type} [Fintype ι]
    (K : FiniteKernel ι) (L : FiniteKernel ι) (p : FiniteProbability ι) :
    StateMap.compose K.toStateMap (StateMap.compose L.toStateMap
      (StateMap.identity (FiniteProbability ι) (fun _ => True))) p =
      StateMap.compose (StateMap.compose K.toStateMap L.toStateMap)
        (StateMap.identity (FiniteProbability ι) (fun _ => True)) p := by
  rw [StateMap.compose_assoc]

example {ι : Type} [Fintype ι]
    (K : FiniteKernel ι) (f : ι → ℝ) (p : FiniteProbability ι)
    (hp : True) :
    (K.step p).expectation f = p.expectation (K.pullback f) :=
  K.toObservableTransport.compatible p hp f

/-! Product processes exercise the reusable multi-subsystem boundary.  The
   definitions below are deliberately domain-neutral: the same API is used
   by tensor-product quantum channels and by finite classical/lattice blocks. -/

def smokeNatStep : Process Nat (fun _ => True) where
  toFun := Nat.succ
  preserves := by intro _ _; trivial

def smokeBoolStep : Process Bool (fun _ => True) where
  toFun := Bool.not
  preserves := by intro _ _; trivial

/-! ## Cross-domain model contracts

The same proof-preserving model interface can describe a finite quantum
channel, a Markov step, a lattice update, or a truncated field evolution.  The
following tiny models exercise the reusable dynamics/observable bridge rather
than a domain-specific theorem. -/

def smokeNatModel : LeanPhy.Mathematics.PhysicalModel Nat where
  State := Nat
  valid := fun _ => True
  step := smokeNatStep
  Observable := Unit
  evaluate := fun n _ => n

def smokeNatModelIdentity : LeanPhy.Mathematics.ModelMap smokeNatModel smokeNatModel :=
  LeanPhy.Mathematics.ModelMap.identity smokeNatModel

def smokeBoolModel : LeanPhy.Mathematics.PhysicalModel Nat where
  State := Bool
  valid := fun _ => True
  step := smokeBoolStep
  Observable := Unit
  evaluate := fun b _ => if b then 1 else 0

def smokeProductModel : LeanPhy.Mathematics.PhysicalModel (Nat × Nat) :=
  LeanPhy.Mathematics.PhysicalModel.product smokeNatModel smokeBoolModel

example (n : Nat) (s : Nat) (hs : smokeNatModel.valid s) :
    smokeNatModelIdentity.state (smokeNatModel.evolve n s) =
      smokeNatModel.evolve n (smokeNatModelIdentity.state s) :=
  LeanPhy.Mathematics.ModelMap.iterate_commutes smokeNatModelIdentity n s hs

example (n : Nat) (s : Nat) (hs : smokeNatModel.valid s) :
    smokeNatModel.evaluate
        (smokeNatModelIdentity.state (smokeNatModel.evolve n s)) () =
      smokeNatModel.evaluate (smokeNatModel.evolve n s)
        (smokeNatModelIdentity.pullback ()) :=
  LeanPhy.Mathematics.ModelMap.evaluate_after_iterate smokeNatModelIdentity n s hs ()

example (n : Nat) (s : Nat) (b : Bool) :
    smokeProductModel.evolve n (s, b) =
      (smokeNatModel.evolve n s, smokeBoolModel.evolve n b) :=
  LeanPhy.Mathematics.PhysicalModel.product_evolve smokeNatModel smokeBoolModel n s b

example {ι : Type*} [Fintype ι]
    (C K L : LeanPhy.StatMech.FiniteKernel ι)
    (h : ∀ p, C.step (K.step p) = L.step (C.step p))
    (n : Nat) (p : FiniteProbability ι) (f : ι → ℝ) :
    (Process.iterate L.toStateMap n (C.step p)).expectation f =
      (Process.iterate K.toStateMap n p).expectation (C.pullback f) :=
  LeanPhy.StatMech.FiniteKernel.modelMap_expectation C K L h n p f

example {ι κ ξ : Type*} [Fintype ι] [Fintype κ] [Fintype ξ]
    [DecidableEq ι]
    (C : TypedKrausChannel ι κ ξ)
    (K : FiniteCPTPMap ι ι) (L : FiniteCPTPMap κ κ)
    (h : ∀ rho, IsFiniteDensity rho → C.apply (K rho) = L (C.apply rho))
    (n : Nat) (rho : Matrix ι ι ℂ) (hrho : IsFiniteDensity rho)
    (A : Matrix κ κ ℂ) :
    Matrix.trace (Process.iterate L.toStateMap n (C.apply rho) * A) =
      Matrix.trace
        (Process.iterate K.toStateMap n rho *
          LeanPhy.QuantumInfo.typedAdjointKraus C.op A) :=
  LeanPhy.QuantumInfo.TypedKrausChannel.modelMap_expectation C K L h n rho hrho A

example :
    LeanPhy.Mathematics.ModelMap.compose
      (LeanPhy.Mathematics.ModelMap.identity smokeNatModel)
      smokeNatModelIdentity = smokeNatModelIdentity := by
  exact LeanPhy.Mathematics.ModelMap.identity_left smokeNatModelIdentity

example (n : Nat) :
    Process.iterate (Process.parallel smokeNatStep smokeBoolStep) n (0, true) =
      (Process.iterate smokeNatStep n 0, Process.iterate smokeBoolStep n true) :=
  Process.iterate_parallel smokeNatStep smokeBoolStep n 0 true

def smokeNatInvariant : Invariant smokeNatStep Nat where
  quantity := fun _ => 7
  preserved := by intro _ _; rfl

def smokeBoolInvariant : Invariant smokeBoolStep Bool where
  quantity := fun _ => true
  preserved := by intro b _; rfl

example :
    (Invariant.parallel smokeNatInvariant smokeBoolInvariant).quantity (0, true) =
      (7, true) := rfl

example :
    (Invariant.parallel smokeNatInvariant smokeBoolInvariant).quantity
        ((Process.parallel smokeNatStep smokeBoolStep) (0, true)) =
      (Invariant.parallel smokeNatInvariant smokeBoolInvariant).quantity (0, true) :=
  (Invariant.parallel smokeNatInvariant smokeBoolInvariant).preserved
    (0, true) (by trivial)

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (t s : ℝ) :
    (finiteHamiltonianEvolution H hH).flow (t + s) =
      (finiteHamiltonianEvolution H hH).flow t *
        (finiteHamiltonianEvolution H hH).flow s := by
  exact (finiteHamiltonianEvolution H hH).add t s

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (O : Matrix ι ι ℂ)
    (hO : LeanPhy.Quantum.Conserved H O) :
    (finiteHamiltonianEvolution H hH).IsInvariant O :=
  finiteHamiltonianEvolution_isInvariant H hH O hO

example {ι : Type} [Fintype ι] [DecidableEq ι] (t : ℝ) :
    (finiteHamiltonianFlow (1 : Matrix ι ι ℂ)
      (by simp [Matrix.IsHermitian]) t).conjugate (1 : Matrix ι ι ℂ) = 1 := by
  apply finiteHamiltonianFlow_conjugate_of_conserved (1 : Matrix ι ι ℂ)
    (by simp [Matrix.IsHermitian]) t (1 : Matrix ι ι ℂ)
  exact LeanPhy.Quantum.commutator_self 1

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : FiniteUnitary ι) (rho : Matrix ι ι ℂ) (hrho : IsFiniteDensity rho) :
    IsFiniteDensity (U.evolveDensity ⟨rho, hrho⟩).rho := by
  exact (U.evolveDensity ⟨rho, hrho⟩).valid

example {ι : Type} [Fintype ι] (C : NamedFiniteChannel ι)
    (rho : NamedState ι) (hrho : IsFiniteDensity rho) :
    IsFiniteDensity (C rho) :=
  namedFiniteChannel_isFiniteDensity C rho hrho

example {n : Nat} (v w : Ket n) :
    braket (unitaryEvolve (identityUnitary (n := n)) v)
      (unitaryEvolve (identityUnitary (n := n)) w) = braket v w :=
  unitaryEvolve_inner (identityUnitary (n := n)) v w

example {n : Nat} (U : UnitaryOperator n) (rho : State n) (A : Observable n) :
    expectation (unitaryConjugate U rho) A =
      expectation rho (unitaryObservableConjugate U A) :=
  unitary_expectation_duality U rho A

example {n : Nat} (rho : State n) (hrho : IsDensity rho) :
    IsDensity (unitaryConjugate (identityUnitary (n := n)) rho) :=
  unitaryConjugate_isDensity (identityUnitary (n := n)) rho hrho

/-! ## Abstract finite CPTP maps -/

example {ι : Type*} [Fintype ι] (rho : Matrix ι ι ℂ)
    (hrho : IsFiniteDensity rho) :
    IsFiniteDensity ((FiniteCPTPMap.identity (ι := ι)) rho) := by
  exact (FiniteCPTPMap.identity (ι := ι)).map_isFiniteDensity rho hrho

example {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : FiniteCPTPMap ι κ) (rho : Matrix ι ι ℂ) :
    (FiniteCPTPMap.identity (ι := κ)).compose C rho = C rho := by
  exact FiniteCPTPMap.compose_identity_right C rho

example {n : Nat} (after before : UnitaryOperator n) (v : Ket n) :
    unitaryEvolve (after.compose before) v =
      unitaryEvolve after (unitaryEvolve before v) :=
  UnitaryOperator.compose_evolve after before v

example {n : Nat} (rho : State n) :
    (unitaryChannel (identityUnitary (n := n))).toFiniteChannel rho =
      unitaryConjugate (identityUnitary (n := n)) rho :=
  unitaryChannel_apply (identityUnitary (n := n)) rho

example {n : Nat} (after before : UnitaryOperator n) (rho : State n) :
    ((unitaryChannel after).compose (unitaryChannel before)).toFiniteChannel rho =
      (unitaryChannel (after.compose before)).toFiniteChannel rho :=
  unitaryChannel_compose_apply after before rho

example (t12 t13 t23 : ℝ) (u : ℂ)
    (hu : (starRingEnd ℂ) u * u = 1) :
    Matrix.conjTranspose (LeanPhy.Particles.ckm t12 t13 t23 u) *
        LeanPhy.Particles.ckm t12 t13 t23 u = 1 :=
  (LeanPhy.Particles.ckm_unitaryOperator t12 t13 t23 u hu).unitary

example {m n : Nat} (U : FiniteUnitary (Fin m)) (V : FiniteUnitary (Fin n)) :
    Matrix.conjTranspose (FiniteUnitary.tensor U V).op *
        (FiniteUnitary.tensor U V).op = 1 :=
  (FiniteUnitary.tensor U V).unitary

/-! ## Spin-1/2 angular momentum -/

example : commutator Jx Jy = Complex.I • Jz := Jx_commutator_Jy
example : casimir = ((3 / 4 : ℂ)) • identity := casimir_eq

/-! ## Field-theory algebra from the CCR -/

example {A : Type} [Ring A] (a adag : A) (h : commutator a adag = 1) :
    commutator (adag * a) adag = adag := LeanPhy.Quantum.number_commutator a adag h

/-! ## Generic conserved-observable algebra -/

example {A : Type} [Ring A] (H O P : A)
    (hO : LeanPhy.Quantum.Conserved H O)
    (hP : LeanPhy.Quantum.Conserved H P) :
    LeanPhy.Quantum.Conserved H (O * P) :=
  LeanPhy.Quantum.conserved_mul H O P hO hP

example {A : Type} [Ring A] (H a b O P : A)
    (ha : LeanPhy.Quantum.Conserved H a)
    (hb : LeanPhy.Quantum.Conserved H b)
    (hO : LeanPhy.Quantum.Conserved H O)
    (hP : LeanPhy.Quantum.Conserved H P) :
    LeanPhy.Quantum.Conserved H (a * O + b * P) :=
  LeanPhy.Quantum.conserved_linear_combination H a b O P ha hb hO hP

example {A : Type} [Ring A] (x y z : A) :
    LeanPhy.Quantum.commutator x (LeanPhy.Quantum.commutator y z) +
        LeanPhy.Quantum.commutator y (LeanPhy.Quantum.commutator z x) +
        LeanPhy.Quantum.commutator z (LeanPhy.Quantum.commutator x y) = 0 :=
  LeanPhy.Mathematics.commutator_jacobi x y z

example (c s : ℂ) (h : c ^ 2 - s ^ 2 = 1) :
    let B : BilinearIsometry LeanPhy.Relativity.etaM :=
      { op := LeanPhy.Relativity.boost c s,
        preserve := LeanPhy.Relativity.boost_lorentz c s h }
    B.opᵀ * LeanPhy.Relativity.etaM * B.op = LeanPhy.Relativity.etaM := by
  dsimp
  exact LeanPhy.Relativity.boost_lorentz c s h

/-! ## Shared Lie-algebra / representation interface -/

-- Lorentz, colour, gauge, lattice and spin modules can all provide the same
-- explicit fields.  The generic theorem then transports the Jacobi identity
-- through any kernel-checked matrix/operator representation.
example {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (F : LeanPhy.Mathematics.FiniteFourierSystem α) (x : α → ℂ) :
    F.inverse (F.forward x) = x :=
  F.inverse_forward x

example (x : Fin 2 → ℂ) :
    LeanPhy.Mathematics.FiniteFourierSystem.hadamardFourier.inverse
      (LeanPhy.Mathematics.FiniteFourierSystem.hadamardFourier.forward x) = x :=
  LeanPhy.Mathematics.FiniteFourierSystem.hadamard_inverse_forward x

example (x : Fin 4 → ℂ) :
    LeanPhy.Mathematics.FiniteFourierSystem.fourier4.inverse
      (LeanPhy.Mathematics.FiniteFourierSystem.fourier4.forward x) = x :=
  LeanPhy.Mathematics.FiniteFourierSystem.fourier4_inverse_forward x

example (x : Fin 4 → ℂ) :
    LeanPhy.Mathematics.FiniteFourierSystem.fourier4.forward
      (LeanPhy.Mathematics.FiniteFourierSystem.fourier4.inverse x) = x :=
  LeanPhy.Mathematics.FiniteFourierSystem.fourier4_forward_inverse x

example :
    Matrix.conjTranspose
        (LeanPhy.Mathematics.FiniteFourierSystem.fourier4Unitary).op *
        (LeanPhy.Mathematics.FiniteFourierSystem.fourier4Unitary).op = 1 :=
  LeanPhy.Mathematics.FiniteFourierSystem.fourier4Unitary.unitary

example (x y : Fin 4 → ℂ) :
    dotProduct
        (star ((LeanPhy.Mathematics.FiniteFourierSystem.fourier4Unitary).evolve x))
        ((LeanPhy.Mathematics.FiniteFourierSystem.fourier4Unitary).evolve y) =
      dotProduct (star x) y :=
  FiniteUnitary.evolve_inner
    LeanPhy.Mathematics.FiniteFourierSystem.fourier4Unitary x y

example (x y : Fin 4 → ℂ) :
    LeanPhy.Mathematics.FiniteFourierSystem.finiteInner
        (LeanPhy.Mathematics.FiniteFourierSystem.fourier4.forward x)
        (LeanPhy.Mathematics.FiniteFourierSystem.fourier4.forward y) =
      (4 : ℂ) * LeanPhy.Mathematics.FiniteFourierSystem.finiteInner x y :=
  LeanPhy.Mathematics.FiniteFourierSystem.fourier4.parseval x y

example (L : LieAlgebra ℝ ℝ) (rho : Representation L ℂ) (x y z : ℝ) :
    ringCommutator (rho x) (ringCommutator (rho y) (rho z)) +
        ringCommutator (rho y) (ringCommutator (rho z) (rho x)) +
        ringCommutator (rho z) (ringCommutator (rho x) (rho y)) = 0 :=
  Representation.preserves_jacobi rho x y z

example (x y z : Operator 2) :
    ringCommutator x (ringCommutator y z) +
        ringCommutator y (ringCommutator z x) +
        ringCommutator z (ringCommutator x y) = 0 := by
  exact Representation.preserves_jacobi
    (associativeLieRepresentation ℂ (Operator 2)) x y z

/-! ## Finite spectral and ladder interface -/

example {n : Nat} (H A : Operator n) (e c : ℂ) (v : Ket n)
    (hshift : commutator H A = c • A)
    (hv : IsEigenvector H e v) :
    IsEigenvector H (e + c) (A.mulVec v) :=
  commutator_eigenvector_shift H A e c v hshift hv

example {n m : Nat} (S : LeanPhy.Quantum.SpectralProjectors n m)
    (e : Fin m → ℂ) (j : Fin m) :
    LeanPhy.Quantum.spectralOperator S e * S.proj j = e j • S.proj j :=
  LeanPhy.Quantum.spectralOperator_mul_projector S e j

example {n m : Nat} (S : LeanPhy.Quantum.SpectralProjectors n m)
    (e : Fin m → ℂ) (j : Fin m) (v : Ket n)
    (hv : (S.proj j).mulVec v = v) :
    (LeanPhy.Quantum.spectralOperator S e).mulVec v = e j • v :=
  LeanPhy.Quantum.spectralOperator_mulVec_of_projector S e j v hv

example :
    LeanPhy.Quantum.spectralOperator
        LeanPhy.Quantum.computationalSpectralProjectors ![1, -1] =
      LeanPhy.Quantum.pauliZ :=
  LeanPhy.Quantum.pauliZ_spectral_reconstruction

example :
    (LeanPhy.Quantum.spectralOperator
        LeanPhy.Quantum.computationalSpectralProjectors ![1, -1]).mulVec
        (fun i : Fin 2 => if i = (0 : Fin 2) then (1 : ℂ) else 0) =
      (1 : ℂ) • (fun i : Fin 2 => if i = (0 : Fin 2) then (1 : ℂ) else 0) :=
  LeanPhy.Quantum.pauliZ_plus_projector_eigenvalue

/-! ## Differential-operator layer for continuum physics -/

example {n : Nat} (D : Fin n → PhysicsDerivation ℝ ℝ)
    (i j k : Fin n) (f : ℝ) :
    (derivationCurvature D i j) (D k f) - D k (derivationCurvature D i j f) +
        (derivationCurvature D j k) (D i f) - D i (derivationCurvature D j k f) +
        (derivationCurvature D k i) (D j f) - D j (derivationCurvature D k i f) = 0 :=
  derivation_bianchi_apply D i j k f

/-! ## Shared Poisson algebra for classical and semiclassical models -/

example {A : Type} [CommRing A] [Algebra ℝ A]
    (P : PoissonAlgebra ℝ A) (H O : A)
    (hO : PoissonAlgebra.Conserved P H O) :
    PoissonAlgebra.Conserved P H (O ^ 3) :=
  PoissonAlgebra.conserved_pow P H O 3 hO

example {A : Type} [CommRing A] [Algebra ℝ A]
    (P : PoissonAlgebra ℝ A) (H O Q : A)
    (hO : PoissonAlgebra.Conserved P H O)
    (hQ : PoissonAlgebra.Conserved P H Q) :
    PoissonAlgebra.Conserved P H (P O Q) :=
  PoissonAlgebra.conserved_bracket P H O Q hO hQ

example {A : Type} [CommRing A] [Algebra ℝ A]
    (P : PoissonAlgebra ℝ A) (H O Q : A) :
    PoissonAlgebra.hamiltonianDerivation P H (O * Q) =
      O * PoissonAlgebra.hamiltonianDerivation P H Q +
        Q * PoissonAlgebra.hamiltonianDerivation P H O :=
  PoissonAlgebra.hamiltonianDerivation_product P H O Q

example {A : Type} [CommRing A] [Algebra ℝ A]
    (P : PoissonAlgebra ℝ A) (H K : A) :
    derivationCommutator (PoissonAlgebra.hamiltonianDerivation P H)
        (PoissonAlgebra.hamiltonianDerivation P K) =
      PoissonAlgebra.hamiltonianDerivation P (P H K) :=
  PoissonAlgebra.hamiltonianDerivation_commutator P H K

example :
    LeanPhy.Classical.canonicalPolynomialPoisson
      (MvPolynomial.X 0) (MvPolynomial.X 1) = 1 :=
  LeanPhy.Classical.canonical_q_p

example :
    LeanPhy.Classical.polynomialPairPoisson (σ := Fin 4) 0 1
      (MvPolynomial.X 0) (MvPolynomial.X 1) = 1 := by
  simp [LeanPhy.Classical.polynomialPairPoisson,
    LeanPhy.Mathematics.PoissonAlgebra.derivationPoissonAlgebra,
    LeanPhy.Mathematics.PoissonAlgebra.derivationBracket]

example (H f g : LeanPhy.Classical.PhasePolynomial) :
    PoissonAlgebra.hamiltonianDerivation
        LeanPhy.Classical.canonicalPolynomialPoisson H (f * g) =
      f * PoissonAlgebra.hamiltonianDerivation
        LeanPhy.Classical.canonicalPolynomialPoisson H g +
      g * PoissonAlgebra.hamiltonianDerivation
        LeanPhy.Classical.canonicalPolynomialPoisson H f :=
  LeanPhy.Classical.canonical_hamiltonian_is_derivation H f g

example :
    LeanPhy.Classical.canonicalPolynomialPoisson
      LeanPhy.Classical.oscillatorPolynomialHamiltonian
      LeanPhy.Classical.qPolynomial = -LeanPhy.Classical.pPolynomial :=
  LeanPhy.Classical.oscillator_hamiltonian_q

example :
    LeanPhy.Mathematics.PoissonAlgebra.Conserved
      LeanPhy.Classical.canonicalPolynomialPoisson
      LeanPhy.Classical.oscillatorPolynomialHamiltonian
      LeanPhy.Classical.oscillatorPolynomialHamiltonian :=
  LeanPhy.Classical.oscillator_hamiltonian_conserved

/-! ## Multi-mode CCR: the total number operator is a ladder for every mode -/

example {ι : Type} [DecidableEq ι] [Fintype ι] {A : Type} [Ring A]
    (M : MultiModeCCR ι A) (j : ι) :
    commutator M.totalNumber (M.cre j) = M.cre j := M.totalNumber_commutator_cre j

/-! ## Multi-mode CAR: the fermionic number ladder -/

example {ι : Type} [DecidableEq ι] [Fintype ι] {A : Type} [Ring A]
    (M : MultiModeCAR ι A) (j : ι) :
    commutator M.totalNumber (M.cre j) = M.cre j :=
  M.totalNumber_commutator_cre j

example {ι : Type} [DecidableEq ι] [Fintype ι] {A : Type} [Ring A]
    (M : MultiModeCAR ι A) (j : ι) :
    commutator M.totalNumber (M.ann j) = -M.ann j :=
  M.totalNumber_commutator_ann j

/-! ## Wick recursion (highest-risk tier): four-point function of the free field -/

example (M : FreeMode) : M.omega ((M.a + M.adag) ^ 4) = 3 := FreeMode.phi_four M

-- the general Wick result: every even moment is a double factorial
example (M : FreeMode) (k : Nat) :
    M.omega ((M.a + M.adag) ^ (2*k)) = (FreeMode.doubleFact k : ℂ) :=
  FreeMode.wick_even_moment M k

-- ... and every odd moment vanishes
example (M : FreeMode) (k : Nat) : M.omega ((M.a + M.adag) ^ (2*k+1)) = 0 :=
  FreeMode.phi_odd M k

-- the pairing count: 3, 15, 105 perfect matchings of 4, 6, 8 objects
example : numMatchings [0,1,2,3] = 3 := numMatchings_four
example : numMatchings [0,1,2,3,4,5] = 15 := numMatchings_six
example : numMatchings [0,1,2,3,4,5,6,7] = 105 := numMatchings_eight

-- Wick's theorem in pairing-count form: the moment is the number of matchings
example (M : FreeMode) (k : Nat) :
    M.omega ((M.a + M.adag) ^ (2*k)) = (numMatchings (List.range (2*k)) : ℂ) :=
  wick_pairing_count M k

/-! ## Finite multi-field Wick contractions -/

-- A covariance kernel over four typed slots expands into the three bosonic
-- pairings.  No time ordering or continuum distribution is hidden here.
example (C : Fin 4 → Fin 4 → ℂ) :
    LeanPhy.FieldTheory.MultiWick.gaussianMoment C [0, 1, 2, 3] =
      C 0 1 * C 2 3 + C 0 2 * C 1 3 + C 0 3 * C 1 2 :=
  LeanPhy.FieldTheory.MultiWick.gaussianMoment_four C

/-! ## Fermionic algebra: N = c†c is a projector -/

example (M : FermionicMode) : M.numberOp * M.numberOp = M.numberOp := FermionicMode.number_idempotent M

example (M : FermionicMode) :
    (M.asMultiCAR).totalNumber = M.numberOp :=
  M.asMultiCAR_totalNumber

/-! ## Hubbard site: double occupancy and the pair operator -/

example (M : LeanPhy.Condensed.HubbardSite) :
    M.doubleOcc * M.doubleOcc = M.doubleOcc :=
  LeanPhy.Condensed.HubbardSite.doubleOcc_idempotent M

example (M : LeanPhy.Condensed.HubbardSite) :
    LeanPhy.Quantum.commutator M.doubleOcc M.pairOp = M.pairOp :=
  LeanPhy.Condensed.HubbardSite.doubleOcc_commutator_pairOp M

/-! ## Physics-facing surface notation -/

-- Dirac notation: `|0⟩`, the bracket `⟨u|v⟩`, the matrix element `⟨u|A|v⟩`
example : (|(0 : Fin 2)⟩ : Ket 2) 0 = 1 := by simp [basisKet]

example : (⟨(|0⟩ : Ket 2)|(|1⟩ : Ket 2)⟩ : ℂ) = 0 := by
  rw [bracket, basisKet_orthonormal]; simp

example (a : Operator 2) : (⟨(|0⟩ : Ket 2)|a|(|1⟩ : Ket 2)⟩ : ℂ) = a 0 1 := by
  simp [bracketOp, braket, basisKet, Matrix.mulVec, dotProduct]

example : (∑ k : Fin 2, ketbra (basisKet k) (basisKet k)) = 1 := completeness 2

example (v : Ket 2) :
    (∑ k : Fin 2, ketbra (basisKet k) (basisKet k)).mulVec v = v := resolution 2 v

-- Index calculus: the epsilon-delta identity
example (j k l m : Fin 3) :
    (∑ i : Fin 3, epsilon i j k * epsilon i l m)
      = delta j l * delta k m - delta j m * delta k l :=
  epsilon_delta j k l m

-- Einstein summation as real syntax: the index type is inferred from context
example {m n p : Nat} (M : Matrix (Fin m) (Fin n) ℂ) (N : Matrix (Fin n) (Fin p) ℂ)
    (i : Fin m) (j : Fin p) : (einsum k, M i k * N k j) = (M * N) i j :=
  einsum_mul_apply M N i j

example {n : Nat} (M : Matrix (Fin n) (Fin n) ℂ) : (einsum i, M i i) = M.trace :=
  einsum_trace M

/-! ## Dirac notation with dimension inference (real elaborator)

The Dirac surface is a term elaborator, so a dimension clash is caught with a
Chinese diagnostic instead of silently elaborating.  The positive cases: -/

-- all slots share one inferred dimension, and the result is the thin definition
example (u v : Ket 2) (A : Operator 2) :
    (⟨u|A|v⟩ : ℂ) = LeanPhy.Quantum.braket u (A.mulVec v) := rfl

-- the bra, the bra-with-operator and the outer product are the thin definitions
example (u : Ket 2) (A : Operator 2) : (⟨u|A : Bra 2) = LeanPhy.Quantum.braMulOp u A := rfl
example (u v : Ket 2) : (|u⟩⟨v| : Operator 2) = LeanPhy.Quantum.ketbra u v := rfl

-- a basis ket infers its dimension from the surrounding bracket
example : (⟨(|0⟩ : Ket 2)|(|1⟩ : Ket 2)⟩ : ℂ) = 0 := by
  rw [LeanPhy.Quantum.bracket, LeanPhy.Quantum.basisKet_orthonormal]
  simp

-- the outer product acting on a ket is the composition rule, in surface syntax
example (u v w : Ket 2) : (|u⟩⟨v| : Operator 2).mulVec w = (⟨v|w⟩ : ℂ) • u :=
  LeanPhy.Quantum.ketbra_mulVec u v w

/-! Finite projectors: the same rank-one object serves spectral bands and POVM
effects.  Normalization is explicit, so these examples do not assume a
spectral theorem. -/
example (v : Ket 2) (h : braket v v = 1) :
    LeanPhy.Quantum.rankOneProjector v * LeanPhy.Quantum.rankOneProjector v =
      LeanPhy.Quantum.rankOneProjector v :=
  LeanPhy.Quantum.rankOneProjector_mul_self v h

example (v : Ket 2) :
    (LeanPhy.Quantum.rankOneProjector v).PosSemidef :=
  LeanPhy.Quantum.rankOneProjector_posSemidef v

example (v : Ket 2) (h : braket v v = 1) :
    Matrix.trace (LeanPhy.Quantum.rankOneProjector v) = 1 :=
  LeanPhy.Quantum.normalized_rankOneProjector_trace v h

/-! ## The Ward identity (gauge invariance of the photon vertex) -/

-- the vertex amplitude is the slash sandwich
example (eps : Fin 4 → ℂ) (ub u : LeanPhy.HighEnergy.Spinor) :
    LeanPhy.HighEnergy.vertexAmplitude eps ub u =
      LeanPhy.HighEnergy.bilinear ub (LeanPhy.HighEnergy.slash eps) u :=
  LeanPhy.HighEnergy.vertexAmplitude_eq_slash eps ub u

-- on shell, the longitudinal polarisation (eps = p' - p) decouples
example (p p' : Fin 4 → ℂ) (ub u : LeanPhy.HighEnergy.Spinor)
    (hu : (LeanPhy.HighEnergy.slash p).mulVec u = 0)
    (hub : LeanPhy.HighEnergy.rowMul ub (LeanPhy.HighEnergy.slash p') = 0) :
    LeanPhy.HighEnergy.vertexAmplitude (p' - p) ub u = 0 :=
  LeanPhy.HighEnergy.ward_identity p p' ub u hu hub

-- gauge invariance: eps -> eps + lam (p' - p) leaves the on-shell amplitude fixed
example (eps p p' : Fin 4 → ℂ) (lam : ℂ) (ub u : LeanPhy.HighEnergy.Spinor)
    (hu : (LeanPhy.HighEnergy.slash p).mulVec u = 0)
    (hub : LeanPhy.HighEnergy.rowMul ub (LeanPhy.HighEnergy.slash p') = 0) :
    LeanPhy.HighEnergy.vertexAmplitude (eps + lam • (p' - p)) ub u =
      LeanPhy.HighEnergy.vertexAmplitude eps ub u :=
  LeanPhy.HighEnergy.gauge_invariance eps p p' lam ub u hu hub

-- a concrete on-shell configuration, so the hypotheses are not vacuous
example : LeanPhy.HighEnergy.vertexAmplitude
    (LeanPhy.HighEnergy.wardP - LeanPhy.HighEnergy.wardP)
    LeanPhy.HighEnergy.wardUb LeanPhy.HighEnergy.wardU = 0 :=
  LeanPhy.HighEnergy.ward_identity_witness

/-! ## Spinor kinematics: the slash square and the mass shell -/

-- the Feynman slash squares to the invariant p . p
example (p : Fin 4 → ℂ) :
    LeanPhy.HighEnergy.slash p * LeanPhy.HighEnergy.slash p =
      (LeanPhy.HighEnergy.minkowskiDot p p) • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  LeanPhy.HighEnergy.slash_sq p

-- its trace shadow: tr (a-slash p a-slash p) = 4 (p . p)
example (p : Fin 4 → ℂ) :
    tr4 (LeanPhy.HighEnergy.slash p * LeanPhy.HighEnergy.slash p)
      = 4 * LeanPhy.HighEnergy.minkowskiDot p p :=
  LeanPhy.HighEnergy.slash_sq_trace p

-- the Dirac equation a-slash p u = m u forces the mass shell: (p.p - m²) u = 0
example (p u : Fin 4 → ℂ) (m : ℂ)
    (h : (LeanPhy.HighEnergy.slash p).mulVec u = m • u) :
    (LeanPhy.HighEnergy.minkowskiDot p p - m * m) • u = 0 :=
  LeanPhy.HighEnergy.mass_shell p u m h

-- a massless on-shell spinor has lightlike momentum
example (p u : Fin 4 → ℂ)
    (h : (LeanPhy.HighEnergy.slash p).mulVec u = 0) :
    (LeanPhy.HighEnergy.minkowskiDot p p) • u = 0 :=
  LeanPhy.HighEnergy.massless_lightlike p u h

/-! ## Clifford algebra -/

example {A : Type} [Ring A] (γ : A) (h : anticommutator γ γ = 0) :
    γ * γ + γ * γ = 0 := h

-- gamma-matrix trace identities (the place a sign error breaks a cross section)
example : tr4 (1 : Matrix (Fin 4) (Fin 4) ℂ) = 4 := tr4_one
example (mu : Fin 4) : tr4 (gammaFin mu) = 0 := tr4_gammaFin mu
example (mu nu : Fin 4) : tr4 (gammaFin mu * gammaFin nu) = 4 * etaFin mu nu :=
  tr4_gammaFin_two mu nu
example (mu nu rho sig : Fin 4) :
    tr4 (gammaFin mu * gammaFin nu * gammaFin rho * gammaFin sig)
      = 4 * (etaFin mu nu * etaFin rho sig - etaFin mu rho * etaFin nu sig
              + etaFin mu sig * etaFin nu rho) :=
  tr4_gammaFin_four mu nu rho sig
example : tr4 gamma5 = 0 := tr4_gamma5
example (mu nu : Fin 4) : tr4 (gamma5 * gammaFin mu * gammaFin nu) = 0 :=
  tr4_gamma5_gammaFin_two mu nu

/-! ## Supersymmetry algebra -/

example (S : SusyQM) : ⟦S.H, S.Q⟧ = 0 := SusyQM.H_commutator_Q S
example (S : SusyQM) : ⟦S.H, S.Qdag⟧ = 0 := SusyQM.H_commutator_Qdag S
example : SusyQM.H SusyExample.susyExample = 1 := SusyExample.susyExample_H

/-! ## Entanglement measures: purity (Renyi-2 core) -/

example : purity halfIdentity = 1/2 := purity_maximallyMixed
example : purity groundProjector = 1 := purity_pure_projector
example : purity (partialTraceRight bellState) = 2 := purity_bell_marginal

/-! ## Dirac bilinear (Feynman-slash) algebra -/

example (a b : Fin 4 → ℂ) : tr4 (slash a * slash b) = 4 * minkowskiDot a b :=
  tr4_slash_mul a b
example (a : Fin 4 → ℂ) : tr4 (slash a) = 0 := tr4_slash a
example (a : Fin 4 → ℂ) : tr4 (gamma5 * slash a) = 0 := tr4_gamma5_slash a

/-! ## Majorana fermions and the Dirac-Majorana correspondence -/

example (M : LeanPhy.Condensed.DiracMode) :
    M.majorana1 * M.majorana1 = 1 := M.majorana1_sq
example (M : LeanPhy.Condensed.DiracMode) :
    M.majorana2 * M.majorana2 = -1 := M.majorana2_sq
example (M : LeanPhy.Condensed.DiracMode) :
    M.majorana1 * M.majorana2 + M.majorana2 * M.majorana1 = 0 := M.majorana_anticommute
example (M : LeanPhy.Condensed.DiracMode) :
    M.majorana1 * M.majorana2 = 2 * (M.cdag * M.c) - 1 := M.number_from_majorana

/-! ## BCS mean field and Bogoliubov quasiparticles -/

-- the BdG matrix squares to the excitation energy: H^2 = (eps^2 + Delta^2) 1
example (eps Delta : ℂ) :
    LeanPhy.Condensed.bdg eps Delta * LeanPhy.Condensed.bdg eps Delta
      = (eps ^ 2 + Delta ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  LeanPhy.Condensed.bdg_sq eps Delta

-- the BdG spectrum is the symmetric pair +/- sqrt(eps^2 + Delta^2)
example (eps Delta : ℂ) : Matrix.trace (LeanPhy.Condensed.bdg eps Delta) = 0 :=
  LeanPhy.Condensed.bdg_trace eps Delta
example (eps Delta : ℂ) :
    Matrix.det (LeanPhy.Condensed.bdg eps Delta) = -(eps ^ 2 + Delta ^ 2) :=
  LeanPhy.Condensed.bdg_det eps Delta

-- H = eps sigma_z + Delta sigma_x
example (eps Delta : ℂ) :
    LeanPhy.Condensed.bdg eps Delta = eps • pauliZ + Delta • pauliX :=
  LeanPhy.Condensed.bdg_eq_pauli eps Delta

-- Bogoliubov invariance: a rotation of a Majorana pair preserves g^2 = 1
example (P : LeanPhy.Condensed.CliffordPair) (c s : ℂ) (h : c * c + s * s = 1) :
    (c • P.g1 + s • P.g2) * (c • P.g1 + s • P.g2) = 1 :=
  LeanPhy.Condensed.CliffordPair.bogoliubov_rotation P c s h

-- and preserves the anticommutator
example (P : LeanPhy.Condensed.CliffordPair) (c s : ℂ) :
    (c • P.g1 + s • P.g2) * ((-s) • P.g1 + c • P.g2)
      + ((-s) • P.g1 + c • P.g2) * (c • P.g1 + s • P.g2) = 0 :=
  LeanPhy.Condensed.CliffordPair.bogoliubov_anticommute P c s

-- the mean-field gap equation
example (M : LeanPhy.Condensed.MeanField) : M.gap + M.g * M.pairingAmp = 0 :=
  LeanPhy.Condensed.MeanField.gap_relation M

-- The same quadratic certificate lifts a finite table of real BdG blocks to
-- one common interval gap; a momentum continuum still needs analysis.
example : LeanPhy.Quantum.HasUniformFiniteSpectralGap
    (fun _ : Bool => LeanPhy.Condensed.bdg (1 : ℝ) 0) 0 1 := by
  apply LeanPhy.Condensed.bdg_uniform_finite_spectral_gap
  · norm_num
  · intro _
    norm_num

/-! ## Quantum channels and finite POVMs -/

-- trace preservation: sum_k K_k† K_k = 1 implies tr (Lambda rho) = tr rho
example {n : Nat} {i : Type} [Fintype i] (K : i → Operator n) (rho : State n)
    (htp : (∑ k, Matrix.conjTranspose (K k) * K k) = 1) :
    Matrix.trace (applyKraus K rho) = Matrix.trace rho :=
  kraus_trace K rho htp

-- Schrödinger and Heisenberg pictures have the same finite trace pairing.
example {n : Nat} {i : Type} [Fintype i] (K : i → Operator n)
    (rho : State n) (A : Operator n) :
    LeanPhy.Quantum.expectation (applyKraus K rho) A =
      LeanPhy.Quantum.expectation rho (LeanPhy.QuantumInfo.adjointKraus K A) :=
  LeanPhy.QuantumInfo.expectation_applyKraus_adjoint K rho A

-- Trace preservation makes the dual observable map unital.
example {n : Nat} {i : Type} [Fintype i] (K : i → Operator n)
    (htp : (∑ k, Matrix.conjTranspose (K k) * K k) = 1) :
    LeanPhy.QuantumInfo.adjointKraus K (1 : Operator n) = 1 :=
  LeanPhy.QuantumInfo.adjointKraus_complete K htp

-- unitality: sum_k K_k K_k† = 1 fixes the identity (the maximally mixed state)
example {n : Nat} {i : Type} [Fintype i] (K : i → Operator n)
    (hu : (∑ k, K k * Matrix.conjTranspose (K k)) = 1) :
    applyKraus K (1 : State n) = 1 :=
  kraus_unital K hu

-- composition: applying K then L is the Kraus family (j, k) |-> L_j K_k
example {n : Nat} {i J : Type} [Fintype i] [Fintype J]
    (K : i → Operator n) (L : J → Operator n) (rho : State n) :
    applyKraus L (applyKraus K rho) = applyKraus (fun q : J × i => L q.1 * K q.2) rho :=
  kraus_comp K L rho

-- the amplitude-damping channel is trace preserving exactly when c² + s² = 1
example (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (rho : State 2) :
    Matrix.trace (applyKraus (ampDamp c s) rho) = Matrix.trace rho :=
  ampDamp_trace c s h rho

-- the depolarising channel at p = 3/4 is total decoherence to I/2
example (rho : State 2) : depolarizing (3 / 4) rho = (1 / 2 : ℂ) • (1 : State 2) :=
  depolarizing_max rho

-- a finite POVM carries positivity and completeness as fields
example (rho : State 2) :
    LeanPhy.QuantumInfo.weight LeanPhy.QuantumInfo.computationalQubit rho 0 +
        LeanPhy.QuantumInfo.weight LeanPhy.QuantumInfo.computationalQubit rho 1 =
      Matrix.trace rho :=
  LeanPhy.QuantumInfo.computationalQubit_weight_sum rho

example (rho : State 2) (hrho : LeanPhy.Quantum.IsDensity rho) :
    (∑ i : Fin 2, LeanPhy.QuantumInfo.weight
      LeanPhy.QuantumInfo.computationalQubit rho i) = 1 :=
  LeanPhy.QuantumInfo.weight_sum_is_one LeanPhy.QuantumInfo.computationalQubit rho hrho

example (rho : State 2) (hrho : LeanPhy.Quantum.IsDensity rho) :
    (∑ i : Fin 2, LeanPhy.QuantumInfo.probability
      LeanPhy.QuantumInfo.computationalQubit rho i) = 1 :=
  LeanPhy.QuantumInfo.probability_sum_is_one LeanPhy.QuantumInfo.computationalQubit rho hrho

example (rho : State 2) (hrho : LeanPhy.Quantum.IsDensity rho) :
    (∑ i : Fin 2,
      (LeanPhy.QuantumInfo.POVM.toFiniteDistribution
        LeanPhy.QuantumInfo.computationalQubit rho hrho).weight i) = 1 := by
  exact LeanPhy.QuantumInfo.probability_sum_is_one
    LeanPhy.QuantumInfo.computationalQubit rho hrho

example (rho : State 2) (hrho : LeanPhy.Quantum.IsDensity rho) (i : Fin 2) :
    0 ≤ LeanPhy.QuantumInfo.probability
      LeanPhy.QuantumInfo.computationalQubit rho i :=
  LeanPhy.QuantumInfo.probability_nonneg LeanPhy.QuantumInfo.computationalQubit rho hrho i

example {n : Nat} {ι : Type} [Fintype ι]
    (I : LeanPhy.QuantumInfo.KrausInstrument n ι)
    (rho : State n) (_hrho : LeanPhy.Quantum.IsDensity rho) (i : ι) :
    Matrix.trace (LeanPhy.QuantumInfo.outcomeState I rho i) =
      LeanPhy.QuantumInfo.weight (LeanPhy.QuantumInfo.toPOVM I) rho i :=
  LeanPhy.QuantumInfo.outcomeState_trace I rho i

example {n : Nat} {ι : Type} [Fintype ι]
    (I : LeanPhy.QuantumInfo.KrausInstrument n ι)
    (rho : State n) (hrho : LeanPhy.Quantum.IsDensity rho) (i : ι)
    (hi : 0 < LeanPhy.QuantumInfo.probability
      (LeanPhy.QuantumInfo.toPOVM I) rho i) :
    LeanPhy.Quantum.IsDensity (LeanPhy.QuantumInfo.conditionalState I rho i) :=
  LeanPhy.QuantumInfo.conditionalState_isDensity I rho hrho i hi

/-! ## Lattice gauge theory: Wilson loops -/

-- gauge covariance of the loop product: W |-> g W g⁻¹
example {G : Type} [Group G] (g U : Fin 4 → G) :
    loopProduct (gaugeTransform g U) = g 0 * loopProduct U * (g 0)⁻¹ :=
  loop_conj g U

-- The same plaquette is an instance of the generic endpoint-indexed path API.
example {G : Type} [Group G] (U : Fin 4 → G) :
    LeanPhy.Mathematics.FinitePath.transport
        (LeanPhy.GaugeTheory.plaquetteLink U)
        LeanPhy.GaugeTheory.plaquettePath = loopProduct U :=
  LeanPhy.GaugeTheory.plaquette_transport_eq_loopProduct U

-- Open-path transport transforms at its two endpoints, independently of the
-- number of edges or the physical interpretation of the graph.
example {V G : Type} [Group G] (g : V → G) (link : V → V → G)
    {x y : V} (p : LeanPhy.Mathematics.FinitePath V x y) :
    LeanPhy.Mathematics.FinitePath.transport
        (LeanPhy.Mathematics.FinitePath.gaugeLink g link) p =
      g x * LeanPhy.Mathematics.FinitePath.transport link p * (g y)⁻¹ :=
  LeanPhy.Mathematics.FinitePath.transport_gauge g link p

-- Any closed path is gauge invariant after applying a class function (for
-- example a trace in a representation); the abelian case is a specialisation.
example {V G R : Type} [Group G] (f : G → R)
    (hf : ∀ a b : G, f (a * b * a⁻¹) = f b)
    (g : V → G) (link : V → V → G) {x : V}
    (p : LeanPhy.Mathematics.FinitePath V x x) :
    f (LeanPhy.Mathematics.FinitePath.transport
        (LeanPhy.Mathematics.FinitePath.gaugeLink g link) p) =
      f (LeanPhy.Mathematics.FinitePath.transport link p) :=
  LeanPhy.Mathematics.FinitePath.classFunction_transport_invariant
    f hf g link p

example {V G : Type} [CommGroup G] (g : V → G) (link : V → V → G)
    {x : V} (p : LeanPhy.Mathematics.FinitePath V x x) :
    LeanPhy.Mathematics.FinitePath.transport
        (LeanPhy.Mathematics.FinitePath.gaugeLink g link) p =
      LeanPhy.Mathematics.FinitePath.transport link p :=
  LeanPhy.Mathematics.FinitePath.abelian_transport_invariant g link p

/-! ## Shared finite-approximation and residual certificates -/

-- Truncation and discretisation errors compose by the checked triangle
-- inequality.  Decimal-looking bounds are exact rational reals here.
example (x y z : ℝ)
    (hxy : ErrorCertificate x y (1 / 10 : ℝ))
    (hyz : ErrorCertificate y z (1 / 5 : ℝ)) :
    ErrorCertificate x z (3 / 10 : ℝ) := by
  have h := ErrorCertificate.trans hxy hyz
  convert h using 1 <;> norm_num

-- Independent operator/field errors add in any seminormed additive group.
example (a b c d : ℝ)
    (hab : ErrorCertificate a b (1 / 10 : ℝ))
    (hcd : ErrorCertificate c d (1 / 5 : ℝ)) :
    ErrorCertificate (a + c) (b + d) (3 / 10 : ℝ) := by
  have h := ErrorCertificate.add hab hcd
  convert h using 1 <;> norm_num

-- A supplied stability/Lipschitz certificate transports a finite-volume or
-- finite-basis error to an observable without claiming convergence.
example (x y : ℝ) (hxy : ErrorCertificate x y (1 / 10 : ℝ)) :
    ErrorCertificate (x + 1) (y + 1) (1 / 10 : ℝ) := by
  have hL : ErrorCertificate.LipschitzCertificate (fun t : ℝ => t + 1) 1 := by
    refine ⟨by norm_num, ?_⟩
    intro a b
    simpa [add_comm] using (show dist a b ≤ (1 : ℝ) * dist a b from le_rfl)
  exact ErrorCertificate.map hL (by simpa using hxy)

-- A residual is a bound against zero; exact algebraic equations are the
-- radius-zero special case, while numerical/PDE residuals require a supplied
-- positive radius.
example (r : ℝ) (h : r = 0) :
    ErrorCertificate.ResidualCertificate r (0 : ℝ) :=
  ErrorCertificate.residual_zero r h

-- Domain vocabulary aliases all point to the same checked certificate, so a
-- lattice, band, mode, ODE or thermal-volume adapter can share composition
-- and stability lemmas without duplicating the proof kernel.
example (x y : ℝ) (h : LeanPhy.Quantum.StateTruncation x y (1 / 10 : ℝ)) :
    LeanPhy.Condensed.BandTruncation x y (1 / 10 : ℝ) := h

example (r : ℝ) (h : r = 0) :
    LeanPhy.GaugeTheory.GaugeResidual r (0 : ℝ) :=
  LeanPhy.Mathematics.ErrorCertificate.residual_zero r h

-- Additive transport covers angle-valued phases and discrete fluxes with the
-- same endpoint telescoping proof.
example {V A : Type} [AddCommGroup A] (g : V → A) (link : V → V → A)
    {x : V} (p : LeanPhy.Mathematics.FinitePath V x x) :
    LeanPhy.Mathematics.AdditivePath.transport
        (LeanPhy.Mathematics.AdditivePath.gaugeLink g link) p =
      LeanPhy.Mathematics.AdditivePath.transport link p :=
  LeanPhy.Mathematics.AdditivePath.closed_gauge_invariant g link p

example {A : Type} [AddCommGroup A] (g U : Fin 4 → A) :
    LeanPhy.Mathematics.AdditivePath.transport
        (LeanPhy.Mathematics.AdditivePath.gaugeLink g
          (LeanPhy.GaugeTheory.plaquetteAdditiveLink U))
        LeanPhy.GaugeTheory.plaquettePath = LeanPhy.GaugeTheory.plaquetteFlux U :=
  LeanPhy.GaugeTheory.plaquette_additive_transport_gauge_invariant g U

-- A finite surrogate and its reconstructed target may live in different
-- types.  The decoder and the metric bound are explicit at the bridge.
example {Y : Type} [PseudoMetricSpace Y]
    (decode : Y → ℝ) (x : ℝ) (y : Y) (ε : ℝ)
    (C : LeanPhy.Mathematics.CrossSpaceApproximation decode x y ε) :
    LeanPhy.Mathematics.FiniteApproximation x (decode y) ε :=
  C.toFiniteApproximation

-- A stable observable can be applied after reconstruction without silently
-- identifying the discrete and target representation types.
example {Y : Type} [PseudoMetricSpace Y]
    (decode : Y → ℝ) (x : ℝ) (y : Y) (f : ℝ → ℝ) (L ε : ℝ)
    (hf : ErrorCertificate.LipschitzCertificate f L)
    (C : LeanPhy.Mathematics.CrossSpaceApproximation decode x y ε) :
    ErrorCertificate (f x) (f (decode y)) (L * ε) :=
  C.map hf

-- Two reconstruction stages compose only with an explicit stability bound for
-- the first decoder; this is the finite analogue of a discretisation chain.
example {Y Z : Type} [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (decodeXY : Y → ℝ) (decodeYZ : Z → Y)
    (x : ℝ) (y : Y) (z : Z) (ε δ L : ℝ)
    (first : LeanPhy.Mathematics.CrossSpaceApproximation decodeXY x y ε)
    (second : LeanPhy.Mathematics.CrossSpaceApproximation decodeYZ y z δ)
    (stable : ErrorCertificate.LipschitzCertificate decodeXY L) :
    LeanPhy.Mathematics.CrossSpaceApproximation
      (decodeXY ∘ decodeYZ) x z (ε + L * δ) :=
  first.compose second stable

example {Y : Type} [PseudoMetricSpace Y]
    (B : LeanPhy.Mathematics.ReconstructionBridge ℝ Y) (x : ℝ) :
    LeanPhy.Mathematics.CrossSpaceApproximation B.decode x (B.encode x) 0 :=
  B.exact x

-- The discrete cochain complex proves d1(d0 phi) = 0 on every triangle.
example {V A : Type} [AddCommGroup A]
    (phi : LeanPhy.Mathematics.DiscreteCochain.Cochain0 V A)
    (x y z : V) :
    LeanPhy.Mathematics.DiscreteCochain.d1
      (fun i j => LeanPhy.Mathematics.DiscreteCochain.d0 phi i j) x y z = 0 :=
  LeanPhy.Mathematics.DiscreteCochain.d1_d0 phi x y z

-- Discrete Maxwell curvature and its Berry-mesh counterpart are the same
-- gauge-invariant cochain theorem under different domain names.
example {V A : Type} [AddCommGroup A]
    (potential : LeanPhy.Mathematics.DiscreteCochain.Cochain1 V A)
    (chi : LeanPhy.Mathematics.DiscreteCochain.Cochain0 V A) (x y z : V) :
    LeanPhy.GaugeTheory.discreteFieldStrength
      (LeanPhy.Mathematics.DiscreteCochain.gaugeShift potential chi) x y z =
      LeanPhy.GaugeTheory.discreteFieldStrength potential x y z :=
  LeanPhy.GaugeTheory.discreteFieldStrength_gauge_invariant potential chi x y z

example {V A : Type} [AddCommGroup A]
    (phase : LeanPhy.Mathematics.DiscreteCochain.Cochain1 V A)
    (gauge : LeanPhy.Mathematics.DiscreteCochain.Cochain0 V A) (x y z : V) :
    LeanPhy.Condensed.discreteBerryCurvature
      (LeanPhy.Mathematics.DiscreteCochain.gaugeShift phase gauge) x y z =
      LeanPhy.Condensed.discreteBerryCurvature phase x y z :=
  LeanPhy.Condensed.discreteBerryCurvature_gauge_invariant phase gauge x y z

-- A finite cyclic mesh has a gauge-invariant total flux whenever its step is
-- a permutation; this is the algebraic seed for winding certificates.
example {V A : Type} [Fintype V] [AddCommGroup A]
    (g link : V → A) (step : Equiv.Perm V) :
    LeanPhy.Mathematics.DiscreteCochain.cycleSum
        (LeanPhy.Mathematics.DiscreteCochain.cycleGauge g link step) =
      LeanPhy.Mathematics.DiscreteCochain.cycleSum link :=
  LeanPhy.Mathematics.DiscreteCochain.cycleGauge_sum_invariant g link step

example {V A : Type} [AddCommGroup A]
    (velocity : LeanPhy.Mathematics.DiscreteCochain.Cochain1 V A)
    (potential : LeanPhy.Mathematics.DiscreteCochain.Cochain0 V A) (x y z : V) :
    LeanPhy.Classical.discreteVorticity
      (LeanPhy.Mathematics.DiscreteCochain.gaugeShift velocity potential) x y z =
      LeanPhy.Classical.discreteVorticity velocity x y z :=
  LeanPhy.Classical.discreteVorticity_potential_shift velocity potential x y z

-- An integer lift of a phase/flux/circulation has a finite winding certificate;
-- integer gauge coboundaries preserve the claimed value.
example {V : Type} [Fintype V] (g link : V → ℤ) (step : Equiv.Perm V)
    (w : ℤ)
    (h : LeanPhy.Mathematics.DiscreteCochain.WindingCertificate link step w) :
    LeanPhy.Mathematics.DiscreteCochain.WindingCertificate
      (LeanPhy.Mathematics.DiscreteCochain.integerGauge g link step) step w :=
  LeanPhy.Mathematics.DiscreteCochain.WindingCertificate.gauge_invariant h

example :
    LeanPhy.Mathematics.DiscreteCochain.integerWinding
      (fun _ : Fin 4 => (1 : ℤ)) = 4 := by
  simp [LeanPhy.Mathematics.DiscreteCochain.integerWinding,
    LeanPhy.Mathematics.DiscreteCochain.cycleSum]

-- A finite-mesh Berry phase is the same Abelian closed-path product.  The
-- curvature integral and patching data are intentionally separate obligations.
example {V G : Type} [CommGroup G] (g : V → G) (phase : V → V → G)
    {x : V} (p : LeanPhy.Mathematics.FinitePath V x x) :
    LeanPhy.Condensed.discreteBerryHolonomy
        (LeanPhy.Mathematics.FinitePath.gaugeLink g phase) p =
      LeanPhy.Condensed.discreteBerryHolonomy phase p :=
  LeanPhy.Condensed.discreteBerryHolonomy_gauge_invariant g phase p

-- In a finite matrix representation, taking the trace removes the conjugation
-- provided the gauge matrix is explicitly invertible.
example {n : Type} [Fintype n] [DecidableEq n]
    (g W : Matrix n n ℂ) (hg : IsUnit g) :
    Matrix.trace (g * W * g⁻¹) = Matrix.trace W :=
  LeanPhy.GaugeTheory.matrix_trace_conjugate g W hg

example {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin 4 → LeanPhy.Mathematics.PhysicsDerivation R A)
    (potential : Fin 4 → A) (chi : A)
    (hcomm : ∀ mu nu, LeanPhy.Mathematics.derivationCommutator (D mu) (D nu) = 0)
    (mu nu : Fin 4) :
    LeanPhy.GaugeTheory.abelianFieldStrength D
        (fun k => potential k + D k chi) mu nu =
      LeanPhy.GaugeTheory.abelianFieldStrength D potential mu nu :=
  LeanPhy.GaugeTheory.abelianFieldStrength_gauge_invariant D potential chi hcomm mu nu

example {A : Type} [Ring A] (C : LeanPhy.GaugeTheory.YangMillsConnection A)
    (mu nu rho : Fin 4) :
    C.covariantDerivative mu (C.curvature nu rho) +
        C.covariantDerivative nu (C.curvature rho mu) +
        C.covariantDerivative rho (C.curvature mu nu) = 0 :=
  C.bianchi mu nu rho

example {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin 4 → LeanPhy.Mathematics.PhysicsDerivation R A)
    (potential : Fin 4 → A)
    (hcomm : ∀ mu nu, LeanPhy.Mathematics.derivationCommutator (D mu) (D nu) = 0)
    (mu nu rho : Fin 4) :
    D mu (LeanPhy.GaugeTheory.abelianFieldStrength D potential nu rho) +
        D nu (LeanPhy.GaugeTheory.abelianFieldStrength D potential rho mu) +
        D rho (LeanPhy.GaugeTheory.abelianFieldStrength D potential mu nu) = 0 :=
  LeanPhy.GaugeTheory.abelianFieldStrength_bianchi D potential hcomm mu nu rho

-- for an abelian gauge group the Wilson loop is gauge invariant
example {G : Type} [CommGroup G] (g U : Fin 4 → G) :
    loopProduct (gaugeTransform g U) = loopProduct U :=
  wilson_loop_invariant g U

-- the plaquette flux is gauge invariant: the gauge-parameter endpoints cancel
example {A : Type} [AddCommGroup A] (g U : Fin 4 → A) :
    plaquetteFlux (fluxGauge g U) = plaquetteFlux U :=
  plaquette_flux_gauge_invariant g U

-- a concrete finite-field witness over ZMod 7, evaluated by the kernel
example : plaquetteFlux (fluxGauge (fun _ => (5 : ZMod 7)) (fun _ => (1 : ZMod 7))) = 4 := by
  decide

/-! ## Coupled spins: the Clebsch-Gordan decomposition 1/2 ⊗ 1/2 = 0 ⊕ 1 -/

example : commutator JtotX JtotY = Complex.I • JtotZ := JtotX_commutator_JtotY
example : JtotSq * JtotSq = (2 : ℂ) • JtotSq := JtotSq_char
example : JtotSq.mulVec singletVec = 0 := singlet_JtotSq

/-! ## End-to-end worked example: the harmonic oscillator -/

-- the ladder identity as an abstract ring theorem, CCR as hypothesis
example {A : Type} [Ring A] (a adag : A) (h : commutator a adag = 1) :
    commutator (adag * a) adag = adag := number_ladder a adag h

-- the same statement read off a concrete two-level truncation
example : truncN = truncAdag * truncA := truncN_eq
example : truncN * truncAdag - truncAdag * truncN = truncAdag := truncN_ladder
example : truncN.mulVec (|(1 : Fin 2)⟩ : Ket 2) = (|(1 : Fin 2)⟩ : Ket 2) :=
  truncN_on_state
example : truncAdag.mulVec (|(0 : Fin 2)⟩ : Ket 2) = (|(1 : Fin 2)⟩ : Ket 2) :=
  truncAdag_on_state

/-! ## Topological band structure: two-band Bloch Hamiltonians -/

-- the Bloch Hamiltonian is the Pauli decomposition d1 sigma_x + d2 sigma_y + d3 sigma_z
example (d1 d2 d3 : ℂ) :
    LeanPhy.Condensed.bloch d1 d2 d3 = d1 • pauliX + d2 • pauliY + d3 • pauliZ :=
  LeanPhy.Condensed.bloch_eq_pauli d1 d2 d3

-- H² = (d . d) 1: the spectrum is the symmetric pair ± sqrt (d . d)
example (d1 d2 d3 : ℂ) :
    LeanPhy.Condensed.bloch d1 d2 d3 * LeanPhy.Condensed.bloch d1 d2 d3
      = LeanPhy.Condensed.blochNorm d1 d2 d3 • (1 : Operator 2) :=
  LeanPhy.Condensed.bloch_sq d1 d2 d3

-- complex gap closing is the bilinear determinant criterion; the real
-- Hermitian specialization is the origin criterion
example (d1 d2 d3 : ℂ) :
    Matrix.det (LeanPhy.Condensed.bloch d1 d2 d3) = 0 ↔ LeanPhy.Condensed.blochNorm d1 d2 d3 = 0 :=
  LeanPhy.Condensed.bloch_gap_closed_iff d1 d2 d3

-- chiral (sublattice) symmetry when d3 = 0: sigma_z H sigma_z = -H
example (d1 d2 : ℂ) :
    pauliZ * LeanPhy.Condensed.bloch d1 d2 0 = -(LeanPhy.Condensed.bloch d1 d2 0 * pauliZ) :=
  LeanPhy.Condensed.bloch_chiral_symmetry d1 d2

-- A finite spectral gap is recorded by an explicit two-sided resolvent witness.
example : LeanPhy.Quantum.HasFiniteResolvent
    (LeanPhy.Condensed.bloch 0 0 1) 0 := by
  refine ⟨LeanPhy.Condensed.bloch 0 0 1, ?_, ?_⟩
  · simpa [LeanPhy.Condensed.blochNorm] using
      LeanPhy.Condensed.bloch_sq 0 0 1
  · simpa [LeanPhy.Condensed.blochNorm] using
      LeanPhy.Condensed.bloch_sq 0 0 1

-- Unitary changes of Bloch/BdG basis preserve the resolvent condition exactly.
example (U : LeanPhy.Quantum.FiniteUnitary (Fin 2)) :
    LeanPhy.Quantum.IsFiniteSpectralGap (U.conjugate pauliZ) 0 1 ↔
      LeanPhy.Quantum.IsFiniteSpectralGap pauliZ 0 1 :=
  U.conjugate_isFiniteSpectralGap_iff pauliZ 0 1

-- Over real Bloch coefficients, zero determinant is exactly the origin;
-- complex coefficients require the weaker bilinear-square criterion.
example : (LeanPhy.Condensed.bloch (0 : ℝ) 0 1).det ≠ 0 := by
  intro h
  have hz := (LeanPhy.Condensed.bloch_real_det_zero_iff 0 0 1).mp h
  norm_num at hz

example : LeanPhy.Condensed.blochNorm 1 Complex.I 0 = 0 ∧
    LeanPhy.Condensed.bloch 1 Complex.I 0 ≠ 0 :=
  LeanPhy.Condensed.bloch_complex_null_counterexample

-- A common radius for a finite momentum/flavor family is a separate
-- certificate from pointwise invertibility.
example : LeanPhy.Quantum.HasUniformFiniteSpectralGap
    (fun _ : Bool => (pauliZ : Operator 2)) 0 1 := by
  apply LeanPhy.Quantum.hasUniformFiniteSpectralGap_of_square
    (q := fun _ : Bool => (1 : ℝ))
  · intro _
    exact pauliZHermitian
  · intro _
    simpa [identity] using pauliZ_sq
  · norm_num
  · intro _
    norm_num

example (U : Bool → LeanPhy.Quantum.FiniteUnitary (Fin 2)) :
    LeanPhy.Quantum.HasUniformFiniteSpectralGap
        (fun k => (U k).conjugate (pauliZ : Operator 2)) 0 1 ↔
      LeanPhy.Quantum.HasUniformFiniteSpectralGap
        (fun _ : Bool => (pauliZ : Operator 2)) 0 1 :=
  LeanPhy.Quantum.uniform_conjugate_isFiniteSpectralGap_iff U
    (fun _ : Bool => (pauliZ : Operator 2)) 0 1

example : LeanPhy.Quantum.HasUniformFiniteSpectralGap
    (fun _ : Bool => LeanPhy.Condensed.bloch (0 : ℝ) 0 1) 0 1 := by
  apply LeanPhy.Condensed.bloch_real_uniform_finite_spectral_gap
  · norm_num
  · intro _
    norm_num

/-! ## Scattering kinematics: the Mandelstam identity s + t + u = Σ m² -/

-- off shell: the defect is 2 p1 . (p1 + p2 - p3 - p4)
example (p1 p2 p3 p4 : Fin 4 → ℂ) :
    LeanPhy.HighEnergy.minkowskiDot (p1 + p2) (p1 + p2)
        + LeanPhy.HighEnergy.minkowskiDot (p1 - p3) (p1 - p3)
        + LeanPhy.HighEnergy.minkowskiDot (p1 - p4) (p1 - p4)
      - (LeanPhy.HighEnergy.minkowskiDot p1 p1 + LeanPhy.HighEnergy.minkowskiDot p2 p2
          + LeanPhy.HighEnergy.minkowskiDot p3 p3 + LeanPhy.HighEnergy.minkowskiDot p4 p4)
      = 2 * LeanPhy.HighEnergy.minkowskiDot p1 (p1 + p2 - p3 - p4) :=
  LeanPhy.HighEnergy.mandelstam_defect p1 p2 p3 p4

-- on shell (p1 + p2 = p3 + p4): s + t + u = m₁² + m₂² + m₃² + m₄²
example (p1 p2 p3 p4 : Fin 4 → ℂ) (h : p1 + p2 - p3 - p4 = 0) :
    LeanPhy.HighEnergy.minkowskiDot (p1 + p2) (p1 + p2)
        + LeanPhy.HighEnergy.minkowskiDot (p1 - p3) (p1 - p3)
        + LeanPhy.HighEnergy.minkowskiDot (p1 - p4) (p1 - p4)
      = LeanPhy.HighEnergy.minkowskiDot p1 p1 + LeanPhy.HighEnergy.minkowskiDot p2 p2
        + LeanPhy.HighEnergy.minkowskiDot p3 p3 + LeanPhy.HighEnergy.minkowskiDot p4 p4 :=
  LeanPhy.HighEnergy.mandelstam p1 p2 p3 p4 h

/-! ## Statistical mechanics: the Ising transfer matrix -/

-- T = c I + s sigma_x
example (c s : ℂ) :
    LeanPhy.StatMech.isingTransferMatrix c s = c • (1 : Operator 2) + s • pauliX :=
  LeanPhy.StatMech.isingTransferMatrix_eq_pauli c s

-- composition: transfer matrices multiply to a transfer matrix (rapidities add)
example (c s c' s' : ℂ) :
    LeanPhy.StatMech.isingTransferMatrix c s * LeanPhy.StatMech.isingTransferMatrix c' s'
      = LeanPhy.StatMech.isingTransferMatrix (c * c' + s * s') (c * s' + s * c') :=
  LeanPhy.StatMech.isingTransferMatrix_mul c s c' s'

-- characteristic polynomial: T² - 2 c T + (c² - s²) I = 0, so the spectrum is {c+s, c-s}
example (c s : ℂ) :
    LeanPhy.StatMech.isingTransferMatrix c s * LeanPhy.StatMech.isingTransferMatrix c s
        - (2 * c) • LeanPhy.StatMech.isingTransferMatrix c s
        + (c * c - s * s) • (1 : Operator 2) = 0 :=
  LeanPhy.StatMech.isingTransferMatrix_charpoly c s

-- the two-site partition function tr (T²) = 2 (c² + s²)
example (c s : ℂ) :
    Matrix.trace (LeanPhy.StatMech.isingTransferMatrix c s * LeanPhy.StatMech.isingTransferMatrix c s)
      = 2 * (c * c + s * s) :=
  LeanPhy.StatMech.isingTransferMatrix_trace_sq c s

/-! Positive transfer weights feed the same finite Markov API. -/

def twoStateBoltzmannWeights : LeanPhy.StatMech.PositiveTransferMatrix Bool where
  weight := fun i j => if i = j then 2 else 1
  nonneg := by
    intro i j
    split <;> norm_num
  rowSum_pos := by
    intro i
    cases i <;> simp <;> norm_num

example (p : LeanPhy.StatMech.FiniteProbability Bool) :
    ∑ j, (twoStateBoltzmannWeights.toKernel.step p).weight j = 1 :=
  twoStateBoltzmannWeights.toKernel_preserves_probability p

example (p : LeanPhy.StatMech.FiniteProbability Bool) (f : Bool → ℝ) :
    (twoStateBoltzmannWeights.toKernel.step p).expectation f =
      p.expectation (twoStateBoltzmannWeights.toKernel.pullback f) :=
  twoStateBoltzmannWeights.toKernel_expectation_duality p f

/-! ## Finite probability shared by statistical and measurement models -/

example (p : LeanPhy.StatMech.FiniteDistribution 3) :
    p.expectation (fun _ => 1) = 1 :=
  LeanPhy.StatMech.FiniteDistribution.expectation_one p

example (p : LeanPhy.StatMech.FiniteDistribution 3) (f : Fin 3 → ℝ) :
    0 ≤ p.variance f :=
  LeanPhy.StatMech.FiniteDistribution.variance_nonneg p f

example (p : LeanPhy.StatMech.FiniteDistribution 3) (f : Fin 3 → ℝ) :
    0 ≤ p.secondMoment f :=
  LeanPhy.StatMech.FiniteDistribution.secondMoment_nonneg p f

example (p : LeanPhy.StatMech.FiniteDistribution 3) :
    0 ≤ p.collisionProbability ∧ p.collisionProbability ≤ 1 :=
  ⟨LeanPhy.StatMech.FiniteDistribution.collisionProbability_nonneg p,
    LeanPhy.StatMech.FiniteDistribution.collisionProbability_le_one p⟩

example (p : LeanPhy.StatMech.FiniteDistribution 3) :
    p.collisionProbability = p.expectation p.weight :=
  LeanPhy.StatMech.FiniteDistribution.collisionProbability_eq_expectation_weight p

example :
  (LeanPhy.StatMech.uniformDistribution 4 (by decide)).collisionProbability =
      (4 : ℝ)⁻¹ :=
  LeanPhy.StatMech.FiniteDistribution.collisionProbability_uniform (n := 4) (by decide)

example {d n : Nat} (M : LeanPhy.QuantumInfo.POVM d (Fin n))
    (rho : LeanPhy.Quantum.State d) (hrho : LeanPhy.Quantum.IsDensity rho) :
    (M.toFiniteDistribution rho hrho).collisionProbability =
      ∑ i, LeanPhy.QuantumInfo.probability M rho i ^ 2 :=
  LeanPhy.QuantumInfo.POVM.measurement_collisionProbability M rho hrho

/-! Finite Markov kernels: normalization, composition, and stationary uniform
measure for the doubly-stochastic case. -/
example {n : Nat} (K L : LeanPhy.StatMech.FiniteMarkovKernel n)
    (p : LeanPhy.StatMech.FiniteDistribution n) :
    LeanPhy.StatMech.stepDistribution L (LeanPhy.StatMech.stepDistribution K p) =
      LeanPhy.StatMech.stepDistribution (LeanPhy.StatMech.compose K L) p :=
  LeanPhy.StatMech.compose_step K L p

example {n : Nat} (hn : 0 < n)
    (K : LeanPhy.StatMech.DoublyStochasticKernel n) :
    LeanPhy.StatMech.stepDistribution K.toFiniteMarkovKernel
        (LeanPhy.StatMech.uniformDistribution n hn) =
      LeanPhy.StatMech.uniformDistribution n hn :=
  LeanPhy.StatMech.doubly_stochastic_uniform hn K

example {n : Nat} (K : LeanPhy.StatMech.FiniteMarkovKernel n)
    (p : LeanPhy.StatMech.FiniteDistribution n) (f : Fin n → ℝ) :
    (LeanPhy.StatMech.stepDistribution K p).expectation f =
      p.expectation (LeanPhy.StatMech.pullbackObservable K f) :=
  LeanPhy.StatMech.step_expectation K p f

/-! ## Continuum gauge field strength and the Bianchi identity -/

-- F_{mu nu} = [D_mu, D_nu] is antisymmetric
example {A : Type} [Ring A] (D : Fin 4 → A) (mu nu : Fin 4) :
    LeanPhy.GaugeTheory.fieldStrength D mu nu = -LeanPhy.GaugeTheory.fieldStrength D nu mu :=
  LeanPhy.GaugeTheory.fieldStrength_antisym D mu nu

-- the algebraic Bianchi identity: the cyclic sum of [F, D] vanishes
example {A : Type} [Ring A] (D : Fin 4 → A) (mu nu rho : Fin 4) :
    LeanPhy.GaugeTheory.fieldStrength D mu nu * D rho
        + LeanPhy.GaugeTheory.fieldStrength D nu rho * D mu
        + LeanPhy.GaugeTheory.fieldStrength D rho mu * D nu
      = D rho * LeanPhy.GaugeTheory.fieldStrength D mu nu
        + D mu * LeanPhy.GaugeTheory.fieldStrength D nu rho
        + D nu * LeanPhy.GaugeTheory.fieldStrength D rho mu :=
  LeanPhy.GaugeTheory.bianchi D mu nu rho

/-! ## Spinor covariants: the antisymmetric tensor sigma^{mu nu} -/

-- sigma^{mu nu} = (i/2)[gamma^mu, gamma^nu] is antisymmetric
example (mu nu : Fin 4) :
    LeanPhy.HighEnergy.sigma nu mu = -LeanPhy.HighEnergy.sigma mu nu :=
  LeanPhy.HighEnergy.sigma_antisym mu nu

-- it vanishes on the diagonal
example (mu : Fin 4) : LeanPhy.HighEnergy.sigma mu mu = 0 :=
  LeanPhy.HighEnergy.sigma_self mu

-- gamma^5 commutes with sigma^{mu nu}: the tensor is a genuine Lorentz covariant
example (mu nu : Fin 4) :
    gamma5 * LeanPhy.HighEnergy.sigma mu nu = LeanPhy.HighEnergy.sigma mu nu * gamma5 :=
  LeanPhy.HighEnergy.gamma5_commute_sigma mu nu

/-! ## Standard Model anomaly cancellation -/

-- all four anomaly coefficients vanish for one generation, by kernel evaluation over Q
example : LeanPhy.Particles.AnomalyFree LeanPhy.Particles.smGen :=
  LeanPhy.Particles.smGen_anomalyFree

-- ... and for any number n of identical generations
example (n : Nat) : LeanPhy.Particles.AnomalyFree (LeanPhy.Particles.smContent n) :=
  LeanPhy.Particles.smContent_anomalyFree n

-- the gravitational anomaly under a uniform hypercharge shift eps is 15 eps
example (eps : ℚ) :
    LeanPhy.Particles.accGrav (LeanPhy.Particles.hyperShift LeanPhy.Particles.smGen eps) =
      15 * eps :=
  LeanPhy.Particles.smGen_accGrav_shift eps

-- so the only shift that keeps the content anomaly free is the trivial one
example (eps : ℚ)
    (h : LeanPhy.Particles.accU1cubed (LeanPhy.Particles.hyperShift LeanPhy.Particles.smGen eps) = 0) :
    eps = 0 :=
  LeanPhy.Particles.smGen_shift_rigid eps h

/-! ## SU(3) colour algebra: the QCD backbone -/

-- the Gell-Mann matrices are traceless and trace-orthonormal, tr(lam_a lam_b) = 2 delta_ab
example (a b : Fin 8) :
    (LeanPhy.Particles.gm a * LeanPhy.Particles.gm b).trace
      = 2 * LeanPhy.Particles.kdelta a b :=
  LeanPhy.Particles.gm_trace_orthonormal a b

-- the fundamental Casimir sum_a lam_a lam_a = (16/3) 1, whose coefficient is 4 C_F = 16/3
example :
    (∑ a : Fin 8, LeanPhy.Particles.gm a * LeanPhy.Particles.gm a)
      = (16 / 3 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) :=
  LeanPhy.Particles.gm_casimir

-- the SU(3) Fierz completeness relation, the identity behind colour rearrangement
example (i j k l : Fin 3) :
    (∑ a : Fin 8, LeanPhy.Particles.gm a i j * LeanPhy.Particles.gm a k l)
      = 2 * (if i = l then 1 else 0) * (if j = k then 1 else 0)
        - (2 / 3) * (if i = j then 1 else 0) * (if k = l then 1 else 0) :=
  LeanPhy.Particles.gm_fierz i j k l

-- sum_a tr(lam_a lam_a) = 16, the colour-singlet coefficient of the one-loop vacuum polarisation
example : (∑ a : Fin 8, (LeanPhy.Particles.gm a * LeanPhy.Particles.gm a).trace) = 16 :=
  LeanPhy.Particles.gm_casimir_trace

/-! ## Dirac covariants: Fierz completeness of the 16 Gamma matrices -/

-- trace orthogonality of the 16 Dirac covariants, tr(Gamma_A Gamma_B) = 4 w_A delta_AB
example (a b : Fin 16) :
    (LeanPhy.HighEnergy.cov a * LeanPhy.HighEnergy.cov b).trace
      = 4 * LeanPhy.HighEnergy.covW a * (if a = b then 1 else 0) :=
  LeanPhy.HighEnergy.cov_trace_orthonormal a b

-- Fierz completeness, entrywise: sum_A w_A (Gamma_A)_ij (Gamma_A)_kl = 4 delta_il delta_jk
example (i j k l : Fin 4) :
    (∑ a : Fin 16, LeanPhy.HighEnergy.covW a * LeanPhy.HighEnergy.cov a i j
        * LeanPhy.HighEnergy.cov a k l)
      = 4 * (if i = l then (1 : ℂ) else 0) * (if j = k then 1 else 0) :=
  LeanPhy.HighEnergy.cov_fierz i j k l

-- closure form: sum_A w_A tr(Gamma_A M) Gamma_A = 4 M for any 4x4 matrix M
example (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (∑ a : Fin 16,
        (LeanPhy.HighEnergy.covW a * (LeanPhy.HighEnergy.cov a * M).trace)
          • LeanPhy.HighEnergy.cov a)
      = (4 : ℂ) • M :=
  LeanPhy.HighEnergy.cov_fierz_expansion M

/-! ## The single-qubit Pauli group: trace orthogonality and the twirl -/

-- trace orthogonality: tr (sigma_a sigma_b) = 2 delta_ab
example (a b : Fin 4) :
    (pauli a * pauli b).trace = 2 * (if a = b then 1 else 0) :=
  pauli_trace_orthonormal a b

-- the Pauli twirl: sum_a sigma_a M sigma_a = 2 tr (M) 1, kernel-evaluated
example (M : Operator 2) :
    (∑ a : Fin 4, pauli a * M * pauli a) = (2 * M.trace) • (1 : Operator 2) :=
  pauli_twirl M

-- the normalised twirl preserves the trace
example (M : Operator 2) :
    (1 / 4 : Complex) * (∑ a : Fin 4, (pauli a * M * pauli a).trace) = M.trace :=
  pauli_twirl_trace M

-- depolarisation: (1/4) sum_a sigma_a M sigma_a = (tr M / 2) 1
example (M : Operator 2) :
    (1 / 4 : Complex) • (∑ a : Fin 4, pauli a * M * pauli a)
      = (M.trace / 2) • (1 : Operator 2) :=
  pauli_twirl_depolarise M

/-! ## CKM quark mixing: unitarity of the three-generation mixing matrix -/

-- V Vᴴ = 1 with the phase carried by a unit-modulus complex number u
example (t12 t13 t23 : Real) (u : Complex) (hu : (starRingEnd Complex) u * u = 1) :
    LeanPhy.Particles.ckm t12 t13 t23 u
      * Matrix.conjTranspose (LeanPhy.Particles.ckm t12 t13 t23 u) = 1 :=
  LeanPhy.Particles.ckm_unitary t12 t13 t23 u hu

-- the unitarity-triangle relation: rows orthonormal, sum_k V_ik (V_jk)* = delta_ij
example (t12 t13 t23 : Real) (u : Complex) (hu : (starRingEnd Complex) u * u = 1)
    (i j : Fin 3) :
    (∑ k : Fin 3, LeanPhy.Particles.ckm t12 t13 t23 u i k
        * (starRingEnd Complex) (LeanPhy.Particles.ckm t12 t13 t23 u j k))
      = if i = j then 1 else 0 :=
  LeanPhy.Particles.ckm_row_orthonormal t12 t13 t23 u hu i j

-- each rotation factor is unitary
example (c s : Real) (hc : c^2 + s^2 = 1) :
    LeanPhy.Particles.rot23 c s * Matrix.conjTranspose (LeanPhy.Particles.rot23 c s) = 1 :=
  LeanPhy.Particles.rot23_unitary c s hc

/-! ## Three-qubit GHZ nonlocality: the Mermin operator -/

-- the Mermin operator M = XYY + YXY + YYX - XXX is symmetric
example (i j : LeanPhy.QuantumInfo.Idx3) :
    LeanPhy.QuantumInfo.mermin i j = LeanPhy.QuantumInfo.mermin j i :=
  LeanPhy.QuantumInfo.mermin_symm i j

-- M (|000> + |111>) = -4 (|000> + |111>), the Mermin-GHZ eigenvalue relation
example (j : LeanPhy.QuantumInfo.Idx3) :
    (∑ i : LeanPhy.QuantumInfo.Idx3,
        LeanPhy.QuantumInfo.mermin i j * LeanPhy.QuantumInfo.ghzVec i)
      = -4 * LeanPhy.QuantumInfo.ghzVec j :=
  LeanPhy.QuantumInfo.mermin_ghz_eigen j

-- the Mermin-GHZ value: the expectation in the GHZ state is -8 (= -4 normalised)
example : LeanPhy.QuantumInfo.ghzExpect LeanPhy.QuantumInfo.mermin = -8 :=
  LeanPhy.QuantumInfo.ghzExpect_mermin

/-! ## Lorentz boosts: rapidity addition and metric invariance -/

-- boosts compose by adding rapidities
example (c1 s1 c2 s2 : Complex) :
    LeanPhy.Relativity.boost c1 s1 * LeanPhy.Relativity.boost c2 s2
      = LeanPhy.Relativity.boost (c1 * c2 + s1 * s2) (c1 * s2 + s1 * c2) :=
  LeanPhy.Relativity.boost_mul c1 s1 c2 s2

-- the Lorentz condition: c^2 - s^2 = 1 makes B^T eta B = eta
example (c s : Complex) (h : c^2 - s^2 = 1) :
    (LeanPhy.Relativity.boost c s)ᵀ * LeanPhy.Relativity.etaM
      * LeanPhy.Relativity.boost c s = LeanPhy.Relativity.etaM :=
  LeanPhy.Relativity.boost_lorentz c s h

-- a boost has determinant one, and its inverse is the negated-rapidity boost
example (c s : Complex) : (LeanPhy.Relativity.boost c s).det = c^2 - s^2 :=
  LeanPhy.Relativity.boost_det c s

example (c s : Complex) (h : c^2 - s^2 = 1) :
    LeanPhy.Relativity.boost c s * LeanPhy.Relativity.boost c (-s) = 1 :=
  LeanPhy.Relativity.boost_inv c s h

/-! ## Condensed matter: Berry curvature of a qubit -/

-- the Bloch vector is a unit vector
example (theta phi : ℝ) :
    LeanPhy.Condensed.dot3 (LeanPhy.Condensed.dhat theta phi)
      (LeanPhy.Condensed.dhat theta phi) = 1 :=
  LeanPhy.Condensed.dhat_unit theta phi

-- the Berry curvature density is the monopole field sin theta
example (theta phi : ℝ) :
    LeanPhy.Condensed.dot3 (LeanPhy.Condensed.dhat theta phi)
      (LeanPhy.Condensed.cross3 (LeanPhy.Condensed.dTheta theta phi)
        (LeanPhy.Condensed.dPhi theta phi)) = Real.sin theta :=
  LeanPhy.Condensed.berry_density theta phi

/-! ## Jordan-Wigner: a two-site fermion chain -/

-- the canonical anticommutation relation across the two sites
example :
    LeanPhy.Condensed.jwC0 * LeanPhy.Condensed.jwC1dag
      + LeanPhy.Condensed.jwC1dag * LeanPhy.Condensed.jwC0 = 0 :=
  LeanPhy.Condensed.car_zero_one

-- the hopping term is the XY spin-chain coupling
example :
    LeanPhy.Condensed.jwHop
      = (1 / 2 : ℂ) • (LeanPhy.Condensed.kron LeanPhy.Condensed.xMat LeanPhy.Condensed.xMat
          + LeanPhy.Condensed.kron LeanPhy.Condensed.yMat LeanPhy.Condensed.yMat) :=
  LeanPhy.Condensed.jwHop_eq_xy

/-! ## Angular momentum one: the spin-1 representation -/

-- the su(2) commutator on the explicit 3x3 generators
example : LeanPhy.Quantum.S1 * LeanPhy.Quantum.S2 - LeanPhy.Quantum.S2 * LeanPhy.Quantum.S1
    = Complex.I • LeanPhy.Quantum.S3 :=
  LeanPhy.Quantum.S1_commutator_S2

-- the Casimir S.S = l(l+1) 1 = 2 * 1 for l = 1
example : LeanPhy.Quantum.S1 * LeanPhy.Quantum.S1 + LeanPhy.Quantum.S2 * LeanPhy.Quantum.S2
      + LeanPhy.Quantum.S3 * LeanPhy.Quantum.S3
    = 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) :=
  LeanPhy.Quantum.spinOne_casimir

/-! ## No-cloning theorem -/

-- a linear U cloning |0> and |1> forces |00> + |11> on the superposition
example (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (b : Fin 2 → ℂ)
    (h0 : U *ᵥ LeanPhy.QuantumInfo.tv LeanPhy.QuantumInfo.e0 b
      = LeanPhy.QuantumInfo.tv LeanPhy.QuantumInfo.e0 LeanPhy.QuantumInfo.e0)
    (h1 : U *ᵥ LeanPhy.QuantumInfo.tv LeanPhy.QuantumInfo.e1 b
      = LeanPhy.QuantumInfo.tv LeanPhy.QuantumInfo.e1 LeanPhy.QuantumInfo.e1) :
    U *ᵥ LeanPhy.QuantumInfo.tv (LeanPhy.QuantumInfo.e0 + LeanPhy.QuantumInfo.e1) b
      ≠ LeanPhy.QuantumInfo.tv (LeanPhy.QuantumInfo.e0 + LeanPhy.QuantumInfo.e1)
          (LeanPhy.QuantumInfo.e0 + LeanPhy.QuantumInfo.e1) :=
  LeanPhy.QuantumInfo.no_cloning U b h0 h1

/-! ## The Lorentz algebra so(3,1) -/

-- two boosts close into a rotation (Thomas-Wigner)
example : LeanPhy.Relativity.B1 * LeanPhy.Relativity.B2
    - LeanPhy.Relativity.B2 * LeanPhy.Relativity.B1 = - LeanPhy.Relativity.R3 :=
  LeanPhy.Relativity.B1_commutator_B2

-- every generator is metric-antisymmetric: X^T eta + eta X = 0
example : (LeanPhy.Relativity.B3)ᵀ * LeanPhy.Relativity.eta4
    + LeanPhy.Relativity.eta4 * LeanPhy.Relativity.B3 = 0 :=
  LeanPhy.Relativity.metric_B3

/-! ## Three-qubit bit-flip code -/

-- the two stabilizers fix every logical code state
example (a b : Complex) :
    LeanPhy.QuantumInfo.zz1q *ᵥ LeanPhy.QuantumInfo.codeVec a b
      = LeanPhy.QuantumInfo.codeVec a b :=
by
  funext j
  exact LeanPhy.QuantumInfo.stab1_code a b j

-- the three single-qubit bit flips have distinct syndromes
example (a b : Complex) :
    LeanPhy.QuantumInfo.zz1q *ᵥ (LeanPhy.QuantumInfo.xx2q *ᵥ LeanPhy.QuantumInfo.codeVec a b)
      = - (LeanPhy.QuantumInfo.xx2q *ᵥ LeanPhy.QuantumInfo.codeVec a b) :=
  LeanPhy.QuantumInfo.xx2_syndrome1 a b

/-! ## Quantum teleportation -/

-- Bell-basis expansion of an arbitrary input qubit
example (a b : Complex) :
    LeanPhy.QuantumInfo.teleportInput a b = (1 / 2 : Complex) •
      (LeanPhy.QuantumInfo.bellTensor LeanPhy.QuantumInfo.bellPhiPlus
          (LeanPhy.QuantumInfo.telePsi a b)
        + LeanPhy.QuantumInfo.bellTensor LeanPhy.QuantumInfo.bellPhiMinus
          (LeanPhy.QuantumInfo.teleZ a b)
        + LeanPhy.QuantumInfo.bellTensor LeanPhy.QuantumInfo.bellPsiPlus
          (LeanPhy.QuantumInfo.teleX a b)
        + LeanPhy.QuantumInfo.bellTensor LeanPhy.QuantumInfo.bellPsiMinus
          (LeanPhy.QuantumInfo.teleXZ a b)) :=
  LeanPhy.QuantumInfo.teleportation_identity a b

-- the Z correction recovers the original state
example (a b : Complex) :
    LeanPhy.QuantumInfo.teleZ (LeanPhy.QuantumInfo.teleZ a b 0)
      (LeanPhy.QuantumInfo.teleZ a b 1) = LeanPhy.QuantumInfo.telePsi a b :=
  LeanPhy.QuantumInfo.teleport_correction_Z a b

/-! ## Variance-aware Lorentz contractions -/

-- lowering and raising are inverse with the explicit (+---) metric
example (x : LeanPhy.Tensor.UpVec) :
    LeanPhy.Tensor.raise (LeanPhy.Tensor.lower x) = x :=
  LeanPhy.Tensor.raise_lower x

-- the typed contraction expands to the Minkowski scalar product
example (x y : LeanPhy.Tensor.UpVec) :
    LeanPhy.Tensor.minkowski x y =
      x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3 :=
  by rw [LeanPhy.Tensor.minkowski, LeanPhy.Tensor.contractUD_lower]

-- rank-two variance tags: mixed tensors compose and have a well-typed trace
example (A : LeanPhy.Tensor.TensorUD) :
    LeanPhy.Tensor.composeMixed LeanPhy.Tensor.mixedIdentity A = A :=
  LeanPhy.Tensor.composeMixed_identity_left A

example (A B : LeanPhy.Tensor.TensorUD) :
    LeanPhy.Tensor.mixedTrace (LeanPhy.Tensor.composeMixed A B) =
      LeanPhy.Tensor.mixedTrace (LeanPhy.Tensor.composeMixed B A) :=
  LeanPhy.Tensor.mixedTrace_comp_comm A B

example {n : Nat} (A B : LeanPhy.Tensor.TensorUDN n) :
    LeanPhy.Tensor.mixedTraceN (LeanPhy.Tensor.composeMixedN A B) =
      LeanPhy.Tensor.mixedTraceN (LeanPhy.Tensor.composeMixedN B A) :=
  LeanPhy.Tensor.mixedTraceN_comp_comm A B

-- Coefficient-generic variance tensors reuse the same checked identities over
-- real, complex, rational, or other commutative coefficient models.
example {n : Nat} (A : LeanPhy.Tensor.TensorUDOver ℝ n) :
    LeanPhy.Tensor.composeMixedOver
      (LeanPhy.Tensor.mixedIdentityOver (R := ℝ) (n := n)) A = A :=
  LeanPhy.Tensor.composeMixedOver_identity_left A

example {R : Type} [CommSemiring R] {n : Nat}
    (A B : LeanPhy.Tensor.TensorUDOver R n) :
    LeanPhy.Tensor.mixedTraceOver (LeanPhy.Tensor.composeMixedOver A B) =
      LeanPhy.Tensor.mixedTraceOver (LeanPhy.Tensor.composeMixedOver B A) :=
  LeanPhy.Tensor.mixedTraceOver_comp_comm A B

example {R : Type} [CommSemiring R] {n : Nat}
    (A B : LeanPhy.Tensor.TensorUDOver R n) (v : Fin n → R) :
    LeanPhy.Tensor.actUpOver (LeanPhy.Tensor.composeMixedOver A B) v =
      LeanPhy.Tensor.actUpOver A (LeanPhy.Tensor.actUpOver B v) :=
  LeanPhy.Tensor.actUpOver_comp A B v

example {n : Nat} {c : LeanPhy.Tensor.VarianceTag}
    (v : LeanPhy.Tensor.Tensor1N n c) :
    LeanPhy.Tensor.contract12 (LeanPhy.Tensor.deltaInsert12 v) =
      ⟨fun k => (n : ℂ) * v k⟩ :=
  LeanPhy.Tensor.contract12_deltaInsert12 v

example {n : Nat} (T : LeanPhy.Tensor.TensorUDUDN n) :
    LeanPhy.Tensor.contract12_34 T = ∑ k, ∑ i, T i i k k :=
  LeanPhy.Tensor.contract12_34_swap T

/-! A finite Kraus channel preserves the full density-matrix invariant. -/
example {n : Nat} {ι : Type} [Fintype ι]
    (K : ι → LeanPhy.Quantum.Operator n) (rho : LeanPhy.Quantum.State n)
    (hrho : LeanPhy.Quantum.IsDensity rho)
    (htp : (∑ k, Matrix.conjTranspose (K k) * K k) = 1) :
    LeanPhy.Quantum.IsDensity (LeanPhy.QuantumInfo.applyKraus K rho) :=
  LeanPhy.QuantumInfo.applyKraus_isDensity K rho hrho htp

example {n : Nat} (C D : LeanPhy.QuantumInfo.FiniteChannel n) (rho : LeanPhy.Quantum.State n) :
    LeanPhy.QuantumInfo.compose C D rho = C (D rho) :=
  LeanPhy.QuantumInfo.compose_apply C D rho

example {n : Nat} (C : LeanPhy.QuantumInfo.FiniteChannel n)
    (rho sig : LeanPhy.Quantum.State n) :
    C (rho + sig) = C rho + C sig := C.map_add rho sig

example {n : Nat} {ι : Type} [Fintype ι]
    (K : ι → LeanPhy.Quantum.Operator n) :
    LeanPhy.QuantumInfo.CompletelyPositiveKraus K :=
  LeanPhy.QuantumInfo.applyKraus_completelyPositive K

example {n : Nat} {ι : Type} [Fintype ι]
    (C : LeanPhy.QuantumInfo.KrausChannel n ι)
    (rho : LeanPhy.Quantum.State n) :
    Matrix.trace (LeanPhy.QuantumInfo.applyKraus C.op rho) = Matrix.trace rho :=
  C.trace_preserving rho

example {n : Nat} {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : LeanPhy.QuantumInfo.KrausChannel n ι)
    (B : LeanPhy.QuantumInfo.KrausChannel n κ)
    (rho : LeanPhy.Quantum.State n) :
    (A.compose B).toFiniteChannel rho =
      A.toFiniteChannel (B.toFiniteChannel rho) :=
  A.compose_toFiniteChannel_apply B rho

example {n : Nat} {ι : Type} [Fintype ι]
    (C : LeanPhy.QuantumInfo.KrausChannel n ι)
    (rho : LeanPhy.Quantum.State n) (hrho : LeanPhy.Quantum.IsDensity rho) :
    LeanPhy.Quantum.IsDensity (LeanPhy.QuantumInfo.applyKraus C.op rho) :=
  C.map_isDensity rho hrho

/-! A typed rectangular channel can change the finite label space.  This is
the common adapter needed by environment embeddings, coarse graining, partial
trace witnesses and finite lattice/band reductions. -/

noncomputable def oneToQubitEmbedding :
    LeanPhy.QuantumInfo.TypedKrausChannel (Fin 1) (Fin 2) PUnit where
  op := fun _ => !![1; 0]
  complete := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ]

noncomputable def qubitToOneDiscard :
    LeanPhy.QuantumInfo.TypedKrausChannel (Fin 2) (Fin 1) (Fin 2) where
  op := fun k => if k = 0 then !![1, 0] else !![0, 1]
  complete := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ]

example (rho : Matrix (Fin 1) (Fin 1) ℂ)
    (hrho : LeanPhy.Quantum.IsFiniteDensity rho) :
    LeanPhy.Quantum.IsFiniteDensity (oneToQubitEmbedding.apply rho) :=
  oneToQubitEmbedding.map_isFiniteDensity rho hrho

example (rho : Matrix (Fin 1) (Fin 1) ℂ) :
    Matrix.trace (oneToQubitEmbedding.apply rho) = Matrix.trace rho :=
  oneToQubitEmbedding.trace_preserving rho

example (rho : Matrix (Fin 1) (Fin 1) ℂ) :
    (qubitToOneDiscard.compose oneToQubitEmbedding).apply rho =
      qubitToOneDiscard.apply (oneToQubitEmbedding.apply rho) :=
  LeanPhy.QuantumInfo.TypedKrausChannel.compose_apply
    qubitToOneDiscard oneToQubitEmbedding rho

example (rho : Matrix (Fin 1) (Fin 1) ℂ)
    (hrho : LeanPhy.Quantum.IsFiniteDensity rho) :
    LeanPhy.Quantum.IsFiniteDensity
      ((qubitToOneDiscard.compose oneToQubitEmbedding).apply rho) :=
  (qubitToOneDiscard.compose oneToQubitEmbedding).map_isFiniteDensity rho hrho

example (rho : Matrix (Fin 1) (Fin 1) ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (oneToQubitEmbedding.apply rho * A) =
      Matrix.trace (rho *
        LeanPhy.QuantumInfo.typedAdjointKraus oneToQubitEmbedding.op A) :=
  LeanPhy.QuantumInfo.typedTracePairing oneToQubitEmbedding.op rho A

example :
    LeanPhy.QuantumInfo.typedAdjointKraus
        oneToQubitEmbedding.op (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
  oneToQubitEmbedding.adjoint_unital

noncomputable example {n : Nat} [NeZero n] (β : ℝ) (E : Fin n → ℝ) :
    LeanPhy.StatMech.FiniteDistribution n :=
  LeanPhy.StatMech.gibbsDistribution β E

example {n : Nat} [NeZero n] (β c : ℝ) (E : Fin n → ℝ) (i : Fin n) :
    LeanPhy.StatMech.gibbsWeight β (fun j => E j + c) i =
      LeanPhy.StatMech.gibbsWeight β E i :=
  LeanPhy.StatMech.gibbsWeight_shift β c E i

example {n : Nat} {ι : Type} [Fintype ι]
    (H : LeanPhy.Quantum.Operator n) (L : ι → LeanPhy.Quantum.Operator n)
    (rho : LeanPhy.Quantum.State n) :
    Matrix.trace (LeanPhy.QuantumInfo.lindbladGenerator H L rho) = 0 :=
  LeanPhy.QuantumInfo.lindblad_trace_zero H L rho

/-! A concrete spin-one family now uses the generic Lie representation API. -/
example (x y : LeanPhy.Mathematics.SU2Coefficients) :
    LeanPhy.Mathematics.ringCommutator
        (LeanPhy.Mathematics.spinOneRepresentation x)
        (LeanPhy.Mathematics.spinOneRepresentation y) =
      LeanPhy.Mathematics.spinOneRepresentation
        (LeanPhy.Mathematics.su2Bracket x y) :=
  LeanPhy.Mathematics.Representation.commutator_map
    LeanPhy.Mathematics.spinOneRepresentation x y

example (a b c : Fin 6) :
    LeanPhy.Mathematics.ringCommutator
        (LeanPhy.Mathematics.lorentzGeneratorFamily a)
        (LeanPhy.Mathematics.ringCommutator
          (LeanPhy.Mathematics.lorentzGeneratorFamily b)
          (LeanPhy.Mathematics.lorentzGeneratorFamily c)) +
      LeanPhy.Mathematics.ringCommutator
        (LeanPhy.Mathematics.lorentzGeneratorFamily b)
        (LeanPhy.Mathematics.ringCommutator
          (LeanPhy.Mathematics.lorentzGeneratorFamily c)
          (LeanPhy.Mathematics.lorentzGeneratorFamily a)) +
      LeanPhy.Mathematics.ringCommutator
        (LeanPhy.Mathematics.lorentzGeneratorFamily c)
        (LeanPhy.Mathematics.ringCommutator
          (LeanPhy.Mathematics.lorentzGeneratorFamily a)
          (LeanPhy.Mathematics.lorentzGeneratorFamily b)) = 0 :=
  LeanPhy.Mathematics.matrixGeneratorFamily_jacobi
    LeanPhy.Mathematics.lorentzGeneratorFamily a b c

example (x y : LeanPhy.Mathematics.LorentzCoefficients) :
    LeanPhy.Mathematics.ringCommutator
        (LeanPhy.Mathematics.lorentzRepresentation x)
        (LeanPhy.Mathematics.lorentzRepresentation y) =
      LeanPhy.Mathematics.lorentzRepresentation
        (LeanPhy.Mathematics.lorentzBracket x y) :=
  LeanPhy.Mathematics.Representation.commutator_map
    LeanPhy.Mathematics.lorentzRepresentation x y

/-! A general finite multi-Kraus instrument preserves conditional-state validity. -/
example {n : Nat} {ι κ : Type} [Fintype ι] [Fintype κ]
    (I : LeanPhy.QuantumInfo.MultiKrausInstrument n ι κ)
    (rho : LeanPhy.Quantum.State n)
    (hrho : LeanPhy.Quantum.IsDensity rho)
    (i : ι)
    (hi : 0 < LeanPhy.QuantumInfo.probability
      (LeanPhy.QuantumInfo.multiToPOVM I) rho i) :
    LeanPhy.Quantum.IsDensity
      (LeanPhy.QuantumInfo.multiConditionalState I rho i) :=
  LeanPhy.QuantumInfo.multiConditionalState_isDensity I rho hrho i hi

/-! ## Symplectic canonical transformations -/

-- the two-dimensional symplectic condition is equivalent to determinant one
example (A : LeanPhy.Classical.M2R) :
    Aᵀ * LeanPhy.Classical.symplecticJ * A = LeanPhy.Classical.symplecticJ ↔ A.det = 1 :=
  LeanPhy.Classical.symplectic_iff_det A

-- phase-space rotations preserve dq wedge dp
example (theta : ℝ) :
    (!![Real.cos theta, -Real.sin theta; Real.sin theta, Real.cos theta] : LeanPhy.Classical.M2R)ᵀ
        * LeanPhy.Classical.symplecticJ
        * !![Real.cos theta, -Real.sin theta; Real.sin theta, Real.cos theta]
      = LeanPhy.Classical.symplecticJ :=
  LeanPhy.Classical.rotation_symplectic theta

example (theta : ℝ) (t : ℝ) :
    let R : BilinearIsometry LeanPhy.Classical.symplecticJ :=
      { op := (!![Real.cos theta, -Real.sin theta; Real.sin theta, Real.cos theta] :
          LeanPhy.Classical.M2R),
        preserve := LeanPhy.Classical.rotation_symplectic theta }
    let S : BilinearIsometry LeanPhy.Classical.symplecticJ :=
      { op := (!![1, t; 0, 1] : LeanPhy.Classical.M2R),
        preserve := LeanPhy.Classical.shear_symplectic t }
    (R.compose S).opᵀ * LeanPhy.Classical.symplecticJ * (R.compose S).op =
      LeanPhy.Classical.symplecticJ := by
  dsimp
  exact (BilinearIsometry.compose
    ({ op := (!![Real.cos theta, -Real.sin theta; Real.sin theta, Real.cos theta] :
        LeanPhy.Classical.M2R),
       preserve := LeanPhy.Classical.rotation_symplectic theta } :
      BilinearIsometry LeanPhy.Classical.symplecticJ)
    ({ op := (!![1, t; 0, 1] : LeanPhy.Classical.M2R),
       preserve := LeanPhy.Classical.shear_symplectic t } :
      BilinearIsometry LeanPhy.Classical.symplecticJ)).preserve

/-! ## Hamiltonian interface: affine Poisson bracket and oscillator flow -/

example : LeanPhy.Classical.poisson LeanPhy.Classical.qObservable
    LeanPhy.Classical.pObservable = 1 :=
  LeanPhy.Classical.poisson_q_p

example {n : Nat} (A : LeanPhy.Quantum.Operator n) :
    Polynomial.aeval A (Matrix.charpoly A) = 0 :=
  LeanPhy.Quantum.cayleyHamilton A

/-! ## Classical--quantum finite interoperability -/

example {n : Nat} (p : LeanPhy.StatMech.FiniteDistribution n) :
    LeanPhy.Quantum.IsDensity (LeanPhy.Quantum.diagonalState p) :=
  LeanPhy.Quantum.diagonalState_isDensity p

example {n : Nat} (p : LeanPhy.StatMech.FiniteDistribution n) :
    LeanPhy.Quantum.matrixPurity (LeanPhy.Quantum.diagonalState p) =
      (p.collisionProbability : ℂ) :=
  LeanPhy.Quantum.diagonalState_purity p

example {n : Nat} (p : LeanPhy.StatMech.FiniteDistribution n)
    (f : Fin n → ℝ) :
    LeanPhy.Quantum.expectation (LeanPhy.Quantum.diagonalState p)
        (LeanPhy.Quantum.diagonalObservable f) =
      (p.expectation f : ℂ) :=
  LeanPhy.Quantum.diagonal_expectation_eq p f

example {d n : Nat} (M : LeanPhy.QuantumInfo.POVM d (Fin n))
    (rho : LeanPhy.Quantum.State d) (hrho : LeanPhy.Quantum.IsDensity rho) :
    LeanPhy.Quantum.matrixPurity
        (LeanPhy.Quantum.diagonalState (M.toFiniteDistribution rho hrho)) =
      ((M.toFiniteDistribution rho hrho).collisionProbability : ℂ) :=
  LeanPhy.QuantumInfo.POVM.measurement_matrixPurity M rho hrho

example {ι : Type} [Fintype ι] (p : LeanPhy.StatMech.FiniteProbability ι)
    (f : ι → ℝ) :
    0 ≤ p.secondMoment f :=
  p.secondMoment_nonneg f

example {d : Nat} {ι : Type} [Fintype ι]
    (M : LeanPhy.QuantumInfo.POVM d ι) (rho : LeanPhy.Quantum.State d)
    (hrho : LeanPhy.Quantum.IsDensity rho) :
    (M.toFiniteProbability rho hrho).collisionProbability ≤ 1 :=
  (M.toFiniteProbability rho hrho).collisionProbability_le_one

example {ι : Type} [Fintype ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) :
    ∑ i, (K.step p).weight i = 1 :=
  (K.step p).normalised

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) (j : ι) :
    LeanPhy.Mathematics.FiniteDivergence.divergence
        LeanPhy.StatMech.FiniteKernel.markovTail
        LeanPhy.StatMech.FiniteKernel.markovHead
        (LeanPhy.StatMech.FiniteKernel.current K p) j =
      (K.step p).weight j - p.weight j :=
  LeanPhy.StatMech.FiniteKernel.divergence_current K p j

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) :
    ∑ j, ((K.step p).weight j - p.weight j) = 0 :=
  LeanPhy.StatMech.FiniteKernel.total_step_source_zero K p

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) :
    LeanPhy.StatMech.MarkovCurrentConservation K p :=
  LeanPhy.StatMech.FiniteKernel.conservationCertificate K p

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι)
    (h : LeanPhy.Condensed.HoppingMarkovCurrent K p) :
    ∑ j, ((K.step p).weight j - p.weight j) = 0 := by
  exact LeanPhy.StatMech.FiniteKernel.total_step_source_zero K p

example {ι : Type} [Fintype ι]
    (K L : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) :
    (L.compose K).step p = L.step (K.step p) :=
  L.step_compose K p

example {ι : Type} [Fintype ι] [Nonempty ι]
    (K : LeanPhy.StatMech.FiniteKernel.DoublyStochasticKernel ι) :
    K.toFiniteKernel.step LeanPhy.StatMech.FiniteKernel.uniformProbability =
    LeanPhy.StatMech.FiniteKernel.uniformProbability :=
  LeanPhy.StatMech.FiniteKernel.doublyStochastic_step_uniform K

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) :
    LeanPhy.Quantum.IsNamedDensity
      (LeanPhy.Quantum.namedDiagonalStep K p) :=
  LeanPhy.Quantum.namedDiagonalStep_isDensity K p

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) (f : ι → ℝ) :
    LeanPhy.Quantum.namedTrace
        (LeanPhy.Quantum.namedDiagonalStep K p *
          LeanPhy.Quantum.diagonalNamedObservable f) =
      ((p.expectation (K.pullback f) : ℝ) : ℂ) :=
  LeanPhy.Quantum.namedDiagonalStep_expectation K p f

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) :
    LeanPhy.Quantum.namedMatrixPurity
        (LeanPhy.Quantum.namedDiagonalStep K p) =
      ((K.step p).collisionProbability : ℂ) :=
  LeanPhy.Quantum.namedDiagonalStep_purity K p

example {n : Nat} (rho : LeanPhy.Quantum.State n)
    (hrho : LeanPhy.Quantum.IsDensity rho) (i : Fin n) :
    0 ≤ hrho.1.eigenvalues i :=
  LeanPhy.Quantum.density_eigenvalue_nonneg rho hrho i

example {n : Nat} (rho : LeanPhy.Quantum.State n)
    (hrho : LeanPhy.Quantum.IsDensity rho) :
    ∑ i, (hrho.1.eigenvalues i : ℂ) = 1 :=
  LeanPhy.Quantum.density_eigenvalue_sum rho hrho

example {ι : Type} [Fintype ι] [Nonempty ι]
    (β : ℝ) (E : ι → ℝ) :
    ∑ i, (LeanPhy.StatMech.finiteGibbsProbability β E).weight i = 1 :=
  (LeanPhy.StatMech.finiteGibbsProbability β E).normalised

example {ι : Type} [Fintype ι] [Nonempty ι]
    (β c : ℝ) (E : ι → ℝ) (i : ι) :
    LeanPhy.StatMech.finiteGibbsWeight β (fun j => E j + c) i =
      LeanPhy.StatMech.finiteGibbsWeight β E i :=
  LeanPhy.StatMech.finiteGibbsWeight_shift β c E i

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : LeanPhy.StatMech.FiniteProbability ι) :
    LeanPhy.Quantum.IsNamedDensity
      (LeanPhy.Quantum.diagonalNamedState p) :=
  LeanPhy.Quantum.diagonalNamedState_isDensity p

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : LeanPhy.StatMech.FiniteProbability ι) :
    LeanPhy.Quantum.namedMatrixPurity
        (LeanPhy.Quantum.diagonalNamedState p) =
      (p.collisionProbability : ℂ) :=
  LeanPhy.Quantum.diagonalNamed_purity_eq_collision p

example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (β : ℝ) (E : ι → ℝ) :
    LeanPhy.Quantum.IsNamedDensity
      (LeanPhy.Quantum.diagonalGibbsState β E) :=
  LeanPhy.Quantum.diagonalGibbsState_isDensity β E

example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (β : ℝ) (E : ι → ℝ) :
    LeanPhy.Quantum.namedMatrixPurity
        (LeanPhy.Quantum.diagonalGibbsState β E) =
      ((LeanPhy.StatMech.finiteGibbsProbability β E).collisionProbability : ℂ) :=
  LeanPhy.Quantum.diagonalGibbs_purity_eq_collision β E

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (rho : LeanPhy.Quantum.NamedState ι)
    (hrho : LeanPhy.Quantum.IsNamedDensity rho) :
    LeanPhy.Quantum.IsNamedDensity
      (LeanPhy.Quantum.namedIdentityKrausChannel rho) := by
  exact LeanPhy.Quantum.namedFiniteChannel_isDensity
    LeanPhy.Quantum.namedIdentityKrausChannel rho hrho

example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (β : ℝ) (E : ι → ℝ) :
    LeanPhy.Quantum.namedIdentityKrausChannel
        (LeanPhy.Quantum.diagonalGibbsState β E) =
      LeanPhy.Quantum.diagonalGibbsState β E := by
  exact LeanPhy.Quantum.namedIdentityKrausChannel_apply _

example {ι : Type} [Fintype ι]
    (after before : LeanPhy.Quantum.NamedFiniteChannel ι)
    (rho : LeanPhy.Quantum.NamedState ι)
    (hrho : LeanPhy.Quantum.IsNamedDensity rho) :
    LeanPhy.Quantum.IsNamedDensity
      (LeanPhy.Quantum.namedChannelCompose after before rho) :=
  LeanPhy.Quantum.namedChannelCompose_isDensity after before rho hrho

example (theta : ℝ) (z : LeanPhy.Classical.PhasePoint) :
    LeanPhy.Classical.oscillatorEnergy (LeanPhy.Classical.oscillatorFlow theta z) =
      LeanPhy.Classical.oscillatorEnergy z :=
  LeanPhy.Classical.oscillatorFlow_energy theta z

/-! ## Algebraic variational equations -/

example :
    LeanPhy.Classical.eulerLagrangeResidual LeanPhy.Classical.oscillatorLagrangian =
      -(LeanPhy.Classical.jetQ + LeanPhy.Classical.jetA) :=
  LeanPhy.Classical.oscillator_euler_lagrange

example {ι : Type} [DecidableEq ι] (x : ι) :
    LeanPhy.Classical.fieldTotalDerivative x (LeanPhy.Classical.fieldJetVar x 0) =
      LeanPhy.Classical.fieldJetVar x 1 :=
  LeanPhy.Classical.fieldTotalDerivative_q x

example {ι : Type} [DecidableEq ι] (x : ι) :
    LeanPhy.Classical.fieldEulerLagrangeResidual x
        (LeanPhy.Classical.fieldOscillatorLagrangian x) =
      -(LeanPhy.Classical.fieldJetVar x 0 + LeanPhy.Classical.fieldJetVar x 2) :=
  LeanPhy.Classical.fieldOscillator_euler_lagrange x

/-! ## Finite differential-form adapters -/

example {n : Nat} {R : Type} {A : Type} [CommRing R] [CommRing A]
    [Algebra R A] (D : Fin n → LeanPhy.Mathematics.PhysicsDerivation R A)
    (ω : LeanPhy.Mathematics.Form1 n A)
    (hcomm : ∀ i j x, D i (D j x) = D j (D i x))
    (i j k : Fin n) :
    LeanPhy.Mathematics.exteriorDerivative2 D
        (LeanPhy.Mathematics.exteriorDerivative1 D ω) i j k = 0 :=
  LeanPhy.Mathematics.exteriorDerivative2_exteriorDerivative1 D ω hcomm i j k

example {n : Nat} {R : Type} {A : Type} [CommRing R] [CommRing A]
    [Algebra R A] (D : Fin n → LeanPhy.Mathematics.PhysicsDerivation R A)
    (ω : LeanPhy.Mathematics.Form1 n A) (χ : A)
    (hcomm : ∀ i j x, D i (D j x) = D j (D i x)) :
    LeanPhy.Mathematics.exteriorDerivative1 D
        ⟨fun i => ω i + D i χ⟩ =
      LeanPhy.Mathematics.exteriorDerivative1 D ω :=
  LeanPhy.Mathematics.exteriorDerivative1_gauge_invariant D ω χ hcomm

example {n : Nat} {A : Type} [CommRing A]
    (α β : LeanPhy.Mathematics.Form1 n A) (i j : Fin n) :
    LeanPhy.Mathematics.wedge1 α β i j =
      -(LeanPhy.Mathematics.wedge1 β α i j) :=
  LeanPhy.Mathematics.wedge1_swap_apply α β i j

example {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin 4 → LeanPhy.Mathematics.PhysicsDerivation R A)
    (potential : Fin 4 → A) (mu nu : Fin 4) :
    LeanPhy.GaugeTheory.abelianFieldStrength D potential mu nu =
      LeanPhy.Mathematics.exteriorDerivative1 D
        (⟨potential⟩ : LeanPhy.Mathematics.Form1 4 A) mu nu :=
  LeanPhy.GaugeTheory.abelianFieldStrength_eq_exteriorDerivative1 D potential mu nu

example {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Fin 4 → LeanPhy.Mathematics.PhysicsDerivation R A)
    (potential : Fin 4 → A)
    (hcomm : ∀ i j x, D i (D j x) = D j (D i x))
    (mu nu rho : Fin 4) :
    D mu (LeanPhy.GaugeTheory.abelianFieldStrength D potential nu rho) +
        D nu (LeanPhy.GaugeTheory.abelianFieldStrength D potential rho mu) +
        D rho (LeanPhy.GaugeTheory.abelianFieldStrength D potential mu nu) = 0 :=
  LeanPhy.GaugeTheory.abelianFieldStrength_bianchi_via_exterior
    D potential hcomm mu nu rho

example {n : Nat} {R : Type} {A : Type} [CommRing R] [CommRing A]
    [Algebra R A] (D : Fin n → LeanPhy.Mathematics.PhysicsDerivation R A)
    (velocity : LeanPhy.Mathematics.Form1 n A)
    (hcomm : ∀ i j x, D i (D j x) = D j (D i x))
    (i j k : Fin n) :
    LeanPhy.Mathematics.exteriorDerivative2 D
        (LeanPhy.Classical.vorticity D velocity) i j k = 0 :=
  LeanPhy.Classical.vorticity_closed D velocity hcomm i j k

example {n : Nat} {R : Type} {A : Type} [CommRing R] [CommRing A]
    [Algebra R A] (D : Fin n → LeanPhy.Mathematics.PhysicsDerivation R A)
    (velocity : LeanPhy.Mathematics.Form1 n A) (χ : A)
    (hcomm : ∀ i j x, D i (D j x) = D j (D i x)) :
    LeanPhy.Classical.vorticity D
        ⟨fun i => velocity i + D i χ⟩ =
      LeanPhy.Classical.vorticity D velocity :=
  LeanPhy.Classical.vorticity_potential_shift D velocity χ hcomm

example {n : Nat} {A : Type} [Ring A]
    (C : LeanPhy.Mathematics.NoncommConnection n A) (i j : Fin n) :
    C.curvature i j = -C.curvature j i :=
  LeanPhy.Mathematics.NoncommConnection.curvature_antisym C i j

example {n : Nat} {A : Type} [Ring A]
    (C : LeanPhy.Mathematics.NoncommConnection n A) (i j k : Fin n) :
    C.covariantDerivative i (C.curvature j k) +
        C.covariantDerivative j (C.curvature k i) +
        C.covariantDerivative k (C.curvature i j) = 0 :=
  LeanPhy.Mathematics.NoncommConnection.bianchi C i j k

example {A : Type} [Ring A] (a x y : A) :
    LeanPhy.Mathematics.innerDerivation a (x * y) =
      LeanPhy.Mathematics.innerDerivation a x * y +
        x * LeanPhy.Mathematics.innerDerivation a y :=
  LeanPhy.Mathematics.AlgebraicDerivation.leibniz
    (LeanPhy.Mathematics.innerDerivation a) x y

example {n : Nat} {A : Type} [Ring A]
    (generators potential : Fin n → A)
    (hcomm : ∀ i j, generators i * generators j = generators j * generators i)
    (i j k : Fin n) :
    (LeanPhy.Mathematics.innerConnection generators potential hcomm).covariantDerivative i
        ((LeanPhy.Mathematics.innerConnection generators potential hcomm).curvature j k) +
        (LeanPhy.Mathematics.innerConnection generators potential hcomm).covariantDerivative j
          ((LeanPhy.Mathematics.innerConnection generators potential hcomm).curvature k i) +
        (LeanPhy.Mathematics.innerConnection generators potential hcomm).covariantDerivative k
          ((LeanPhy.Mathematics.innerConnection generators potential hcomm).curvature i j) = 0 :=
  LeanPhy.Mathematics.NoncommConnection.bianchi
    (LeanPhy.Mathematics.innerConnection generators potential hcomm) i j k

example {A : Type} [Ring A]
    (C : LeanPhy.GaugeTheory.YangMillsConnection A) (mu nu rho : Fin 4) :
    C.covariantDerivative mu (C.curvature nu rho) +
        C.covariantDerivative nu (C.curvature rho mu) +
        C.covariantDerivative rho (C.curvature mu nu) = 0 :=
  LeanPhy.GaugeTheory.YangMillsConnection.bianchi_via_noncommExterior C mu nu rho

/-! ## Cross-domain residual and plaquette regression -/

example {V : Type} [AddCommGroup ℤ] (α : V → V → ℤ) (φ : V → ℤ)
    (x y z w : V) :
    LeanPhy.Mathematics.Plaquette.flux
        (LeanPhy.Mathematics.Plaquette.gaugeShift α φ) x y z w =
      LeanPhy.Mathematics.Plaquette.flux α x y z w := by
  exact LeanPhy.Mathematics.Plaquette.flux_gaugeShift α φ x y z w

example {V : Type} (α : V → V → ℤ)
    (hanti : ∀ a b, α b a = -α a b) (x y z w : V) :
    LeanPhy.Mathematics.Plaquette.flux α w z y x =
      -LeanPhy.Mathematics.Plaquette.flux α x y z w := by
  exact LeanPhy.Mathematics.Plaquette.flux_reverse α hanti x y z w

example {V : Type} [Fintype V] (s₁ s₂ : Equiv.Perm V)
    (hcomm : Function.Commute s₁ s₂) (a b φ : V → ℤ) (x : V) :
    LeanPhy.Mathematics.PeriodicPlaquette.flux s₁ s₂
        (LeanPhy.Mathematics.PeriodicPlaquette.shift s₁ a φ)
        (LeanPhy.Mathematics.PeriodicPlaquette.shift s₂ b φ) x =
      LeanPhy.Mathematics.PeriodicPlaquette.flux s₁ s₂ a b x := by
  exact LeanPhy.Mathematics.PeriodicPlaquette.flux_gauge_invariant
    s₁ s₂ hcomm a b φ x

example {V : Type} [Fintype V] (s₁ s₂ : Equiv.Perm V) (a b : V → ℤ) :
    ∑ x, LeanPhy.Mathematics.PeriodicPlaquette.flux s₁ s₂ a b x = 0 := by
  exact LeanPhy.Mathematics.PeriodicPlaquette.total_flux_zero s₁ s₂ a b

example {V : Type} [Fintype V] (s₁ s₂ : Equiv.Perm V)
    (hcomm : Function.Commute s₁ s₂) (φ : V → ℤ) (x : V) :
    LeanPhy.Mathematics.PeriodicPlaquette.flux s₁ s₂
        (LeanPhy.Mathematics.PeriodicPlaquette.shift s₁ (fun _ => 0) φ)
        (LeanPhy.Mathematics.PeriodicPlaquette.shift s₂ (fun _ => 0) φ) x = 0 := by
  exact LeanPhy.Mathematics.PeriodicPlaquette.exact_flux_zero s₁ s₂ hcomm φ x

example {V : Type} [Fintype V] (s₁ s₂ : Equiv.Perm V)
    (hcomm : Function.Commute s₁ s₂) (a b φ : V → ℤ) :
    (∑ x, LeanPhy.Mathematics.PeriodicPlaquette.flux s₁ s₂
      (LeanPhy.Mathematics.PeriodicPlaquette.shift s₁ a φ)
      (LeanPhy.Mathematics.PeriodicPlaquette.shift s₂ b φ) x) =
      ∑ x, LeanPhy.Mathematics.PeriodicPlaquette.flux s₁ s₂ a b x := by
  exact LeanPhy.Mathematics.PeriodicPlaquette.total_flux_gauge_invariant
    s₁ s₂ hcomm a b φ

/-! ## Finite matrix representations and symmetry interfaces -/

example {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    (R : LeanPhy.Mathematics.FiniteMatrixRepresentation G ι) (g : G) :
    R.rep g * R.rep g⁻¹ = (1 : Matrix ι ι ℂ) :=
  LeanPhy.Mathematics.rep_mul_inv R g

example {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    (R : LeanPhy.Mathematics.FiniteMatrixRepresentation G ι) (a g : G) :
    R.character (a * g * a⁻¹) = R.character g :=
  LeanPhy.Mathematics.character_conjugate R a g

example {H G ι : Type} [Monoid H] [Monoid G] [Fintype ι] [DecidableEq ι]
    (R : LeanPhy.Mathematics.FiniteMatrixRepresentation G ι) (f : H →* G) (h : H) :
    (R.pullback f).character h = R.character (f h) :=
  LeanPhy.Mathematics.FiniteMatrixRepresentation.pullback_character R f h

example {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι]
    (R : LeanPhy.Mathematics.FiniteMatrixRepresentation G ι) :
    LeanPhy.Mathematics.Intertwiner R R (1 : Matrix ι ι ℂ) :=
  LeanPhy.Mathematics.Intertwiner.identity R

example {G ι κ μ : Type} [Monoid G]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ]
    {R : LeanPhy.Mathematics.FiniteMatrixRepresentation G ι}
    {S : LeanPhy.Mathematics.FiniteMatrixRepresentation G κ}
    {Q : LeanPhy.Mathematics.FiniteMatrixRepresentation G μ}
    {T : Matrix κ ι ℂ} {U : Matrix μ κ ℂ}
    (hT : LeanPhy.Mathematics.Intertwiner R S T)
    (hU : LeanPhy.Mathematics.Intertwiner S Q U) :
    LeanPhy.Mathematics.Intertwiner R Q (U * T) :=
  LeanPhy.Mathematics.Intertwiner.compose hT hU

example {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    (R : LeanPhy.Mathematics.UnitaryMatrixRepresentation G ι) (g : G) :
    R.rep g⁻¹ = Matrix.conjTranspose (R.rep g) :=
  LeanPhy.Mathematics.UnitaryMatrixRepresentation.rep_inv_eq_adjoint R g

example {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    (R : LeanPhy.Mathematics.FiniteMatrixRepresentation G ι) (g : G)
    (X : Matrix ι ι ℂ) :
    R.rep g * LeanPhy.Mathematics.groupTwirl R X * R.rep g⁻¹ =
      LeanPhy.Mathematics.groupTwirl R X :=
  LeanPhy.Mathematics.groupTwirl_conjugate R g X

example {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    (R : LeanPhy.Mathematics.FiniteMatrixRepresentation G ι) (g : G)
    (X : Matrix ι ι ℂ) :
    R.rep g * LeanPhy.Mathematics.groupTwirl R X =
      LeanPhy.Mathematics.groupTwirl R X * R.rep g :=
  LeanPhy.Mathematics.groupTwirl_commute R g X

/-! ## Finite divergence and continuity certificates -/

example {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V]
    [AddCommGroup A] (tail head : E → V) (current : E → A) :
    ∑ v, LeanPhy.Mathematics.FiniteDivergence.divergence tail head current v = 0 :=
  LeanPhy.Mathematics.FiniteDivergence.total_divergence_zero tail head current

example {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V]
    [AddCommGroup A] (tail head : E → V) (current : E → A)
    (source : V → A)
    (h : LeanPhy.Mathematics.FiniteDivergence.ConservationCertificate
      tail head current source) :
    ∑ v, source v = 0 :=
  h.total_source_zero

example {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V]
    [AddCommGroup A] (tail head : E → V) (current : E → A)
    (source : V → A) :
    (∀ v, LeanPhy.Mathematics.FiniteDivergence.residual
      tail head current source v = 0) ↔
      LeanPhy.Mathematics.FiniteDivergence.ConservationCertificate
        tail head current source :=
  LeanPhy.Mathematics.FiniteDivergence.residual_zero_iff tail head current source

-- Physical names remain type aliases, so a lattice current and a finite-volume
-- flux use exactly the same local equation and total-source theorem.
example {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (current : E → ℤ) (source : V → ℤ)
    (h : LeanPhy.GaugeTheory.LatticeCurrentConservation
      tail head current source) :
    ∑ v, source v = 0 :=
  h.total_source_zero

example {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (current : E → ℤ) (source : V → ℤ)
    (h : LeanPhy.Classical.FiniteVolumeConservation
      tail head current source) :
    ∑ v, source v = 0 :=
  h.total_source_zero

example {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (current : E → ℝ) (source radius : V → ℝ)
    (h : LeanPhy.Mathematics.FiniteDivergence.ConservationError
      tail head current source radius) :
    |∑ v, source v| ≤ ∑ v, radius v :=
  h.total_source_abs_le

example {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (current : E → ℝ) (source : V → ℝ)
    (hlocal : ∀ v, LeanPhy.Mathematics.FiniteDivergence.residual
      tail head current source v = 0) :
    LeanPhy.Mathematics.ApproximateConservation
      tail head current source (fun _ => 0) :=
  LeanPhy.Mathematics.FiniteDivergence.ConservationError.of_zero hlocal

example {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (current : E → ℝ) (source : V → ℝ)
    {ε : ℝ}
    (h : LeanPhy.Mathematics.FiniteDivergence.ConservationError
      tail head current source (fun _ => ε)) :
    |∑ v, source v| ≤ (Fintype.card V : ℝ) * ε :=
  h.total_source_abs_le_uniform

example {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (current : E → ℝ) (source radius : V → ℝ)
    (h : LeanPhy.GaugeTheory.LatticeConservationError
      tail head current source radius) :
    |∑ v, source v| ≤ ∑ v, radius v :=
  h.total_source_abs_le

example :
    LeanPhy.Mathematics.MatrixEigenpairResidual
      (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 0 := by
  apply LeanPhy.Mathematics.matrixEigenpairResidual_of_eigenpair
  simp

example (nextState rhs : ℝ) (h : nextState = rhs) :
    LeanPhy.Mathematics.StepResidual nextState rhs 0 := by
  exact LeanPhy.Mathematics.stepResidual_of_eq nextState rhs h

example (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    LeanPhy.Mathematics.Hilbert.matrixOperator A v = A.mulVec v := by
  exact LeanPhy.Mathematics.Hilbert.matrixOperator_apply A v

example (U : LeanPhy.Mathematics.Hilbert.Unitary
    (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin 2)))
    (v : EuclideanSpace ℂ (Fin 2)) :
    ‖U.op v‖ = ‖v‖ := by
  exact U.norm_preserved v

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    LeanPhy.Mathematics.Hilbert.euclideanMatrixOperator (A * B) =
      LeanPhy.Mathematics.Hilbert.euclideanMatrixOperator A ∘SL
        LeanPhy.Mathematics.Hilbert.euclideanMatrixOperator B := by
  exact LeanPhy.Mathematics.Hilbert.euclideanMatrixOperator_mul A B

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    ContinuousLinearMap.adjoint
        (LeanPhy.Mathematics.Hilbert.euclideanMatrixOperator A) =
      LeanPhy.Mathematics.Hilbert.euclideanMatrixOperator (Matrix.conjTranspose A) := by
  exact LeanPhy.Mathematics.Hilbert.euclideanMatrixOperator_adjoint A

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : FiniteUnitary ι) (v : EuclideanSpace ℂ ι) :
    ‖U.toHilbert.op v‖ = ‖v‖ := by
  exact U.toHilbert.norm_preserved v

noncomputable example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : Matrix.conjTranspose A = A) :
    LeanPhy.Mathematics.Hilbert.SelfAdjoint
      (𝕜 := ℂ) (E := EuclideanSpace ℂ ι) := by
  exact hermitianMatrixToHilbert A hA

noncomputable example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : Matrix.conjTranspose A = A)
    (v : EuclideanSpace ℂ ι) :
    RCLike.im ((hermitianMatrixToHilbert A hA).expectation v) = 0 := by
  exact (hermitianMatrixToHilbert A hA).expectation_re_im_zero v

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    ContinuousLinearMap.adjoint
        (LeanPhy.Mathematics.Hilbert.euclideanMatrixOperator A) =
      LeanPhy.Mathematics.Hilbert.euclideanMatrixOperator (Matrix.conjTranspose A) := by
  exact LeanPhy.Mathematics.Hilbert.euclideanMatrixOperator_adjoint A

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : LeanPhy.Mathematics.FiniteMatrixFlow (𝕜 := ℝ) ι) (t s : ℝ) :
    (F.toHilbertFlow).op (t + s) =
      (F.toHilbertFlow).op t ∘SL (F.toHilbertFlow).op s := by
  exact (F.toHilbertFlow).add t s

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : LeanPhy.Mathematics.FiniteMatrixFlow (𝕜 := ℂ) ι)
    (t s : ℝ) (v : EuclideanSpace ℂ ι) :
    (F.toHilbertFlow).evolve (t + s) v =
      (F.toHilbertFlow).evolve t ((F.toHilbertFlow).evolve s v) := by
  exact (F.toHilbertFlow).evolve_add t s v

example {I : Type} {A : Type} [CommRing A]
    (C : I → I → A) (i j k l : I) :
    LeanPhy.FieldTheory.FermionicWick.fourPoint C i j k l =
      C i j * C k l - C i k * C j l + C i l * C j k := by
  rfl

example {I : Type} {A : Type} [CommRing A]
    (C : I → I → A) (hanti : ∀ a b, C b a = -C a b)
    (i j k l : I) :
    LeanPhy.FieldTheory.FermionicWick.fourPoint C j i k l =
      -LeanPhy.FieldTheory.FermionicWick.fourPoint C i j k l := by
  exact LeanPhy.FieldTheory.FermionicWick.fourPoint_swap12 C hanti i j k l

example {A : Type} [CommRing A]
    (K : Matrix (Fin 4) (Fin 4) A) :
    LeanPhy.FieldTheory.FermionicWick.pfaffian4 K =
      LeanPhy.FieldTheory.FermionicWick.fourPoint (fun i j => K i j) 0 1 2 3 := by
  exact LeanPhy.FieldTheory.FermionicWick.pfaffian4_eq_fourPoint K

example {I : Type} {A : Type} [CommRing A]
    (C : I → I → A) (hdiag : ∀ i, C i i = 0) (i k l : I) :
    LeanPhy.FieldTheory.FermionicWick.fourPoint C i i k l = 0 := by
  exact LeanPhy.FieldTheory.FermionicWick.fourPoint_repeat12 C hdiag i k l

example {V : Type} (φ : V → ℤ) (x y z : V) :
    LeanPhy.Mathematics.HigherCochain.d1Alt
      (fun a b => φ b - φ a) x y z = 0 := by
  exact LeanPhy.Mathematics.HigherCochain.d1Alt_d0 φ x y z

example {V : Type} (α : V → V → ℤ) (w x y z : V) :
    LeanPhy.Mathematics.HigherCochain.d2
      (LeanPhy.Mathematics.HigherCochain.d1Alt α) w x y z = 0 := by
  exact LeanPhy.Mathematics.HigherCochain.d2_d1Alt α w x y z

example {F : Type} [Fintype F] (β γ : F → ℤ)
    (h : ∀ f, β f = γ f) :
    LeanPhy.Mathematics.HigherCochain.faceSum β =
      LeanPhy.Mathematics.HigherCochain.faceSum γ := by
  exact LeanPhy.Mathematics.HigherCochain.faceSum_congr h

example {V : Type} (α : V → V → ℤ) :
    LeanPhy.Mathematics.HigherCochain.d2
      (LeanPhy.Mathematics.HigherCochain.d1Alt α) = 0 := by
  exact LeanPhy.Mathematics.HigherCochain.d2_d1Alt_eq α

/-! ## Finite chain complexes: one incidence contract across domains -/

def zeroFiniteChainComplex (C0 C1 C2 A : Type)
    [Fintype C0] [Fintype C1] [Fintype C2] [CommRing A] :
    FiniteChainComplex C0 C1 C2 A where
  boundary10 := fun _ _ => 0
  boundary21 := fun _ _ => 0
  boundary_sq := by simp

example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A) (c : C2 → A) :
    K.boundary1 (K.boundary2 c) = 0 :=
  K.boundary1_boundary2 c

example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A) (φ : C0 → A) :
    K.coboundary1 (K.coboundary0 φ) = 0 :=
  K.coboundary1_coboundary0 φ

example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (φ : C0 → A) (c : C1 → A) :
    FiniteChainComplex.pairing (K.coboundary0 φ) c =
      FiniteChainComplex.pairing φ (K.boundary1 c) :=
  K.pairing_coboundary0_boundary1 φ c

example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (φ : C0 → A) (c : C1 → A) (hcycle : K.boundary1 c = 0) :
    FiniteChainComplex.pairing (K.coboundary0 φ) c = 0 :=
  K.exact_pairing_zero φ c hcycle

example {V E F : Type} [Fintype V] [Fintype E] [Fintype F] :
    GaugeTheory.LatticeChainComplex V E F ℤ :=
  zeroFiniteChainComplex V E F ℤ

example {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V]
    [CommRing A] (tail head : E → V) (current : E → A) :
    (FiniteChainAdapters.graphChainComplex tail head).boundary1 current =
      FiniteDivergence.divergence tail head current := by
  exact FiniteChainAdapters.graph_boundary1_eq_divergence tail head current

example {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V]
    [CommRing A] (tail head : E → V) (current : E → A) (source : V → A)
    (h : FiniteDivergence.ConservationCertificate tail head current source) :
    (FiniteChainAdapters.graphChainComplex tail head).boundary1 current = source := by
  exact FiniteChainAdapters.graph_conservation_boundary_eq_source tail head current source h

example {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V]
    [CommRing A] (tail head : E → V) :
    GaugeTheory.GraphChainComplex V E A tail head =
      FiniteChainAdapters.graphChainComplex tail head := rfl

example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A) (b : C2 → A) :
    K.IsCycle1 (K.boundary2 b) :=
  K.boundary_isCycle1 b

example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A) (φ : C0 → A) :
    K.IsCocycle1 (K.coboundary0 φ) :=
  K.exact_isCocycle1 φ

example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (α : C1 → A) (b : C2 → A) :
    FiniteChainComplex.pairing (K.coboundary1 α) b =
      FiniteChainComplex.pairing α (K.boundary2 b) :=
  K.pairing_coboundary1_boundary2 α b

example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (α : C1 → A) (b : C2 → A) (hα : K.IsCocycle1 α) :
    FiniteChainComplex.pairing α (K.boundary2 b) = 0 :=
  K.cocycle_pairing_boundary_zero α b hα

example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (φ : C0 → A) (c : C1 → A) (hcycle : K.IsCycle1 c) :
    FiniteChainComplex.pairing (K.coboundary0 φ) c = 0 :=
  K.exact_pairing_cycle_zero φ c hcycle

example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (α : C1 → A) (c : C2 → A) (hcycle : K.IsCycle2 c) :
    FiniteChainComplex.pairing (K.coboundary1 α) c = 0 :=
  K.coboundary1_pairing_cycle2_zero α c hcycle

example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (β : C2 → A) (α : C1 → A) (c : C2 → A) (hcycle : K.IsCycle2 c) :
    FiniteChainComplex.pairing (fun f => β f + K.coboundary1 α f) c =
      FiniteChainComplex.pairing β c :=
  K.pairing_add_coboundary1_cycle2 β α c hcycle

example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (c : C2 → A) (hcycle : K.IsCycle2 c) :
    LeanPhy.Mathematics.GaugeTheory.ClosedFluxSurface K c := hcycle

example {C0 C1 C2 : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    (K : FiniteChainComplex C0 C1 C2 ℤ) :
    LeanPhy.Mathematics.Condensed.ChernMeshCycle K = FiniteChainComplex.IsCycle2 K := rfl

/-! ## Detailed balance: finite reversible dynamics -/

example {ι : Type} [Fintype ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι)
    (h : K.IsDetailedBalance p) : K.step p = p :=
  K.step_eq_of_detailedBalance p h

example {ι : Type} [Fintype ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι)
    (h : K.IsDetailedBalance p) (f g : ι → ℝ) :
    p.expectation (fun i => f i * K.pullback g i) =
      p.expectation (fun i => K.pullback f i * g i) :=
  K.pullback_pairing_symmetric p h f g

example {ι : Type} [Fintype ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι)
    (h : K.IsDetailedBalance p) :
    LeanPhy.StatMech.ReversibleFiniteKernel K p := h

example {ι : Type} [Fintype ι] [Nonempty ι]
    (M : LeanPhy.StatMech.ConductanceModel ι) :
    0 < M.partition :=
  M.partition_pos

example {ι : Type} [Fintype ι] [Nonempty ι]
    (M : LeanPhy.StatMech.ConductanceModel ι) (i : ι) :
    ∑ j, M.kernel.transition i j = 1 :=
  M.kernel.row_normalized i

example {ι : Type} [Fintype ι] [Nonempty ι]
    (M : LeanPhy.StatMech.ConductanceModel ι) :
    M.kernel.IsDetailedBalance M.equilibrium :=
  M.detailedBalance

example {ι : Type} [Fintype ι] [Nonempty ι]
    (M : LeanPhy.StatMech.ConductanceModel ι) :
    M.kernel.step M.equilibrium = M.equilibrium :=
  M.stationary

example {ι : Type} [Fintype ι] [Nonempty ι]
    (M : LeanPhy.StatMech.ConductanceModel ι) :
    LeanPhy.Condensed.HoppingConductanceModel (ι := ι) := M

example {ι : Type} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    ((LeanPhy.StatMech.ConductanceModel.fromWeights w hw).kernel).step
        (LeanPhy.StatMech.ConductanceModel.fromWeights w hw).equilibrium =
      (LeanPhy.StatMech.ConductanceModel.fromWeights w hw).equilibrium :=
  LeanPhy.StatMech.ConductanceModel.fromWeights_stationary w hw

example {ι : Type} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (i j : ι) :
    (LeanPhy.StatMech.ConductanceModel.fromWeights w hw).conductance i j =
      w i * w j / (∑ k, w k) :=
  LeanPhy.StatMech.ConductanceModel.fromWeights_conductance w hw i j

/-! ## Dirichlet forms: a shared finite energy for reversible dynamics -/

example {ι : Type} [Fintype ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) (f : ι → ℝ) :
    0 ≤ K.dirichletForm p f f :=
  K.dirichletForm_nonneg p f

example {ι : Type} [Fintype ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) (f g : ι → ℝ) :
    K.dirichletForm p f g = K.dirichletForm p g f :=
  K.dirichletForm_swap p f g

example {ι : Type} [Fintype ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) (f : ι → ℝ) (c : ℝ) :
    K.dirichletForm p f (fun _ => c) = 0 :=
  K.dirichletForm_const_right p f c

example {ι : Type} [Fintype ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) (g : ι → ℝ) (c : ℝ) :
    K.dirichletForm p (fun _ => c) g = 0 :=
  K.dirichletForm_const_left p g c

example {ι : Type} [Fintype ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) (f g h : ι → ℝ) :
    K.dirichletForm p (fun i => f i + g i) h =
      K.dirichletForm p f h + K.dirichletForm p g h :=
  K.dirichletForm_add_left p f g h

example {ι : Type} [Fintype ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) (f g h : ι → ℝ) :
    K.dirichletForm p f (fun i => g i + h i) =
      K.dirichletForm p f g + K.dirichletForm p f h :=
  K.dirichletForm_add_right p f g h

example {ι : Type} [Fintype ι]
    (K : LeanPhy.StatMech.FiniteKernel ι) (p : LeanPhy.StatMech.FiniteProbability ι) :
    LeanPhy.Condensed.FiniteHoppingEnergy (ι := ι) K p =
      LeanPhy.StatMech.FiniteDirichletEnergy (ι := ι) K p := rfl

example {ι : Type} [Fintype ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι)
    (h : K.IsDetailedBalance p) (f g : ι → ℝ) :
    K.dirichletForm p f g =
      p.expectation (fun i => f i * K.laplacian g i) :=
  K.dirichletForm_eq_laplacian_pairing p f g h

/-! ## Finite Kubo/linear-response algebra -/

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (rho A B : Matrix ι ι ℂ) :
    LeanPhy.Mathematics.commutatorResponse rho A B =
      Matrix.trace (rho * A * B) - Matrix.trace (rho * B * A) :=
  LeanPhy.Mathematics.commutatorResponse_eq_correlator_sub rho A B

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (rho A B : Matrix ι ι ℂ) :
    LeanPhy.Mathematics.commutatorResponse rho B A =
      -LeanPhy.Mathematics.commutatorResponse rho A B :=
  LeanPhy.Mathematics.commutatorResponse_swap rho A B

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (rho A B : Matrix ι ι ℂ) (hAB : A * B = B * A) :
    LeanPhy.Mathematics.commutatorResponse rho A B = 0 :=
  LeanPhy.Mathematics.commutatorResponse_eq_zero_of_commute rho A B hAB

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (rho A B : Matrix ι ι ℂ) :
    LeanPhy.Mathematics.commutatorResponse rho A B =
      Matrix.trace ((rho * A - A * rho) * B) :=
  LeanPhy.Mathematics.commutatorResponse_eq_state_commutator rho A B

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (rho A B C : Matrix ι ι ℂ) :
    LeanPhy.Mathematics.commutatorResponse rho (A + B) C =
      LeanPhy.Mathematics.commutatorResponse rho A C +
        LeanPhy.Mathematics.commutatorResponse rho B C :=
  LeanPhy.Mathematics.commutatorResponse_add_left rho A B C

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (rho A B : Matrix ι ι ℂ) :
    LeanPhy.QuantumInfo.FiniteKuboResponse rho A B =
      LeanPhy.Condensed.FiniteLinearResponse rho A B := rfl

/-! ## Finite path integrals, coarse graining and weak PDEs -/

example {ι : Type} [Fintype ι] (P : FinitePathIntegral ι) (c : ℂ) :
    P.expectation (fun _ => c) = c :=
  FinitePathIntegral.expectation_const P c

example {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ) :
    ∑ y, R.coarseWeight y = ∑ x, R.fineWeight x :=
  R.partition_preserved

example {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ) (O : κ → ℂ) :
    ∑ y, R.coarseWeight y * O y =
      ∑ x, R.fineWeight x * O (R.coarse x) :=
  R.insertion_preserved O

example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0) :
    (∑ y, R.coarseWeight y) ≠ 0 :=
  R.coarse_partition_ne_zero h

example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0) (O : κ → ℂ) :
    (R.coarsePathIntegral h).expectation O =
      (R.finePathIntegral h).expectation (fun x => O (R.coarse x)) :=
  R.expectation_preserved h O

example {ι κ W : Type} [Fintype ι] [Fintype κ] [Fintype W]
    (R : FinitePathIntegral.FiniteRGStep ι κ) (next : κ → W) (O : W → ℂ) :
    ∑ z, (R.coarsen next).coarseWeight z * O z =
      ∑ x, R.fineWeight x * O (next (R.coarse x)) :=
  R.coarsen_insertion_preserved next O

example {ι κ W : Type} [Fintype ι] [Fintype κ] [Fintype W]
    (R : FinitePathIntegral.FiniteRGStep ι κ) (next : κ → W) (z : W) :
    (R.coarsen next).coarseWeight z =
      FinitePathIntegral.pushforwardWeight next R.coarseWeight z :=
  R.coarsen_weight_eq_pushforward_coarseWeight next z

example {ι κ W Z : Type} [Fintype ι] [Fintype κ] [Fintype W] [Fintype Z]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (next : κ → W) (last : W → Z) :
    ((R.coarsen next).coarsen last).coarseWeight =
      (R.coarsen (last ∘ next)).coarseWeight :=
  R.coarsen_weight_assoc next last

example {ι κ W : Type} [Fintype ι] [Fintype κ] [Fintype W]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (next : κ → W) (fineObs : ι → ℂ) (middleObs : κ → ℂ)
    (coarseObs : W → ℂ) (lambda mu : ℂ)
    (h₁ : FinitePathIntegral.FiniteRGStep.ScalingCertificate
      R fineObs middleObs lambda)
    (h₂ : ∀ y, middleObs y = mu * coarseObs (next y)) :
    FinitePathIntegral.FiniteRGStep.ScalingCertificate
      (R.coarsen next) fineObs coarseObs (lambda * mu) :=
  FinitePathIntegral.FiniteRGStep.ScalingCertificate.compose
    R next fineObs middleObs coarseObs lambda mu h₁ h₂

example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (fineObs : ι → ℂ) (coarseObs : κ → ℂ) (lambda : ℂ)
    (hscale : FinitePathIntegral.FiniteRGStep.ScalingCertificate
      R fineObs coarseObs lambda) :
    ∑ x, R.fineWeight x * fineObs x =
      lambda * (∑ y, R.coarseWeight y * coarseObs y) :=
  R.insertion_scales fineObs coarseObs lambda hscale

example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (fineObs : ι → ℂ) (coarseObs : κ → ℂ) (lambda : ℂ)
    (hscale : FinitePathIntegral.FiniteRGStep.ScalingCertificate
      R fineObs coarseObs lambda) :
    (R.finePathIntegral h).expectation fineObs =
      lambda * (R.coarsePathIntegral h).expectation coarseObs :=
  R.expectation_scales h fineObs coarseObs lambda hscale

example {ι : Type} [Fintype ι] (S : ι → ℂ)
    (h : (∑ i, Complex.exp (-S i)) ≠ 0) (c : ℂ) (O : ι → ℂ) :
    (FinitePathIntegral.fromAction (fun i => S i + c)
      (by
        rw [FinitePathIntegral.action_shift_weight_sum]
        exact mul_ne_zero (Complex.exp_ne_zero (-c)) h)).expectation O =
      (FinitePathIntegral.fromAction S h).expectation O :=
  FinitePathIntegral.action_shift_expectation S c O h

example {ι : Type} [Fintype ι] [Nonempty ι] (S : ι → ℝ) :
    0 < (FinitePathIntegral.fromRealAction S).partition.re :=
  FinitePathIntegral.fromRealAction_partition_pos S

example {ι : Type} [Fintype ι] [Nonempty ι] (S : ι → ℝ) (i₀ : ι) :
    Real.exp (-S i₀) ≤ ‖(FinitePathIntegral.fromRealAction S).partition‖ :=
  FinitePathIntegral.fromRealAction_partition_lower_bound S i₀

example {ι : Type} [Fintype ι]
    (P Q : FinitePathIntegral ι) (O : ι → ℂ)
    (C : FinitePathIntegral.ApproximationCertificate P Q O) :
    ErrorCertificate (P.expectation O) (Q.expectation O)
      (C.insertionRadius / C.exactLower +
        C.insertionUpper * C.partitionRadius /
          (C.exactLower * C.approximateLower)) :=
  C.expectation_error

noncomputable example {ι : Type} [Fintype ι]
    (P Q : FinitePathIntegral ι) (O : ι → ℂ)
    (C : FinitePathIntegral.ApproximationCertificate P Q O) :
    FinitePathIntegral.NormalizedExpectationCertificate P Q O :=
  FinitePathIntegral.NormalizedExpectationCertificate.ofApproximation C

example {ι : Type} [Fintype ι]
    (P Q R : FinitePathIntegral ι) (O : ι → ℂ)
    (C₁ : FinitePathIntegral.NormalizedExpectationCertificate P Q O)
    (C₂ : FinitePathIntegral.NormalizedExpectationCertificate Q R O) :
    FinitePathIntegral.NormalizedExpectationCertificate P R O :=
  FinitePathIntegral.NormalizedExpectationCertificate.compose C₁ C₂

noncomputable example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι) (O : ι → ℂ) :
    FinitePathIntegral.ApproximationCertificate P P O :=
  FinitePathIntegral.ApproximationCertificate.exact P O

example {ι : Type} [Fintype ι]
    (P Q : FinitePathIntegral ι) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i)
    (h : ∀ i, ErrorCertificate (P.weight i) (Q.weight i) (radius i)) :
    ErrorCertificate P.partition Q.partition (∑ i, radius i) :=
  FinitePathIntegral.ApproximationCertificate.partition_error_of_pointwise
    P Q radius hr h

example {ι : Type} [Fintype ι]
    (P Q : FinitePathIntegral ι) (O : ι → ℂ) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i)
    (h : ∀ i, ErrorCertificate (P.weight i) (Q.weight i) (radius i)) :
    ErrorCertificate (P.insertion O) (Q.insertion O)
      (∑ i, radius i * ‖O i‖) :=
  FinitePathIntegral.ApproximationCertificate.insertion_error_of_pointwise
    P Q O radius hr h

example {ι : Type} [Fintype ι] (P : FinitePathIntegral ι)
    (O O' : ι → ℂ)
    (C : FinitePathIntegral.ObservableApproximationCertificate O O')
    (lower : ℝ) (hlower_pos : 0 < lower)
    (hlower : lower ≤ ‖P.partition‖) :
    ErrorCertificate (P.expectation O) (P.expectation O')
      ((∑ i, ‖P.weight i‖ * C.radius i) / lower) :=
  C.expectation_error P O O' lower hlower_pos hlower

example {ι : Type} [Fintype ι]
    (P Q : FinitePathIntegral ι) (O O' : ι → ℂ)
    (C : FinitePathIntegral.ApproximationCertificate P Q O)
    (D : FinitePathIntegral.ObservableApproximationCertificate O O') :
    ErrorCertificate
      (P.expectation O) (Q.expectation O')
      (C.insertionRadius / C.exactLower +
        C.insertionUpper * C.partitionRadius /
          (C.exactLower * C.approximateLower) +
        (∑ i, ‖Q.weight i‖ * D.radius i) / C.approximateLower) :=
  C.expectation_error_with_observable D

noncomputable example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (Q : FinitePathIntegral κ) (O : κ → ℂ)
    (radius : κ → ℝ) (hr : ∀ y, 0 ≤ radius y)
    (hw : ∀ y, ErrorCertificate (R.coarseWeight y) (Q.weight y) (radius y))
    (exactLower approximateLower : ℝ)
    (hexact_pos : 0 < exactLower) (happrox_pos : 0 < approximateLower)
    (hexact_lower : exactLower ≤
      ‖(R.coarsePathIntegral h).partition‖)
    (happrox_lower : approximateLower ≤ ‖Q.partition‖)
    (insertionUpper : ℝ) (hinsertionUpper_nonneg : 0 ≤ insertionUpper)
    (hinsertion_upper : ‖Q.insertion O‖ ≤ insertionUpper) :
    ErrorCertificate
      ((R.coarsePathIntegral h).expectation O) (Q.expectation O)
      ((∑ y, radius y * ‖O y‖) / exactLower +
        insertionUpper * (∑ y, radius y) /
          (exactLower * approximateLower)) :=
  (FinitePathIntegral.FiniteRGStep.coarse_approximation_certificate
    R h Q O radius hr hw exactLower approximateLower hexact_pos happrox_pos
      hexact_lower happrox_lower insertionUpper hinsertionUpper_nonneg
      hinsertion_upper).expectation_error

noncomputable example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (Q : FinitePathIntegral κ) (O : κ → ℂ)
    (radius : κ → ℝ) (hr : ∀ y, 0 ≤ radius y)
    (hw : ∀ y, ErrorCertificate (R.coarseWeight y) (Q.weight y) (radius y))
    (exactLower approximateLower : ℝ)
    (hexact_pos : 0 < exactLower) (happrox_pos : 0 < approximateLower)
    (hexact_lower : exactLower ≤
      ‖(R.coarsePathIntegral h).partition‖)
    (happrox_lower : approximateLower ≤ ‖Q.partition‖)
    (insertionUpper : ℝ) (hinsertionUpper_nonneg : 0 ≤ insertionUpper)
    (hinsertion_upper : ‖Q.insertion O‖ ≤ insertionUpper) :
    FinitePathIntegral.NormalizedExpectationCertificate
      (R.coarsePathIntegral h) Q O :=
  FinitePathIntegral.FiniteRGStep.coarse_expectation_certificate
    R h Q O radius hr hw exactLower approximateLower hexact_pos happrox_pos
      hexact_lower happrox_lower insertionUpper hinsertionUpper_nonneg
      hinsertion_upper

example {ι κ τ : Type} [Fintype ι] [Fintype κ] [Fintype τ]
    (P : FinitePathIntegral ι) (Q : FinitePathIntegral κ)
    (R : FinitePathIntegral τ) (O : ι → ℂ) (O' : κ → ℂ) (O'' : τ → ℂ)
    (C₁ : FinitePathIntegral.ExpectationComparisonCertificate P Q O O')
    (C₂ : FinitePathIntegral.ExpectationComparisonCertificate Q R O' O'') :
    FinitePathIntegral.ExpectationComparisonCertificate P R O O'' :=
  FinitePathIntegral.ExpectationComparisonCertificate.compose C₁ C₂

example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (maps : List (κ → κ))
    (h : (∑ x, R.fineWeight x) ≠ 0) (O : κ → ℂ) :
    ((R.coarsenMany maps).coarsePathIntegral
      (by simpa only [FinitePathIntegral.FiniteRGStep.coarsenMany_fineWeight]
        using h)).expectation O =
      (R.finePathIntegral h).expectation
        (fun x => O ((R.coarsenMany maps).coarse x)) :=
  R.coarsenMany_expectation_preserved maps h O

example {ι κ τ : Type} [Fintype ι] [Fintype κ] [Fintype τ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (next : κ → τ)
    (h : (∑ x, R.fineWeight x) ≠ 0) (O : τ → ℂ) :
    ((R.coarsen next).coarsePathIntegral
      (by simpa [FinitePathIntegral.FiniteRGStep.coarsen] using h)).expectation O =
      (R.finePathIntegral h).expectation
        (fun x => O (next (R.coarse x))) :=
  R.coarsen_expectation_preserved next h O

example {ι : Type} [Fintype ι]
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (h : (∑ y, R.fineWeight y) ≠ 0)
    (hR : FinitePathIntegral.FiniteRGStep.IsFixedPoint R) (O : ι → ℂ) :
    (R.coarsePathIntegral h).expectation O =
      (R.finePathIntegral h).expectation O :=
  R.fixedPoint_expectation h hR O

example {V E : Type} [Fintype V] [Fintype E]
    (G : FiniteGradient V E) (u : V → ℝ) :
    0 ≤ G.energy u u :=
  G.energy_nonneg u

example {V E : Type} [Fintype V] [Fintype E]
    (G : FiniteGradient V E) (u v : V → ℝ) :
    G.energy u v = ∑ x, u x * G.laplacian v x :=
  G.energy_eq_pairing_laplacian u v

example {V E : Type} [Fintype V] [Fintype E]
    (G : FiniteGradient V E) (u source : V → ℝ)
    (h : G.laplacian u = source) :
    EquationResidual (fun v => G.poissonResidual v source) u 0 :=
  G.poissonResidual_zero u source h

example {ι : Type} [Fintype ι]
    (P : FiniteLinearPDE ι) (u : ι → ℝ)
    (h : P.IsSolution u) :
    EquationResidual (fun v => P.residual v) u 0 :=
  P.residual_zero u h

example {ι : Type} [Fintype ι]
    (P : FiniteLinearPDE ι) (C : P.CoercivityCertificate)
    {u v : ι → ℝ} (hu : P.IsSolution u) (hv : P.IsSolution v) :
    u = v :=
  P.solution_unique_of_coercive C hu hv

example {ι : Type} (B : FiniteBoundaryData ι)
    {u v : ι → ℝ} (hu : SatisfiesBoundary B u)
    (hv : SatisfiesBoundary B v) :
    ∀ i, B.isBoundary i → u i = v i :=
  boundary_values_agree B hu hv

example {ι : Type} [Fintype ι]
    (P : FiniteLinearPDE ι) (B : FiniteBoundaryData ι)
    (C : BoundaryCoercivityCertificate P B) {u v : ι → ℝ}
    (hu : P.IsSolution u) (hv : P.IsSolution v)
    (huB : SatisfiesBoundary B u) (hvB : SatisfiesBoundary B v) : u = v :=
  P.solution_unique_of_boundary_coercive B C hu hv huB hvB

example {ι : Type} [Fintype ι]
    (P : FiniteEllipticProblem ι) (u : ι → ℝ)
    (h : P.IsSolution u) : FiniteEllipticCertificate P u :=
  FiniteEllipticCertificate.exact P u h

example {ι : Type} [Fintype ι]
    {P : FiniteEllipticProblem ι} {u : ι → ℝ}
    (C : FiniteEllipticCertificate P u) {δ : ℝ}
    (hδ : C.residualRadius ≤ δ) :
    (FiniteEllipticCertificate.weaken C hδ).residualRadius = δ := rfl

example {ι : Type} [Fintype ι]
    {P : FiniteEllipticProblem ι} {u : ι → ℝ}
    (C₁ C₂ : FiniteEllipticCertificate P u) :
    (FiniteEllipticCertificate.combine C₁ C₂).residualRadius =
      C₁.residualRadius + C₂.residualRadius := by
  simp [FiniteEllipticCertificate.combine]

example {ι : Type} [Fintype ι]
    {P : FiniteEllipticProblem ι} {u v : ι → ℝ}
    (C : FiniteEllipticCertificate P u) (hv : P.IsSolution v)
    (S : FinitePDEResidualStability P.equation P.boundary) :
    FiniteApproximation v u (S.modulus * C.residualRadius) :=
  C.toFiniteApproximation hv S

example {ι : Type} [Fintype ι]
    (P : FiniteLinearPDE ι) (B : FiniteBoundaryData ι)
    (I : FinitePDELeftInverseCertificate P B) :
    FinitePDEResidualStability P B :=
  I.toResidualStability

example {ι : Type} [Fintype ι]
    (B : FiniteBoundaryData ι) (u : ι → ℝ)
    (h : SatisfiesBoundary B u) :
    FiniteBoundaryResidualCertificate B u :=
  FiniteBoundaryResidualCertificate.exact B u h

example {ι : Type} [Fintype ι]
    (P : FiniteEllipticProblem ι) (u : ι → ℝ)
    (h : P.IsSolution u) :
    FiniteEllipticApproximationCertificate P u :=
  FiniteEllipticApproximationCertificate.exact P u h

example {ι : Type} [Fintype ι]
    {P : FiniteEllipticProblem ι} {u : ι → ℝ}
    (C : FiniteEllipticApproximationCertificate P u)
    (hres : C.residualRadius = 0)
    (hboundary : ∀ i, C.boundary.radius i = 0) :
    P.IsSolution u :=
  C.isSolution_of_zero hres hboundary

example {ι : Type} [Fintype ι]
    (P : FiniteEllipticProblem ι) (u : ι → ℝ)
    (hbudget : ∀ i, 0 ≤ (fun _ : ι => (1 : ℝ)) i) :
    0 ≤ boundaryResidualBudget P.boundary (fun _ => (1 : ℝ)) :=
  boundaryResidualBudget_nonneg P.boundary (fun _ => (1 : ℝ)) hbudget

example {ι : Type} [Fintype ι]
    {P : FiniteEllipticProblem ι} {u v : ι → ℝ}
    (C : FiniteEllipticApproximationCertificate P u)
    (hv : P.IsSolution v)
    (S : FiniteEllipticResidualStability P) :
    ErrorCertificate u v
      (S.equationModulus * C.residualRadius +
        S.boundaryModulus *
          boundaryResidualBudget P.boundary C.boundary.radius) :=
  C.error_to_exact hv S

example {X Y : Type} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
    {A : X →+ Y} (I : AdditiveLeftInverseCertificate A)
    {x y : X} {ε : ℝ}
    (h : ErrorCertificate (A x) (A y) ε) :
    FiniteApproximation x y (I.modulus * ε) :=
  I.approximate h

/-! ## Finite time-step stability and finite correlation functions -/

example {X : Type} [PseudoMetricSpace X]
    (S : FiniteEvolutionStep X) (initial : ℝ) (stepRadius : ℕ → ℝ) (n : ℕ)
    (hi : 0 ≤ initial) (hs : ∀ k, 0 ≤ stepRadius k) :
    0 ≤ S.propagatedRadius initial stepRadius n :=
  S.propagatedRadius_nonneg hi hs n

example {X : Type} [PseudoMetricSpace X]
    (S : FiniteEvolutionStep X)
    (exact approximate : ℕ → X) (initial : ℝ) (stepRadius : ℕ → ℝ)
    (C : S.TrajectoryCertificate exact approximate initial stepRadius)
    (n : ℕ) :
    ErrorCertificate (exact n) (approximate n)
      (S.propagatedRadius initial stepRadius n) :=
  C.bound n

example {X : Type} [PseudoMetricSpace X]
    (S : FiniteEvolutionStep X) (initial : ℝ) (stepRadius : ℕ → ℝ)
    (hi : 0 ≤ initial) (hs : ∀ k, 0 ≤ stepRadius k)
    (hcontract : S.modulus ≤ 1) (n : ℕ) :
    S.propagatedRadius initial stepRadius n ≤
      initial + ∑ k ∈ Finset.range n, stepRadius k :=
  S.propagatedRadius_le_add_sum hi hs hcontract n

example {X : Type} (S : FiniteEnergyStep X) (n : ℕ) (x : X) :
    S.energy (S.iterate n x) ≤ S.factor ^ n * S.energy x :=
  S.iterate_energy_bound n x

example {X : Type} (S : FiniteEnergyStep X)
    (hfactor : S.factor ≤ 1) (n : ℕ) (x : X) :
    S.energy (S.iterate n x) ≤ S.energy x :=
  S.iterate_energy_nonincreasing hfactor n x

example {X : Type} (step : X → X) (energy : X → ℝ)
    (henergy : ∀ x, 0 ≤ energy x)
    (hconserve : ∀ x, energy (step x) = energy x) (n : ℕ) (x : X) :
    (FiniteEnergyStep.ofConserved step energy henergy hconserve).energy
        ((FiniteEnergyStep.ofConserved step energy henergy hconserve).iterate n x) =
      energy x :=
  (FiniteEnergyStep.ofConserved step energy henergy hconserve).iterate_energy_eq_of_conserved
    hconserve n x

example {X : Type} [PseudoMetricSpace X]
    (C : FiniteEvolutionEnergyStep X) (n : ℕ) (x : X) :
    C.energy.energy (C.evolution.evolve n x) ≤
      C.energy.factor ^ n * C.energy.energy x :=
  C.energy_bound n x

example {X : Type} [PseudoMetricSpace X]
    (C : FiniteEvolutionEnergyStep X)
    (exact approximate : ℕ → X) (initialRadius : ℝ)
    (stepRadius : ℕ → ℝ) (initialState : X)
    (T : C.EnergyTrajectoryCertificate exact approximate
      initialRadius stepRadius initialState) (n : ℕ) :
    ErrorCertificate (exact n) (approximate n)
      (C.evolution.propagatedRadius initialRadius stepRadius n) :=
  T.state_error n

example {X : Type} [PseudoMetricSpace X]
    (C : FiniteEvolutionEnergyStep X)
    (exact approximate : ℕ → X) (initialRadius : ℝ)
    (stepRadius : ℕ → ℝ) (initialState : X)
    (T : C.EnergyTrajectoryCertificate exact approximate
      initialRadius stepRadius initialState) (n : ℕ) :
    C.energy.energy (exact n) ≤
      C.energy.factor ^ n * C.energy.energy initialState :=
  T.exact_energy_bound n

example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι) (u : ι → ℝ)
    (hu : ∀ j, 0 ≤ u j) :
    ∀ i, 0 ≤ K.step u i :=
  K.step_nonneg hu

example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι) (u : ι → ℝ)
    (lower upper : ℝ) (hlo : ∀ j, lower ≤ u j)
    (hhi : ∀ j, u j ≤ upper) :
    ∀ i, lower ≤ K.step u i ∧ K.step u i ≤ upper :=
  K.step_bounds u lower upper hlo hhi

example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι) (u : ι → ℝ)
    (lower upper : ℝ) (hlo : ∀ j, lower ≤ u j)
    (hhi : ∀ j, u j ≤ upper) (n : ℕ) :
    ∀ i, lower ≤ K.iterate n u i ∧ K.iterate n u i ≤ upper :=
  K.iterate_bounds u lower upper hlo hhi n

example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι) (u : ι → ℝ)
    (C : FinitePositiveStep.MassConservationCertificate K) :
    ∑ i, K.step u i = ∑ i, u i :=
  K.sum_preserved C u

example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι) (u : ι → ℝ)
    (C : FinitePositiveStep.MassConservationCertificate K) (n : ℕ) :
    ∑ i, K.iterate n u i = ∑ i, u i :=
  K.iterate_sum_preserved C u n

example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι) (u v : ι → ℝ) (radius : ℝ)
    (h : FinitePositiveStep.UniformError u v radius) :
    FinitePositiveStep.UniformError (K.step u) (K.step v) radius :=
  K.step_uniformError h

example {ι : Type} [Fintype ι]
    (u v w : ι → ℝ) (r s : ℝ)
    (h₁ : FinitePositiveStep.UniformError u v r)
    (h₂ : FinitePositiveStep.UniformError v w s) :
    FinitePositiveStep.UniformError u w (r + s) :=
  FinitePositiveStep.UniformError.trans h₁ h₂

example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι)
    (exact approximate : ℕ → (ι → ℝ))
    (initialRadius : ℝ) (stepRadius : ℕ → ℝ)
    (C : FinitePositiveStep.TrajectoryCertificate
      K exact approximate initialRadius stepRadius) (n : ℕ) :
    FinitePositiveStep.UniformError (exact n) (approximate n)
      (FinitePositiveStep.propagatedRadius initialRadius stepRadius n) :=
  C.bound n

example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι) (O Q : ι → ℂ) :
    P.correlator O Q = P.correlator Q O :=
  P.correlator_swap O Q

example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι) (O Q : ι → ℂ) (c : ℂ) :
    P.connectedCorrelator (fun i => O i + c) Q =
      P.connectedCorrelator O Q :=
  P.connectedCorrelator_shift_left O Q c

example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι) (O Q : ι → ℂ)
    (h : P.correlator O Q = P.expectation O * P.expectation Q) :
    P.connectedCorrelator O Q = 0 :=
  P.connectedCorrelator_eq_zero_of_factorizes O Q h

example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι) (e : Equiv.Perm ι)
    (hsym : FinitePathIntegral.WeightSymmetry P e) (O : ι → ℂ) :
    ∑ i, P.weight i * O (e i) = ∑ i, P.weight i * O i :=
  P.insertion_reindex_of_weightSymmetry e hsym O

example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι) (e : Equiv.Perm ι)
    (hsym : FinitePathIntegral.WeightSymmetry P e) (O : ι → ℂ) :
    P.expectation (fun i => O (e i)) = P.expectation O :=
  P.expectation_reindex_of_weightSymmetry e hsym O

example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι) (e : Equiv.Perm ι)
    (hsym : FinitePathIntegral.WeightSymmetry P e) (O : ι → ℂ) :
    ∑ i, P.weight i * (O (e i) - O i) = 0 :=
  P.insertion_symmetry_difference_zero e hsym O

example {ι : Type} [Fintype ι] (P : FinitePathIntegral ι) :
    P.multiCorrelator [] = 1 :=
  P.multiCorrelator_nil

example {ι : Type} [Fintype ι] (P : FinitePathIntegral ι)
    {xs ys : List (ι → ℂ)} (h : xs.Perm ys) :
    P.multiCorrelator xs = P.multiCorrelator ys :=
  P.multiCorrelator_perm h

example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (observables : List (κ → ℂ)) :
    (R.coarsePathIntegral h).multiCorrelator observables =
      (R.finePathIntegral h).multiCorrelator
        (observables.map (fun O => fun x => O (R.coarse x))) :=
  FinitePathIntegral.multiCorrelator_coarsen R h observables

example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι) (u f : ι → ℝ)
    (lower upper sourceLower sourceUpper : ℝ)
    (hlo : ∀ j, lower ≤ u j) (hhi : ∀ j, u j ≤ upper)
    (hslo : ∀ i, sourceLower ≤ f i)
    (hshi : ∀ i, f i ≤ sourceUpper) :
    ∀ i, lower + sourceLower ≤ K.drivenStep u f i ∧
      K.drivenStep u f i ≤ upper + sourceUpper :=
  K.drivenStep_bounds u f lower upper sourceLower sourceUpper hlo hhi hslo hshi

example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι)
    (source : ℕ → (ι → ℝ))
    (exact approximate : ℕ → (ι → ℝ))
    (initialRadius : ℝ) (stepRadius : ℕ → ℝ)
    (C : FinitePositiveStep.DrivenTrajectoryCertificate K source
      exact approximate initialRadius stepRadius) (n : ℕ) :
    FinitePositiveStep.UniformError (exact n) (approximate n)
      (FinitePositiveStep.propagatedRadius initialRadius stepRadius n) :=
  C.bound n

example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι) (u f g : ι → ℝ) (radius : ℝ)
    (h : FinitePositiveStep.UniformError f g radius) :
    FinitePositiveStep.UniformError (K.drivenStep u f)
      (K.drivenStep u g) radius :=
  K.drivenStep_source_uniformError h

example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι)
    (exactSource approximateSource : ℕ → (ι → ℝ))
    (exact approximate : ℕ → (ι → ℝ))
    (initialRadius : ℝ) (sourceRadius stepRadius : ℕ → ℝ)
    (C : FinitePositiveStep.SourceDrivenTrajectoryCertificate K
      exactSource approximateSource exact approximate initialRadius
      sourceRadius stepRadius) (n : ℕ) :
    FinitePositiveStep.UniformError (exact n) (approximate n)
      (FinitePositiveStep.sourcePropagatedRadius initialRadius
        sourceRadius stepRadius n) :=
  C.bound n

example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι) (field : ι → ℂ) (source : ℂ) :
    P.sourceGeneratingPolynomial field source 0 = 1 :=
  P.sourceGeneratingPolynomial_zero field source

example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι) (field : ι → ℂ) (source : ℂ) :
    P.sourceInsertion field (fun _ => source) = source * P.moment field 1 :=
  P.sourceInsertion_eq_source_mul_moment field source

example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι)
    (V : FinitePathIntegral.InvolutiveVariation P) (O : ι → ℂ) :
    P.expectation (fun i => O (V.map i) - O i) =
      P.expectation (fun i => (V.jacobian i - 1) * O i) :=
  P.schwinger_dyson_expectation V O

example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι)
    (V : FinitePathIntegral.InvolutiveVariation P)
    (hjac : ∀ i, V.jacobian i = 1) (O : ι → ℂ) :
    P.expectation (fun i => O (V.map i) - O i) = 0 :=
  P.schwinger_dyson_of_invariant_weight V hjac O

example {ι : Type} [Fintype ι]
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (hR : FinitePathIntegral.FiniteRGStep.IsFixedPoint R) :
    FinitePathIntegral.FiniteRGStep.FixedPointDefect R :=
  FinitePathIntegral.FiniteRGStep.FixedPointDefect.exact R hR

example {ι : Type} [Fintype ι]
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (C : FinitePathIntegral.FiniteRGStep.FixedPointDefect R) :
    ErrorCertificate (∑ y, R.coarseWeight y) (∑ y, R.fineWeight y)
      (∑ y, C.radius y) :=
  C.partition_error R

example {ι : Type} [Fintype ι]
    (R S : FinitePathIntegral.FiniteRGStep ι ι)
    (hmiddle : S.fineWeight = R.coarseWeight)
    (first : FinitePathIntegral.FiniteRGStep.FixedPointDefect R)
    (second : FinitePathIntegral.FiniteRGStep.FixedPointDefect S) :
    FinitePathIntegral.FiniteRGStep.FixedPointDefect (R.coarsen S.coarse) :=
  FinitePathIntegral.FiniteRGStep.FixedPointDefect.compose
    R S hmiddle first second

example {ι : Type} [Fintype ι]
    (R S : FinitePathIntegral.FiniteRGStep ι ι)
    (hmiddle : S.fineWeight = R.coarseWeight)
    (first : FinitePathIntegral.FiniteRGStep.FixedPointDefect R)
    (second : FinitePathIntegral.FiniteRGStep.FixedPointDefect S) :
    ErrorCertificate
      (∑ y, (R.coarsen S.coarse).coarseWeight y)
      (∑ y, R.fineWeight y)
      (∑ y, (first.radius y + second.radius y)) :=
  FinitePathIntegral.FiniteRGStep.FixedPointDefect.compose_partition_error
    R S hmiddle first second

example {ι α : Type} [Fintype ι] [Fintype α]
    (G : FiniteGramKernel ι α) (f : ι → ℝ) :
    0 ≤ G.quadratic f :=
  G.quadratic_nonneg f

example {ι α : Type} [Fintype ι] [Fintype α]
    (G : FiniteGramKernel ι α) (f : ι → ℝ) :
    0 ≤ G.kernelQuadratic f :=
  G.kernelQuadratic_nonneg f

example {ι α : Type} [Fintype ι] [Fintype α]
    (C : FiniteReflectionCertificate ι α) (f : ι → ℝ) :
    0 ≤ C.reflectedQuadratic f :=
  C.reflectedQuadratic_nonneg f

example {ι α : Type} [Fintype ι] [Fintype α]
    (C : FiniteReflectionCertificate ι α) (f : ι → ℝ) :
    0 ≤ C.reflectedKernelQuadratic f :=
  C.reflectedKernelQuadratic_nonneg f

example {ι : Type} [Fintype ι]
    (P : FinitePositivePathIntegral ι) :
    0 < (P.toComplex).partition.re :=
  P.toComplex_partition_pos

example {ι α : Type} [Fintype ι] [Fintype α]
    (G : FiniteWeightedGramKernel ι α) (f : ι → ℝ) :
    0 ≤ G.kernelQuadratic f :=
  G.kernelQuadratic_nonneg f

example {ι α : Type} [Fintype ι] [Fintype α]
    (P : FinitePositivePathIntegral α) (feature : ι → α → ℝ)
    (f : ι → ℝ) :
    0 ≤ (FiniteWeightedGramKernel.fromPath P feature).kernelQuadratic f :=
  (FiniteWeightedGramKernel.fromPath P feature).kernelQuadratic_nonneg f

example {ι α : Type} [Fintype ι] [Fintype α]
    (C : FiniteWeightedReflectionCertificate ι α) (f : ι → ℝ) :
    0 ≤ C.reflectedKernelQuadratic f :=
  C.reflectedKernelQuadratic_nonneg f

/-! ## Cross-domain proof-preserving process API

These checks exercise the reusable adapters rather than a new physical model:
the same validity-preserving composition and iteration laws are instantiated
for positive finite updates, abstract CPTP maps, rectangular Kraus channels,
Markov kernels and finite unitary density evolution. -/

example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι) (u : ι → ℝ)
    (hu : FinitePositiveStep.NonnegativeField u) :
    FinitePositiveStep.NonnegativeField
      (FinitePositiveStep.toStateMap K u) := by
  exact StateMap.valid_apply (FinitePositiveStep.toStateMap K) hu

example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι) (u : ι → ℝ) (n : ℕ)
    (hu : FinitePositiveStep.NonnegativeField u) :
    FinitePositiveStep.NonnegativeField
      (Process.iterate (FinitePositiveStep.toStateMap K) n u) :=
  Process.iterate_valid (FinitePositiveStep.toStateMap K) n hu

example {S Q : Type} {Valid : S → Prop}
    (P : Process S Valid) (I : Invariant P Q) (s : S) (hs : Valid s) (n : ℕ) :
    I.quantity (Process.iterate P n s) = I.quantity s :=
  I.iterate P n hs

example {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (after : FiniteCPTPMap κ μ) (before : FiniteCPTPMap ι κ)
    (rho : Matrix ι ι ℂ) (hrho : IsFiniteDensity rho) :
    IsFiniteDensity
      ((FiniteCPTPMap.toStateMap after).compose
        (FiniteCPTPMap.toStateMap before) rho) := by
  exact StateMap.valid_apply
    ((FiniteCPTPMap.toStateMap after).compose
      (FiniteCPTPMap.toStateMap before)) hrho

example {ι κ μ ξ ζ : Type}
    [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ξ] [Fintype ζ]
    [DecidableEq ι] [DecidableEq κ]
    (after : TypedKrausChannel κ μ ζ)
    (before : TypedKrausChannel ι κ ξ)
    (rho : Matrix ι ι ℂ) (hrho : IsFiniteDensity rho) :
    IsFiniteDensity
      ((TypedKrausChannel.toStateMap after).compose
        (TypedKrausChannel.toStateMap before) rho) := by
  exact StateMap.valid_apply
    ((TypedKrausChannel.toStateMap after).compose
      (TypedKrausChannel.toStateMap before)) hrho

example {ι : Type} [Fintype ι]
    (K : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) :
    (K.toStateMap p).expectation (fun _ => (1 : ℝ)) =
      p.expectation (K.toObservableTransport.pullback (fun _ => (1 : ℝ))) := by
  exact K.step_expectation p (fun _ => 1)

example {ι : Type} [Fintype ι]
    (K L : LeanPhy.StatMech.FiniteKernel ι)
    (p : LeanPhy.StatMech.FiniteProbability ι) (f : ι → ℝ) :
    ((L.toStateMap.compose K.toStateMap) p).expectation f =
      p.expectation
        ((ObservableTransport.compose L.toObservableTransport
          K.toObservableTransport).pullback f) := by
  exact (ObservableTransport.compose L.toObservableTransport
    K.toObservableTransport).compatible p trivial f

example {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : FiniteUnitary ι) (rho : FiniteDensity ι) :
    (FiniteUnitary.toStateMap U) rho = U.evolveDensity rho := rfl

/-! ## Continuum and operator-boundary smoke tests

These examples exercise the public certificates added for approximation,
dissipation, dense-domain operators and renormalisation.  Each one keeps the
analytic or physical existence statement in an explicit hypothesis. -/

example :
    UniformOperatorApproximationCertificate
      (fun _ : ℕ => (ContinuousLinearMap.id ℝ ℝ))
      (ContinuousLinearMap.id ℝ ℝ)
      (fun _ => (0 : ℝ)) := by
  refine { nonneg := ?_, bound := ?_, radius_tendsto_zero := ?_ }
  · intro n; norm_num
  · intro n; simp
  · simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

example (x : ℝ) :
    Tendsto
      (fun n : ℕ => (ContinuousLinearMap.id ℝ ℝ) x)
      atTop (𝓝 ((ContinuousLinearMap.id ℝ ℝ) x)) := by
  exact tendsto_const_nhds

example : EnergyDissipationCertificate
    (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => (0 : ℝ))
    (fun _ : ℝ => (0 : ℝ)) 0 1 := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; norm_num
  · intro t; norm_num
  · simpa using (intervalIntegrable_const (μ := volume) (c := (0 : ℝ)) (a := (0 : ℝ)) (b := 1))
  · simpa using (intervalIntegrable_const (μ := volume) (c := (0 : ℝ)) (a := (0 : ℝ)) (b := 1))
  · simp

example : EnergyResidualCertificate
    (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => (0 : ℝ))
    (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => (0 : ℝ)) 0 1 := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; norm_num
  · simpa using (intervalIntegrable_const (μ := volume) (c := (0 : ℝ)) (a := (0 : ℝ)) (b := 1))
  · simpa using (intervalIntegrable_const (μ := volume) (c := (0 : ℝ)) (a := (0 : ℝ)) (b := 1))
  · simpa using (intervalIntegrable_const (μ := volume) (c := (0 : ℝ)) (a := (0 : ℝ)) (b := 1))
  · simp

noncomputable section

noncomputable def smokeDenseZero : DenseDomainOperator (𝕜 := ℂ) (E := ℂ) where
  domain := ⊤
  dense := by simpa using (dense_univ : Dense (Set.univ : Set ℂ))
  operator := (0 : (⊤ : Submodule ℂ ℂ) →ₗ[ℂ] ℂ)

def smokeInverse : ℂ →ₗ[ℂ] (⊤ : Submodule ℂ ℂ) where
  toFun := fun y => ⟨y, by simp⟩
  map_add' := by intro x y; apply Subtype.ext; simp
  map_smul' := by intro c y; apply Subtype.ext; simp

example : DomainResolventCertificate smokeDenseZero 1 where
  inverse := smokeInverse
  right_inverse := by
    intro y
    change (1 : ℂ) • y - 0 = y
    simp
  left_inverse := by
    intro x
    apply Subtype.ext
    change (↑(smokeInverse ((1 : ℂ) • (↑x : ℂ) - (0 : ℂ))) : ℂ) = ↑x
    rw [show (1 : ℂ) • (↑x : ℂ) - (0 : ℂ) = ↑x by simp]
    rfl

/-! The `LinearPMap` bridge keeps the dense domain visible while exposing
mathlib's formal-adjoint and graph-operator interfaces.  This smoke object is
deliberately bounded as a map, but is represented through the same domain-aware
API used by unbounded Hamiltonians. -/

noncomputable section UnboundedOperatorBridgeSmoke

def smokeZeroSymmetric : SymmetricDomainCertificate smokeDenseZero where
  inner_eq := by
    intro x y
    change (y : ℂ) * star (0 : ℂ) = (0 : ℂ) * star (x : ℂ)
    simp

example :
    smokeDenseZero.asPMap.IsFormalAdjoint smokeDenseZero.asPMap :=
  DenseDomainOperator.symmetric_formalAdjoint smokeDenseZero smokeZeroSymmetric

example : (LinearPMap.adjoint smokeDenseZero.asPMap).IsClosed :=
  DenseDomainOperator.formalAdjoint_isClosed smokeDenseZero

def smokeZeroGraphBound :
    DenseDomainOperator.GraphBoundCertificate smokeDenseZero
      smokeDenseZero.operator 0 0 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro x
  change ‖(0 : ℂ)‖ ≤ 0 * ‖(x : ℂ)‖ + 0 * ‖(0 : ℂ)‖
  norm_num

example (x : smokeDenseZero.domain) :
    ‖smokeDenseZero.operator x‖ ≤
      max 0 0 * smokeDenseZero.graphNorm x := by
  exact smokeZeroGraphBound.by_graphNorm x

def smokeIdentityPreserving :
    DenseDomainOperator.DomainPreserving smokeDenseZero where
  bounded := ContinuousLinearMap.id ℂ ℂ
  maps_domain := by
    intro x
    exact x.property

example (x : smokeDenseZero.domain) :
    (smokeIdentityPreserving.onDomain x : ℂ) = (x : ℂ) := by
  simpa [smokeIdentityPreserving] using
    smokeIdentityPreserving.onDomain_coe x

end UnboundedOperatorBridgeSmoke

def smokeRenormalization : RenormalizationCertificate
    (fun _ : ℕ => (0 : ℝ)) (fun _ : ℕ => (0 : ℝ))
    (fun _ : ℕ => (0 : ℝ)) 0 where
  relation := by intro n; norm_num
  limit_tendsto := tendsto_const_nhds

example : (0 : ℝ) = 0 :=
  RenormalizationCertificate.value_unique smokeRenormalization smokeRenormalization

example : (0 : ℝ) = 0 := by
  apply RenormalizationCertificate.values_eq_of_bare_counterterm_differences
    smokeRenormalization smokeRenormalization
  · simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end

/-! ## Polynomial spectral calculus and finite self-adjoint bridge -/

noncomputable section SpectralCalculusSmoke

def spectralIdentity : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  LinearMap.id

def spectralIdentityCertificate :
    FiniteSelfAdjointSpectrumCertificate
      (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin 2)) spectralIdentity 2 := by
  refine ⟨?_, ?_⟩
  · intro x y
    simp [spectralIdentity]
  · simp [spectralIdentity]

example (p : Polynomial ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    (aeval spectralIdentity p) v = p.eval 1 • v := by
  apply polynomial_aeval_apply_eigenvector
  simp [spectralIdentity]

example (i : Fin 2) :
    spectralIdentity
        (FiniteSelfAdjointSpectrumCertificate.eigenvectorBasis
          spectralIdentityCertificate i) =
      (FiniteSelfAdjointSpectrumCertificate.eigenvalues
          spectralIdentityCertificate i : ℂ) •
        FiniteSelfAdjointSpectrumCertificate.eigenvectorBasis
          spectralIdentityCertificate i := by
  exact FiniteSelfAdjointSpectrumCertificate.basis_apply
    spectralIdentityCertificate i

example (A : ℂ →L[ℂ] ℂ) (p : Polynomial ℂ) :
    spectrum ℂ (aeval A p) = (fun z => p.eval z) '' spectrum ℂ A :=
  polynomial_spectrum_map A p

example (A : ℂ →L[ℂ] ℂ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (‖A ^ n‖ ^ (1 / n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ A)) :=
  spectral_radius_gelfand_limit A

example (A : ℂ →L[ℂ] ℂ) (v : ℂ) (eigenvalue : ℂ)
    (hA : A v = eigenvalue • v) (p : Polynomial ℂ) :
    polynomialAction A p v = p.eval eigenvalue • v :=
  polynomialAction_apply_eigenvector A v eigenvalue hA p

end SpectralCalculusSmoke

/-! ## Spectral-gap contraction smoke -/

noncomputable section SpectralGapSmoke

def zeroSpectralGapCertificate :
    SpectralGapCertificate (0 : ℂ →L[ℂ] ℂ) (0 : ℂ →L[ℂ] ℂ) 0 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · ext x
    simp
  · ext x
    simp
  · ext x
    simp
  · intro x
    simp

def halfSpectralGapCertificate :
    SpectralGapCertificate
      ((1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) (0 : ℂ →L[ℂ] ℂ) (1 / 2 : ℝ) := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · ext x
    simp
  · ext x
    simp
  · ext x
    simp
  · intro x
    simp

example (n : ℕ) (x : ℂ) :
    ‖((0 : ℂ →L[ℂ] ℂ) ^ n) x - (0 : ℂ →L[ℂ] ℂ) x‖ ≤
      (0 : ℝ) ^ n * ‖x - (0 : ℂ →L[ℂ] ℂ) x‖ :=
  SpectralGapCertificate.iterate_decay zeroSpectralGapCertificate n x

example (x : ℂ) :
    Tendsto (fun n : ℕ => ((0 : ℂ →L[ℂ] ℂ) ^ n) x) atTop
      (𝓝 ((0 : ℂ →L[ℂ] ℂ) x)) :=
  SpectralGapCertificate.iterate_tendsto_projection zeroSpectralGapCertificate x

example (x : ℂ) :
    Tendsto
        (fun n : ℕ => (((1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) ^ n) x) atTop
        (𝓝 ((0 : ℂ →L[ℂ] ℂ) x)) :=
  SpectralGapCertificate.iterate_tendsto_projection halfSpectralGapCertificate x

example (L : ℂ →L[ℂ] ℂ) (x : ℂ) :
    Tendsto (fun n : ℕ => L (((0 : ℂ →L[ℂ] ℂ) ^ n) x)) atTop
      (𝓝 (L ((0 : ℂ →L[ℂ] ℂ) x))) :=
  SpectralGapCertificate.observable_tendsto_projection
    zeroSpectralGapCertificate L x

end SpectralGapSmoke

/-! ## Constrained symmetry and gauge-orbit smoke -/

namespace ConstrainedSymmetrySmoke

instance : SMul Unit Nat := ⟨fun _ n => n⟩
instance : MulAction Unit Nat where
  one_smul := by intro n; rfl
  mul_smul := by intro _ _ n; rfl

def system : ConstrainedSymmetry Unit Nat where
  admissible := fun n => n ≤ 10
  constrained := fun n => n % 2 = 0
  admissible_preserved := by intro _ n hn; exact hn
  constrained_preserved := by intro _ n hn; exact hn

def parityConstraint : EquivariantConstraint Unit Nat Nat where
  value := fun n => n % 2
  equivariant := by intro _ n; rfl
  zero_fixed := by intro _; rfl

def equationSystem : ConstrainedSymmetry Unit Nat :=
  parityConstraint.toConstrainedSymmetry (fun n => n ≤ 10)
    (by intro _ n hn; exact hn)

example : equationSystem.physical 2 := by
  refine ⟨?_, ?_⟩
  · change 2 ≤ 10
    norm_num
  change parityConstraint.value 2 = 0
  norm_num [parityConstraint]

def dynamics : ConstrainedSymmetry.ConstrainedDynamics system where
  step := id
  preserves_physical := by intro n hn; exact hn
  equivariant := by intro _ n; rfl

def observable : ConstrainedSymmetry.ConstrainedObservable system Nat where
  eval := fun n => n % 2
  invariant_on_physical := by intro _ n _; rfl

def physicalTwo : system.physical 2 := by
  simpa [ConstrainedSymmetry.physical, system] using
    (show 2 ≤ 10 ∧ 2 % 2 = 0 by norm_num)

def physicalTwoState : ConstrainedSymmetry.PhysicalState system :=
  ⟨2, physicalTwo⟩

example : system.physical (dynamics.evolve 12 2) :=
  dynamics.evolve_physical 12 physicalTwo

example : system.orbitEquivalent 2 2 :=
  ConstrainedSymmetry.orbitEquivalent_refl system 2

example : observable.eval (dynamics.evolve 12 2) = observable.eval 2 := by
  apply dynamics.observable_evolve_eq observable 12 physicalTwo
  exact ConstrainedSymmetry.orbitEquivalent_refl system 2

example : observable.descend (Quotient.mk _ physicalTwoState) = 0 := by
  simp [physicalTwoState, observable]

end ConstrainedSymmetrySmoke

/-! ## First-class constraint algebra

This finite polynomial example exercises the algebraic Dirac-constraint
boundary.  The constraint ideal and first-class closure are explicit inputs;
weak equality and closure of Dirac observables are derived in the kernel.  No
gauge fixing, quotient regularity, or Hamiltonian flow is inferred.
-/
namespace FirstClassConstraintSmoke

open LeanPhy.Classical

noncomputable def qConstraint :
    FirstClassConstraintAlgebra ℝ PhasePolynomial Unit where
  poisson := canonicalPolynomialPoisson
  constraint := fun _ => qPolynomial
  first_class := by
    intro _ _
    simpa [qPolynomial] using canonical_q_q

example : qPolynomial ∈ qConstraint.constraintIdeal :=
  qConstraint.constraint_mem ()

example : qConstraint.poisson qPolynomial qPolynomial ∈ qConstraint.constraintIdeal :=
  qConstraint.bracket_constraint_mem () ()

example : qConstraint.WeaklyEqual qPolynomial 0 := by
  exact qConstraint.weaklyEqual_zero_iff.mpr (qConstraint.constraint_mem ())

example : qConstraint.IsDiracObservable qPolynomial :=
  qConstraint.constraint_isDiracObservable ()

example {f g : PhasePolynomial}
    (hf : qConstraint.IsDiracObservable f)
    (hg : qConstraint.IsDiracObservable g) :
    qConstraint.IsDiracObservable (f * g) :=
  qConstraint.dirac_mul hf hg

example {f g : PhasePolynomial}
    (hf : qConstraint.IsDiracObservable f)
    (hg : qConstraint.IsDiracObservable g) :
    qConstraint.IsDiracObservable (qConstraint.poisson f g) :=
  qConstraint.dirac_bracket hf hg

noncomputable def qConstraintMap :
    FirstClassConstraintAlgebra.ConstraintMap qConstraint qConstraint :=
  FirstClassConstraintAlgebra.ConstraintMap.id qConstraint

theorem qConstraintCover :
    FirstClassConstraintAlgebra.ConstraintMap.CoversConstraintIdeal
      qConstraintMap := by
  intro c hc
  exact ⟨c, hc, rfl⟩

example {f g : PhasePolynomial}
    (hfg : qConstraint.WeaklyEqual f g) :
    qConstraint.WeaklyEqual (qConstraintMap f) (qConstraintMap g) :=
  qConstraintMap.map_weaklyEqual hfg

example {f : PhasePolynomial}
    (hf : qConstraint.IsDiracObservable f) :
    qConstraint.IsDiracObservable (qConstraintMap f) :=
  qConstraintMap.map_diracObservable qConstraintCover hf

example :
    FirstClassConstraintAlgebra.ConstraintMap.comp
      (FirstClassConstraintAlgebra.ConstraintMap.id qConstraint) qConstraintMap =
      qConstraintMap :=
  qConstraintMap.comp_id_left

end FirstClassConstraintSmoke

/-! ## Executable acceptance report -/

def capabilities : List (String × String) :=
   [("Banach contraction fixed point", "a certified contraction on any nonempty complete metric space has a kernel-checked unique fixed point and convergent iteration"),
   ("first-class constraint ideal", "declared constraint generators form a first-class ideal whose Poisson bracket closure is checked"),
   ("Dirac weak equality", "equality modulo the generated constraint ideal is an explicit equivalence relation"),
   ("Dirac observable normalizer", "observables whose brackets with every constraint are weakly zero are represented by a checked predicate"),
   ("constraint observable closure", "Dirac observables are closed under scalar action, products, sums and Poisson brackets"),
   ("constraint-ideal map", "a Poisson algebra map sends the generated source constraint ideal into the target ideal"),
   ("weak-equality transport", "constraint-preserving maps transport equality modulo the constraint ideal"),
   ("composable constraint maps", "constraint-preserving Poisson maps compose and have a checked identity"),
   ("Dirac-observable map", "a target-ideal cover makes transport of Dirac observables a checked theorem"),
   ("constraint-preserving symmetry", "admissible and constrained physical states are preserved by a declared group action"),
   ("covariant constraint equation", "a value-valued equivariant constraint yields a checked zero-fibre physical-state predicate when the group fixes zero"),
   ("gauge-orbit equivalence", "the orbit relation is kernel-checked as an equivalence and transports physical-state predicates"),
   ("orbit-invariant observables", "a physical observable descends along declared symmetry orbits only after its invariance proof"),
   ("equivariant constrained dynamics", "finite iterates preserve constraints and carry orbit-equivalent states to orbit-equivalent states"),
   ("uniform operator approximation", "operator-norm error radii imply checked vector and bounded-observable convergence; the radius-to-zero hypothesis is explicit"),
   ("strong operator convergence", "pointwise convergence of bounded operators transports through every bounded observable"),
   ("energy dissipation budget", "nonnegative dissipation and forcing integrability give a checked integrated energy bound"),
   ("residual energy budget", "a numerical or finite-volume residual is carried as an explicit nonnegative energy error budget"),
   ("dense-domain unbounded operator", "a declared dense domain keeps unbounded operators separate from bounded maps and records symmetry/resolvent equations"),
   ("LinearPMap domain bridge", "a declared dense-domain operator is exposed as mathlib's partially defined LinearPMap without erasing its domain"),
   ("formal adjoint and closedness", "symmetry, formal-adjoint maximality and adjoint closedness are available only through kernel-checked domain-aware interfaces"),
   ("graph-norm relative bounds", "explicit graph-norm estimates compose relative perturbation bounds without treating an unbounded operator as ambiently bounded"),
   ("domain-preserving bounded composition", "bounded maps can be restricted and composed on an unbounded operator domain only after maps-domain proofs are supplied"),
   ("renormalisation limit certificate", "bare quantity, counterterm, regulator relation and limit remain explicit; uniqueness and scheme independence are derived only from supplied limits"),
   ("contraction a priori error", "Picard iterates carry an explicit geometric distance bound from the fixed point"),
   ("contraction perturbation stability", "uniform map error gives a checked C divided by one-minus-K bound between fixed points"),
   ("invariant-subset contraction interface", "complete forward-invariant subsets expose fixed-point membership and iterate error bounds"),
   ("bounded Hilbert-flow envelope", "an explicit operator-norm envelope gives state-norm and semigroup bounds for any bounded Hilbert flow"),
   ("interval Bochner integral certificates", "interval integrability plus an equality certificate composes under sums, scalar actions and bounded linear maps"),
   ("Duhamel variation-of-constants bounds", "a supplied endpoint representation and source majorant yield a checked finite-time propagation error bound"),
   ("bounded resolvent identity", "two checked bounded-operator inverses imply the perturbative resolvent identity"),
   ("resolvent inverse witness", "a proof-valued resolvent certificate exposes its selected inverse only after both inverse equations are checked"),
   ("resolvent inverse uniqueness", "any independently checked two-sided inverse agrees with the certificate's selected inverse"),
   ("quantitative resolvent perturbation", "explicit inverse and operator-difference norm envelopes give a kernel-checked resolvent error bound"),
   ("infinite-dimensional mean ergodic theorem", "a contractive bounded operator on any complete Hilbert space has Birkhoff averages converging to the fixed-point projection"),
   ("Hilbert observable ergodic limit", "bounded linear observables preserve the certified mean-ergodic limit"),
   ("fixed-state time average", "a nonzero finite Birkhoff average of a fixed vector is exactly that vector"),
   ("spectral-radius power limit", "Gelfand's formula exposes the checked ENNReal limit of operator-power norms"),
   ("polynomial spectral mapping", "the spectrum of a bounded complex operator polynomial is the polynomial image of the original spectrum"),
   ("polynomial eigenvector action", "a polynomial in a linear operator acts on a certified eigenvector by scalar polynomial evaluation"),
   ("spectral-gap iteration decay", "an explicit invariant projection and one-step residual contraction give a kernel-checked geometric bound for every iterate"),
   ("spectral-gap observable limit", "bounded linear observables converge to the invariant projection under the certified discrete spectral gap"),
   ("nontrivial scalar spectral gap", "the scalar half-contraction example exercises the geometric limit with rho = 1/2 rather than only the zero map"),
   ("finite self-adjoint eigenbasis bridge", "finite-dimensional symmetry supplies a kernel-checked real eigenvalue list, orthonormal eigenbasis and diagonal characteristic polynomial"),
   ("finite spectral interval ledger", "supplied lower and upper eigenvalue bounds become reusable interval certificates without inferring bounds from samples"),
   ("weak Hilbert-space PDE", "a coercive bilinear form exposes Lax--Milgram existence, variational identity and uniqueness with explicit witnesses"),
   ("finite-dimensional QM", "Pauli algebra, Heisenberg commutator, spin-1/2 su(2) and Casimir"),
   ("dominated-convergence certificates", "Bochner integral limits require explicit measurability, integrable domination and almost-everywhere convergence"),
   ("normalized path-observable limits", "separate weight and insertion domination plus a nonzero limiting partition imply normalized expectation convergence"),
   ("Rayleigh interval certificates", "bounded self-adjoint quadratic-form bounds imply checked Rayleigh and operator-norm bounds"),
   ("positive bounded-Hilbert bridge", "complex positive-operator certificates restrict the real spectrum to nonnegative values"),
   ("continuous limits as explicit certificates", "Filter.Tendsto certificates compose through continuous maps, sums, differences, scalar actions and norms; existence is never inferred"),
   ("Bochner integral certificates", "Integrable functions carry checked integral equalities and compose under sums, scalar multiplication and continuous linear maps"),
   ("continuous path-integral certificates", "an integrable complex weight, nonzero partition function and observable insertion certificates give checked normalized expectations; path-measure existence, OS positivity and renormalisation remain explicit"),
   ("bounded-operator spectrum bridge", "continuous linear maps expose mathlib spectrum/resolvent predicates, checked two-sided inverses, compact/closed spectrum and norm-based spectral exclusion"),
   ("Neumann spectral exclusion", "a bounded operator with norm below one gets a checked two-sided inverse for one minus the operator and is excluded from the spectrum at one"),
   ("coefficient-generic variance tensors", "mixed composition, identity, trace cyclicity and vector action work over any commutative semiring, not only ℂ"),
   ("dimension-aware quotients", "division carries the difference of SI exponent vectors and rejects dimensionally invalid result types"),
   ("dimension-aware inverse", "inverse is an explicit dimension-changing operation, avoiding Lean's same-type Inv shortcut"),
   ("dimension-aware powers", "natural powers expose n-fold exponent scaling in the Quantity result type"),
   ("mechanics dimension aliases", "frequency, momentum, energy, action and charge tags are reusable across mechanics and field domains"),
   ("dimension algebra laws", "dimension vectors expose zero, negation and subtraction identities for simplification"),
   ("typed quantity map", "coefficient changes preserve physical dimensions through Quantity.map"),
   ("dimension-safe energy products", "momentum times velocity and energy times time expose checked action/energy dimensions"),
   ("dimension-safe scalar action", "ordinary complex prefactors act on a Quantity without erasing its dimension tag"),
   ("coefficient-polymorphic dimensions", "the same length/time and derived tags work over real, rational or abstract coefficient domains"),
   ("dimension exponent scaling", "dimensionScale is additive in the natural exponent, supporting compositional power bookkeeping"),
   ("physical model contract", "an admissible state predicate, proof-preserving step and typed observable evaluation form one domain-neutral model interface"),
   ("model refinement map", "a state map with dynamics and observable commutation gives a checked bridge between exact, truncated and domain-adapted models"),
   ("finite model-map iteration", "the refinement bridge commutes with every finite iterate, so repeated simulation does not require re-proving the one-step law"),
   ("model-map composition", "dynamics-preserving maps compose associatively with observable pullbacks, enabling multi-stage discretisation and cross-domain derivations"),
   ("product physical models", "independent quantum, Markov, lattice or field subsystems form a product model while retaining validity and paired observables"),
   ("Markov model adapter", "finite kernels instantiate PhysicalModel and a one-step intertwining proof yields finite-time expectation transport"),
   ("quantum model adapter", "finite CPTP and rectangular Kraus maps instantiate PhysicalModel with trace-pairing observables and checked finite-time transport"),
   ("proof-preserving state maps", "a common dependent StateMap contract composes only when source and target validity predicates are proved"),
   ("product state maps", "independent subsystem maps combine with a conjunctive validity proof and a checked product composition law"),
   ("finite process iteration", "the same kernel-checked validity and invariant laws cover repeated finite updates across domains"),
   ("parallel process iteration", "product processes satisfy a shared iterate law, so tensor-product and hybrid finite evolutions reuse one theorem"),
   ("parallel invariants", "component invariants combine into a product invariant without restating domain-specific preservation proofs"),
   ("positive-step state adapter", "finite diffusion and Markov-style positive updates reuse StateMap without dropping componentwise nonnegativity"),
   ("abstract finite CPTP maps", "arbitrary finite linear maps carry positivity, trace preservation and all finite ancillary complete-positivity obligations as composable structure fields"),
   ("CPTP state-map composition", "CPTP maps of different finite matrix sizes compose through the shared density-state invariant"),
   ("rectangular Kraus state-map composition", "cross-dimensional Kraus channels enter the same proof-preserving graph with positivity and trace one retained"),
   ("CPTP identity and composition", "the abstract channel bundle has kernel-checked state transport, identity and composition laws independent of any Kraus presentation"),
   ("finite Hamiltonian exponential flow", "a Hermitian Pauli Hamiltonian yields exp(i t H) as a kernel-checked finite unitary; time addition, trace preservation and density positivity are verified"),
   ("generic finite linear flow", "a scalar-polymorphic matrix flow records zero-time and semigroup composition, providing one algebraic interface for quantum, classical, BdG, transfer and response evolutions"),
   ("generic finite-flow invariant", "a commuting observable is fixed by matrix-exponential conjugation using only a checked inverse law; no physical interpretation is built into the theorem"),
   ("quantum flow-invariant adapter", "the Heisenberg-style finite invariant is exposed under quantum vocabulary while reusing the domain-neutral flow theorem"),
   ("classical linear-flow invariant", "real RCLike matrix exponentials use the same commutation-to-invariance theorem for finite classical and relativistic systems"),
   ("BdG flow-invariant adapter", "a conserved finite BdG mode is represented by the shared matrix-flow invariant contract"),
   ("transfer-flow invariant adapter", "finite statistical transfer generators reuse the same invariant contract as quantum and classical propagators"),
   ("finite-mode field-flow invariant", "finite field-theory mode generators reuse the generic exponential invariant while continuum and Fock limits remain explicit"),
   ("real linear exponential evolution", "the generic matrix-exponential flow and state propagation compile over real RCLike scalars, covering finite classical and relativistic linear systems"),
   ("finite flow state semigroup", "state-vector evolution satisfies the checked composition law U(t+s)v = U(t)(U(s)v), with no hidden ODE or positivity claim"),
   ("Hamiltonian flow adapter", "the finite Hermitian quantum propagator instantiates the domain-neutral linear-flow structure, so later physics modules can consume its semigroup law directly"),
   ("Hamiltonian flow-invariant adapter", "the finite Hermitian Hamiltonian consumes the generic commutation-to-invariance theorem, exposing the same conservation contract to downstream domains"),
   ("finite Hamiltonian conservation", "an observable commuting with a Hermitian finite Hamiltonian is fixed by its checked matrix-exponential Heisenberg conjugation"),
   ("named-index Hamiltonian conservation", "the same conservation theorem accepts arbitrary finite label types, so lattice, band, colour and polarization indices need not be encoded as Fin n"),
   ("common finite density invariant", "Fin n states and arbitrary named-index matrices share IsFiniteDensity; bundled finite density states remain valid under any finite unitary"),
   ("density invariant through named channels", "Kraus and bundled named channels now return the same IsFiniteDensity invariant, so finite Gibbs and measurement outputs share downstream checks"),
   ("classical--quantum diagonal adapter", "a finite probability distribution becomes a density matrix; matrix purity is exactly collision probability, reusing statistical and quantum APIs"),
   ("classical--quantum expectation adapter", "a diagonal quantum expectation is exactly the finite classical expectation of the corresponding observable"),
   ("POVM--classical--quantum bridge", "a finite POVM output distribution can be embedded back into a diagonal state, whose matrix purity is the measurement collision probability"),
   ("generic finite outcome probabilities", "arbitrary finite labels, rather than only Fin n, carry normalized weights, expectations, second moments and collision bounds"),
   ("generic finite Markov kernels", "arbitrary finite labels support state push-forward, observable pullback and kernel composition with normalization checked by the kernel"),
   ("generic observable transport", "Markov expectation pullbacks are represented by a composable Schrödinger/Heisenberg transport certificate"),
   ("Markov--named quantum bridge", "a finite Markov step becomes a named diagonal density state; its matrix expectation is the classical observable pullback and its purity is the stepped collision probability"),
   ("generic doubly-stochastic equilibrium", "a doubly-stochastic kernel on any nonempty finite label type preserves the uniform state"),
   ("symmetric conductance equilibrium", "positive site weights and a symmetric nonnegative conductance automatically construct a normalized finite kernel and its equilibrium probability"),
   ("conductance detailed balance", "the conductance constructor proves pairwise detailed balance by cancellation, so Gibbs-like reversibility is inherited from local symmetry"),
   ("conductance stationary state", "the same local conductance certificate yields a kernel-fixed finite state without separately restating row normalization or balance"),
   ("cross-domain hopping conductance adapter", "condensed hopping, gauge-lattice and statistical reversible-network models share the ConductanceModel contract while continuum transport remains explicit"),
   ("Gibbs-to-Markov conductance bridge", "any positive finite Gibbs weight family yields a rank-one symmetric conductance model, so its normalized distribution is automatically stationary"),
   ("constructive conductance formula", "the generated conductance and transition entries are exposed by checked equalities, allowing downstream hopping and sampling proofs to rewrite without unfolding proofs"),
   ("finite Dirichlet energy", "a finite kernel and probability define the shared reversible-dynamics energy; nonnegativity is proved from transition and weight certificates"),
   ("Dirichlet symmetry", "the finite energy is symmetric in its observables, giving one bilinear contract for Markov, hopping, lattice and measurement calculations"),
   ("constant zero mode", "adding a constant observable gives zero finite Dirichlet energy, exposing the algebraic kernel of graph and reversible dynamics"),
   ("Dirichlet bilinearity", "addition in either observable is checked once by finite sum reflection and reused across domain adapters"),
   ("condensed hopping energy adapter", "the finite hopping namespace reuses the same Dirichlet form without duplicating graph-sum proofs"),
   ("gauge-lattice Dirichlet adapter", "finite lattice models expose the Dirichlet form under gauge-theory vocabulary while continuum dissipation remains explicit"),
   ("measurement post-processing energy adapter", "finite outcome kernels and quantum-information post-processing can consume the same nonnegative energy contract"),
   ("finite graph energy adapter", "graph, finite-element and network observables share the kernel-checked energy interface, with spectral-gap claims kept separate"),
   ("finite Laplacian bridge", "under detailed balance the edge Dirichlet form equals the weighted pairing with the discrete Laplacian I-K"),
   ("reversible energy-generator contract", "the same checked identity connects Gibbs/Markov dissipation, lattice hopping energies and finite graph stiffness forms"),
   ("finite path-integral normalization", "a finite complex weighted configuration space carries an explicit nonzero partition certificate; normalized expectations of constants, sums and scalar multiples are kernel-checked"),
   ("finite path reindexing", "finite partition functions and observable insertions are invariant under equivalence reindexing, including oscillatory complex weights"),
   ("exact finite coarse graining", "push-forward weights along a finite coarse map preserve the partition sum and pulled-back observable insertions exactly"),
   ("finite RG step", "a finite renormalization/blocking record exposes fine configurations, coarse map and weights while retaining exact partition/insertion preservation; continuum RG universality is outside the contract"),
   ("finite RG normalization transport", "a nonzero fine partition certificate is transported to every exact finite coarse partition, so normalized coarse expectations cannot be formed without an explicit normalization proof"),
   ("finite RG expectation invariance", "normalized coarse expectations equal fine expectations of pulled-back coarse observables, with both denominators checked by the kernel"),
   ("composable finite coarse graining", "finite blocking maps compose through push-forward insertion identities while keeping the original fine weights visible"),
   ("finite action path-integral adapter", "complex Euclidean or oscillatory action weights become a normalized finite path integral only with an explicit nonzero exponential-sum certificate"),
   ("action-shift invariance", "adding a configuration-independent complex constant to a finite action rescales partition and insertion equally, so normalized expectations are kernel-checked invariant"),
   ("finite Euclidean action positivity", "a real finite action on a nonempty configuration space yields strictly positive real partition part, discharging normalization without an arbitrary nonzero assumption"),
   ("constructive Euclidean denominator bound", "each chosen finite configuration supplies an explicit positive lower bound for the real-action partition norm, so normalized error certificates can obtain a denominator witness from the action"),
   ("finite RG fixed-point certificate", "an exact same-label coarse weight equality proves finite partition and normalized-observable invariance, while continuum fixed points and critical exponents remain outside the predicate"),
   ("finite normalized path-integral error", "insertion and partition ErrorCertificates plus explicit positive denominator lower bounds yield a checked normalized-expectation error bound; near-zero denominators are rejected by the certificate interface"),
   ("pointwise partition error aggregation", "per-configuration weight ErrorCertificates sum to an explicit partition-function error budget before normalization"),
   ("pointwise insertion error aggregation", "per-configuration weight errors are weighted by observable norms to produce an auditable insertion error budget"),
   ("observable truncation error", "a pointwise observable ErrorCertificate is weighted by the finite path measure and normalized with an explicit partition lower bound"),
   ("combined normalized expectation error", "weight, partition and observable approximation budgets compose into one kernel-checked bound for the reported expectation"),
   ("RG coarse-weight approximation certificate", "pointwise coarse-weight errors, denominator lower bounds and an insertion upper bound construct a normalized finite RG expectation error certificate"),
   ("composable normalized expectation certificates", "single-step normalized expectation error certificates compose by adding nonnegative radii, so several truncation or post-processing stages retain one auditable budget"),
   ("RG coarse expectation certificate", "the RG coarse-weight constructor exposes its normalized expectation error directly as a composable certificate, while denominator bounds remain explicit"),
   ("cross-space expectation comparison chain", "normalized expectation certificates compose across different finite configuration spaces and transformed observables, matching multi-step RG blocking"),
   ("cross-space exact RG expectation", "a finite coarse map between different label types preserves normalized expectations with the observable pulled back through the full map"),
   ("finite RG chain", "a list of finite blocking maps composes into one exact push-forward with partition, insertion and normalized-expectation preservation, while continuum RG flow remains outside the contract"),
   ("finite RG chain scaling", "an explicit observable ScalingCertificate transports through a multi-step finite blocking chain and proves the corresponding finite expectation scaling"),
   ("two-stage push-forward weight identity", "each twice-coarsened finite weight equals the push-forward of the intermediate coarse weight, making the numerical RG weight ledger explicit"),
   ("finite coarse-map associativity", "successive finite blocking maps have the same coarse weights as their composed map, with equality checked pointwise"),
   ("composed finite operator scaling", "two explicit finite operator-scaling certificates compose with factor lambda*mu; missing intermediate scaling data cannot elaborate"),
   ("finite RG fixed-point defect", "a configuration-wise coarse/fine weight mismatch carries an explicit nonnegative radius and aggregates to a partition-function defect"),
   ("finite reflection Gram positivity", "an explicit finite feature factorisation proves non-negativity of the associated Gram quadratic form"),
   ("reflected finite quadratic positivity", "a supplied finite reflection permutation preserves the Gram-square certificate; continuum Osterwalder--Schrader positivity remains explicit"),
   ("finite reflection kernel bridge", "the kernel double-sum quadratic form is proved equal to the supplied finite Gram square-sum factorisation"),
   ("reflected kernel positivity", "the reflected kernel presentation inherits a kernel-checked nonnegative quadratic certificate, with the involution recorded explicitly"),
   ("positive finite path integral adapter", "real nonnegative weights construct a complex finite path integral with a kernel-checked positive partition real part"),
   ("weighted path Gram positivity", "a finite path weight and feature table prove the usual weighted kernel double sum is a nonnegative sum of squares"),
   ("path integral reflection bridge", "finite positive path weights feed a reflection certificate while preserving explicit involution and Gram data; continuum OS positivity remains outside scope"),
   ("composed finite RG defects", "two consecutive blocking defects compose only after the second fine weights are identified with the first coarse weights; the final pointwise radius is the sum of both ledgers"),
   ("composed RG partition defect", "the two-stage RG defect composition yields a kernel-checked partition-function error budget with both local radii retained"),
   ("finite RG defect expectation bound", "pointwise fixed-point defects plus denominator lower bounds and an insertion upper bound produce a normalized-expectation error certificate"),
   ("finite RG operator scaling", "an explicit fine-to-coarse observable scaling equation transports unnormalized insertions and normalized expectations with a supplied factor lambda"),
   ("finite two-point correlator", "the finite path-integral two-point function is defined as a normalized product insertion and is symmetric under exchange of commuting observables"),
   ("connected correlator linearity", "the connected finite two-point function is linear in either observable, making source/operator expansions auditable"),
   ("connected correlator shift invariance", "adding a configuration-independent constant to either observable leaves the connected correlator unchanged"),
   ("factorization-to-zero connected correlator", "an explicit finite factorization equality implies a zero connected correlator; factorization is not inferred from notation"),
   ("finite evolution residual budget", "a one-step Lipschitz certificate and nonnegative local residuals generate a recursive finite-time error radius"),
   ("finite discrete Gronwall trajectory", "an exact recurrence plus approximate one-step certificates yields a kernel-checked propagated trajectory error at every natural time"),
   ("finite energy stability", "a nonnegative energy and explicit one-step amplification factor propagate to an energy bound at every finite step"),
   ("finite wave and Maxwell energy adapter", "wave, Maxwell, lattice and finite-mode solvers share the same factor-one conservation or factor-at-most-one stability contract"),
   ("finite energy conservation constructor", "an explicit one-step energy identity constructs a factor-one certificate whose iterate conservation is kernel-checked"),
   ("coupled evolution-energy ledger", "one shared step map carries both the discrete Gronwall state-error ledger and the independent finite-time energy bound"),
   ("energy trajectory certificate", "initial and local residuals remain visible through the evolution certificate while the exact trajectory receives a separate energy estimate"),
   ("nonexpansive evolution error sum", "when the supplied step modulus is at most one, the propagated error is bounded by the initial error plus the sum of local residuals"),
   ("finite positive parabolic step", "a nonnegative row-stochastic finite update is an explicit heat/diffusion/Markov step with constants preserved"),
   ("finite discrete maximum principle", "the positive step preserves pointwise lower and upper bounds by a kernel-checked convex-combination argument"),
   ("iterated finite maximum principle", "every finite iterate preserves the supplied pointwise bounds; no continuum maximum principle or CFL claim is inferred"),
   ("finite mass conservation certificate", "unweighted total mass is preserved only under an explicit column-sum certificate, separate from row-stochasticity"),
   ("iterated finite mass conservation", "the column-sum certificate composes over any finite number of diffusion or Markov steps"),
   ("finite parabolic pointwise error", "a nonnegative row-stochastic update is nonexpansive for the explicit componentwise absolute-error certificate"),
   ("finite pointwise error ledger", "componentwise error certificates compose by an explicit triangle budget, so PDE step residuals cannot be silently discarded"),
   ("finite parabolic trajectory ledger", "an exact finite diffusion recurrence plus initial and per-step UniformError certificates yields a checked error radius at every finite time"),
   ("finite driven parabolic step", "an explicit source/forcing field is added to a positive finite step; source lower and upper bounds yield a checked inhomogeneous maximum-principle budget"),
   ("driven parabolic error cancellation", "a common source cancels from approximate-versus-exact comparisons, so forced heat and master-equation residuals retain a componentwise error certificate"),
   ("finite forced trajectory ledger", "an explicit source recurrence, initial error and every local forced-step residual produce a kernel-checked finite-time error bound"),
   ("driven source perturbation ledger", "a separately approximated source field receives its own UniformError certificate, so state, forcing and local-step errors are all visible in the propagated radius"),
   ("finite source-aware trajectory ledger", "an exact/approximate source recurrence plus source and step residuals produces a checked finite-time bound; omitting source error is rejected by elaboration"),
   ("finite n-point correlator", "a list of finite observables defines an explicit normalized multi-insertion, including the empty insertion value one"),
   ("n-point permutation symmetry", "finite n-point insertions are invariant under list permutations because the coefficient algebra is commutative"),
   ("n-point RG pullback", "a finite coarse map preserves arbitrary list-valued correlators after pulling every observable back through the map"),
   ("finite path-integral weight symmetry", "an explicit permutation invariance of finite weights yields a checked insertion reindexing identity"),
   ("finite Ward expectation identity", "the same weight-symmetry certificate proves invariance of normalized expectations under a finite change of variables"),
   ("finite Ward insertion residual", "the weighted insertion of an observable change under a certified symmetry sums exactly to zero"),
   ("finite source generating polynomial", "a truncated source functional is a finite sum of explicitly retained moments; no infinite functional integral is silently introduced"),
   ("finite source insertion", "constant source insertion is exactly source times the first finite moment, checked by expectation linearity"),
   ("finite Schwinger-Dyson balance", "an involutive finite variation with an explicit Jacobian/weight balance yields the weighted insertion identity and its normalized expectation form"),
   ("invariant-weight Schwinger-Dyson signal", "when the supplied finite variation has unit Jacobian, the variation insertion is kernel-checked to vanish; continuum integration by parts remains external"),
   ("finite weak PDE energy", "a finite incidence/gradient table defines a stiffness energy whose diagonal is nonnegative and whose constants are zero modes"),
   ("finite summation-by-parts", "the kernel proves energy(u,v) = sum_x u_x (BᵀB v)_x, the shared weak-form identity for lattice and finite-element discretisations"),
   ("finite Poisson residual", "an exact solution carries a radius-zero equation residual certificate; residual radii remain explicit for approximate discretisations"),
   ("finite matrix PDE residual", "matrix-based finite linear PDEs share the same residual certificate and safe weakening of an error budget"),
   ("finite coercivity certificate", "a supplied positive coercivity modulus is an explicit stability assumption for a finite operator"),
   ("finite PDE uniqueness", "the kernel derives uniqueness of finite linear-PDE solutions from the coercivity certificate rather than assuming an inverse exists"),
   ("finite boundary certificate", "Dirichlet boundary predicates and values are carried separately, and agreement of two boundary-satisfying fields is checked pointwise"),
   ("boundary coercivity uniqueness", "coercivity restricted to homogeneous Dirichlet perturbations proves uniqueness with the supplied boundary data, exposing the exact finite PDE stability assumption"),
   ("structured elliptic certificate", "a finite PDE certificate binds residual radius, nonnegativity and boundary values into one auditable object; exact solutions construct the zero-radius case"),
   ("finite residual budget combination", "independent PDE residual budgets combine through a kernel-checked widening step, so truncation and discretisation errors cannot be silently dropped"),
   ("residual-to-solution stability", "an explicitly supplied residual-to-solution modulus turns a finite PDE residual into an ErrorCertificate for the approximate solution, without claiming mesh convergence"),
   ("left-inverse PDE stability", "a supplied finite left inverse with a Lipschitz bound is kernel-composed into residual-to-solution stability on the homogeneous Dirichlet subspace"),
   ("finite boundary residual certificate", "pointwise Dirichlet errors carry explicit nonnegative radii, can be widened or combined, and recover exact boundary values only at zero radius"),
   ("joint finite PDE approximation certificate", "equation and boundary residual budgets are stored together, preventing a numerical adapter from dropping boundary error"),
   ("zero-radius PDE recovery", "the kernel recovers an exact finite PDE solution only when both equation and boundary residual radii are zero"),
   ("boundary residual budget", "marked boundary-node error radii are summed into a nonnegative finite budget, with no hidden boundary norm or convergence claim"),
   ("boundary-aware residual stability", "an explicitly supplied two-modulus estimate converts equation and Dirichlet boundary residuals into one total finite solution-error certificate"),
   ("domain-neutral additive stability", "an additive operator left-inverse certificate transports an explicit residual bound to a solution approximation, with aliases for modes, bands, transfer matrices, lattices and classical dynamics"),
   ("finite Kubo correlator expansion", "the weighted commutator response Tr(rho[A,B]) expands to the difference of two finite correlators, exposing every sign and ordering"),
   ("finite response antisymmetry", "exchanging the two probes negates the Kubo response, so commutator-order mistakes become kernel-checkable failures"),
   ("finite response commuting-zero test", "a supplied matrix commutation certificate forces zero weighted response without assuming a physical state interpretation"),
   ("finite Kubo cyclic identity", "trace cyclicity rewrites Tr(rho[A,B]) as Tr([rho,A]B), the algebraic core shared by response and transport derivations"),
   ("finite response linearity", "probe addition and scalar multiplication are checked once and reusable for condensed, statistical, quantum-information and scattering calculations"),
   ("cross-domain response adapter", "quantum, condensed, statistical, high-energy and classical namespaces expose the same finite commutator-response contract"),
   ("closed finite surface certificate", "a finite two-chain with zero one-boundary is an explicit closed surface hypothesis for discrete flux and Chern pairings"),
   ("exact-flux pairing vanishes", "a coboundary two-form pairs to zero with every supplied closed finite surface by the discrete Stokes theorem"),
   ("finite Chern gauge invariance", "adding an exact curvature term leaves the pairing on a closed surface unchanged, without claiming continuum quantization"),
   ("cross-domain Chern-surface adapter", "gauge, Berry/Chern, finite-element and discrete-fluid namespaces reuse the same closed-surface certificate"),
   ("finite Hermitian spectral bridge", "mathlib's spectral theorem is exposed for density matrices: eigenvalues are nonnegative and sum to one, with explicit unitary diagonalization"),
   ("generic finite Gibbs ensembles", "arbitrary finite labels support positive partition functions, normalized Gibbs probabilities and energy-shift invariance"),
   ("named finite quantum states", "lattice, spin, band, colour and polarization labels can index diagonal density matrices, observables and purity directly"),
   ("finite Gibbs density-state adapter", "finite Gibbs ensembles become named diagonal density matrices, with thermal expectations and purity linked to the probability layer"),
   ("generic named Kraus channels", "arbitrary finite labels support CPTP Kraus maps, ancillary complete positivity, density preservation and channel composition; Gibbs named states can pass through the same interface"),
   ("typed rectangular Kraus channels", "input and output label types may differ; rectangular Kraus operators preserve positivity and trace under an input-space completeness proof"),
   ("typed channel density transport", "a rectangular finite channel transports the shared IsFiniteDensity/IsNamedDensity invariant across different finite Hilbert labels"),
   ("typed channel composition", "rectangular channels compose across intermediate spaces with a product Kraus family and a kernel-checked density result"),
   ("embedding and discard adapter", "a one-dimensional embedding followed by a two-outcome discard channel gives a concrete cross-dimension regression for environment and coarse-graining workflows"),
   ("typed Schrödinger--Heisenberg pairing", "a rectangular Kraus channel and its output-observable pullback have the finite trace-pairing identity across different input and output spaces"),
   ("typed dual unitality", "input-space Kraus completeness makes the rectangular Heisenberg dual unital, so measurement and control observables reuse the same invariant"),
   ("finite unitary dynamics", "unitary operators preserve ket inner products and density-matrix validity; conjugation and unitary composition are kernel-checked"),
   ("unitary Heisenberg duality", "Schrödinger unitary conjugation and Heisenberg observable conjugation satisfy the finite trace-pairing identity"),
   ("unitary-to-channel adapter", "a finite unitary is exposed as a singleton Kraus/CPTP channel, so closed gates reuse trace, positivity and channel-composition interfaces"),
   ("closed/open dynamics compatibility", "unitary composition agrees with singleton-Kraus channel composition at the state level"),
   ("CKM unitary adapter", "the high-energy CKM right-unitarity theorem is converted to the shared UnitaryOperator interface"),
   ("generic tensor unitaries", "a finite-index unitary API proves tensor-product unitarity for composite Hilbert, lattice and internal-index spaces"),
   ("quantum information", "Bell state, EPR correlations, CHSH operator and Tsirelson bound"),
   ("field-theory algebra", "single- and multi-mode CCR, ladder identities"),
   ("multi-mode CAR algebra", "finite fermionic modes carry explicit anticommutation relations; individual and total number operators raise/lower the matching creation and annihilation modes"),
   ("single-mode CAR adapter", "the condensed-matter FermionicMode is definitionally connected to the shared MultiModeCAR interface, so Hubbard and lattice proofs reuse one number-operator API"),
   ("conserved-observable algebra", "commuting with a Hamiltonian is closed under sums, products, powers, commutators, natural multiples, and linear combinations with explicit central coefficients"),
   ("associative-algebra Lie core", "the commutator Jacobi identity, adjoint Leibniz rule and center criterion are proved once for all operator models"),
   ("generic Lie representations", "a reusable linear Lie-algebra interface; any kernel-checked matrix/operator representation inherits the commutator Jacobi identity"),
   ("concrete Lie adapters", "the explicit spin-one matrices are packaged as an su(2) representation, so abstract Jacobi and commutator theorems apply to a physics generator family"),
   ("matrix generator tables", "one finite-family Jacobi theorem is reused by the Lorentz six-generator table and the SU(3) colour table"),
   ("Lorentz Lie representation", "the six explicit rotation/boost matrices are packaged as a checked so(3,1) representation with [R,R]=R, [R,B]=B and [B,B]=-R structure constants"),
   ("derivation / continuum bridge", "mathlib derivations with Leibniz rule; covariant-derivative curvature, antisymmetry, and pointwise Bianchi identity for gauge, Maxwell and geometric models"),
   ("finite exterior calculus", "a reusable finite-index one-/two-/three-form layer exposes wedge antisymmetry and d(dω)=0 under an explicit commuting-derivation hypothesis"),
   ("exterior gauge adapter", "adding an exact derivative Dχ to a finite potential leaves its exterior derivative unchanged; smoothness, manifolds and boundary conditions remain explicit"),
   ("cross-domain wedge algebra", "commutative coefficient forms share a checked antisymmetric wedge identity for Maxwell, discrete differential forms and future geometric/fluid adapters"),
   ("finite vorticity adapter", "a finite/discrete velocity one-form produces vorticity d u, whose closedness is inherited from the same d²=0 theorem; Navier–Stokes and continuum limits remain explicit"),
   ("potential-flow gauge reuse", "adding an exact discrete potential to a velocity one-form leaves its vorticity unchanged, reusing the exterior gauge-invariance theorem"),
   ("Poisson algebra bridge", "a reusable bilinear, Jacobi and Leibniz interface for classical mechanics, statistical mechanics, kinetic theory and semiclassical models; conservation closes under products, powers, linear combinations and brackets"),
   ("Poisson–derivation bridge", "the Hamiltonian action {H, ·} is packaged as a mathlib Leibniz derivation, so classical and semiclassical models can reuse the curvature/Bianchi layer without claiming a time-flow existence theorem"),
   ("Hamiltonian Lie action", "the commutator of Hamiltonian derivations equals the derivation generated by the Poisson bracket, exposing the classical Lie representation used by symmetry and gauge calculations"),
   ("polynomial canonical phase space", "formal q/p derivatives on MvPolynomial construct a nontrivial canonical Poisson algebra with {q,p}=1 and a checked Hamiltonian derivation"),
   ("multivariable polynomial phase space", "any selected pair of variables in a larger finite polynomial algebra has commuting formal derivatives and a kernel-checked canonical Poisson bracket"),
   ("polynomial Hamiltonian oscillator", "the polynomial Hamiltonian H=(q²+p²)/2 yields the checked equations {H,q}=-p, {H,p}=q and conservation of H"),
   ("finite spectral algebra", "exact eigenvector equations, commuting-operator eigenspaces, and ladder-operator eigenvalue shifts; existence/completeness of spectra remains an explicit analysis layer"),
   ("finite spectral decomposition", "complete pairwise-orthogonal projector families reconstruct a finite operator and kernel-check the eigenvalue action on each projector range; existence of such a family remains explicit"),
   ("concrete spectral projectors", "computational qubit projectors reconstruct Pauli Z and certify both eigenvalue branches, a reusable witness for spin, two-band and truncated BdG models"),
   ("finite Fourier systems", "a finite complex kernel with explicit left/right orthogonality has a kernel-checked forward and inverse transform; roots-of-unity, boundary and continuum limits remain explicit inputs"),
   ("unitary Fourier adapter", "an explicit normalization hypothesis turns any finite Fourier system into a generic finite unitary; the four-site periodic kernel is a checked instance"),
   ("finite unitary inner-product API", "generic finite-index unitary evolution preserves the finite inner product, including the normalized Fourier regression"),
   ("four-site Fourier adapter", "the explicit four-point periodic kernel is orthogonal and invertible, providing a shared lattice, finite-volume and optical-mode regression case"),
   ("finite Fourier Parseval", "the same kernel proves the unnormalised finite Parseval identity, preserving inner-product and norm bookkeeping for lattice and optical calculations"),
   ("finite characteristic polynomials", "monicity, dimension degree, and Cayley-Hamilton for every finite operator; spectral existence and completeness remain explicit analysis layers"),
   ("finite projectors and spectral modes", "rank-one ket-bra projectors act by the Dirac rule, are positive semidefinite and Hermitian, become idempotent under normalization, and have normalized trace"),
   ("Wick algebra (risk tier)", "general even moments = double factorial, odd moments vanish"),
   ("Wick pairing theorem", "explicit matching enumeration; the pairing count equals (2k-1)!! and equals the moment"),
   ("finite multi-field Wick kernel", "a covariance kernel over four typed field slots expands into all three bosonic contractions; time ordering, distributions and renormalisation remain explicit"),
   ("fermionic algebra", "CAR: number operator is a projector, raising/lowering"),
   ("condensed matter", "Hubbard site: commuting spin projectors, double occupancy, Cooper-pair operator"),
   ("Majorana fermions", "g1² = 1, g2² = -1, {g1,g2} = 0 (Cl(1,1)), and c†c = (1 - i γ₁γ₂)/2 recovered"),
   ("quantum channels", "Kraus operator-sum: trace preservation, unitality and channel composition; positive-semidefinite and IsDensity preservation; amplitude-damping completeness; depolarising decoherence"),
   ("finite complete positivity", "every finite ancillary extension of a Kraus operator-sum has the explicit I⊗K form and preserves positive semidefiniteness"),
   ("finite POVM", "positive effects with an identity completeness relation; Born weights are real and nonnegative and sum to one for density matrices"),
   ("quantum-to-classical measurement bridge", "a Fin-indexed POVM and density matrix are packaged as a finite classical distribution, so measurement outcomes can reuse Markov and statistical expectation APIs"),
   ("measurement instrument", "one Kraus operator per outcome; branch positivity, Born-rule trace, and normalized conditional states for positive-probability outcomes"),
   ("general multi-Kraus measurement", "finite internal Kraus families per outcome; coarse-grained effects, branch traces, total normalization, and normalized conditional states are kernel-checked"),
   ("lattice gauge theory", "Wilson-loop gauge covariance W -> g W g⁻¹, abelian gauge invariance, plaquette flux invariance, concrete ZMod 7 witness"),
   ("generic finite-path transport", "typed endpoint paths compose associatively and transport products compose for any group-valued link field"),
   ("open-path gauge covariance", "the same transport theorem applies to arbitrary graph, lattice and discrete-band paths, with conjugation at the two endpoints"),
   ("holonomy class-function adapter", "closed-path holonomy is invariant under non-Abelian gauge transformations after any conjugation-invariant observable"),
   ("abelian holonomy adapter", "closed lattice flux and discrete Berry-phase products are gauge invariant by the shared commutative-group theorem"),
   ("discrete Berry holonomy adapter", "finite-mesh Berry link products reuse the Abelian path theorem while smooth patches and Chern integrals stay explicit"),
   ("additive path transport", "angle-valued links and discrete one-forms compose additively, with endpoint gauge terms telescoping on every closed path"),
   ("generic plaquette flux bridge", "the legacy additive plaquette flux is connected to the shared additive path transport theorem"),
   ("finite approximation certificates", "explicit nonnegative distance bounds model basis truncation, finite volume, lattice and numerical surrogates without treating an approximation as equality"),
   ("error-bound composition", "triangle-inequality certificates compose additive errors, so independent truncation and discretisation budgets can be audited together"),
   ("cross-space reconstruction bridge", "a finite surrogate may have a different representation type; an explicit decoder and metric bound are required before it becomes a target-space approximation"),
   ("cross-space observable transport", "a supplied Lipschitz certificate transports a reconstructed finite error to observables without identifying unlike state spaces"),
   ("composed reconstruction stages", "two finite-to-target stages compose only with an explicit stability bound for the first decoder, preserving both error radii"),
   ("exact reconstruction bridge", "an encode/decode roundtrip yields a radius-zero cross-space certificate while keeping the representation map explicit"),
   ("additive error budgets", "independent operator, field or observable errors add in a seminormed group with a kernel-checked norm bound"),
   ("stability transport", "a supplied Lipschitz certificate transports a finite approximation bound through an observable or post-processing map"),
   ("residual certificates", "exact equations are radius-zero residual certificates while approximate PDE, ODE and variational equations retain an explicit residual radius"),
   ("cross-domain approximation vocabulary", "quantum state, field-theory mode, gauge lattice, band, thermal-volume and classical discretisation aliases share one checked certificate API"),
   ("cross-domain finite equation residuals", "approximate eigenpairs and one-step equations reduce to explicit ErrorCertificate bounds, reusable for QM, BdG, transfer matrices, finite modes and ODE discretisations"),
   ("residual budget weakening", "a certified finite residual can be safely widened to a larger advertised error budget without changing the underlying equation"),
   ("basis-free Hilbert operators", "continuous linear operators on complete inner-product spaces carry explicit adjoints, self-adjoint expectation values and unitary invariants, providing the bridge beyond matrices"),
   ("Hilbert unitary norm preservation", "a two-sided adjoint inverse preserves inner products and norms on arbitrary complete Hilbert spaces, with surjectivity retained as an explicit field"),
   ("matrix-to-Hilbert bridge", "a finite complex matrix is exposed as a bounded operator on a finite function space with a kernel-checked application theorem, so matrix regressions can feed basis-free APIs"),
   ("matrix-to-Hilbert multiplication", "finite matrix multiplication is transported to composition of bounded operators on EuclideanSpace, allowing one proof to serve matrix, truncated-mode and basis-free layers"),
   ("matrix adjoint bridge", "conjugate transpose is proved to be the Hilbert adjoint in the canonical finite basis, so Hermitian and unitary certificates survive a change of API"),
   ("finite unitary Hilbert adapter", "every checked finite unitary becomes a two-sided bounded Hilbert unitary with norm preservation inherited from the matrix certificate"),
   ("finite Hermitian Hilbert adapter", "a supplied matrix Hermiticity equation constructs a basis-free self-adjoint operator and keeps the Hermiticity obligation explicit"),
   ("real and complex Hilbert bridge", "the same Euclidean operator and adjoint theorems are polymorphic over RCLike scalars, so quantum complex matrices and classical/relativistic real matrices share one adapter"),
   ("Hermitian expectation bridge", "a finite Hermitian certificate feeds the basis-free expectation theorem, which proves a real-valued expectation without adding a physical assumption"),
   ("finite-flow Hilbert adapter", "a finite matrix semigroup lifts to bounded operators on EuclideanSpace with the same zero-time and composition laws"),
   ("basis-free flow state semigroup", "the lifted bounded-operator flow propagates Hilbert vectors with a kernel-checked composition law, retaining the finite/continuous boundary"),
   ("finite fermionic Wick kernel", "the four-point contraction is the sign-correct Pfaffian C12 C34 - C13 C24 + C14 C23, shared by finite CAR, BdG and truncated QFT models"),
   ("fermionic Wick antisymmetry", "adjacent slot exchanges are proved to reverse the four-point sign under an explicit antisymmetric contraction law"),
   ("finite Pfaffian matrix adapter", "a Fin 4 contraction matrix is definitionally connected to the fermionic Wick formula, so BdG or lattice covariance tables can reuse it"),
   ("Pauli exclusion residual", "a zero diagonal contraction forces repeated fermionic slots to vanish, providing a kernel-checked exclusion regression"),
   ("alternating finite curvature", "a standard alternating d1 turns arbitrary finite edge tables into triangle curvature with exact potentials in its kernel"),
   ("finite Bianchi d2d1", "the alternating finite cochain complex proves d2(d1 alpha)=0 by boundary cancellation, reusable for gauge, Berry and fluid meshes"),
   ("finite face-sum adapter", "abstract finite face labels carry a checked flux sum and pointwise congruence theorem, leaving mesh orientation and topology explicit"),
   ("global finite Bianchi equality", "the pointwise d2d1 identity is lifted to an equality of face fields for downstream finite-element and lattice APIs"),
   ("discrete cochain complex", "arbitrary vertex potentials and edge fields expose d0, triangle d1, cyclicity and the kernel-checked identity d1 d0 = 0"),
   ("quadrilateral plaquette flux", "the oriented four-edge boundary sum is gauge invariant under exact vertex shifts and reverses sign under an explicit antisymmetry hypothesis, covering lattice, Berry, fluid and network models"),
   ("periodic plaquette curl", "two commuting finite translations define a reusable torus plaquette field for Berry meshes, lattice gauge links, periodic finite differences and discrete vorticity"),
   ("periodic plaquette gauge invariance", "a vertex potential shift in both lattice directions leaves every periodic plaquette curl unchanged, with the commuting-translation condition explicit"),
   ("periodic total curl cancellation", "the finite sum of a globally defined periodic plaquette curl vanishes by permutation telescoping, separating exact global fields from patch-based Chern data"),
   ("periodic flux gauge certificate", "the total periodic flux is invariant under an exact gauge shift, giving one checked regression for condensed, gauge and fluid adapters"),
   ("plaquette orientation certificate", "reverse-orientation signs are checked only when antisymmetry of the edge field is supplied, preventing an unoriented edge table from being mistaken for a flux"),
   ("finite divergence", "incoming-minus-outgoing current is defined on arbitrary finite oriented graphs, with no continuum divergence theorem hidden in the definition"),
   ("closed finite graph cancellation", "the total divergence of every internal finite edge graph is zero by a kernel-checked incidence sum"),
   ("local conservation certificate", "a pointwise discrete continuity equation is a first-class certificate whose source field remains explicit"),
   ("global source constraint", "a local conservation certificate implies a checked zero total source, exposing the closed-boundary assumption"),
   ("cross-domain current conservation adapter", "gauge, condensed-matter, classical finite-volume, statistical and quantum-outcome vocabularies reuse the same conservation theorem"),
   ("Markov current bridge", "a finite Markov step is represented as a current on the complete directed state graph, and its divergence is exactly the probability change"),
   ("Markov conservation certificate", "row-normalized stochastic transitions yield a kernel-checked local continuity certificate with zero total source"),
   ("stochastic-to-lattice current adapter", "Markov, hopping and lattice vocabulary can consume the common finite divergence contract without duplicating sum proofs"),
   ("probability-flow source audit", "the source field is definitionally the pushed-forward distribution minus the input distribution, making normalization assumptions visible"),
   ("approximate conservation certificate", "finite-volume, lattice and truncated models may attach a nonnegative pointwise residual radius instead of silently claiming exact conservation"),
   ("global conservation residual bound", "the absolute total source is bounded by the finite sum of local residual radii using a kernel-checked triangle inequality"),
   ("uniform conservation residual bound", "a common local radius yields an explicit cardinality-times-radius global bound, with no convergence claim"),
   ("cross-domain residual adapter", "gauge, condensed, statistical and quantum-information names reuse the same approximate continuity certificate"),
   ("finite matrix group representations", "a monoid or group acts by finite square matrices through an explicit homomorphism, retaining the index and multiplication assumptions"),
   ("finite representation characters", "the matrix trace character is defined for arbitrary finite representations and is invariant under group conjugation"),
   ("representation pullback", "subgroups, quotient maps and parameter relabelings reuse one checked representation by pulling back along a monoid homomorphism"),
   ("intertwiner algebra", "identity, zero, addition, scalar multiplication and composition of finite representation intertwiners are kernel-checked"),
   ("unitary finite representations", "a supplied adjoint-unitarity field proves that the inverse group action equals the matrix adjoint"),
   ("cross-domain symmetry adapters", "gauge, particle, point-group and quantum-symmetry vocabularies share the same finite representation contract"),
   ("finite group average", "left and right reindexing of any finite group sum is kernel-checked, so orbit sums do not duplicate symmetry bookkeeping"),
   ("finite representation twirl", "matrix conjugation averages are invariant under every represented group element and therefore commute with the finite symmetry action; quantum, gauge and point-group names share the theorem"),
   ("finite chain complexes", "finite incidence tables with an explicit boundary-squared-zero certificate provide one algebraic interface for lattice gauge, Berry meshes, finite elements and network models"),
   ("boundary of boundary", "the checked incidence certificate proves that every finite two-chain has zero boundary boundary"),
   ("dual coboundary complex", "the same finite incidence data proves coboundary-squared-zero, with no manifold or continuum limit assumed"),
   ("discrete Stokes pairing", "finite cochain-chain pairing of a coboundary equals pairing with the chain boundary by a kernel-checked sum rearrangement"),
   ("exact cycle pairing", "an exact finite cochain pairs to zero with any explicitly supplied cycle; the cycle hypothesis remains visible"),
   ("cross-domain chain-complex adapters", "lattice gauge, condensed Berry, classical finite-element and statistical network names share the same finite chain-complex contract"),
   ("graph-current chain adapter", "the finite graph incidence boundary is definitionally connected to the existing incoming-minus-outgoing divergence theorem"),
   ("conservation-to-chain adapter", "a finite divergence conservation certificate becomes a chain boundary equals source equation without repeating the sum proof"),
   ("domain graph-chain vocabulary", "gauge, hopping, finite-volume and network names expose the same graph-to-chain construction with coefficient and finiteness assumptions explicit"),
   ("finite cycles and boundaries", "every finite two-chain boundary is a one-cycle, while the boundary predicate remains an explicit existential certificate"),
   ("finite cocycles and exact cochains", "the coboundary-square-zero theorem turns every exact one-cochain into a cocycle without quotienting by boundaries"),
   ("degree-one discrete Stokes", "pairing a one-coboundary with a two-chain equals pairing the one-cochain with its boundary"),
   ("cocycle-boundary annihilation", "a supplied finite cocycle pairs to zero with every supplied boundary, the algebraic homology pairing constraint"),
   ("exact-cycle annihilation", "a supplied exact one-cochain pairs to zero with every supplied cycle, making the finite cohomology pairing assumption explicit"),
   ("finite detailed balance", "pairwise weighted transition equality is an explicit reversible-kernel certificate for finite Gibbs, lattice and measurement dynamics"),
   ("detailed-balance stationarity", "the kernel proves that a finite detailed-balance distribution is stationary, without assuming irreducibility or mixing"),
   ("reversible observable pairing", "detailed balance makes the finite Markov pullback symmetric in the probability-weighted expectation pairing"),
   ("discrete Maxwell adapter", "finite-difference triangle curvature is invariant under an exact potential shift, with no continuum chart hidden in the theorem"),
   ("discrete Berry curvature adapter", "finite-mesh Berry triangle flux reuses the cochain gauge theorem while phase branches and Chern integration remain explicit"),
   ("finite cyclic flux certificate", "a permutation-indexed cycle sum cancels every additive gauge coboundary and forms the algebraic seed for winding checks"),
   ("integer winding/flux certificate", "an explicit finite integer lift records a claimed circulation or phase winding and proves invariance under integer gauge coboundaries; continuum topology and Chern integration remain explicit"),
   ("discrete fluid vorticity adapter", "lattice/network velocity one-forms reuse the same exact-shift invariance as Maxwell and Berry curvature"),
   ("Wilson plaquette generic bridge", "the legacy four-link Wilson loop is definitionally connected to the generic path transport API"),
   ("matrix Wilson trace invariant", "finite matrix representations turn Wilson-loop conjugation into trace invariance under an explicit IsUnit gauge transform; non-invertible matrices are rejected as gauge changes"),
   ("gauge field strength", "continuum F = [D, D]: antisymmetry, the algebraic Bianchi identity, the abelian F = 0 case, and a non-vacuity matrix witness"),
   ("Abelian Maxwell adapter", "potential-defined F_mu nu is antisymmetric, invariant under A -> A + D chi for commuting derivations, and obeys the cyclic Bianchi identity; smoothness, boundary conditions and PDE existence remain explicit"),
   ("Maxwell--exterior bridge", "the component field strength is definitionally the shared finite exterior derivative, so Maxwell proofs can use the common form API"),
   ("exterior Bianchi reuse", "the Maxwell cyclic identity is re-proved through the generic d²=0 theorem under explicit commuting-derivation hypotheses"),
   ("non-Abelian Yang--Mills adapter", "matrix-valued connection with explicit Leibniz derivations, curvature dA + [A,A], adjoint covariant derivative and kernel-checked Bianchi identity; gauge group global analysis remains explicit"),
   ("generic noncommutative curvature", "an arbitrary finite-index noncommutative connection exposes curvature antisymmetry and the adjoint covariant derivative without fixing four-dimensional spacetime"),
   ("generic noncommutative Bianchi", "the finite noncommutative exterior layer proves the covariant Bianchi identity using only Leibniz, additive and commuting-derivation hypotheses"),
   ("Yang--Mills noncommutative bridge", "the existing four-direction Yang--Mills object is definitionally adapted to the generic noncommutative connection, so its Bianchi proof reuses the shared theorem"),
   ("inner-derivation adapter", "commutator actions x -> a x - x a are packaged as Leibniz derivations; pairwise commuting generators construct a concrete noncommutative connection"),
   ("matrix/discrete gauge instantiation", "inner-derived connections feed the same arbitrary-index curvature and Bianchi theorem, while the generator-commutation condition remains explicit"),
   ("topological bands", "two-band Bloch Hamiltonian: Pauli decomposition, H² = (d·d)1, complex determinant criterion, real-coefficient zero-gap criterion, and chiral symmetry when d3 = 0"),
   ("finite resolvent and spectrum", "an explicit two-sided inverse is equivalent to a nonzero determinant and to exclusion from the finite matrix spectrum; a resolvent point has no nonzero eigenvector"),
   ("finite spectral gap certificate", "a Hermitian finite matrix gets a real interval gap from explicit resolvents; quadratic relations A² = q I provide a checked inverse with the pole condition q - z² ≠ 0"),
   ("finite BdG gap adapter", "the real BCS/BdG matrix family instantiates the common quadratic gap certificate, so discrete momentum or finite-volume blocks share one explicit radius"),
   ("finite Bloch-family gap adapter", "real two-band Bloch blocks instantiate the same uniform finite-gap interface on a finite momentum mesh, with the lower bound supplied explicitly"),
   ("unitary spectral-gap invariance", "finite unitary similarity transports the resolvent and preserves the real finite spectral-gap predicate in both directions"),
   ("uniform parameter-family gap", "one radius is checked for every finite momentum, flavor, boundary or volume label; a common quadratic lower bound constructs the family certificate"),
   ("complex versus real Bloch semantics", "over complex coefficients det H = 0 iff d·d = 0; only real Hermitian coefficients justify d1=d2=d3=0, preventing a false topological-gap claim"),
   ("scattering kinematics", "Mandelstam invariants: s + t + u = Σ m² on shell, with the off-shell defect and a massless witness"),
   ("statistical mechanics", "Ising transfer matrix: Pauli form, composition (rapidities add), commuting family, char. poly T² - 2cT + (c²-s²)1 = 0, two-site partition function"),
   ("transfer-matrix Markov adapter", "arbitrary finite nonnegative Boltzmann weights with positive row sums normalize to a finite Markov kernel; probability normalization and observable expectation duality are inherited kernel theorems"),
   ("finite probability", "normalized finite distributions, linear expectations, positivity of nonnegative observables, and nonnegative variance shared by statistical and measurement post-processing layers"),
   ("finite second moments and collision entropy", "a shared second-moment and collision-probability API for Gibbs states, Markov states and POVM outputs; nonnegativity, the [0,1] bound and the uniform-state value are kernel-checked, while logarithmic/continuum entropy remains an explicit analysis boundary"),
   ("finite Markov kernels", "nonnegative row-normalized transitions push finite distributions to finite distributions; composition and the dual observable expectation identity are kernel-checked, and doubly-stochastic kernels preserve the uniform state"),
   ("finite Gibbs ensembles", "positive finite partition function, normalized Gibbs distribution, nonnegative weights, and invariance under an additive energy shift; thermodynamic limits and entropy derivatives remain explicit analysis layers"),
   ("BCS / Bogoliubov", "Bogoliubov rotation preserves the Majorana Clifford pair; the BdG matrix squares to (eps²+Delta²)1, is traceless with det -(eps²+Delta²); a finite real BdG family gets a common spectral-gap certificate; the gap equation"),
   ("coupled spins", "total su(2), singlet state, Casimir spectrum {0,2} (1/2 ⊗ 1/2 = 0 ⊕ 1)"),
   ("Clifford / gamma algebra", "anticommuting generators, Dirac gamma matrices"),
   ("gamma-matrix traces", "traceless gammas, tr(γ^μ γ^ν) = 4 η^{μν}, the four-point trace, chiral traces"),
   ("supersymmetry", "H = {Q, Q†}: nilpotent supercharges, [H,Q] = [H,Q†] = 0, BPS zero-energy state"),
   ("Dirac bilinears", "Feynman slash: tr(a̸ b̸) = 4 (a·b), odd slashes traceless, γ⁵ a̸ traceless"),
   ("Ward identity", "gauge invariance: on shell, eps -> eps + lam (p'-p) leaves the photon vertex fixed; concrete on-shell witness"),
   ("spinor kinematics", "Feynman slash squares to p·p; the Dirac equation forces the mass shell (p·p - m²) u = 0"),
   ("spinor covariants", "the antisymmetric tensor sigma^{mu nu} = (i/2)[gamma^mu,gamma^nu]: antisymmetry, diagonal vanishing, and commutation with gamma^5"),
   ("entanglement measures", "purity tr(ρ²): maximally mixed 1/2, pure state 1, Bell marginal maximum"),
   ("Dirac notation elaborator", "basis kets, bra, brackets, matrix elements, outer product; dimension inferred and clashes reported in Chinese"),
   ("index calculus surface", "Kronecker delta, contractions, Levi-Civita and the epsilon-delta identity"),
   ("Einstein summation elaborator", "einsum k, M i k * N k j infers the index type; physics-facing diagnostics"),
   ("physics tactics", "physics_ring/linear/noncomm_ring, commutator_nf, dirac_unfold, index_unfold"),
   ("Einstein sums", "finite contraction identities"),
   ("Lorentz boosts", "one-axis boosts B(c,s) = [[c,-s],[-s,c]]: they compose by adding rapidities (the relativistic velocity-addition law), preserve the Minkowski metric B^T eta B = eta exactly when c^2 - s^2 = 1 (interval invariance), have determinant c^2 - s^2, and invert by negating the rapidity"),
   ("relativity", "Minkowski metric and lightlike relation"),
   ("worked example", "harmonic oscillator: [N,a†]=a† abstractly and on a 2-level truncation"),
   ("dimensions", "type-indexed SI exponents; mismatched-dimension addition rejected by the elaborator"),
   ("Standard Model anomalies", "the four gauge-anomaly coefficients of one generation vanish over the rationals, for any number of generations; hypercharge normalisation is rigid under a uniform shift"),
   ("SU(3) colour algebra", "Gell-Mann matrices: traceless, trace-orthonormal tr(lam_a lam_b)=2 delta_ab, Casimir sum_a lam_a lam_a = (16/3) 1 (quark colour factor C_F = 4/3), SU(3) Fierz completeness, and the colour-singlet trace sum_a tr(lam_a lam_a) = 16"),
   ("GHZ nonlocality (Mermin)", "the three-qubit Mermin operator M = XYY + YXY + YYX - XXX on the explicit 8x8 Pauli matrices (Kronecker products): it is symmetric, it maps the GHZ vector |000> + |111> to -4 times itself, and its GHZ expectation is -8, i.e. -4 on the normalised state.  The Bell combination that separates quantum mechanics (4) from local hidden variables (<= 2)"),
   ("CKM quark mixing", "the Cabibbo-Kobayashi-Maskawa matrix as a product R_23 P(delta) R_12 of two real rotations and one phase-carrying rotation: each factor is proved unitary (kernel-checked entrywise), hence V Vᴴ = 1; the rows are orthonormal (the unitarity-triangle relations sum_k V_ik V_jk* = delta_ij), the source of the standard CP-violation triangle.  The phase is an abstract unit-modulus complex number u (u* u = 1), so no analysis enters"),
   ("Pauli group and the twirl", "the single-qubit Pauli group: trace orthogonality tr(sigma_a sigma_b) = 2 delta_ab, the Pauli twirl sum_a sigma_a M sigma_a = 2 tr(M) 1, trace preservation of the normalised twirl, and complete depolarisation (1/4) sum_a sigma_a M sigma_a = (tr M / 2) 1"),
   ("symplectic canonical transformations", "2D real phase-space linear algebra shared by Hamiltonian mechanics, optics, accelerator lattices and bosonic Gaussian systems: A^T J A = J iff det A = 1, symplectic maps compose, rotations and free-particle shears are kernel-checked"),
   ("bilinear-form isometry interface", "a generic finite matrix structure packages Aᵀ G A = G and proves composition closure, shared by symplectic, Lorentz and future material/lattice forms"),
   ("Hamiltonian interface", "affine phase-space observables with a kernel-checked canonical Poisson bracket, plus the dimensionless harmonic-oscillator rotation and exact energy conservation"),
   ("algebraic variational equations", "finite jet-polynomial total derivatives and componentwise Euler–Lagrange residuals; harmonic oscillator equation q+a=0 is normalized by the kernel for mechanical and field/lattice jets"),
   ("variance-aware Lorentz tensors", "distinct UpVec and DownVec types; metric lowering/raising are inverse; only upper-lower contractions are exposed, with bilinearity, symmetry, and the (+---) Minkowski component formula kernel-checked, so variance mistakes are rejected before proving"),
   ("rank-two variance tensors", "type-level UU/UD/DU/DD slots; metric raising/lowering are inverse, mixed tensors compose associatively with a typed identity, mixed traces are cyclic, and illegal same-variance traces fail at elaboration"),
   ("generic finite typed tensors", "the same variance-safe mixed composition and trace API is parameterized by any Fin n, so Lorentz, colour, lattice and finite Hilbert indices share one algebraic layer"),
   ("higher-rank typed tensors", "rank-3/rank-4 tensors with variance-aware slot permutations, legal contractions, double contractions, and elaboration-time rejection of same-variance contractions"),
   ("density-matrix validity", "finite Kraus operator-sums preserve positive semidefiniteness; with the completeness relation they preserve the full IsDensity invariant (Hermitian, positive, trace one)"),
   ("bundled finite channels", "FiniteChannel stores linearity, positivity and trace preservation as fields, supports identity and composition, and prevents channel invariants from being dropped during a derivation"),
   ("bundled Kraus channels", "KrausChannel stores the completeness relation, exposes trace preservation and finite complete positivity, and composes with a kernel-checked product Kraus family"),
   ("Heisenberg-picture channels", "the finite trace-pairing dual of a Kraus channel is explicit, unital under Kraus completeness, and reverses channel composition"),
   ("Lindblad generators", "finite-dimensional Hamiltonian plus dissipator generator has exactly zero trace by kernel-checked cyclicity; positivity and semigroup existence remain explicit analytic obligations"),
   ("quantum teleportation", "the Bell-basis expansion of an arbitrary qubit a|0>+b|1> tensored with |Phi+>: four branches Phi+, Phi-, Psi+, Psi- carrying the Pauli-corrected states; Z, X, and ZX corrections are proved to recover the input exactly"),
   ("three-qubit bit-flip code", "the repetition code |0_L> = |000>, |1_L> = |111> with stabilizers ZZI and IZZ: both fix arbitrary a|000>+b|111>, while X_1, X_2, X_3 produce the distinct syndromes (-,+), (-,-), (+,-), checked as exact 8x8 matrix-vector identities"),
   ("Lorentz algebra so(3,1)", "the six Lorentz generators (three rotations R_i, three boosts B_i) as explicit 4x4 matrices: rotations close on so(3), rotations act on boosts as vectors [R_i,B_j] = eps_ijk B_k, two boosts close into a rotation [B_i,B_j] = -eps_ijk R_k (Thomas-Wigner), and every generator is metric-antisymmetric X^T eta + eta X = 0"),
   ("no-cloning theorem", "a linear U copying the basis states |0>, |1> (with a blank ancilla) must send the superposition |0> + |1> to the entangled |00> + |11>, which is not a product state: no linear operation clones every state.  The algebraic core, over C on explicit qubit vectors"),
   ("angular momentum one (spin-1)", "explicit 3x3 Cartesian generators S_1, S_2, S_3: the su(2) commutators [S_i,S_j] = i eps_ijk S_k, the Casimir S.S = 2 * 1 = l(l+1) 1 for l = 1, the cubic identity S_i^3 = S_i (eigenvalues -1, 0, 1), and the raising/lowering operators J_+/- = S_1 +/- i S_2 with [S_3, J_+] = J_+, [S_3, J_-] = -J_-"),
   ("Jordan-Wigner transformation", "the two-site fermion chain as explicit 4x4 matrices: c_0 = sigma^- (x) 1 and c_1 = sigma^z (x) sigma^-, the full canonical anticommutation relations ({c_0,c_0^dag} = 1, {c_0,c_1^dag} = 0, c_0^2 = 0, ...) checked entrywise, the stringless candidate proved nonzero (the sigma^z string is needed), each number operator a projector, and the hopping term equal to (1/2)(sigma^x (x) sigma^x + sigma^y (x) sigma^y) and conserving particle number"),
   ("Berry curvature of a qubit", "the two-level Bloch vector in spherical coordinates: it has unit norm; the Berry curvature density dhat . (d_theta dhat x d_phi dhat) is exactly sin theta (the charge-one Dirac monopole field), with the spherical frame orthonormal; the Chern-number integral itself is out of scope"),
   ("Dirac covariant completeness", "the 16 Dirac Gamma matrices: trace orthogonality tr(Gamma_A Gamma_B) = 4 w_A delta_AB with the axial sign w = -1, entrywise Fierz completeness sum_A w_A (Gamma_A)_ij (Gamma_A)_kl = 4 delta_il delta_jk, and the closure form sum_A w_A tr(Gamma_A M) Gamma_A = 4 M"),
   ("theory-package workflow", "assumptions, kernel-checked claims and explicit scope boundaries share one replaceable research-package interface"),
   ("proof-producing derivation chain", "addDerivedTheorem consumes the predecessor proposition and proof term, so a ledger dependency is enforced by Lean rather than recorded only as metadata"),
   ("proof-producing multi-dependency chain", "addDerivedTheorem2 passes two predecessor proofs to a new derivation step and records both dependency links"),
   ("registered local derivation", "addDerivedTheoremRegistered requires the predecessor to be present in the current package before creating a local dependency"),
   ("registered multi-dependency derivation", "addDerivedTheorem2Registered checks both predecessor registrations while retaining both proof terms"),
   ("proof-producing assumption witness", "AssumptionWitness carries a proposition and proof; addTheoremUnderAssumption consumes that proof and links the named model assumption"),
   ("two-assumption witness bridge", "addTheoremUnderAssumptions2 combines two proof-bearing model assumptions while retaining both audit links"),
   ("proof-producing external certificate", "a CAS-style envelope becomes a claim only after a Lean CertificateChecker supplies a soundness proof"),
   ("typed external obligation bridge", "an open analysis or numerical obligation is closed only through a proof of its explicit Lean proposition, and the derived claim consumes that proof"),
   ("cross-package dependency audit", "qualified package::claim links are resolved at project scope and included in the machine-readable report"),
   ("project integrity diagnostics", "duplicate package names and missing cross-package claims invalidate a research project before publication"),
   ("proof-producing cross-package derivation", "ResearchProject.addDerivedTheorem consumes a source claim proof and inserts a qualified dependency into the target package"),
   ("proof-producing two-package derivation", "ResearchProject.addDerivedTheorem2 combines proof terms from two packages while retaining both qualified links"),
   ("cross-domain theory adapters", "quantum, finite PDE, Euclidean, classical, gauge, condensed, relativity and statistical packages consume the same ledger API"),
   ("finite EFT truncation certificates", "a finite Wilson-operator tail is connected to the retained expansion through an explicit ErrorCertificate and cutoff power bound"),
   ("finite EFT matching certificates", "a uniform UV/IR coefficient mismatch becomes a kernel-checked observable error budget for bounded finite weights"),
   ("conditional verification report", "the leanphy_check executable reports VERIFIED-CONDITIONAL only for compiled proof-bearing packages")]

example : QuantumTheoryPackage.claimCount = 4 := rfl
example : FinitePDETheoryPackage.claimCount = 3 := rfl
example : FiniteEuclideanTheoryPackage.claimCount = 3 := rfl
example : QuantumTheoryPackage.missingAssumptionReferenceCount = 0 := rfl
example : FinitePDETheoryPackage.missingAssumptionReferenceCount = 0 := rfl

/- Keep each construction step named.  This avoids relying on the parser's
   precedence between a leading parenthesised term and chained dot syntax,
   and gives a researcher useful checkpoints when a package grows. -/
def researcherBase : TheoryPackage :=
  TheoryPackage.addObligationText
    (TheoryPackage.empty "researcher extension" "finite operator model")
    "continuum interpretation"
    "provide the external analysis needed to lift the finite result"
    "research project"

def researcherObligationWitness : ExternalObligationWitness where
  metadata :=
    { name := "continuum interpretation"
      statement := "provide the external analysis needed to lift the finite result"
      source := "research project" }
  proposition := True

def researcherTypedClosed : TheoryPackage :=
  researcherBase.resolveObligationWitness researcherObligationWitness
    (by native_decide)
    "typed continuum bridge"
    "the declared finite result is transported through the typed bridge"
    "researcher_extension.lean" [] [] (fun h => h) True.intro

example : researcherTypedClosed.claimCount = 1 := rfl
example : researcherTypedClosed.obligationCount = 0 := rfl

def researcherWithAssumption : TheoryPackage :=
  TheoryPackage.addAssumptionText researcherBase
    "finite dimension" "the operator acts on a two-level space" "model declaration"

def researcherWithClaim : TheoryPackage :=
  TheoryPackage.addTheoremWithAssumptions researcherWithAssumption
    "Pauli X square" "σx² = 1" "LeanPhy.Quantum.pauliX_sq"
    ["finite dimension"]
    LeanPhy.Quantum.pauliX_sq

def researcherClaimEntry : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions
    "Pauli X square" "σx² = 1" "LeanPhy.Quantum.pauliX_sq"
    ["finite dimension"] LeanPhy.Quantum.pauliX_sq

def researcherWithDerivedClaim : TheoryPackage :=
  TheoryPackage.addDerivedTheoremRegistered researcherWithClaim researcherClaimEntry
    (by native_decide)
    "Pauli X involution consequence" "the next derivation step reuses σx² = 1"
    "researcher_extension.lean" ["finite dimension"] (fun h => h)

def researcherSecondClaimEntry : CheckedClaim :=
  CheckedClaim.ofTheoremFromWithAssumptions
    "Pauli X identity copy" "σx² = 1 (independent derivation input)"
    "researcher_extension.lean" ["finite dimension"] LeanPhy.Quantum.pauliX_sq

def researcherWithTwoClaims : TheoryPackage :=
  researcherWithClaim.addClaim researcherSecondClaimEntry

def researcherWithCombinedClaim : TheoryPackage :=
  TheoryPackage.addDerivedTheorem2Registered researcherWithTwoClaims
    researcherClaimEntry researcherSecondClaimEntry
    (by native_decide)
    (by native_decide)
    "combined Pauli consequence" "a step consuming two checked predecessors"
    "researcher_extension.lean" ["finite dimension"] (fun h₁ _h₂ => h₁)

def finiteModelWitness : AssumptionWitness where
  metadata :=
    { name := "finite model witness"
      statement := "the declared finite model is available to the derivation"
      source := "model declaration" }
  proposition := True
  proof := True.intro

def coefficientWitness : AssumptionWitness where
  metadata :=
    { name := "coefficient witness"
      statement := "the coefficient convention used by the model is fixed"
      source := "model declaration" }
  proposition := True
  proof := True.intro

def witnessPackage : TheoryPackage :=
  TheoryPackage.empty "witnessed model" "finite algebra"
    |>.addAssumptionWitness finiteModelWitness
    |>.addTheoremUnderAssumption finiteModelWitness
      "witnessed step" "a theorem consumes the model witness" "Main.lean"
      (fun h => h)

def twoWitnessPackage : TheoryPackage :=
  TheoryPackage.empty "two-witness model" "finite algebra"
    |>.addAssumptionWitness finiteModelWitness
    |>.addAssumptionWitness coefficientWitness
    |>.addTheoremUnderAssumptions2 finiteModelWitness coefficientWitness
      "combined witnessed step" "a theorem consumes both model witnesses" "Main.lean"
      (fun h₁ h₂ => And.intro h₁ h₂)

def unregisteredWitnessPackage : TheoryPackage :=
  TheoryPackage.empty "unregistered witness" "finite algebra"
    |>.addTheoremUnderAssumption finiteModelWitness
      "invalid witnessed step" "the witness was not registered in the ledger"
      "Main.lean" (fun h => h)

def researcherPackage : TheoryPackage :=
  TheoryPackage.addBoundaryText researcherWithDerivedClaim
    "continuum limit" "the two-level calculation does not establish an infinite-dimensional result"

example : researcherPackage.assumptionCount = 1 := rfl
example : researcherPackage.claimCount = 2 := rfl
example : researcherPackage.boundaryCount = 1 := rfl
example : researcherPackage.obligationCount = 1 := rfl
example : researcherPackage.missingAssumptionReferenceCount = 0 := rfl
example : researcherPackage.missingClaimReferenceCount = 0 := rfl
example : researcherWithCombinedClaim.claimCount = 3 := rfl
example : researcherWithCombinedClaim.missingClaimReferenceCount = 0 := rfl
example : witnessPackage.claimCount = 1 := rfl
example : witnessPackage.missingAssumptionReferenceCount = 0 := rfl
example : twoWitnessPackage.claimCount = 1 := rfl
example : twoWitnessPackage.missingAssumptionReferenceCount = 0 := rfl
example : unregisteredWitnessPackage.hasErrors = true := by decide
example : (TheoryPackage.empty "empty" "draft").status = "UNVERIFIED" := rfl
example : (ResearchProject.empty "empty project" |>.addPackage
    (TheoryPackage.empty "draft package" "draft")).status = "UNVERIFIED" := rfl
example : (QuantumTheoryPackage.append FinitePDETheoryPackage).claimCount = 7 := rfl

/-! External certificate and project-level integration tests.  The payloads
are shaped like what a CAS adapter would parse, but the final equality still
comes from the Lean checker and its dependent proof field. -/

def pauliCertificateMetadata : CertificateMetadata :=
  { producer := "finite-cas-adapter"
    format := "matrix-equality-v1"
    digest := "demo-pauli-square"
    source := "Main.lean" }

def pauliCertificatePayload : MatrixEqualityPayload
    (pauliX * pauliX) (identity : Operator 2) :=
  { marker := "pauli-square" }

def pauliExternalCertificate : VerifiedCertificate
    (matrixEqualityChecker (lhs := (pauliX * pauliX))
      (rhs := (identity : Operator 2))) :=
  verifyMatrixEquality pauliCertificateMetadata pauliCertificatePayload pauliX_sq

def pauliExternalClaim : CheckedClaim :=
  CheckedClaim.ofVerifiedCertificate
    (matrixEqualityChecker (lhs := (pauliX * pauliX))
      (rhs := (identity : Operator 2)))
    pauliExternalCertificate "CAS-backed Pauli square"
    "σx² = 1 after external certificate checking"
    "finite-cas-adapter" ["finite dimension", "scalar field"]

def pauliExternalPackage : TheoryPackage :=
  TheoryPackage.empty "external-certificate demo" "finite quantum algebra"
    |>.addAssumptionText "finite dimension" "the matrix is 2 × 2" "model declaration"
    |>.addAssumptionText "scalar field" "entries are complex numbers" "mathlib"
    |>.addClaim pauliExternalClaim

example : pauliX * pauliX = (identity : Operator 2) :=
  pauliExternalCertificate.proof
example : pauliExternalPackage.hasErrors = false := by decide

/- JSON is a transport format only.  The round-trip test checks that a typed
payload can cross the data boundary; theorem production still requires the
separate `verifyEnvelope`/checker proof above. -/
def jsonCertificateEnvelope : CertificateEnvelope String :=
  { metadata := pauliCertificateMetadata
    payload := "pauli-square" }

example :
    (decodeEnvelope (C := String) (encodeEnvelope jsonCertificateEnvelope)).isOk = true := by
  native_decide

def malformedJsonCertificate : Lean.Json :=
  Lean.Json.mkObj
    [("metadata", Lean.Json.mkObj
      [("producer", Lean.Json.str "finite-cas-adapter"),
       ("format", Lean.Json.str "matrix-equality-v1"),
       ("digest", Lean.Json.str "demo-pauli-square"),
       ("source", Lean.Json.str "Main.lean")]),
     ("payload", Lean.Json.num 3)]

example : (decodeEnvelope (C := String) malformedJsonCertificate).isOk = false := by
  native_decide

/- Keep the JSON transport API universe-polymorphic.  `ULift Nat` is a small
Type-1 payload with an explicitly supplied codec; it exercises the same path a
domain-specific certificate type can use without weakening the checker. -/
namespace JsonUniverseSmoke

open Lean

instance : ToJson (ULift Nat) :=
  ⟨fun value => toJson value.down⟩

instance : FromJson (ULift Nat) :=
  ⟨fun json => (fromJson? (α := Nat) json).map ULift.up⟩

def envelope : CertificateEnvelope (ULift Nat) :=
  { metadata := pauliCertificateMetadata
    payload := ULift.up 3 }

example :
    (decodeEnvelope (C := ULift Nat) (encodeEnvelope envelope)).isOk = true := by
  native_decide

end JsonUniverseSmoke

/-! ## Finite EFT power counting and matching certificates

The high-energy interface turns two common exploratory-workflow steps into
proof-bearing objects: a finite Wilson-operator tail receives a uniform
power-counting bound, and coefficient matching receives an observable error
bound.  The expansion parameter and coefficient bounds remain explicit; no
continuum EFT or UV-completion claim is inferred.
-/
namespace EffectiveTheorySmoke

open scoped BigOperators
open LeanPhy.HighEnergy

noncomputable def epsilon : ExpansionParameter where
  value := (1 : ℝ) / 10
  nonneg := by norm_num
  le_one := by norm_num

noncomputable def toy : FiniteEFT (Fin 2) where
  order := fun i => if i = 0 then 5 else 6
  coefficient := fun i => if i = 0 then 2 else -3
  coefficientBound := 3
  coefficientBound_nonneg := by norm_num
  coefficient_abs_le := by
    intro i
    fin_cases i <;> norm_num

example :
    |toy.tailAmplitude epsilon ({0, 1} : Finset (Fin 2))| ≤
      (({0, 1} : Finset (Fin 2)).card : ℝ) * toy.coefficientBound * epsilon.value ^ 5 := by
  apply toy.tail_bound epsilon ({0, 1} : Finset (Fin 2)) 5
  intro i hi
  fin_cases i <;> simp [toy]

example :
    LeanPhy.Mathematics.ErrorCertificate (toy.amplitude epsilon)
      (toy.retainedAmplitude epsilon (∅ : Finset (Fin 2)))
      (((Finset.univ : Finset (Fin 2)).card : ℝ) * toy.coefficientBound *
        epsilon.value ^ 5) := by
  apply toy.truncation_error_certificate epsilon (∅ : Finset (Fin 2)) 5
  intro i hi
  fin_cases i <;> simp [toy]

noncomputable def matching : FiniteEFT.MatchingCertificate (Fin 2) where
  uvCoefficient := fun i => if i = 0 then 1 else 2
  irCoefficient := fun i => if i = 0 then (9 : ℝ) / 10 else (21 : ℝ) / 10
  uniformError := (1 : ℝ) / 10
  uniformError_nonneg := by norm_num
  coefficient_error := by
    intro i
    fin_cases i <;> norm_num

example :
    |∑ i ∈ ({0, 1} : Finset (Fin 2)),
      (if i = 0 then (1 : ℝ) else -1) *
        (matching.uvCoefficient i - matching.irCoefficient i)| ≤
      (({0, 1} : Finset (Fin 2)).card : ℝ) * 1 * matching.uniformError := by
  apply matching.weighted_error_bound
    (fun i => if i = 0 then (1 : ℝ) else -1)
    ({0, 1} : Finset (Fin 2)) 1 (by norm_num)
  intro i hi
  fin_cases i <;> norm_num

example :
    LeanPhy.Mathematics.ErrorCertificate
      (FiniteEFT.MatchingCertificate.observable matching.uvCoefficient
        (fun i => if i = 0 then (1 : ℝ) else -1) ({0, 1} : Finset (Fin 2)))
      (FiniteEFT.MatchingCertificate.observable matching.irCoefficient
        (fun i => if i = 0 then (1 : ℝ) else -1) ({0, 1} : Finset (Fin 2)))
      ((({0, 1} : Finset (Fin 2)).card : ℝ) * 1 * matching.uniformError) := by
  apply matching.error_certificate
    (fun i => if i = 0 then (1 : ℝ) else -1)
    ({0, 1} : Finset (Fin 2)) 1 (by norm_num)
  intro i hi
  fin_cases i <;> norm_num

end EffectiveTheorySmoke

def projectProducer : TheoryPackage :=
  TheoryPackage.empty "producer" "finite algebra"
    |>.addAssumptionText "finite dimension" "the matrix is 2 × 2" "model declaration"
    |>.addClaim researcherClaimEntry

def projectConsumerClaim : CheckedClaim :=
  { name := "consumer step"
    statement := "a second package consumes the producer claim"
    source := "Main.lean"
    requiredAssumptions := []
    dependencies := [ResearchProject.qualifiedDependency "producer" "Pauli X square"]
    models := []
    proposition := True
    proof := True.intro }

def projectConsumer : TheoryPackage :=
  TheoryPackage.empty "consumer" "finite algebra"
    |>.addClaim projectConsumerClaim

def crossPackageProject : ResearchProject :=
  ResearchProject.ofPackages "cross-package demo" [projectProducer, projectConsumer]

example : crossPackageProject.hasErrors = false := by native_decide
example : crossPackageProject.diagnosticCount = 0 := by native_decide

def crossPackageDerivedProject : ResearchProject :=
  ResearchProject.addDerivedTheorem crossPackageProject "producer" researcherClaimEntry
    projectConsumer "cross-derived step"
    "a target package consumes a theorem compiled in another package"
    "Main.lean" [] (fun h => h)

example : crossPackageDerivedProject.hasErrors = false := by native_decide
example : crossPackageDerivedProject.diagnosticCount = 0 := by native_decide

def auxiliaryClaim : CheckedClaim :=
  { name := "auxiliary fact"
    statement := "an auxiliary proposition"
    source := "Main.lean"
    requiredAssumptions := []
    dependencies := []
    models := []
    proposition := True
    proof := True.intro }

def auxiliaryPackage : TheoryPackage :=
  TheoryPackage.empty "auxiliary" "finite algebra"
    |>.addClaim auxiliaryClaim

def threePackageProject : ResearchProject :=
  crossPackageProject.addPackage auxiliaryPackage

def crossPackageTwoDerivedProject : ResearchProject :=
  ResearchProject.addDerivedTheorem2 threePackageProject
    "producer" researcherClaimEntry "auxiliary"
    auxiliaryClaim
    projectConsumer "cross-derived two-source step"
    "a target package consumes two independently compiled packages"
    "Main.lean" [] (fun h₁ h₂ => And.intro h₁ h₂)

example : crossPackageTwoDerivedProject.hasErrors = false := by native_decide
example : crossPackageTwoDerivedProject.diagnosticCount = 0 := by native_decide

def duplicatePackageProject : ResearchProject :=
  ResearchProject.ofPackages "duplicate package demo" [projectProducer, projectProducer]

example : duplicatePackageProject.hasErrors = true := by decide

def main : IO Unit := do
  IO.println "LeanPhy kernel-checked smoke test"
  IO.println "=================================="
  for (name, detail) in capabilities do
    IO.println s!"  [ok] {name}: {detail}"
  IO.println "All listed statements are checked by the Lean kernel at build time."
