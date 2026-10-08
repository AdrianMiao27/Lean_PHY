#!/usr/bin/env bash
set -euo pipefail

# These files must fail during elaboration.  The tests protect the main safety
# promise of the physics-facing layer: dimensional and variance mistakes are
# rejected before an invalid proof can be attempted.  They are kept outside
# the source tree so the normal proof-hole scanner never treats an intentional
# failure as library code.
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD_ROOT="${LEANPHY_BUILD_ROOT:-${PROJECT_ROOT}}"
if [[ ! -f "${BUILD_ROOT}/lakefile.toml" ]]; then
  BUILD_ROOT="${PROJECT_ROOT}"
fi
export PATH="/root/.elan/bin:${PATH}"

TMP_ROOT="$(mktemp -d /tmp/leanphy-negative.XXXXXX)"
trap 'rm -rf "${TMP_ROOT}"' EXIT

# Collect independent source files before running them. Lake sets the import
# environment once; each Lean invocation still gets an isolated environment.
expect_failure() {
  local label="$1"
  local source="$2"
  printf '%s\n' "$source" >"${TMP_ROOT}/${label}.lean"
}

expect_failure "heavy_matching_requires_mass_symmetry" 'import LeanPhy.FieldTheory.HeavyFieldMatching
open LeanPhy.FieldTheory.PropagatingHeavy
example (M : (Matrix (Fin 2) (Fin 2) ℝ)ˣ) : Model ℝ (Fin 2) Unit :=
  { derivative := fun _ => 0, mass := M, coupling := fun _ _ _ _ => 0,
    coupling_symmetric := by intros; rfl }'

expect_failure "driven_inverse_is_not_negative_time" 'import LeanPhy.Quantum.TimeDependentEvolution
open LeanPhy.Quantum.TimeDependent
open scoped Matrix
example {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Evolution (fun _ : ℝ => (0 : Matrix ι ι ℂ)) 0) (t : ℝ) :
    U.op (-t) = (U.op t)ᴴ := by
  exact U.unique (U.restart t)'

expect_failure "driven_response_requires_actual_family" 'import LeanPhy.Quantum.DrivenResponse
open LeanPhy.Quantum.TimeDependent
example {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ O : Matrix ι ι ℂ) (t : ℝ) (f : ℝ → Matrix ι ι ℂ) :
    HasDerivAt f (∫ s in (0 : ℝ)..t, f s) 0 := by
  exact hasDerivAt_const 0 _'

expect_failure "driven_pulse_requires_hermitian_probe" 'import LeanPhy.Quantum.DrivenPulse
open LeanPhy.Quantum.TimeDependent
noncomputable example {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Evolution (fun _ : ℝ => (0 : Matrix ι ι ℂ)) 0)
    (B : Matrix ι ι ℂ) (f : ℝ → ℝ) (hf : Continuous f) :
    DrivenFamily (fun _ : ℝ => (0 : Matrix ι ι ℂ)) (rotatingDrive U B f) 0 :=
  pulseFamily U B (by simp) f hf'

expect_failure "driven_pulse_requires_continuous_envelope" 'import LeanPhy.Quantum.DrivenPulse
open LeanPhy.Quantum.TimeDependent
noncomputable example {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Evolution (fun _ : ℝ => (0 : Matrix ι ι ℂ)) 0)
    (B : Matrix ι ι ℂ) (hB : B.IsHermitian) (f : ℝ → ℝ) :
    DrivenFamily (fun _ : ℝ => (0 : Matrix ι ι ℂ)) (rotatingDrive U B f) 0 :=
  pulseFamily U B hB f (by fun_prop)'

expect_failure "driven_response_outside_interval" 'import LeanPhy.Quantum.DrivenResponse
open LeanPhy.Quantum.TimeDependent
example {ι : Type} [Fintype ι] [DecidableEq ι]
    {H V W : ℝ → Matrix ι ι ℂ} {a : ℝ}
    (F : DrivenFamily H V a) (G : DrivenFamily H W a)
    (ρ O : Matrix ι ι ℂ) (t : ℝ) :
    (∫ s in a..t, F.kernel ρ O t s) = ∫ s in a..t, G.kernel ρ O t s := by
  exact DrivenFamily.response_congr F G ρ O t (by intro s hs; rfl)'

expect_failure "heavy_matching_differentiates_coefficients" 'import LeanPhy.FieldTheory.HeavyFieldMatching
open LeanPhy.FieldTheory LeanPhy.FieldTheory.PropagatingHeavy
noncomputable def x : JetPolynomial ℝ Unit Unit := JetPolynomial.jet () 0
example : MvPolynomial.eval (fun p : Unit × (Unit →₀ ℕ) =>
    if p.2 () ≤ 1 then (1 : ℝ) else 0)
    (kinetic JetPolynomial.totalDerivative (fun _ _ _ _ => x) (fun _ : Unit => x) ()) = 0 := by
  norm_num [kinetic, gradientFlux, x, JetPolynomial.totalDerivative, JetPolynomial.jet,
    Derivation.leibniz, smul_eq_mul]'

expect_failure "heavy_matching_preserves_operator_order" 'import LeanPhy.FieldTheory.PropagatingHeavy
open LeanPhy.FieldTheory.PropagatingHeavy
example (M : (Module.End ℝ (Fin 2 → ℝ))ˣ) (L : Module.End ℝ (Fin 2 → ℝ))
    (ε : ℝ) (N : ℕ) (J : Fin 2 → ℝ) :
    equation M L ε J (reconstruct M L ε N J) =
      ε ^ N • (((M : Module.End ℝ (Fin 2 → ℝ)) * (L * ↑(M⁻¹)) ^ N * ↑(M⁻¹)) J) :=
  equation_reconstruct_order M L ε N J'

expect_failure "heavy_matching_cutoff_is_exclusive" 'import LeanPhy.FieldTheory.PropagatingHeavy
open LeanPhy.FieldTheory.PropagatingHeavy
example (M : (Module.End ℝ (Fin 2 → ℝ))ˣ) (L : Module.End ℝ (Fin 2 → ℝ))
    (ε : ℝ) (N : ℕ) (J : Fin 2 → ℝ) :
    equation M L ε J (reconstruct M L ε N J) =
      ε ^ (N+1) • (((M : Module.End ℝ (Fin 2 → ℝ)) * (↑(M⁻¹) * L) ^ N * ↑(M⁻¹)) J) :=
  equation_reconstruct_order M L ε N J'

expect_failure "heavy_matching_residual_is_not_zero" 'import LeanPhy.FieldTheory.HeavyFieldMatching
open LeanPhy.FieldTheory.PropagatingHeavy
example (M : Model ℝ (Fin 2) Unit) (ε : ℝ) (N : ℕ) (J : Fin 2 → ℝ) :
    M.residual ε J (M.field ε N J) = 0 := M.residual_field ε N J'

expect_failure "heavy_matching_source_contact_required" 'import LeanPhy.FieldTheory.HeavyFieldMatching
open LeanPhy.FieldTheory.PropagatingHeavy
example (M : Model ℝ (Fin 2) Unit) (ε s : ℝ) (N : ℕ) (V : ℝ) (J Q : Fin 2 → ℝ) :
    M.effective ε N V (J + s • Q) = M.effective ε N V J +
      (s / 2) • (pair (M.field ε N J) Q + pair (M.field ε N Q) J) :=
  M.effective_source_shift ε s N V J Q'

expect_failure "heavy_matching_readout_changes_with_source" 'import LeanPhy.FieldTheory.HeavyFieldMatching
open LeanPhy.FieldTheory.PropagatingHeavy
example (M : Model ℝ (Fin 2) Unit) (ε s : ℝ) (N : ℕ) (O : ℝ) (Q J S : Fin 2 → ℝ) :
    M.readout ε N O Q (J + s • S) = M.readout ε N O Q J :=
  M.readout_source_shift ε s N O Q J S'

expect_failure "heavy_matching_endpoint_flux_required" 'import LeanPhy.FieldTheory.HeavyFieldInterval
open LeanPhy.FieldTheory LeanPhy.FieldTheory.PropagatingHeavy
open scoped ContDiff
example (φ : Unit → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (M : Model (JetPolynomial ℝ Unit Unit) Unit Unit)
    (hδ : M.derivative () = JetPolynomial.totalDerivative ()) (ε a b : ℝ) (N : ℕ)
    (V : JetPolynomial ℝ Unit Unit) (J : Unit → JetPolynomial ℝ Unit Unit) :
    Interval.action φ hφ M ε a b V J (M.field ε N J) = Interval.effectiveAction φ hφ M ε N a b V J +
      (1 / 2 : ℝ) * Interval.integral φ hφ a b (pair (M.field ε N J) (M.residual ε J (M.field ε N J))) :=
  Interval.action_matching φ hφ M hδ ε N a b V J'

expect_failure "heavy_matching_needs_smooth_profiles" 'import LeanPhy.FieldTheory.HeavyFieldInterval
open LeanPhy.FieldTheory.PropagatingHeavy
example (φ : Unit → ℝ → ℝ) (hφ : ∀ i, Continuous (φ i)) :
    Interval.ProfilePolynomial Unit →ₗ[ℝ] ℝ := Interval.integral φ hφ 0 1'

expect_failure "heavy_matching_needs_uniform_residual" 'import LeanPhy.FieldTheory.HeavyFieldInterval
open LeanPhy.FieldTheory LeanPhy.FieldTheory.PropagatingHeavy LeanPhy.Mathematics
open scoped ContDiff
example (φ : Unit → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (M : Model (JetPolynomial ℝ Unit Unit) Unit Unit)
    (hδ : M.derivative () = JetPolynomial.totalDerivative ()) (ε a b ρ β : ℝ) (N : ℕ)
    (V : JetPolynomial ℝ Unit Unit) (J : Unit → JetPolynomial ℝ Unit Unit)
    (hR : ErrorCertificate (CurveJet.evaluate φ a (pair (M.field ε N J) (M.residual ε J (M.field ε N J)))) 0 ρ)
    (hB : ErrorCertificate (CurveJet.evaluate φ b (M.flux (M.field ε N J) (M.field ε N J) ()))
      (CurveJet.evaluate φ a (M.flux (M.field ε N J) (M.field ε N J) ())) β) :
    ErrorCertificate (Interval.action φ hφ M ε a b V J (M.field ε N J))
      (Interval.effectiveAction φ hφ M ε N a b V J) ((ρ * |b-a| + |ε| * β) / 2) :=
  Interval.action_error φ hφ M hδ ε N a b V J ρ β hR hB'

expect_failure "multipoint_requires_vacuum_evidence" 'import LeanPhy.FieldTheory.FermionVacuumWick
open LeanPhy.FieldTheory LeanPhy.Quantum
open scoped Matrix
example (M : MultiModeCAR (Fin 2) (Matrix (Fin 4) (Fin 4) ℂ))
    (h : ∀ i, M.cre i = (M.ann i)ᴴ) (rho : FiniteDensity (Fin 4)) :
    FermionVacuum (Fin 2) (Fin 4) :=
  { car := M, adjoint := h, state := rho }'

expect_failure "multipoint_exchange_retains_contact" 'import LeanPhy.FieldTheory.FermionVacuumWick
open LeanPhy.FieldTheory
example (V : FermionVacuum (Fin 2) (Fin 4))
    (before after : List (FermionProbe (Fin 2))) (p q : FermionProbe (Fin 2)) :
    V.moment (before ++ p :: q :: after) + V.moment (before ++ q :: p :: after) = 0 :=
  V.moment_exchange before after p q'

expect_failure "multipoint_crossing_sign_required" 'import LeanPhy.FieldTheory.FermionVacuumWick
open LeanPhy.FieldTheory.FermionWord
example : vacuumMoment (ι := Fin 3) [ann 0, ann 1, ann 2, cre 0, cre 1, cre 2] = 1 :=
  by decide +kernel'

expect_failure "multipoint_oddness_required" 'import LeanPhy.FieldTheory.FermionVacuumWick
open LeanPhy.FieldTheory
example (V : FermionVacuum (Fin 2) (Fin 4)) (ps : List (FermionProbe (Fin 2)))
    (h : ps.length % 2 = 0) : V.moment ps = 0 := V.moment_odd ps h'

expect_failure "multipoint_readout_binds_probes" 'import LeanPhy.FieldTheory.FermionVacuumWick
open LeanPhy.FieldTheory
example (V : FermionVacuum (Fin 2) (Fin 4)) (ps qs : List (FermionProbe (Fin 2))) :
    V.moment ps = FermionicWick.moment FermionProbe.contraction qs := V.moment_eq ps'

expect_failure "multipoint_vacuum_kernel_is_ordered" 'import LeanPhy.FieldTheory.FermionVacuumWick
open LeanPhy.FieldTheory.FermionWord
example : vacuumContraction (ι := Fin 1) (cre 0) (ann 0) = 1 := by decide +kernel'

expect_failure "multipoint_expression_binds_coefficients" 'import LeanPhy.FieldTheory.FermionVacuumWick
open LeanPhy.FieldTheory FermionWord FermionPolynomial
example : vacuumValue (R := ℤ) (ι := Fin 1) [(3, [ann 0, cre 0]), (-1, [])] = 3 :=
  by decide +kernel'

expect_failure "multipoint_repeated_probe_is_not_zero" 'import LeanPhy.FieldTheory.FermionicMoment
open LeanPhy.FieldTheory.FermionicWick
example : moment (fun _ _ : Unit => (1 : ℤ)) [(), (), (), (), (), ()] = 0 :=
  by decide +kernel'

expect_failure "rational_exp_requires_range_reduction" 'import LeanPhy.Mathematics.RationalExp
open LeanPhy.Mathematics.RationalExp
example (q : ℚ) (depth order : ℕ) (h : |q| ≤ (2 : ℚ) ^ (depth + 1)) :
    (enclose q depth order).Contains (Real.exp (q : ℝ)) := enclose_contains q depth order h'

expect_failure "rational_exp_rounding_error_cannot_be_erased" 'import LeanPhy.Mathematics.RationalExp
open LeanPhy.Mathematics
example (q value error : ℚ) (depth order : ℕ)
    (h : RationalExp.Accepted q depth order value error) :
    ErrorCertificate (value : ℝ) (Real.exp (q : ℝ)) 0 :=
  RationalExp.sound q depth order value error h'

expect_failure "gibbs_partition_lower_must_be_positive" 'import LeanPhy.StatMech.GibbsCertificate
open LeanPhy.StatMech.GibbsCertificate
example : (Candidate.mk 0 0 0 1 1).Accepted (fun _ : Fin 1 => 1) (fun _ => 1) :=
  by decide +kernel'

expect_failure "gibbs_certificate_binds_model" 'import LeanPhy.Examples.Generated.BiasedFeedbackCertificate
open LeanPhy.StatMech LeanPhy.Mathematics
open LeanPhy.Generated.GibbsCertificates.BiasedFeedback
example : ErrorCertificate (fun a => (point a : ℝ))
    (SourceFeedback.feedback (fun i => (action i : ℝ)) (fun a i => (observables a i : ℝ))
      (fun _ => 0) (fun a b => (coupling a b : ℝ)) (fun a => (point a : ℝ))) (error : ℝ) := valid'

expect_failure "gibbs_checker_binds_payload" 'import LeanPhy.StatMech.GibbsCertificate
open LeanPhy.StatMech.GibbsCertificate
example (q O : Fin 2 → ℚ) (c : Candidate) (h : c.Accepted q O) :
    (checker q O c).check { c with value := c.value + 1 } := by
  exact ⟨rfl, h⟩'

expect_failure "gibbs_feedback_binds_candidate_value" 'import LeanPhy.Examples.Generated.BiasedFeedbackCertificate
open LeanPhy.Generated.GibbsCertificates.BiasedFeedback
example : ∀ a, (candidates a).value = point a + 1 := values_match'

expect_failure "gibbs_solution_requires_strict_contraction" 'import LeanPhy.StatMech.GibbsCertificate
open LeanPhy.StatMech SourceFeedback
example (S : Fin 2 → ℝ) (A : Unit → Fin 2 → ℝ) (J : Unit → ℝ) (K : Unit → Unit → ℝ)
    (e : Envelope A K) (h : e.rate ≤ 1) : Unit → ℝ := e.solution S J h'

expect_failure "gibbs_readout_retains_evaluation_error" 'import LeanPhy.Examples.SelfConsistencyResearch
open LeanPhy.StatMech LeanPhy.Mathematics SourceFeedback
open LeanPhy.Examples.SelfConsistencyResearch.Numerical
open LeanPhy.Generated.GibbsCertificates.BiasedFeedback
example : ErrorCertificate (readoutCandidate.value : ℝ)
    ((SourceEnsemble.probability (fun i => (action i : ℝ)) (fun a i => (observables a i : ℝ))
      (source (fun a => (bias a : ℝ)) (fun a b => (coupling a b : ℝ))
        (envelope.solution (fun i => (action i : ℝ)) (fun a => (bias a : ℝ)) small))).expectation
          (fun i => (readout i : ℝ))) (1 / 200000) := readout_error'

expect_failure "euler_transport_requires_c2" 'import LeanPhy.FieldTheory.EulerTransport
open LeanPhy.FieldTheory PointTransformation
open scoped ContDiff BigOperators
example (F : Unit → MvPolynomial Unit ℝ) (L : FirstOrderLagrangian ℝ Unit Unit)
    (e : Unit → ℝ) (ψ : Unit → ℝ → ℝ) (hψ : ∀ b, ContDiff ℝ 1 (ψ b)) (x : ℝ) :
    FieldEvaluation.euler (pullback F L) e ψ () x =
      ∑ a, FieldEvaluation.euler L e (transformed F ψ) a x * jacobian F ψ a () x :=
  euler_pullback F L e ψ hψ x ()'

expect_failure "euler_jacobian_cannot_be_erased" 'import LeanPhy.FieldTheory.EulerTransport
open LeanPhy.FieldTheory PointTransformation
open scoped ContDiff
example (F : Unit → MvPolynomial Unit ℝ) (L : FirstOrderLagrangian ℝ Unit Unit)
    (e : Unit → ℝ) (ψ : Unit → ℝ → ℝ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (x : ℝ) :
    FieldEvaluation.euler (pullback F L) e ψ () x =
      FieldEvaluation.euler L e (transformed F ψ) () x := by
  simpa only [Fintype.sum_unique] using euler_pullback F L e ψ hψ x ()'

expect_failure "euler_force_keeps_hessian_terms" 'import LeanPhy.FieldTheory.EulerTransport
open LeanPhy.FieldTheory PointTransformation
open scoped BigOperators
example (F : Unit → MvPolynomial Unit ℝ) (L : FirstOrderLagrangian ℝ Unit Unit)
    (e : Unit → ℝ) (ψ : Unit → ℝ → ℝ) (x : ℝ)
    (hψ : ∀ b, DifferentiableAt ℝ (ψ b) x) :
    FieldEvaluation.force (pullback F L) e ψ () x =
      ∑ a, FieldEvaluation.force L e (transformed F ψ) a x * jacobian F ψ a () x :=
  force_pullback F L e ψ x hψ ()'

expect_failure "euler_current_keeps_pushed_variation" 'import LeanPhy.FieldTheory.EulerTransport
open LeanPhy.FieldTheory PointTransformation
example (F : Unit → MvPolynomial Unit ℝ) (L : FirstOrderLagrangian ℝ Unit Unit)
    (e : Unit → ℝ) (ψ η : Unit → ℝ → ℝ) (x : ℝ)
    (hψ : ∀ b, DifferentiableAt ℝ (ψ b) x) :
    FieldEvaluation.boundary (pullback F L) e ψ η () x =
      FieldEvaluation.boundary L e (transformed F ψ) η () x :=
  boundary_pullback F L e ψ η x hψ ()'

expect_failure "euler_inverse_requires_regular_jacobian" 'import LeanPhy.FieldTheory.EulerTransport
open LeanPhy.FieldTheory PointTransformation
open scoped ContDiff
example (F : Unit → MvPolynomial Unit ℝ) (L : FirstOrderLagrangian ℝ Unit Unit)
    (e : Unit → ℝ) (ψ : Unit → ℝ → ℝ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (x : ℝ)
    (hdet : (jacobianMatrix F ψ x).det = 0) :
    (∀ b, FieldEvaluation.euler (pullback F L) e ψ b x = 0) ↔
      (∀ a, FieldEvaluation.euler L e (transformed F ψ) a x = 0) :=
  euler_zero_iff_of_det_ne_zero F L e ψ hψ x hdet'

expect_failure "euler_right_inverse_cannot_be_left_inverse" 'import LeanPhy.FieldTheory.EulerTransport
open LeanPhy.FieldTheory PointTransformation
open scoped ContDiff BigOperators
example (F : Fin 2 → MvPolynomial Unit ℝ) (L : FirstOrderLagrangian ℝ (Fin 2) Unit)
    (e : Unit → ℝ) (ψ : Unit → ℝ → ℝ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (x : ℝ)
    (K : Unit → Fin 2 → ℝ)
    (hleft : ∀ b c : Unit, ∑ a, K b a * jacobian F ψ a c x = if b = c then 1 else 0) :
    (∀ b, FieldEvaluation.euler (pullback F L) e ψ b x = 0) ↔
      (∀ a, FieldEvaluation.euler L e (transformed F ψ) a x = 0) :=
  euler_zero_iff_of_rightInverse F L e ψ hψ x K hleft'

expect_failure "euler_regular_domain_cannot_be_enlarged" 'import LeanPhy.FieldTheory.EulerTransport
open LeanPhy.FieldTheory PointTransformation
open scoped ContDiff
example (F : Unit → MvPolynomial Unit ℝ) (L : FirstOrderLagrangian ℝ Unit Unit)
    (e : Unit → ℝ) (ψ : Unit → ℝ → ℝ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b))
    (S T : Set ℝ) (hdet : ∀ x ∈ S, (jacobianMatrix F ψ x).det ≠ 0) :
    (∀ x ∈ T, ∀ b, FieldEvaluation.euler (pullback F L) e ψ b x = 0) ↔
      (∀ x ∈ T, ∀ a, FieldEvaluation.euler L e (transformed F ψ) a x = 0) :=
  euler_zero_iff_on_of_det_ne_zero F L e ψ hψ T hdet'

expect_failure "euler_singular_map_cannot_reflect_solution" 'import LeanPhy.Examples.FieldRedefinitionResearch
open LeanPhy.FieldTheory FirstOrderLagrangian PointTransformation MvPolynomial
example : FieldEvaluation.euler (field () : FirstOrderLagrangian ℝ Unit Unit)
    IntervalAction.direction
    (transformed (fun _ : Unit => X () ^ 2) (fun (_ : Unit) (_ : ℝ) => 0)) () 0 = 0 :=
  LeanPhy.Examples.FieldRedefinitionResearch.singular_map_loses_equation.2'

expect_failure "vacuum_requires_annihilation_condition" 'import LeanPhy.FieldTheory.FermionVacuum
open LeanPhy.FieldTheory LeanPhy.Quantum
example (rho : FiniteDensity (FiniteFermion.Occupation 1)) :
    FermionVacuum (Fin 1) (FiniteFermion.Occupation 1) :=
  { car := (FiniteFermion.modes 1).car
    adjoint := (FiniteFermion.modes 1).adjoint
    state := rho
    annihilates := fun i => by simp }'

expect_failure "vacuum_crossed_contraction_has_minus_sign" 'import LeanPhy.FieldTheory.FermionVacuum
open LeanPhy.FieldTheory LeanPhy.FieldTheory.FiniteFermion
noncomputable def a : FermionProbe (Fin 2) := ⟨![1, 0], ![0, 0]⟩
noncomputable def b : FermionProbe (Fin 2) := ⟨![0, 1], ![0, 0]⟩
noncomputable def c : FermionProbe (Fin 2) := ⟨![0, 0], ![1, 0]⟩
noncomputable def d : FermionProbe (Fin 2) := ⟨![0, 0], ![0, 1]⟩
example : (vacuumState 2).expectation (a.operator (vacuumState 2).car * b.operator (vacuumState 2).car *
    c.operator (vacuumState 2).car * d.operator (vacuumState 2).car) = 1 := by
  rw [(vacuumState 2).fourPoint a b c d]
  norm_num [a, b, c, d, FermionProbe.contraction, Fin.sum_univ_succ]'

expect_failure "vacuum_repeated_probe_retains_contact" 'import LeanPhy.FieldTheory.FermionVacuum
open LeanPhy.FieldTheory LeanPhy.FieldTheory.FiniteFermion
noncomputable def p : FermionProbe (Fin 1) := ⟨![1], ![1]⟩
example : (vacuumState 1).expectation (p.operator (vacuumState 1).car * p.operator (vacuumState 1).car *
    p.operator (vacuumState 1).car * p.operator (vacuumState 1).car) = 0 := by
  rw [(vacuumState 1).fourPoint p p p p]
  norm_num [p, FermionProbe.contraction, Fin.sum_univ_succ]'

expect_failure "vacuum_contraction_does_not_conjugate_coefficients" 'import LeanPhy.FieldTheory.FermionVacuum
open LeanPhy.FieldTheory LeanPhy.FieldTheory.FiniteFermion
noncomputable def p : FermionProbe (Fin 1) := ⟨![Complex.I], ![0]⟩
noncomputable def q : FermionProbe (Fin 1) := ⟨![0], ![1]⟩
example : (vacuumState 1).expectation (p.operator (vacuumState 1).car * q.operator (vacuumState 1).car) =
    -Complex.I := by
  rw [(vacuumState 1).twoPoint p q]
  norm_num [p, q, FermionProbe.contraction, Fin.sum_univ_succ, Complex.ext_iff]'

expect_failure "field_change_keeps_gradient_jacobian" 'import LeanPhy.Examples.FieldRedefinitionResearch
open LeanPhy.FieldTheory FirstOrderLagrangian PointTransformation LeanPhy.Examples.FieldRedefinitionResearch
example (g : ℝ) : pullback (cubicChange g)
  ((gradient () () : FirstOrderLagrangian ℝ Unit Unit) ^ 2) = gradient () () ^ 2 :=
  nonlinear_kinetic g'

expect_failure "field_change_transports_sources" 'import LeanPhy.Examples.FieldRedefinitionResearch
open LeanPhy.FieldTheory FirstOrderLagrangian PointTransformation LeanPhy.Examples.FieldRedefinitionResearch
example (g J : ℝ) : pullback (cubicChange g)
  (MvPolynomial.C J * (field () : FirstOrderLagrangian ℝ Unit Unit)) =
  MvPolynomial.C J * field () := nonlinear_source g J'

expect_failure "field_change_inverse_requires_composition" 'import LeanPhy.FieldTheory.PointTransformation
open LeanPhy.FieldTheory PointTransformation
example (F G : Unit → MvPolynomial Unit ℝ) (L : FirstOrderLagrangian ℝ Unit Unit) :
  pullback G (pullback F L) = L := pullback_inverse F G (fun _ => rfl) L'

expect_failure "field_change_boundary_cannot_be_erased" 'import LeanPhy.Examples.FieldRedefinitionResearch
open LeanPhy.FieldTheory PointTransformation LeanPhy.Examples.FieldRedefinitionResearch
example : HasDerivAt (fun s => IntervalAction.action
  (pullback (infinitesimal (fun _ : Unit => MvPolynomial.X ()) s) kinetic) straight 0 1) 0 0 :=
  boundary_variation_nonzero'

expect_failure "field_change_on_shell_needs_endpoint_flux" 'import LeanPhy.FieldTheory.RedefinitionVariation
open LeanPhy.FieldTheory PointTransformation
open scoped ContDiff
example (P : Unit → MvPolynomial Unit ℝ) (L : FirstOrderLagrangian ℝ Unit Unit)
  (ψ : Unit → ℝ → ℝ) (hψ : ∀ i, ContDiff ℝ 2 (ψ i)) (a b : ℝ)
  (hE : ∀ t ∈ Set.uIcc a b, ∀ i, FieldEvaluation.euler L IntervalAction.direction ψ i t = 0) :
  HasDerivAt (fun s => IntervalAction.action (pullback (infinitesimal P s) L) ψ a b) 0 0 :=
  action_infinitesimal_on_shell P L ψ hψ a b (by rfl) hE'

expect_failure "field_change_first_order_is_not_finite" 'import LeanPhy.Examples.FieldRedefinitionResearch
open LeanPhy.FieldTheory PointTransformation LeanPhy.Examples.FieldRedefinitionResearch
example : IntervalAction.action (pullback (infinitesimal (fun _ : Unit => MvPolynomial.X ()) 1) kinetic)
  straight 0 1 = IntervalAction.action kinetic straight 0 1 + 2 := by
  exact finite_change_keeps_higher_order'

expect_failure "field_change_regularity_needed" 'import LeanPhy.FieldTheory.TransformationEvaluation
open LeanPhy.FieldTheory PointTransformation
example (F : Unit → MvPolynomial Unit ℝ) (L : FirstOrderLagrangian ℝ Unit Unit)
  (ψ : Unit → ℝ → ℝ) (a b : ℝ) :
  IntervalAction.action (pullback F L) ψ a b = IntervalAction.action L (transformed F ψ) a b :=
  action_pullback F L ψ (fun _ _ => by assumption) a b'

expect_failure "field_change_euler_requires_c2" 'import LeanPhy.FieldTheory.RedefinitionVariation
open LeanPhy.FieldTheory PointTransformation
open scoped ContDiff
example (P : Unit → MvPolynomial Unit ℝ) (L : FirstOrderLagrangian ℝ Unit Unit)
  (ψ : Unit → ℝ → ℝ) (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (a b : ℝ)
  (hb : IntervalAction.endpoint L ψ (transformed P ψ) b = IntervalAction.endpoint L ψ (transformed P ψ) a)
  (he : ∀ t ∈ Set.uIcc a b, ∀ i, FieldEvaluation.euler L IntervalAction.direction ψ i t = 0) :
  HasDerivAt (fun s => IntervalAction.action (pullback (infinitesimal P s) L) ψ a b) 0 0 :=
  action_infinitesimal_on_shell P L ψ hψ a b hb he'

expect_failure "field_change_finite_slots_must_transform" 'import LeanPhy.FieldTheory.TransformationEvaluation
open LeanPhy.FieldTheory FirstOrderLagrangian PointTransformation
example (F : Unit → MvPolynomial Unit ℝ) (L : FirstOrderLagrangian ℝ Unit Unit)
  (volume : Unit → ℝ) (v : Fin 2 → Unit → Unit × Option Unit → ℝ) :
  finiteProbability (pullback F L) volume v = finiteProbability L volume v :=
  finiteProbability_pullback F L volume v'

expect_failure "field_change_shear_direction" 'import LeanPhy.Examples.FieldRedefinitionResearch
open LeanPhy.FieldTheory PointTransformation LeanPhy.Examples.FieldRedefinitionResearch
example (g : ℝ) (L : FirstOrderLagrangian ℝ (Fin 2) Unit) :
  pullback (shear g) (pullback (shear g) L) = L := shear_density_roundtrip g L'

expect_failure "self_consistency_strict_domain" 'import LeanPhy.Examples.SelfConsistencyResearch
open LeanPhy.Examples.SelfConsistencyResearch
example : (binaryEnvelope (1 / 2)).rate < 1 := by rw [binary_rate]; norm_num'

expect_failure "self_consistency_beta_factor" 'import LeanPhy.Examples.SelfConsistencyResearch
open LeanPhy.StatMech SourceFeedback LeanPhy.Examples.SelfConsistencyResearch
example : HasDerivAt (fun t => feedback (fun _ : Fin 2 => 0) (fun _ : Unit => binarySpin)
  (fun _ => 0) (fun _ _ => 2) (fun _ => t) ()) 1 0 := binary_temperature_derivative 2 1'

expect_failure "self_consistency_solution_budget" 'import LeanPhy.Examples.SelfConsistencyResearch
open LeanPhy.Mathematics LeanPhy.Examples.SelfConsistencyResearch
example : ErrorCertificate (fun _ : Unit => (0 : ℝ))
  ((binaryEnvelope (1 / 8)).solution (fun _ => 0) (fun _ => Real.log 2) weak_coupling) 0 :=
  biased_solution_error'

expect_failure "self_consistency_readout_budget" 'import LeanPhy.Examples.SelfConsistencyResearch
open LeanPhy.StatMech LeanPhy.Mathematics SourceFeedback LeanPhy.Examples.SelfConsistencyResearch
example : ErrorCertificate (3 / 5 : ℝ)
  ((SourceEnsemble.probability (fun _ : Fin 2 => 0) (fun _ : Unit => binarySpin)
    (source (fun _ => Real.log 2) (fun _ _ => 1 / 8)
      ((binaryEnvelope (1 / 8)).solution (fun _ => 0) (fun _ => Real.log 2) weak_coupling))).expectation
      binarySpin) 0 := biased_readout_error'

expect_failure "self_consistency_update_error_retained" 'import LeanPhy.StatMech.FeedbackCertificate
open LeanPhy.StatMech LeanPhy.Mathematics SourceFeedback
example (A : Unit → Fin 2 → ℝ) (K : Unit → Unit → ℝ) (e : Envelope A K)
  (S : Fin 2 → ℝ) (J : Unit → ℝ) (h : e.rate < 1) (m y : Unit → ℝ) (δ : ℝ)
  (hy : ErrorCertificate y (feedback S A J K m) δ) :
  ErrorCertificate m (e.solution S J h) (dist m y / (1 - e.rate)) :=
  e.solution_error_of_update S J h m y δ hy'

expect_failure "self_consistency_model_binding" 'import LeanPhy.StatMech.FeedbackCertificate
open LeanPhy.StatMech LeanPhy.Mathematics SourceFeedback
example (A : Unit → Fin 2 → ℝ) (K : Unit → Unit → ℝ) (e : Envelope A K)
  (S : Fin 2 → ℝ) (J Jnew : Unit → ℝ) (h : e.rate < 1) (m : Unit → ℝ) (ε : ℝ)
  (hr : ErrorCertificate m (feedback S A J K m) ε) :
  ErrorCertificate m (e.solution S Jnew h) (ε / (1 - e.rate)) :=
  e.solution_error S Jnew h m ε hr'

expect_failure "self_consistency_symmetry_required" 'import LeanPhy.StatMech.MeanFieldFunctional
open LeanPhy.StatMech SourceFeedback
open scoped BigOperators
example (S : Fin 2 → ℝ) (A : Fin 2 → Fin 2 → ℝ) (J : Fin 2 → ℝ)
  (K : Fin 2 → Fin 2 → ℝ) (m v : Fin 2 → ℝ) :
  HasDerivAt (fun s => stationaryFunctional S A J K (SourceEnsemble.sourceLine m v s))
    (∑ a, (∑ b, K a b * v b) * (m a - feedback S A J K m a)) 0 :=
  functional_derivative S A J K (fun _ _ => rfl) m v'

expect_failure "self_consistency_stationary_converse" 'import LeanPhy.Examples.SelfConsistencyResearch
open LeanPhy.StatMech SourceFeedback LeanPhy.Examples.SelfConsistencyResearch
example : feedback (fun _ : Fin 2 => 0) (fun _ : Unit => binarySpin)
  (fun _ => 0) (fun _ _ => 0) (fun _ => 1) = fun _ => 1 := by
  exact stationary_not_selfconsistent.1'

expect_failure "self_consistency_nonempty_ensemble" 'import LeanPhy.StatMech.FeedbackCertificate
open LeanPhy.StatMech SourceFeedback
example : Unit → ℝ := feedback (fun _ : Fin 0 => 0) (fun _ : Unit => fun _ => 0)
  (fun _ => 0) (fun _ _ => 0) (fun _ => 0)'

expect_failure "self_consistency_evaluation_error_retained" 'import LeanPhy.StatMech.FeedbackCertificate
open LeanPhy.StatMech LeanPhy.Mathematics SourceFeedback
open scoped NNReal
example (A : Unit → Fin 2 → ℝ) (K : Unit → Unit → ℝ) (e : Envelope A K)
  (S : Fin 2 → ℝ) (J : Unit → ℝ) (h : e.rate < 1) (m : Unit → ℝ) (ε : ℝ)
  (hr : ErrorCertificate m (feedback S A J K m) ε)
  (O : Fin 2 → ℝ) (N : ℝ≥0) (hO : ∀ i, |O i| ≤ N) (value η : ℝ)
  (hv : ErrorCertificate value ((SourceEnsemble.probability S A (source J K m)).expectation O) η) :
  ErrorCertificate value
    ((SourceEnsemble.probability S A (source J K (e.solution S J h))).expectation O)
    ((2 * N * e.coupling) * (ε / (1 - e.rate))) :=
  e.evaluated_observable_error S J h m ε hr O N hO value η hv'

expect_failure "fermion_word_contraction_cannot_be_dropped" 'import LeanPhy.FieldTheory.FermionPolynomial
open LeanPhy.FieldTheory FermionWord FermionPolynomial
example : compile (sub (term (1 : ℤ) [ann (0 : Fin 1), cre 0])
  (term (-1) [cre 0, ann 0])) = [] := by decide'

expect_failure "fermion_word_swap_keeps_sign" 'import LeanPhy.FieldTheory.FermionPolynomial
open LeanPhy.FieldTheory FermionWord FermionPolynomial
example : compile (sub (term (1 : ℤ) [cre (1 : Fin 2), cre 0])
  (term 1 [cre 0, cre 1])) = [] := by decide'

expect_failure "fermion_word_pauli_cannot_be_ignored" 'import LeanPhy.FieldTheory.FermionPolynomial
open LeanPhy.FieldTheory FermionWord FermionPolynomial
example : compile (term (1 : ℤ) [cre (0 : Fin 1), cre 0]) =
  term 1 [cre 0, cre 0] := by decide'

expect_failure "fermion_word_adjoint_reverses_order" 'import LeanPhy.FieldTheory.FermionPolynomial
open LeanPhy.FieldTheory FermionWord FermionPolynomial
example : compile (sub (FermionPolynomial.adjoint (term (1 : ℤ) [cre (0 : Fin 2), ann 1]))
  (term 1 [ann 0, cre 1])) = [] := by decide'

expect_failure "fermion_word_adjoint_conjugates_coefficients" 'import LeanPhy.FieldTheory.FermionPolynomial
open LeanPhy.FieldTheory FermionWord FermionPolynomial
example : FermionPolynomial.adjoint (term Complex.I [cre (0 : Fin 1)]) =
  term Complex.I [ann 0] := by
  simp [FermionPolynomial.adjoint, term, FermionWord.adjoint]'

expect_failure "fermion_word_embedding_requires_distinct_modes" 'import LeanPhy.FieldTheory.FermionEmbedding
open LeanPhy.FieldTheory FermionPolynomial FiniteFermion
example : MultiModeCAR (Fin 2) (Matrix (Occupation 1) (Occupation 1) ℂ) :=
  selectCAR (modes 1).car (fun _ => 0) (by decide)'

expect_failure "fermion_word_quartic_keeps_cubic_equation" 'import LeanPhy.Examples.FermionWordResearch
open LeanPhy.FieldTheory FermionPolynomial LeanPhy.Examples.FermionWordResearch
example : compile (sub (FermionPolynomial.commutator interaction probe) []) = [] := by decide'

expect_failure "fermion_word_commutator_orientation" 'import LeanPhy.Examples.FermionWordResearch
open LeanPhy.FieldTheory FermionPolynomial LeanPhy.Examples.FermionWordResearch
example : compile (sub (FermionPolynomial.commutator probe interaction) interactionEquation) = [] := by decide'

expect_failure "fermion_word_hermiticity_requires_actual_adjoint" 'import LeanPhy.FieldTheory.FermionPolynomial
open LeanPhy.FieldTheory FermionWord FermionPolynomial
example : compile (sub (FermionPolynomial.adjoint (letter (ann (0 : Fin 1)) : Expression ℤ (Fin 1)))
  (letter (ann 0))) = [] := by decide'

expect_failure "fermion_word_certificate_keeps_coefficients" 'import LeanPhy.Examples.FermionWordResearch
open LeanPhy.FieldTheory FermionWord FermionPolynomial LeanPhy.Examples.FermionWordResearch
example : compile (sub (FermionPolynomial.commutator interaction probe)
  (term (-2) [ann 0, cre 1, ann 1])) = [] := by decide'

expect_failure "action_boundary_cannot_be_dropped" 'import LeanPhy.Examples.ActionEvaluationResearch
open LeanPhy.FieldTheory LeanPhy.Examples.ActionEvaluationResearch
example : HasDerivAt (fun s => IntervalAction.action freeDensity
    (FieldEvaluation.perturb straight straight s) 0 1) 0 0 := nonzero_boundary_variation'

expect_failure "action_integral_orientation_is_retained" 'import LeanPhy.Examples.ActionEvaluationResearch
open LeanPhy.FieldTheory LeanPhy.Examples.ActionEvaluationResearch
example : HasDerivAt (fun s => IntervalAction.action freeDensity
    (FieldEvaluation.perturb straight straight s) 0 1) (-1) 0 := nonzero_boundary_variation'

expect_failure "action_endpoint_condition_cannot_be_omitted" 'import LeanPhy.FieldTheory.IntervalAction
open LeanPhy.FieldTheory
open scoped ContDiff
example (L : FirstOrderLagrangian ℝ Unit Unit) (φ η : Unit → ℝ → ℝ)
    (hφ : ∀ i, ContDiff ℝ 2 (φ i)) (hη : ∀ i, ContDiff ℝ 1 (η i)) (a b : ℝ) :
    HasDerivAt (fun s => IntervalAction.action L (FieldEvaluation.perturb φ η s) a b)
      (∫ t in a..b, IntervalAction.bulk L φ η t) 0 :=
  IntervalAction.hasDerivAt_action_fixed_endpoints L φ η hφ hη a b'

expect_failure "action_c2_requirement_cannot_be_replaced_by_c1" 'import LeanPhy.FieldTheory.IntervalAction
open LeanPhy.FieldTheory
open scoped ContDiff
example (L : FirstOrderLagrangian ℝ Unit Unit) (φ η : Unit → ℝ → ℝ)
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) (hη : ∀ i, ContDiff ℝ 1 (η i)) (a b : ℝ) :
    HasDerivAt (fun s => IntervalAction.action L (FieldEvaluation.perturb φ η s) a b)
      ((∫ t in a..b, IntervalAction.bulk L φ η t) +
        IntervalAction.endpoint L φ η b - IntervalAction.endpoint L φ η a) 0 :=
  IntervalAction.hasDerivAt_action_boundary L φ η hφ hη a b'

expect_failure "action_actual_jet_derivative_cannot_be_relabelled" 'import LeanPhy.Examples.ActionEvaluationResearch
open LeanPhy.FieldTheory LeanPhy.Examples.ActionEvaluationResearch
example : HasDerivAt (fun t => CurveJet.evaluate straight t (JetPolynomial.jet () 0)) 0 1 :=
  CurveJet.hasDerivAt_evaluate straight straight_smooth (JetPolynomial.jet () 0) 1'

expect_failure "action_mixed_equation_keeps_other_component" 'import LeanPhy.Examples.ActionEvaluationResearch
open LeanPhy.FieldTheory LeanPhy.Examples.ActionEvaluationResearch
open scoped ContDiff
example (g : ℝ) (φ : Fin 2 → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (t : ℝ) :
    FieldEvaluation.euler (LeanPhy.Examples.VariationalResearch.kineticMixing g)
      IntervalAction.direction φ 0 t = -g * iteratedDeriv 2 (φ 0) t :=
  mixed_profile_equation g φ hφ t'

expect_failure "action_refutation_cannot_close_original_question" 'import LeanPhy.Examples.ActionEvaluationResearch
open LeanPhy.Examples.ActionEvaluationResearch
example : boundaryQuestion.Answer := boundaryCounterexample.refutes'

expect_failure "action_current_drift_cannot_be_zeroed" 'import LeanPhy.Examples.ActionEvaluationResearch
open LeanPhy.FieldTheory LeanPhy.Examples.ActionEvaluationResearch
example : LeanPhy.Mathematics.ErrorCertificate
    (CurveJet.evaluate curved 1 (FirstOrderLagrangian.noetherCurrent freeDensity (fun _ => 1) (fun _ => 0) ()))
    (CurveJet.evaluate curved 0 (FirstOrderLagrangian.noetherCurrent freeDensity (fun _ => 1) (fun _ => 0) ())) 0 :=
  off_shell_drift'

expect_failure "action_field_equation_keeps_actual_profile" 'import LeanPhy.Examples.ActionEvaluationResearch
open LeanPhy.FieldTheory LeanPhy.Examples.ActionEvaluationResearch
example (t : ℝ) : FieldEvaluation.euler freeDensity IntervalAction.direction curved () t = 0 :=
  straight_on_shell t'

expect_failure "action_noether_conservation_needs_euler_equations" 'import LeanPhy.FieldTheory.IntervalAction
open LeanPhy.FieldTheory
open scoped ContDiff
example (L : FirstOrderLagrangian ℝ Unit Unit) (η : Unit → JetPolynomial ℝ Unit Unit)
    (B : Unit → JetPolynomial ℝ Unit Unit)
    (hSym : FirstOrderLagrangian.firstVariation L η = FirstOrderLagrangian.divergence B)
    (φ : Unit → ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (a b : ℝ) :
    CurveJet.evaluate φ b (FirstOrderLagrangian.noetherCurrent L η B ()) =
      CurveJet.evaluate φ a (FirstOrderLagrangian.noetherCurrent L η B ()) :=
  IntervalAction.noether_conserved L η B hSym φ hφ a b'

expect_failure "matrix_certificate_keeps_complex_residual" 'import LeanPhy.Examples.Generated.ComplexHeavyCertificate
open LeanPhy.Mathematics LeanPhy.Mathematics.MatrixCertificate
open LeanPhy.Generated.MatrixCertificates.ComplexHeavy
example : (candidate.residual nominal).Bounded 0 := by decide +kernel'

expect_failure "matrix_certificate_margin_must_be_strict" 'import LeanPhy.Examples.Generated.ComplexHeavyCertificate
open LeanPhy.Mathematics LeanPhy.Mathematics.MatrixCertificate
open LeanPhy.Generated.MatrixCertificates.ComplexHeavy
example : ({ candidate with modelRadius := 3 } : Candidate 2).Accepted nominal := by decide +kernel'

expect_failure "matrix_certificate_negative_radius_rejected" 'import LeanPhy.Examples.Generated.ComplexHeavyCertificate
open LeanPhy.Mathematics LeanPhy.Mathematics.MatrixCertificate
open LeanPhy.Generated.MatrixCertificates.ComplexHeavy
example : ({ candidate with modelRadius := -1 } : Candidate 2).Accepted nominal := by decide +kernel'

expect_failure "matrix_certificate_inverse_norm_not_optional" 'import LeanPhy.Examples.Generated.ComplexHeavyCertificate
open LeanPhy.Mathematics LeanPhy.Mathematics.MatrixCertificate
open LeanPhy.Generated.MatrixCertificates.ComplexHeavy
example : ({ candidate with inverseBound := 0 } : Candidate 2).Accepted nominal := by decide +kernel'

expect_failure "matrix_certificate_keeps_model_error_budget" 'import LeanPhy.Examples.Generated.ComplexHeavyCertificate
open LeanPhy.Mathematics.MatrixCertificate LeanPhy.Generated.MatrixCertificates.ComplexHeavy
example : candidate.errorBound = (1 / 12 : ℚ) := by decide +kernel'

expect_failure "matrix_certificate_cannot_relabel_the_nominal_matrix" 'import LeanPhy.Examples.Generated.ComplexHeavyCertificate
open LeanPhy.Mathematics LeanPhy.Mathematics.MatrixCertificate
open LeanPhy.Generated.MatrixCertificates.ComplexHeavy
example : candidate.Accepted (RationalMatrix.zero 2 2) := accepted'

expect_failure "matrix_certificate_wrong_payload_rejected" 'import LeanPhy.Examples.Generated.ComplexHeavyCertificate
open LeanPhy.Mathematics LeanPhy.Mathematics.MatrixCertificate
open LeanPhy.Generated.MatrixCertificates.ComplexHeavy
example : (checker nominal candidate).check { candidate with modelRadius := 4 } := by
  constructor
  · rfl
  · exact accepted'

expect_failure "matrix_resolvent_keeps_energy_domain" 'import LeanPhy.Examples.MatrixCertificateResearch
open LeanPhy.Examples.MatrixCertificateResearch
example : (3 : ℂ) ∉ spectrum ℂ heavy := disk_excluded 3 (by norm_num)'

expect_failure "matrix_effective_error_is_not_exact_equality" 'import LeanPhy.Examples.MatrixCertificateResearch
open LeanPhy.Mathematics LeanPhy.Examples.MatrixCertificateResearch
open scoped Matrix.Norms.Operator
example : ErrorCertificate (model 0 (by simp)).effectiveHamiltonian !![-(1 / 2 : ℂ)] 0 :=
  effective_disk_error 0 (by simp)'

expect_failure "matrix_residual_bound_requires_margin" 'import LeanPhy.Mathematics.ResidualInverse
open LeanPhy.Mathematics.ResidualInverse
example {R : Type} [NormedRing R] (D : Rˣ) (K : R) (κ r : ℝ)
    (hK : ‖K‖ ≤ κ) (hR : ‖1 - (D : R) * K‖ ≤ r) :
    ‖(↑(D⁻¹) : R)‖ ≤ κ / (1 - r) := by
  exact inverse_norm_bound D K κ r hK hR'

expect_failure "exploration_same_label_is_not_same_condition" 'import LeanPhy.Examples.ExplorationResearch
open LeanPhy.Workflow.Exploration LeanPhy.Examples.ExplorationResearch
example : ((Branch.root pairingQuestion).refine "real pairing"
    ⟨"real order parameter", "same label, changed predicate", fun _ => True⟩).Goal :=
  real_pairing_branch'

expect_failure "exploration_conditional_is_not_root_answer" 'import LeanPhy.Examples.ExplorationResearch
open LeanPhy.Examples.ExplorationResearch
example : pairingQuestion.Answer := real_pairing_branch'

expect_failure "exploration_refutation_is_not_positive_evidence" 'import LeanPhy.Examples.ExplorationResearch
open LeanPhy.Examples.ExplorationResearch
example : pairingQuestion.Answer := phaseCounterexample.refutes'

expect_failure "exploration_revision_does_not_prove_old_goal" 'import LeanPhy.Examples.ExplorationResearch
open LeanPhy.Examples.ExplorationResearch
example : massQuestion.Answer := invertible_mass_answer'

expect_failure "exploration_changed_target_requires_rechecking" 'import LeanPhy.Examples.ExplorationResearch
open LeanPhy.Examples.ExplorationResearch
example : pairingQuestion.Answer := corrected_pairing_answer'

expect_failure "exploration_notebook_cannot_mix_question_types" 'import LeanPhy.Examples.ExplorationResearch
open LeanPhy.Workflow.Exploration LeanPhy.Examples.ExplorationResearch
example : Notebook correctedPairing := pairingNotebook'

expect_failure "exploration_completion_requires_domain_discharge" 'import LeanPhy.Examples.ExplorationResearch
open LeanPhy.Workflow LeanPhy.Examples.ExplorationResearch
example : TheoryPackage := pairingNotebook.complete "report" "condensed matter" real_pairing_branch'

expect_failure "exploration_failed_search_is_not_refutation" 'import LeanPhy.Workflow.Exploration
open LeanPhy.Workflow
example : ExplorationEvidence True := .refuted (show True from True.intro)'

expect_failure "exploration_counterexample_must_satisfy_conditions" 'import LeanPhy.Examples.ExplorationResearch
open LeanPhy.Workflow.Exploration LeanPhy.Examples.ExplorationResearch
example : Condition.Holds massiveBranch.conditions 0 := by
  simp [massiveBranch, Branch.refine, nonzeroMass, Branch.root]'

expect_failure "exploration_one_case_does_not_cover_root" 'import LeanPhy.Examples.ExplorationResearch
open LeanPhy.Workflow.Exploration LeanPhy.Examples.ExplorationResearch
example : (Branch.root regularizedQuestion).Goal :=
  (Branch.root regularizedQuestion).joinSplit nonzeroMass "nonzero" "zero"
    regularized_nonzero regularized_nonzero'

expect_failure "exploration_indexed_update_reads_stored_goal" 'import LeanPhy.Examples.ExplorationResearch
open LeanPhy.Workflow.Exploration LeanPhy.Examples.ExplorationResearch
example : Notebook pairingQuestion :=
  let n := Notebook.start pairingQuestion
  n.record ⟨⟨0, by decide⟩⟩ (.checked real_pairing_branch)'

expect_failure "exploration_proved_conditional_records_keep_goal_open" 'import LeanPhy.Examples.ExplorationResearch
open LeanPhy.Examples.ExplorationResearch
example : pairingOpen.obligationCount = 0 := by decide'

expect_failure "exploration_empty_branch_cannot_cover_domain" 'import LeanPhy.Workflow.Exploration
open LeanPhy.Workflow.Exploration
example (Q : Question Unit) (hx : Q.domain ()) :
    ∀ x, Q.domain x → Condition.Holds [⟨"empty", "False", fun _ => False⟩] x := by
  intro x hx
  simp [Condition.Holds]'

expect_failure "dynamics_wrong_time_sign" 'import LeanPhy.Examples.DynamicsResearch
open LeanPhy.Quantum LeanPhy.Quantum.Dynamics LeanPhy.Examples.DynamicsResearch
open scoped Matrix Matrix.Norms.Operator
example : HasDerivAt (heisenberg pauliZ pauliX) ((2 : ℂ) • pauliY) 0 := by
  exact time_sign'

expect_failure "dynamics_kernel_source_sign" 'import LeanPhy.Examples.DynamicsResearch
open LeanPhy.Quantum LeanPhy.Quantum.Dynamics LeanPhy.Examples.DynamicsResearch
example : kernel initialState.rho pauliZ pauliX pauliY 0 0 = 2 := by
  rw [kernel_sign]
  norm_num'

expect_failure "dynamics_noncommuting_pauli_input" 'import LeanPhy.Examples.DynamicsResearch
open LeanPhy.Quantum
example : Commute pauliZ pauliX := by
  constructor
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauliZ, pauliX, Matrix.mul_apply, Fin.sum_univ_two]'

expect_failure "dynamics_scalar_exponential_rule_requires_commute" 'import LeanPhy.Mathematics.Duhamel
open LeanPhy.Mathematics.Duhamel
example {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] (G V : A) (t : ℝ) :
    insertion G V t = t • (flow G t * V) := by
  exact insertion_of_commute G V t'

expect_failure "thermal_response_requires_normalization" 'import LeanPhy.Examples.DynamicsResearch
open LeanPhy.Quantum.ThermalPerturbation
example : response (0 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 0 1 = -2 := by
  rw [response_identity]
  norm_num'

expect_failure "thermal_probe_contact_cannot_be_dropped" 'import LeanPhy.Examples.DynamicsResearch
open LeanPhy.Quantum.ThermalPerturbation LeanPhy.Examples.DynamicsResearch
example : response (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 1 1 = 0 := by
  rw [contact_required]
  norm_num'

expect_failure "thermal_response_keeps_beta" 'import LeanPhy.Examples.DynamicsResearch
open LeanPhy.Quantum LeanPhy.Quantum.ThermalPerturbation LeanPhy.Examples.DynamicsResearch
example : response (0 : Matrix (Fin 2) (Fin 2) ℂ) pauliZ pauliZ 0 2 = -1 := by
  rw [beta_factor]
  norm_num'

expect_failure "thermal_energy_source_sign" 'import LeanPhy.Examples.DynamicsResearch
open LeanPhy.Quantum LeanPhy.Quantum.ThermalPerturbation LeanPhy.Examples.DynamicsResearch
example : response (0 : Matrix (Fin 2) (Fin 2) ℂ) pauliZ pauliZ 0 2 = 2 := by
  rw [beta_factor]
  norm_num'

expect_failure "dynamics_switched_source_has_no_past_response" 'import LeanPhy.Quantum.DynamicalResponse
open LeanPhy.Quantum.Dynamics
example (ρ H V O : Matrix (Fin 2) (Fin 2) ℂ) : stepResponse ρ H V O (-1) = 1 := by
  rw [step_response_causal _ _ _ _ _ (by norm_num)]
  norm_num'

expect_failure "thermal_perturbation_requires_hermitian_coupling" 'import LeanPhy.Quantum.ThermalPerturbation
open LeanPhy.Quantum.ThermalPerturbation
example (H V : Matrix (Fin 2) (Fin 2) ℂ) (hH : H.IsHermitian) :
    (H + (1 : ℝ) • V).IsHermitian := by
  exact perturbed_hermitian H V hH'

expect_failure "fermion_complex_pairing_requires_conjugate" 'import LeanPhy.Examples.FermionResearch
open LeanPhy.Condensed LeanPhy.Examples.FermionResearch
example : ComplexPairing.block 0 Complex.I = bdg 0 Complex.I := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [ComplexPairing.block, bdg]'

expect_failure "fermion_pairing_square_requires_norm" 'import LeanPhy.Condensed.ComplexPairing
open LeanPhy.Condensed
example : ComplexPairing.block 0 Complex.I * ComplexPairing.block 0 Complex.I =
    Complex.I ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [ComplexPairing.square]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Complex.normSq]'

expect_failure "fermion_spinless_diagonal_pairing_forbidden" 'import LeanPhy.FieldTheory.FermionBdG
open LeanPhy.FieldTheory.FermionBdG
example : Coefficients Unit :=
  { normal := 0, pairing := 1, normal_hermitian := by simp,
    pairing_skew := by ext i j; norm_num }'

expect_failure "fermion_particle_hole_is_antilinear" 'import LeanPhy.FieldTheory.FermionBdG
open LeanPhy.FieldTheory.FermionBdG
example : particleHole (Complex.I • (fun _ : Unit ⊕ Unit => (1 : ℂ))) =
    Complex.I • particleHole (fun _ : Unit ⊕ Unit => (1 : ℂ)) := by
  funext i
  norm_num [particleHole]'

expect_failure "fermion_nambu_energy_requires_half" 'import LeanPhy.Examples.FermionResearch
open LeanPhy.FieldTheory.FiniteFermion LeanPhy.FieldTheory.FermionBdG
example (n : ℕ) (K : Coefficients (Fin n)) :
    (modes n).hamiltonian K = nambuQuadratic (modes n).car K + Matrix.trace K.normal • 1 :=
  LeanPhy.Examples.FermionResearch.constructed_energy n K'

expect_failure "fermion_normal_order_keeps_trace" 'import LeanPhy.Examples.FermionResearch
open LeanPhy.FieldTheory.FiniteFermion LeanPhy.FieldTheory
example : (modes 1).car.antiNormal (1 : Matrix (Fin 1) (Fin 1) ℂ) =
    -(modes 1).car.normal 1 := by
  rw [MultiModeCAR.antiNormal_eq]
  simp'

expect_failure "fermion_majorana_occupation_sign" 'import LeanPhy.Examples.FermionResearch
open LeanPhy.FieldTheory.FiniteFermion
example (n : ℕ) (i : Fin n) : (modes n).car.numberOp i = (1 / 2 : ℂ) •
    (1 - Complex.I • ((modes n).car.majoranaX i * (modes n).car.majoranaY i)) :=
  (modes n).car.occupation_majorana i'

expect_failure "fermion_pair_basis_uses_transpose" 'import LeanPhy.FieldTheory.FermionBasis
open LeanPhy.Quantum LeanPhy.FieldTheory.FermionBdG
open scoped Matrix
example (K : Coefficients (Fin 2)) (U : FiniteUnitary (Fin 2)) :
    (K.rotate U).pairing = U.op * K.pairing * U.opᴴ := rfl'

expect_failure "fermion_tensor_local_modes_need_parity" 'import LeanPhy.Examples.FermionResearch
open LeanPhy.Quantum LeanPhy.Condensed
open scoped Kronecker
example : ⟪smMat ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ), 1 ⊗ₖ smMat⟫ = 0 := by
  ext i j
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [anticommutator, ← Matrix.mul_kronecker_mul, smMat, Matrix.kronecker_apply]'

expect_failure "fermion_nambu_is_not_manybody_space" 'import LeanPhy.FieldTheory.FiniteFermion
open LeanPhy.Quantum LeanPhy.FieldTheory.FiniteFermion LeanPhy.FieldTheory.FermionBdG
example (K : Coefficients (Fin 3)) : FiniteDensity (Fin 3 ⊕ Fin 3) :=
  (modes 3).thermalState K 1'

expect_failure "fermion_wick_not_from_arbitrary_density" 'import LeanPhy.FieldTheory.FermionicQuasiFree
open LeanPhy.Quantum LeanPhy.FieldTheory LeanPhy.FieldTheory.SingleModeVacuum
example (rho : FiniteDensity (Fin 2)) :
    Matrix.trace (rho.rho * (generator 0 * generator 1 * generator 0 * generator 1)) =
      FermionicWick.fourPoint (orderedContraction (slots 0 1 0 1)) 0 1 2 3 := by
  exact vacuum_fourPoint 0 1 0 1'

expect_failure "fermion_normal_coupling_requires_adjoint" 'import LeanPhy.FieldTheory.FermionBdG
open LeanPhy.FieldTheory.FermionBdG
open scoped Matrix
example : Coefficients (Fin 2) :=
  { normal := !![0, 1; 0, 0], pairing := 0, pairing_skew := by simp,
    normal_hermitian := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply] }'

expect_failure "fermion_mode_mixing_requires_isometry" 'import LeanPhy.FieldTheory.FiniteFermion
import LeanPhy.FieldTheory.FermionLinear
open LeanPhy.FieldTheory.FiniteFermion
open scoped Matrix
example := (modes 1).car.mix ((2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) (by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply])'

expect_failure "singular_heavy_block_has_no_certified_inverse" 'import LeanPhy.Mathematics.BlockElimination
def invalidInverse : (Matrix Unit Unit ℚ)ˣ :=
  ⟨0, 0, by norm_num, by norm_num⟩'

expect_failure "elimination_requires_transformed_source" 'import LeanPhy.Examples.EffectiveResearch
open LeanPhy.Examples.EffectiveResearch
example : drivenBlock.effectiveSource (fun _ => 11) (fun _ => 13) () = 11 := by
  rw [driven_source_and_reconstruction.2.1]
  norm_num'

expect_failure "effective_readout_requires_source_offset" 'import LeanPhy.Examples.EffectiveResearch
open LeanPhy.Examples.EffectiveResearch
example : drivenBlock.readoutOffset (fun _ : Unit => fun _ => 3) (fun _ => 13) () = 0 := by
  rw [driven_readout.2]
  norm_num'

expect_failure "reconstruction_metric_is_not_identity" 'import LeanPhy.Examples.EffectiveResearch
open LeanPhy.Examples.EffectiveResearch
example : mixedModel.normMetric () () = 1 := by
  rw [mixed_metric]
  norm_num'

expect_failure "formal_product_retains_operator_order" 'import LeanPhy.Examples.EffectiveResearch
open LeanPhy.Examples.EffectiveResearch PowerSeries
example : coeff 2 ((PowerSeries.X * C forward) * (PowerSeries.X * C backward)) =
    coeff 2 ((PowerSeries.X * C backward) * (PowerSeries.X * C forward)) := by
  exact False.elim (order_two_is_ordered (by rfl))'

expect_failure "retained_order_does_not_prove_exact_equality" 'import LeanPhy.Examples.EffectiveResearch
open LeanPhy.Examples.EffectiveResearch
example : (1 + (PowerSeries.X : PowerSeries ℚ)^2) = 1 := by
  exact truncation_is_not_exact.1'

expect_failure "formal_inverse_requires_correct_constant" 'import LeanPhy.Mathematics.FormalExpansion
open LeanPhy.Mathematics.FormalExpansion PowerSeries
example : truncate 2 (invOfUnit (truncate 2 (2 : PowerSeries ℚ)) 1) =
    truncate 2 (invOfUnit (2 : PowerSeries ℚ) 1) := by
  exact truncate_inverse 2 2 1 (by norm_num) (by norm_num)'

expect_failure "massless_auxiliary_field_cannot_be_solved" 'import LeanPhy.FieldTheory.HeavyFieldElimination
open LeanPhy.FieldTheory.HeavyFieldElimination
example (V J : MvPolynomial Unit ℝ) :
    eliminate 0 J (MvPolynomial.pderiv none (action 0 V J)) = 0 := by
  exact eliminated_heavy_equation 0 (by norm_num) V J'

expect_failure "induced_action_retains_source_quadratic_term" 'import LeanPhy.FieldTheory.HeavyFieldElimination
open LeanPhy.FieldTheory.HeavyFieldElimination
example : effective 1 (0 : MvPolynomial Unit ℝ) 1 = 0 := by
  norm_num [effective]'

expect_failure "geometric_inverse_is_not_exact_at_finite_order" 'import LeanPhy.Examples.EffectiveResearch
open LeanPhy.Examples.EffectiveResearch LeanPhy.Mathematics
example : 1 - (1 - (1 / 2 : ℝ)) * EliminationError.geometricInverse (1 / 2 : ℝ) 3 = 0 := by
  rw [geometric_remainder_regression]
  norm_num'

expect_failure "energy_elimination_requires_actual_resolvent" 'import LeanPhy.Quantum.EffectiveHamiltonian
open LeanPhy.Quantum.EnergyElimination
def invalidModel : Model Unit Unit where
  light := 1
  toLight := 0
  toHeavy := 0
  heavy := 1
  energy := 1
  resolvent := 1
  resolvent_eq := by norm_num'

expect_failure "inverse_residual_does_not_give_zero_error" 'import LeanPhy.Mathematics.EliminationError
open LeanPhy.Mathematics
example (D : ℝˣ) (K : ℝ) : ErrorCertificate (↑(D⁻¹) : ℝ) K 0 := by
  exact EliminationError.inverse_error D K'

expect_failure "thermal_state_requires_hermitian_hamiltonian" 'import LeanPhy.Quantum.FiniteThermalState
open LeanPhy.Quantum
noncomputable def invalidThermalState := finiteThermalState
  (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)
  (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply]) 1'

expect_failure "thermal_basis_change_requires_probe_transport" 'import LeanPhy.Examples.SourceResponseResearch
open LeanPhy.Quantum LeanPhy.Examples.SourceResponseResearch
example : Matrix.trace (flipBasis.conjugate (diagonalDensity leftProbability).rho *
    realDiagonal leftProbability.weight) =
    Matrix.trace ((diagonalDensity leftProbability).rho * realDiagonal leftProbability.weight) := by
  rw [changing_only_state_changes_readout.1, changing_only_state_changes_readout.2]
  norm_num'

expect_failure "quantum_trace_response_retains_beta" 'import LeanPhy.Examples.SourceResponseResearch
open LeanPhy.Quantum LeanPhy.Examples.SourceResponseResearch
example (U : FiniteUnitary Bool) : deriv (fun h => (Matrix.trace
    ((thermalStateInBasis U 2 (fun b => -h * spinValue b)).rho *
      U.conjugate (realDiagonal spinValue))).re) 0 = 1 := by
  rw [thermal_beta_factor_regression]
  norm_num'

expect_failure "diagonal_density_requires_positive_probability" 'import LeanPhy.Quantum.FiniteThermalState
open LeanPhy.Quantum LeanPhy.StatMech
noncomputable def invalidDensity := diagonalDensity
  ({ weight := fun i : Fin 2 => if i = 0 then -1 else 2,
     nonneg := by intro i; fin_cases i <;> norm_num,
     normalised := by norm_num [Fin.sum_univ_two] } : FiniteProbability (Fin 2))'

expect_failure "source_partition_zero_cannot_be_normalized" 'import LeanPhy.Examples.SourceResponseResearch
open LeanPhy.Examples.SourceResponseResearch
noncomputable def invalidSource := cancellingBase.withSource cancellationInsertion (Complex.log 2)
  (by rw [source_partition_can_vanish]; norm_num)'

expect_failure "gibbs_response_cannot_drop_beta" 'import LeanPhy.Examples.SourceResponseResearch
open LeanPhy.StatMech LeanPhy.Examples.SourceResponseResearch
example : deriv (fun h => (finiteGibbsProbability 2
    (fun b : Bool => -h * spinValue b)).expectation spinValue) 0 = 1 := by
  rw [beta_factor_regression]
  norm_num'

expect_failure "moving_observable_requires_contact_term" 'import LeanPhy.Examples.SourceResponseResearch
open LeanPhy.StatMech LeanPhy.Examples.SourceResponseResearch
example : deriv (fun s => (SourceEnsemble.probability (fun _ : Unit => 0)
    (fun _ : Unit => fun _ : Unit => 0)
    (SourceEnsemble.sourceLine (fun _ : Unit => 0) (fun _ : Unit => 1) s)).expectation
      (fun _ => s)) 0 = 0 := by
  rw [(moving_constant_contact (fun _ : Unit => 0) (fun _ : Unit => fun _ : Unit => 0)
    (fun _ => 0) (fun _ => 1) 0).deriv]
  norm_num'

expect_failure "signed_connected_fluctuation_need_not_be_positive" 'import LeanPhy.Examples.SourceResponseResearch
open LeanPhy.Examples.SourceResponseResearch
example : 0 ≤ (cancellingBase.connectedCorrelator cancellationInsertion cancellationInsertion).re := by
  rw [signed_connected_negative]
  norm_num'

expect_failure "normalized_response_requires_partition_nonzero" 'import LeanPhy.Mathematics.FiniteWeightedResponse
open LeanPhy.Mathematics
example (w : ℝ → Unit → ℝ) (O score : Unit → ℝ) (t : ℝ)
    (hw : ∀ i, HasDerivAt (fun s => w s i) (w t i * score i) t) :
    HasDerivAt (fun s => FiniteWeighted.expectation (w s) O)
      (FiniteWeighted.connected (w t) O score) t := by
  exact FiniteWeighted.hasDerivAt_expectation_fixed w O score t hw (by intro h; contradiction)'

expect_failure "source_error_requires_uniform_observable_bound" 'import LeanPhy.StatMech.ResponseBound
open LeanPhy.StatMech LeanPhy.Mathematics
example (S : Unit → ℝ) (A : Unit → Unit → ℝ) (O : Unit → ℝ)
    (J v : Unit → ℝ) (s t : ℝ)
    (hA : ∀ i, |SourceEnsemble.directionObservable A v i| ≤ 1) :
    ErrorCertificate ((SourceEnsemble.probability S A (SourceEnsemble.sourceLine J v s)).expectation O)
      ((SourceEnsemble.probability S A (SourceEnsemble.sourceLine J v t)).expectation O)
      (2 * 1 * 1 * |s - t|) := by
  exact SourceEnsemble.expectation_source_error S A J v O 1 1 (by norm_num) (by norm_num)
    (by intro i; exact le_rfl) hA s t'

expect_failure "euclidean_action_response_has_negative_sign" 'import LeanPhy.Examples.SourceResponseResearch
open LeanPhy.Examples.SourceResponseResearch LeanPhy.FieldTheory.FirstOrderLagrangian
example (L V : LeanPhy.FieldTheory.FirstOrderLagrangian ℝ Unit Unit)
    (values : Fin 2 → Unit → Unit × Option Unit → ℝ) (O : Fin 2 → ℝ) (h : ℝ) :
    HasDerivAt (fun t => (finiteProbability (L + t • V) (fun _ => 1) values).expectation O)
      ((finiteProbability (L + h • V) (fun _ => 1) values).covariance O
        (finiteAction V (fun _ => 1) values)) h := by
  exact density_coupling_response L V values O h'

expect_failure "temperature_response_requires_nonzero_temperature" 'import LeanPhy.StatMech.GibbsResponse
open LeanPhy.StatMech
example (E : Unit → ℝ) :
    HasDerivAt (fun t => (finiteGibbsProbability t⁻¹ E).expectation E)
      ((finiteGibbsProbability (0 : ℝ)⁻¹ E).variance E / (0 : ℝ)^2) 0 := by
  exact hasDerivAt_finiteGibbs_temperature E 0 (by norm_num)'

expect_failure "coupled_euler_requires_cross_acceleration" 'import LeanPhy.Classical.Lagrangian
open LeanPhy.Classical
example : fieldEulerLagrangeResidual (0 : Fin 2)
    (fieldJetVar 0 1 * fieldJetVar 1 1) = 0 := by
  simp [fieldEulerLagrangeResidual, fieldTimeDerivative, fieldJetVar]'

expect_failure "full_jets_do_not_drop_higher_derivatives" 'import LeanPhy.FieldTheory.Jet
open LeanPhy.FieldTheory LeanPhy.FieldTheory.JetPolynomial
example : totalDerivative () (jet () (Finsupp.single () 2) : JetPolynomial ℝ Unit Unit) = 0 := by
  simp [jet, totalDerivative]'

expect_failure "first_order_action_rejects_second_jet" 'import LeanPhy.FieldTheory.Variational
open LeanPhy.FieldTheory
noncomputable def invalidAction : FirstOrderLagrangian ℝ Unit Unit :=
  (JetPolynomial.jet () (Finsupp.single () 2) : JetPolynomial ℝ Unit Unit)'

expect_failure "kinetic_momentum_requires_tensor_symmetry" 'import LeanPhy.FieldTheory.PolynomialAction
open LeanPhy.FieldTheory.FirstOrderLagrangian LeanPhy.FieldTheory.JetPolynomial
open scoped BigOperators
example (K : (Fin 2 × Unit) → (Fin 2 × Unit) → ℝ) :
    momentum (quadraticKinetic K) 0 () =
      ∑ j, MvPolynomial.C (K (0, ()) j) * jet j.1 (Finsupp.single j.2 1) := by
  exact momentum_quadraticKinetic_of_symmetric K (by intro i j; rfl) 0 ()'

expect_failure "field_merge_is_not_relabeling" 'import LeanPhy.FieldTheory.Variational
open LeanPhy.FieldTheory LeanPhy.FieldTheory.FirstOrderLagrangian
example (L : FirstOrderLagrangian ℝ (Fin 2) Unit) :
    eulerLagrange (renameFields (fun _ => ()) L) () =
      JetPolynomial.renameFields (fun _ => ()) (eulerLagrange L 0) := by
  exact eulerLagrange_renameFields (fun _ => ()) (by intro a b h; rfl) L 0'

expect_failure "noether_requires_symmetry_variation" 'import LeanPhy.FieldTheory.Variational
open LeanPhy.FieldTheory LeanPhy.FieldTheory.FirstOrderLagrangian
example (L : FirstOrderLagrangian ℝ Unit Unit) :
    divergence (noetherCurrent L (fun _ => 1) (fun _ => 0)) =
      -(∑ a, eulerLagrange L a * 1) := by
  exact noether_off_shell L (fun _ => 1) (fun _ => 0) (by rfl)'

expect_failure "stress_conservation_requires_euler_equations" 'import LeanPhy.FieldTheory.EnergyMomentum
open LeanPhy.FieldTheory LeanPhy.FieldTheory.FirstOrderLagrangian
example (L : FirstOrderLagrangian ℝ Unit Unit)
    (ev : JetPolynomial ℝ Unit Unit →+* ℝ) :
    ev (divergence (fun μ => canonicalStressTensor L μ ())) = 0 := by
  exact canonicalStressTensor_on_shell L () ev (by intro a; rfl)'

expect_failure "first_variation_cannot_drop_boundary_current" 'import LeanPhy.FieldTheory.Variational
open LeanPhy.FieldTheory LeanPhy.FieldTheory.FirstOrderLagrangian
example (L : FirstOrderLagrangian ℝ Unit Unit)
    (η : Unit → JetPolynomial ℝ Unit Unit) :
    firstVariation L η = ∑ a, eulerLagrange L a * η a := by
  exact first_variation L η'

expect_failure "current_budget_requires_symmetry_breaking_bound" 'import LeanPhy.FieldTheory.VariationalResidual
open LeanPhy.FieldTheory LeanPhy.FieldTheory.FirstOrderLagrangian LeanPhy.Mathematics
example (L : FirstOrderLagrangian ℝ Unit Unit)
    (η : Unit → JetPolynomial ℝ Unit Unit) (B : Unit → JetPolynomial ℝ Unit Unit)
    (ev : JetPolynomial ℝ Unit Unit →+* ℝ) (ε M : Unit → ℝ)
    (hE : ∀ a, ErrorCertificate (ev (eulerLagrange L a)) 0 (ε a))
    (hη : ∀ a, |ev (η a)| ≤ M a) :
    ErrorCertificate (ev (divergence (noetherCurrent L η B))) 0 (∑ a, ε a * M a) := by
  simpa using noether_residual_certificate L η B ev ε M 0 hE hη
    (ErrorCertificate.of_eq (by rfl))'

expect_failure "current_error_budget_does_not_imply_exact_conservation" 'import LeanPhy.Examples.VariationalResearch
open LeanPhy.Examples.VariationalResearch LeanPhy.FieldTheory.FirstOrderLagrangian
example : candidateJets (divergence (noetherCurrent (kineticMixing 1)
    (fun _ => 1) (fun _ => 0))) = 0 := by
  rw [candidate_current_defect]
  norm_num'

expect_failure "text_obligation_cannot_be_closed" 'import LeanPhy.Workflow.Core
open LeanPhy.Workflow
def package := (TheoryPackage.empty "model" "test").addObligationText "bridge" "continuum" "test"
def ref : ObligationRef package := ⟨⟨0, by decide⟩⟩
def invalidResolution := package.resolveObligation ref "closed" "bridge" "test" [] [] True.intro'

expect_failure "same_name_target_substitution" 'import LeanPhy.Workflow.Core
open LeanPhy.Workflow
def original : ExternalObligationWitness :=
  { metadata := { name := "bridge", statement := "original target", source := "test" }, proposition := False }
def replacement : ExternalObligationWitness := { original with proposition := True }
def base := TheoryPackage.empty "model" "test"
def package := base.addObligationWitness original
def invalidResolution := package.resolveObligation (base.addedObligationRef replacement)
  "closed" "bridge" "test" [] [] True.intro'

expect_failure "obligation_reference_wrong_project" 'import LeanPhy.Workflow.Core
open LeanPhy.Workflow
def goal : ExternalObligationWitness :=
  { metadata := { name := "bridge", statement := "target", source := "test" }, proposition := 1 = (1 : Nat) }
def first := TheoryPackage.empty "first" "test"
def second := TheoryPackage.empty "second" "test"
def package := second.addObligationWitness goal
def invalidResolution := package.resolveObligation (first.addedObligationRef goal)
  "closed" "bridge" "test" [] [] rfl'

expect_failure "weaker_consequence_does_not_close_target" 'import LeanPhy.Workflow.Core
open LeanPhy.Workflow
def goal : ExternalObligationWitness :=
  { metadata := { name := "bridge", statement := "target", source := "test" }, proposition := False }
def base := TheoryPackage.empty "model" "test"
def package := base.addObligationWitness goal
def invalidResolution := package.resolveObligationWitness (base.addedObligationRef goal)
  "closed" "weaker" "test" [] [] (fun _ => True.intro) True.intro'

expect_failure "declaration_index_rejects_untrusted_proof" 'import LeanPhy.Library.Index
namespace LeanPhy.IndexNegative
axiom untrustedInput : False
theorem untrustedConclusion : False := untrustedInput
end LeanPhy.IndexNegative
physics_index invalidIndex'

expect_failure "dimension_mismatch" 'import LeanPhy
open LeanPhy
example (x : Length) (y : TimeQ) : Length := x + y'

expect_failure "dimension_quotient_mismatch" 'import LeanPhy
open LeanPhy
example (x : Length) (t : TimeQ) : Length := x / t'

expect_failure "integral_certificate_requires_integrability" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
example (μ : MeasureTheory.Measure ℝ) :
    IntegralCertificate μ (fun _ : ℝ => (0 : ℝ)) 0 :=
  { integral_eq := by simp }'

expect_failure "eft_truncation_requires_hierarchy" 'import LeanPhy.Entry.HighEnergy
open LeanPhy.HighEnergy
open LeanPhy.Mathematics
def epsilon : ExpansionParameter :=
  { value := (1 : ℝ) / 10, nonneg := by norm_num, le_one := by norm_num }
def eft : FiniteEFT (Fin 1) :=
  { order := fun _ => 2, coefficient := fun _ => 1,
    coefficientBound := 1, coefficientBound_nonneg := by norm_num,
    coefficient_abs_le := by intro i; simp }
example : ErrorCertificate (eft.amplitude epsilon)
    (eft.retainedAmplitude epsilon (∅ : Finset (Fin 1))) 1 := by
  exact eft.truncation_error_certificate epsilon (∅ : Finset (Fin 1)) 1'

expect_failure "continuous_path_integral_requires_weight_integrability" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
def badPath : ContinuousPathIntegral Unit (MeasureTheory.Measure.dirac ()) :=
  { weight := fun _ => (1 : ℂ), partition := 1,
    partition_eq := by simp, partition_ne_zero := one_ne_zero }'

expect_failure "continuous_path_integral_requires_nonzero_partition" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
def badPath : ContinuousPathIntegral Unit (MeasureTheory.Measure.dirac ()) :=
  { weight := fun _ => (1 : ℂ),
    weight_integrable := by simpa using (MeasureTheory.integrable_const
      (μ := MeasureTheory.Measure.dirac ()) (c := (1 : ℂ))),
    partition := 0, partition_eq := by simp, partition_ne_zero := by simp }'

expect_failure "checked_claim_proof_required" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def missingProof : CheckedClaim :=
  { name := "invalid", statement := "True", proposition := True }'

expect_failure "constrained_dynamics_equivariance_required" 'import LeanPhy.Minimal
open LeanPhy.Mathematics
instance : SMul Unit Nat := ⟨fun _ n => n⟩
instance : MulAction Unit Nat where
  one_smul := by intro n; rfl
  mul_smul := by intro _ _ n; rfl
def system : ConstrainedSymmetry Unit Nat where
  admissible := fun _ => True
  constrained := fun _ => True
  admissible_preserved := by intro _ _ _; trivial
  constrained_preserved := by intro _ _ _; trivial
def missingEquivariance : ConstrainedSymmetry.ConstrainedDynamics system where
  step := id
  preserves_physical := by intro _ _; trivial'

expect_failure "first_class_constraint_closure_required" 'import LeanPhy
open LeanPhy
open LeanPhy.Mathematics
open LeanPhy.Classical
noncomputable def missingFirstClass :
    FirstClassConstraintAlgebra ℝ PhasePolynomial Unit where
  poisson := canonicalPolynomialPoisson
  constraint := fun _ => qPolynomial'

expect_failure "constraint_map_bracket_compatibility_required" 'import LeanPhy
open LeanPhy
open LeanPhy.Mathematics
open LeanPhy.Classical
noncomputable def sourceConstraint :
    FirstClassConstraintAlgebra ℝ PhasePolynomial Unit where
  poisson := canonicalPolynomialPoisson
  constraint := fun _ => qPolynomial
  first_class := by
    intro _ _
    simpa [qPolynomial] using canonical_q_q
noncomputable def missingConstraintMapLaw :
    FirstClassConstraintAlgebra.ConstraintMap sourceConstraint sourceConstraint where
  map := AlgHom.id ℝ PhasePolynomial
  maps_constraint := by
    intro i
    exact sourceConstraint.constraint_mem i'

expect_failure "brst_nilpotency_required" 'import LeanPhy
open LeanPhy
open LeanPhy.Mathematics
noncomputable def missingBRST : BRSTDifferential ℝ PhasePolynomial where
  differential := 0'

expect_failure "graded_brst_nilpotency_required" 'import LeanPhy
open LeanPhy.Mathematics
noncomputable def missingGradedNilpotent :
    GradedBRSTDifferential (GradedRing.parityTrivial ℤ) where
  toGradedDerivation := GradedDerivation.zero _'

expect_failure "finite_ghost_grading_certificate_required" "import LeanPhy.Entry.Gauge
open LeanPhy.Mathematics
open LeanPhy.GaugeTheory
noncomputable def missingFiniteGhostGrade :
    GradedBRSTDifferential (finiteGhostGrading (R := ℚ)) where
  toGradedDerivation := {
    differential := finiteGhostDifferential
    map_zero' := finiteGhostDifferential_zero
    map_add' := finiteGhostDifferential_add
    map_neg' := finiteGhostDifferential_neg
    leibniz' := by
      intro g h x y hx hy
      exact finiteGhost_leibniz hx hy
  }
  nilpotent := finiteGhostDifferential_sq
"

expect_failure "grassmann_derivative_sign_required" 'import LeanPhy.Entry.Gauge
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial
example : derivative 1 (generator (R := ℚ) (0 : Fin 3) * generator 1) = generator 0 := by
  exact derivative_pair 0 1 (by decide)'

expect_failure "ghost_generator_is_not_even" 'import LeanPhy.Entry.Gauge
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial
example : (grading (R := ℚ) (n := 3)).IsHomogeneous .even (generator 0) := by
  exact generator_isOdd 0'

expect_failure "koszul_exactness_requires_unit_pairing" 'import LeanPhy.Entry.Gauge
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial
example (f : Module.Dual ℚ (Fin 3 → ℚ)) (v : Fin 3 → ℚ)
    (x : GhostPolynomial ℚ 3) (hx : (koszul f).IsClosed x) : (koszul f).IsExact x := by
  exact exact_of_closed_of_pairing_one f v hx'

expect_failure "zero_constraints_do_not_make_one_exact" 'import LeanPhy.Entry.Gauge
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial
example : (koszul (0 : Module.Dual ℚ (Fin 3 → ℚ))).IsExact (1 : GhostPolynomial ℚ 3) := by
  rw [koszul_zero_exact_iff]
  norm_num'

expect_failure "quadratic_nonzero_requires_distinct_generators" 'import LeanPhy.Entry.Gauge
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial
example : quadratic (R := ℚ) (0 : Fin 3) 0 (generator 0) ≠ 0 := by
  exact quadratic_nonzero 0 0 (by decide)'

expect_failure "lie_ghost_requires_finite_certificate" 'import LeanPhy.GaugeTheory.LieGhost
open LeanPhy.Mathematics LeanPhy.GaugeTheory.GhostPolynomial
example (L : LeanPhy.Mathematics.LieAlgebra ℚ (Fin 3 → ℚ)) :
    GradedBRSTDifferential (grading (R := ℚ) (n := 3)) := lieBRST L'

expect_failure "ghost_vector_field_requires_even_images" 'import LeanPhy.GaugeTheory.LieGhost
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial
example (F : Fin 3 → GhostPolynomial ℚ 3) (x y : GhostPolynomial ℚ 3) :
    vectorField F (x * y) = vectorField F x * y + parityInvolution x * vectorField F y := by
  exact vectorField_mul F x y'

expect_failure "incompatible_ghost_images_are_not_nilpotent" 'import LeanPhy.Examples.LieGhostResearch
open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Examples.LieGhostResearch
example : ∀ x, vectorField incompatibleImages (vectorField incompatibleImages x) = 0 := by
  apply vectorField_sq_of_generators _ incompatible_even
  intro i
  fin_cases i <;> simp [incompatibleImages, c, vectorField, derivative, contract_mul,
    generator, Fin.sum_univ_succ, Pi.single_apply]'

expect_failure "sl2_ghost_wrong_ce_sign" 'import LeanPhy.Examples.LieGhostResearch
open LeanPhy.Examples.LieGhostResearch
example : LeanPhy.Generated.Sl2Ghost.brst (c 0) = c 1 * c 2 := by
  rw [sl2_images.1]
  rfl'

expect_failure "canonical_ghost_requires_jacobi" 'import LeanPhy.GaugeTheory.LieGhostFamily
open LeanPhy.Mathematics LeanPhy.GaugeTheory
def incompleteLie : LeanPhy.Mathematics.LieAlgebra ℚ (Fin 3 → ℚ) where
  bracket := LieGhostFamily.bracket 1 1
  add_left := (LieGhostFamily.algebra 1 1).add_left
  add_right := (LieGhostFamily.algebra 1 1).add_right
  smul_left := (LieGhostFamily.algebra 1 1).smul_left
  smul_right := (LieGhostFamily.algebra 1 1).smul_right
  zero_left := (LieGhostFamily.algebra 1 1).zero_left
  alternating := (LieGhostFamily.algebra 1 1).alternating
  antisymm := (LieGhostFamily.algebra 1 1).antisymm'

expect_failure "ghost_pair_closedness_requires_weight_sum" 'import LeanPhy.GaugeTheory.LieGhostFamily
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial
example : LieGhostFamily.differential (1 : ℚ) 1 (generator 1 * generator 2) = 0 := by
  rw [LieGhostFamily.pair_closed_iff]
  norm_num'

expect_failure "ghost_closedness_retains_second_parameter" 'import LeanPhy.GaugeTheory.LieGhostFamily
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial
example (a b : ℚ) (ha : a = 0) :
    LieGhostFamily.differential a b (generator 1 * generator 2) = 0 := by
  rw [LieGhostFamily.pair_closed_iff, ha]
  simp'

expect_failure "ghost_degree_two_ce_sign_required" 'import LeanPhy.GaugeTheory.LieGhostFamily
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial
example (ω : LieCochain2 (LieGhostFamily.algebra (1 : ℚ) 1)
    (trivialLieModule (LieGhostFamily.algebra (1 : ℚ) 1) : LieModule (LieGhostFamily.algebra (1 : ℚ) 1) ℚ)) :
    lieDifferential (LieGhostFamily.algebra 1 1) (ghostTwo _ ω) =
      -ghostThree _ (differential2Cochain _ ω) := by
  exact lieDifferential_ghostTwo _ ω'

expect_failure "adjoint_normalization_requires_closed_direction" 'import LeanPhy.Entry.Gauge
set_option maxSynthPendingDepth 5
noncomputable section
open LeanPhy.Generated.Sl2Adjoint
example (ω : C2) : LeanPhy.Mathematics.LieDeformation.Equivalence ω (reduction.represent (reduction.project ω)) := by
  exact normalizeDeformation ω
end'

expect_failure "affine_adjoint_rigidity_excludes_origin" 'import LeanPhy.Examples.AdjointDeformationResearch
set_option maxSynthPendingDepth 5
noncomputable section
open LeanPhy.Mathematics LeanPhy.Examples.AdjointDeformationResearch
example : Nonempty (LieDeformation.Equivalence (affineOriginDirection (K := ℚ)) 0) := by
  exact affine_all_removable 0 (by norm_num) affineOriginDirection affine_origin_closed
end'

expect_failure "heisenberg_adjoint_dimension_not_trivial_coefficients" 'import LeanPhy.Examples.AdjointDeformationResearch
set_option maxSynthPendingDepth 5
noncomputable section
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology LeanPhy.Generated
example : Module.finrank ℚ (H2 (adjointLieModule (HeisenbergAdjointParameter.algebra ![(1 : ℚ)] ⟨⟩))) = 2 := by
  rw [LeanPhy.Examples.AdjointDeformationResearch.heisenberg_dimension]
  norm_num
end'

expect_failure "heisenberg_distinct_coordinates_not_equivalent" 'import LeanPhy.Examples.AdjointDeformationResearch
set_option maxSynthPendingDepth 5
noncomputable section
open LeanPhy.Mathematics LeanPhy.Examples.AdjointDeformationResearch
example : Nonempty (LieDeformation.Equivalence (heisenbergRepresentative (1 : ℚ) one_ne_zero ![1,0,0,0,0])
    (heisenbergRepresentative (1 : ℚ) one_ne_zero 0)) := by
  rw [heisenberg_representatives_equivalent_iff]
  norm_num
end'

expect_failure "computed_generator_change_requires_equal_coordinates" 'import LeanPhy.Examples.AdjointDeformationResearch
set_option maxSynthPendingDepth 5
noncomputable section
open LeanPhy.Mathematics LeanPhy.Examples.AdjointDeformationResearch
example (a b : Fin 5 → ℚ) : LieDeformation.Equivalence (heisenbergRepresentative (1 : ℚ) one_ne_zero a)
    (heisenbergRepresentative (1 : ℚ) one_ne_zero b) := by
  exact LieDeformation.Reduction.equivalenceOfCoordinates (heisenbergReduction (1 : ℚ) one_ne_zero)
    _ _ (heisenberg_representative_closed 1 one_ne_zero a) (heisenberg_representative_closed 1 one_ne_zero b)
end'

expect_failure "sl2_arbitrary_direction_is_not_closed" 'import LeanPhy.Entry.Gauge
set_option maxSynthPendingDepth 5
noncomputable section
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology LeanPhy.Mathematics.LieCochainCoordinates
open LeanPhy.Generated.Sl2Adjoint
example : IsTwoCocycle coefficients (twoFrom ![1,0,0,0,0,0,0,0,0]) := by
  apply readThird_detect
  ext i
  fin_cases i <;> norm_num [readThird, differential2_apply, coefficients, adjointLieModule,
    algebra, bracket, twoFrom, e]
end'

expect_failure "first_order_deformation_requires_cocycle" 'import LeanPhy.Entry.Gauge
open LeanPhy.Mathematics
example {L : LeanPhy.Mathematics.LieAlgebra ℚ (Fin 3 → ℚ)} (ω : LieDeformation.Cochain L) :
    LeanPhy.Mathematics.LieAlgebra ℚ ((Fin 3 → ℚ) × (Fin 3 → ℚ)) := by
  exact LieDeformation.algebra ω'

expect_failure "second_order_deformation_requires_correction" 'import LeanPhy.Examples.LieDeformationResearch
open LeanPhy.Mathematics LeanPhy.Examples.LieDeformationResearch
example : LeanPhy.Mathematics.LieAlgebra ℚ (Space ℚ × Space ℚ × Space ℚ) := by
  exact LieDeformation.secondAlgebra (direction 1 1) 0 (every_direction_firstOrder 1 1)'

expect_failure "first_order_class_does_not_guarantee_extension" 'import LeanPhy.Examples.LieDeformationResearch
open LeanPhy.Mathematics LeanPhy.Examples.LieDeformationResearch
example : ∃ ν : LieDeformation.Cochain abelian,
    ∃ A : LeanPhy.Mathematics.LieAlgebra ℚ (Space ℚ × Space ℚ × Space ℚ),
      A.bracket = LieDeformation.secondBracket (direction 1 1) ν := by
  rw [secondOrder_exists_iff]
  norm_num'

expect_failure "nonzero_deformation_class_not_removable" 'import LeanPhy.Examples.LieDeformationResearch
open LeanPhy.Mathematics LeanPhy.Examples.LieDeformationResearch
example : Nonempty (LieDeformation.Equivalence (direction (1 : ℚ) 1) 0) := by
  rw [direction_removable_iff]
  norm_num'

expect_failure "nonzero_cochain_not_nonzero_deformation_class" 'import LeanPhy.Examples.LieDeformationResearch
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology LeanPhy.Examples.LieDeformationResearch
example : classOf (adjointLieModule affine) scalingDirection scalingDirection_closed ≠ 0 := by
  rw [scaling_class_zero]
  norm_num'

expect_failure "deformation_obstruction_preserves_legal_axis" 'import LeanPhy.Examples.LieDeformationResearch
open LeanPhy.Mathematics LeanPhy.Examples.LieDeformationResearch
example : ¬∃ ν : LieDeformation.Cochain abelian,
    ∃ A : LeanPhy.Mathematics.LieAlgebra ℚ (Space ℚ × Space ℚ × Space ℚ),
      A.bracket = LieDeformation.secondBracket (direction 0 1) ν := by
  rw [secondOrder_exists_iff]
  norm_num'

expect_failure "deformation_generator_change_sign_matters" 'import LeanPhy.Examples.LieDeformationResearch
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology LeanPhy.Examples.LieDeformationResearch
example : differential1 (adjointLieModule affine) (-LinearMap.id) = scalingDirection := by
  ext x y i
  simp [differential1, adjointLieModule, affine, scalingDirection,
    LeanPhy.Generated.DiscoveredLieDomain.algebra, LeanPhy.Generated.DiscoveredLieDomain.bracket]'

expect_failure "discovered_domain_not_all_parameters" 'import LeanPhy.Examples.ModelDomainResearch
example : LeanPhy.Generated.DiscoveredLieDomain.ModelLaws ![(1 : ℝ),0,1] := by
  rw [LeanPhy.Examples.ModelDomainResearch.laws_iff_domain]
  norm_num'

expect_failure "discovered_domain_preserves_other_factor" 'import LeanPhy.Examples.ModelDomainResearch
open LeanPhy.Examples.ModelDomainResearch
example : ∀ a b t : ℝ, LeanPhy.Generated.DiscoveredLieDomain.ModelLaws ![a,b,t] → a=0 := by
  intro a b t h
  rw [laws_iff_domain] at h
  rcases h with ha | hbt
  · exact ha
  · simp_all'

expect_failure "discovered_model_requires_domain_evidence" 'import LeanPhy.Entry.Gauge
open LeanPhy.Generated.DiscoveredLieDomain
example (p : Fin 3 → ℚ) : LeanPhy.Mathematics.LieAlgebra ℚ (Space ℚ) := by
  exact algebra p'

expect_failure "impossible_bracket_has_no_model_laws" 'import LeanPhy.Examples.ModelDomainResearch
example (p : Fin 0 → ℝ) : LeanPhy.Generated.ImpossibleLieDomain.ModelLaws p := by
  have hc := (LeanPhy.Generated.ImpossibleLieDomain.conditions_iff p).mpr ⟨⟨⟩, by constructor <;> intros <;> rfl⟩
  exact ((LeanPhy.Generated.ImpossibleLieDomain.conditions_iff p).mp hc).2'

expect_failure "discovered_vector_domain_requires_character" 'import LeanPhy.Examples.ModelDomainResearch
example : LeanPhy.Generated.DiscoveredVectorDomain.ModelLaws ![(1 : ℝ),0] := by
  rw [LeanPhy.Examples.ModelDomainResearch.vector_laws_iff]
  norm_num'

expect_failure "symbolic_lie_requires_jacobi_conditions" 'import LeanPhy.Entry.Gauge
open LeanPhy.Generated.JacobiParameters
example (p : Fin 2 → ℚ) : LeanPhy.Mathematics.LieAlgebra ℚ (Space ℚ) := by
  exact algebra p'

expect_failure "symbolic_vector_rejects_wrong_character" 'import LeanPhy.Examples.SymbolicLieResearch
example : LeanPhy.Generated.AffineVectorParameters.Conditions ![(1 : ℝ),0] := by
  rw [LeanPhy.Examples.SymbolicLieResearch.affine_domain_iff]
  norm_num'

expect_failure "symbolic_jacobi_rejects_invalid_point" 'import LeanPhy.Examples.SymbolicLieResearch
example : LeanPhy.Generated.JacobiParameters.Conditions ![(1 : ℝ),1] := by
  rw [LeanPhy.Examples.SymbolicLieResearch.jacobi_domain_iff]
  norm_num'

expect_failure "symbolic_dimension_retains_zero_bracket" 'import LeanPhy.Examples.SymbolicLieResearch
open LeanPhy.Mathematics.LieCohomology LeanPhy.Generated LeanPhy.Examples.SymbolicLieResearch
example : Module.finrank ℝ (H2 (HeisenbergParameter.coefficients ![(0 : ℝ)] (heisenbergConditions 0))) = 2 := by
  rw [heisenberg_zero]
  norm_num'

expect_failure "symbolic_boundary_requires_cocycle" 'import LeanPhy.Entry.Gauge
open LeanPhy.Mathematics.LieCohomology LeanPhy.Generated.AffineVectorParameters
example (p : Fin 2 → ℚ) (hp : Conditions p) (ω : C2 p hp) :
    IsTwoCoboundary (coefficients p hp) ω ↔ (reduction p hp).project ω = 0 := by
  exact boundary_iff p hp ω'

expect_failure "automatic_branch_requires_pivot_conditions" 'import LeanPhy.Entry.Gauge
open LeanPhy.Mathematics LeanPhy.Generated.DeterminantStrata
example (x : Fin 2 → ℚ) : MatrixCohomologyReduction (d1 x) (d2 x) 0 := by
  exact branch_4 x'

expect_failure "automatic_dimension_retains_resonance" 'import LeanPhy.Examples.AutomatedParameterResearch
open LeanPhy.Mathematics.LieCohomology LeanPhy.Mathematics.SolvableLieFamily
example : Module.finrank ℝ (H2 (coefficients (1 : ℝ) 1 1)) = 0 := by
  rw [LeanPhy.Examples.AutomatedParameterResearch.computed_double_resonance]
  norm_num'

expect_failure "automatic_exactness_requires_closedness" 'import LeanPhy.Examples.AutomatedParameterResearch
open LeanPhy.Mathematics.LieCohomology LeanPhy.Mathematics.SolvableLieFamily
open LeanPhy.Examples.AutomatedParameterResearch
example (a b t : ℚ) (ω : C2 a b t) :
    IsTwoCoboundary (coefficients a b t) ω ↔ (automaticReduction a b t).project ω = 0 := by
  exact automatic_exactness a b t ω'

expect_failure "determinant_generic_requires_both_factors" 'import LeanPhy.Examples.AutomatedParameterResearch
open LeanPhy.Examples.AutomatedParameterResearch
example (s t : ℝ) (hm : s - t ≠ 0) : Module.finrank ℝ (DeterminantCohomology s t) = 0 := by
  exact determinant_generic s t hm'

expect_failure "determinant_intersection_not_one_class" 'import LeanPhy.Examples.AutomatedParameterResearch
open LeanPhy.Examples.AutomatedParameterResearch
example : Module.finrank ℝ (DeterminantCohomology (0 : ℝ) 0) = 1 := by
  rw [determinant_intersection]
  norm_num'

expect_failure "diagonal_reduction_requires_complex_law" 'import LeanPhy.Entry.Gauge
open LeanPhy.Mathematics
example : CohomologyReduction (DiagonalCohomology.diagonal (fun _ : Fin 1 => (1 : ℚ)))
    (DiagonalCohomology.diagonal (fun _ : Fin 1 => (1 : ℚ)))
    (DiagonalCohomology.Surviving (fun _ : Fin 1 => (1 : ℚ)) (fun _ : Fin 1 => (1 : ℚ)) → ℚ) :=
  DiagonalCohomology.reduction _ _ (by intro i; norm_num)'

expect_failure "generic_dimension_requires_nonresonance" 'import LeanPhy.Entry.Gauge
open LeanPhy.Mathematics.LieCohomology LeanPhy.Mathematics.SolvableLieFamily
example (a b t : ℚ) : Module.finrank ℚ (H2 (coefficients a b t)) = 0 := by
  exact generic_h2_zero a b t'

expect_failure "coincident_resonances_count_separately" 'import LeanPhy.Examples.ParameterCohomologyResearch
open LeanPhy.Mathematics.LieCohomology LeanPhy.Mathematics.SolvableLieFamily
example : Module.finrank ℝ (H2 (coefficients (1 : ℝ) 1 1)) = 1 := by
  rw [LeanPhy.Examples.ParameterCohomologyResearch.double_resonance]
  norm_num'

expect_failure "unit_cochain_not_always_closed" 'import LeanPhy.Entry.Gauge
open LeanPhy.Mathematics.LieCohomology LeanPhy.Mathematics.SolvableLieFamily
example : IsTwoCocycle (coefficients (1 : ℚ) 1 0) (unit12 1 1 0) := by
  rw [unit12_closed_iff]
  norm_num'

expect_failure "stratum_transport_requires_pattern" 'import LeanPhy.Entry.Gauge
open LeanPhy.Mathematics.LieCohomology LeanPhy.Mathematics.SolvableLieFamily
example : H2 (coefficients (1 : ℚ) 1 0) ≃ₗ[ℚ] H2 (coefficients (1 : ℚ) 1 1) := by
  exact stratumEquiv 1 1 0 1 1 1'

expect_failure "generated_vector_boundary_requires_cocycle" 'import LeanPhy.Examples.Generated.SolvableVector
open LeanPhy.Mathematics.LieCohomology LeanPhy.Generated.SolvableVector
set_option maxSynthPendingDepth 5
example (ω : C2) : IsTwoCoboundary coefficients ω ↔ reduction.project ω = 0 := by
  exact boundary_iff ω'

expect_failure "coefficient_actions_not_interchangeable" 'import LeanPhy.Examples.StructureConstantResearch
open LeanPhy.Mathematics.LieCohomology LeanPhy.Examples.StructureConstantResearch
example : Module.finrank ℚ (H2 LeanPhy.Generated.AffineCharacter.coefficients) = 0 := by
  rw [affine_character_dimension]
  norm_num'

expect_failure "zero_coordinates_do_not_prove_closedness" 'import LeanPhy.Examples.StructureConstantResearch
open LeanPhy.Mathematics.LieCohomology LeanPhy.Examples.StructureConstantResearch
example : IsTwoCocycle LeanPhy.Generated.SolvableVector.coefficients nonclosed := by
  unfold IsTwoCocycle
  exact nonclosed_zero_coordinates'

expect_failure "increasing_triples_need_all_values" 'import LeanPhy.Entry.Gauge
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
example (L : LeanPhy.Mathematics.LieAlgebra ℚ (Fin 3 → ℚ))
    (𝒨 : LeanPhy.Mathematics.LieModule L ℚ) (ω : LieCochain2 L 𝒨) : IsTwoCocycle 𝒨 ω := by
  exact LieCochainCoordinates.differential2_eq_zero_of_increasing 𝒨 ω'

expect_failure "reduction_requires_completeness" 'import LeanPhy.Entry.Gauge
open LeanPhy.Mathematics
example : CohomologyReduction (0 : ℚ →ₗ[ℚ] ℚ) (0 : ℚ →ₗ[ℚ] ℚ) ℚ :=
  { project := LinearMap.id, represent := LinearMap.id, primitive := 0, correction := 0,
    chain := by simp, closed := by simp, boundary := by simp, retract := by simp }'

expect_failure "reduction_exactness_requires_closedness" 'import LeanPhy.Entry.Gauge
open LeanPhy.Mathematics
example (d₁ d₂ : ℚ →ₗ[ℚ] ℚ) (S : CohomologyReduction d₁ d₂ ℚ) (b : ℚ)
    (hb : S.project b = 0) : ∃ a, d₁ a = b := by
  exact (S.exact_iff b (by exact hb)).mpr hb'

expect_failure "heisenberg_h2_is_not_one_dimensional" 'import LeanPhy.Examples.HeisenbergCohomology
open LeanPhy.Mathematics.LieCohomology LeanPhy.Examples.HeisenbergCohomology
example : Module.finrank ℚ (H2 coefficients) = 1 := by
  rw [h2_finrank]
  norm_num'

expect_failure "nonzero_heisenberg_parameter_not_boundary" 'import LeanPhy.Examples.HeisenbergCohomology
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Examples.HeisenbergCohomology
example : IsTwoCoboundary coefficients
    (LieCochainCoordinates.twoOfComponents (![0, 1, 0] : Space)) := by
  rw [boundary_iff]
  norm_num [LieCochainCoordinates.twoOfComponents, LieCochainCoordinates.e]'

expect_failure "h2_class_requires_cocycle" 'import LeanPhy.Entry.Gauge
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
example (L : LeanPhy.Mathematics.LieAlgebra ℚ ℚ) (𝒨 : LeanPhy.Mathematics.LieModule L ℚ)
    (ω : LieCochain2 L 𝒨) : H2 𝒨 := classOf 𝒨 ω'

expect_failure "central_extension_requires_cocycle" 'import LeanPhy.Entry.Gauge
open LeanPhy.Mathematics
example (L : LeanPhy.Mathematics.LieAlgebra ℚ ℚ)
    (ω : LieCochain2 L (trivialLieModule L : LeanPhy.Mathematics.LieModule L ℚ)) :
    LeanPhy.Mathematics.LieAlgebra ℚ (ℚ × ℚ) := CentralExtension.algebra ω'

expect_failure "extension_equivalence_requires_bracket_preservation" 'import LeanPhy.Entry.Gauge
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
example (L : LeanPhy.Mathematics.LieAlgebra ℚ ℚ)
    (ω η : LieCochain2 L (trivialLieModule L : LeanPhy.Mathematics.LieModule L ℚ))
    (hω : IsTwoCocycle (trivialLieModule L) ω) (hη : IsTwoCocycle (trivialLieModule L) η) :
    CentralExtension.Equivalence ω η :=
  { source_cocycle := hω, target_cocycle := hη,
    linearEquiv := LinearEquiv.refl ℚ (ℚ × ℚ),
    map_projection := by intro x; rfl,
    map_inclusion := by intro m; rfl }'

expect_failure "heisenberg_cocycle_is_not_a_boundary" 'import LeanPhy.Examples.LieCohomologyResearch
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.Examples.LieCohomologyResearch
example : classOf (trivialLieModule abelianPlane) areaCocycle area_closed = 0 := by
  apply (classOf_eq_zero_iff _ _ _).mpr
  exact area_closed'

expect_failure "nonzero_cochain_does_not_imply_nonzero_class" 'import LeanPhy.Examples.LieCohomologyResearch
open LeanPhy.Mathematics.LieCohomology LeanPhy.Examples.LieCohomologyResearch
example : classOf affineCoefficients affineBoundary affineBoundary_closed ≠ 0 := by
  intro h
  exact affineBoundary_nonzero h'

expect_failure "lie_module_representation_required" "import LeanPhy.Entry.Gauge
open LeanPhy.Mathematics
def missingLieModule (L : LieAlgebra ℝ ℝ) : LieModule L ℝ where
  act := fun _ _ => 0
  act_add_left' := by intro; simp
  act_smul_left' := by intro; simp
  act_add_right' := by intro; simp
  act_smul_right' := by intro; simp"

expect_failure "equivariant_constraint_zero_fixed_required" 'import LeanPhy.Minimal
open LeanPhy.Mathematics
instance : SMul Unit Nat := ⟨fun _ n => n⟩
instance : MulAction Unit Nat where
  one_smul := by intro n; rfl
  mul_smul := by intro _ _ n; rfl
def missingZeroFixed : EquivariantConstraint Unit Nat Nat where
  value := fun n => n
  equivariant := by intro _ n; rfl'

expect_failure "constrained_observable_invariance_required" 'import LeanPhy.Minimal
open LeanPhy.Mathematics
instance : SMul Unit Nat := ⟨fun _ n => n⟩
instance : MulAction Unit Nat where
  one_smul := by intro n; rfl
  mul_smul := by intro _ _ n; rfl
def system : ConstrainedSymmetry Unit Nat where
  admissible := fun _ => True
  constrained := fun _ => True
  admissible_preserved := by intro _ _ _; trivial
  constrained_preserved := by intro _ _ _; trivial
def missingInvariant : ConstrainedSymmetry.ConstrainedObservable system Nat where
  eval := id'

expect_failure "model_map_dynamics_proof_required" 'import LeanPhy.Minimal
open LeanPhy.Mathematics
def idStep : Process Nat (fun _ => True) where
  toFun := id
  preserves := by intro _ _; trivial
def succStep : Process Nat (fun _ => True) where
  toFun := Nat.succ
  preserves := by intro _ _; trivial
def source : PhysicalModel Nat where
  State := Nat
  valid := fun _ => True
  step := idStep
  Observable := Unit
  evaluate := fun n _ => n
def target : PhysicalModel Nat where
  State := Nat
  valid := fun _ => True
  step := succStep
  Observable := Unit
  evaluate := fun n _ => n
def bad : ModelMap source target where
  state := StateMap.identity Nat (fun _ => True)
  pullback := id
  step_commutes := by intro n _; rfl
  evaluate_commutes := by intro n _ o; rfl'

expect_failure "registered_local_dependency_required" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def detached : CheckedClaim :=
  { name := "detached", statement := "True", source := "test", requiredAssumptions := [],
    dependencies := [], proposition := True, proof := True.intro }
def invalidRegisteredStep : TheoryPackage :=
  TheoryPackage.empty "invalid" "test"
    |>.addDerivedTheoremRegistered detached (by simp)
      "derived" "detached predecessor" "test" [] (fun h : True => h)'

expect_failure "registered_model_reference_required" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def package : TheoryPackage :=
  TheoryPackage.empty "model" "test" |>.addModelText
    "known" "finite" "P" "S" "O" "step" []
def invalidModelReference : TheoryPackage :=
  package.addTheoremForModelRegistered "missing" (by simp [package])
    "claim" "the model must be registered" "test" [] True.intro'

expect_failure "registered_model_assumption_required" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def package : TheoryPackage :=
  TheoryPackage.empty "model" "test"
    |>.addAssumptionText "known" "known premise" "test"
def invalidModel : TheoryPackage :=
  package.addModelTextRegistered "model" "finite" "P" "S" "O" "step"
    ["missing"] (by simp [package])'

expect_failure "assumption_witness_proof_required" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def witness : AssumptionWitness :=
  { metadata := { name := "model", statement := "model premise", source := "test" },
    proposition := True, proof := True.intro }
def invalidWitnessStep : TheoryPackage :=
  TheoryPackage.empty "invalid" "test"
    |>.addAssumptionWitness witness
    |>.addTheoremUnderAssumption witness "claim" "claim" "test"
      (fun h : False => h)'

expect_failure "obligation_reference_out_of_range" 'import LeanPhy.Workflow.Core
open LeanPhy.Workflow
def package := TheoryPackage.empty "empty" "test"
def invalidReference : ObligationRef package := ⟨⟨0, by decide⟩⟩'

expect_failure "external_certificate_proof_required" 'import LeanPhy.Mathematics.ExternalCertificate
open LeanPhy.Mathematics
def checker : CertificateChecker True String :=
  { check := fun _ => True, sound := fun _ => True.intro }
def envelope : CertificateEnvelope String :=
  { metadata := { producer := "test", format := "raw", digest := "x", source := "test" },
    payload := "untrusted" }
def invalidCertificate : VerifiedCertificate checker :=
  { envelope := envelope }'

expect_failure "typed_obligation_proof_required" 'import LeanPhy.Workflow.Core
open LeanPhy.Workflow
def obligation : ExternalObligationWitness :=
  { metadata := { name := "bridge", statement := "target", source := "test" }, proposition := False }
def base := TheoryPackage.empty "model" "test"
def package := base.addObligationWitness obligation
def invalidResolution := package.resolveObligation (base.addedObligationRef obligation)
  "closed" "target" "test" [] [] True.intro'

expect_failure "cross_package_dependency_missing" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def badClaim : CheckedClaim :=
  { name := "consumer", statement := "bad link", source := "test",
    requiredAssumptions := [], dependencies := [ResearchProject.qualifiedDependency "missing" "claim"],
    proposition := True, proof := True.intro }
def badPackage : TheoryPackage := TheoryPackage.empty "consumer" "test" |>.addClaim badClaim
def badProject : ResearchProject := ResearchProject.ofPackages "bad" [badPackage]
example : badProject.hasErrors = false := by native_decide'

expect_failure "cross_package_proof_missing_source" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def prior : CheckedClaim :=
  { name := "prior", statement := "True", source := "test",
    requiredAssumptions := [], dependencies := [], proposition := True, proof := True.intro }
def target : TheoryPackage := TheoryPackage.empty "target" "test"
def badDerived : ResearchProject :=
  ResearchProject.addDerivedTheorem (ResearchProject.empty "bad" "test")
    "missing" prior target "derived" "bad source" "test" [] (fun h => h)
example : badDerived.hasErrors = false := by native_decide'

expect_failure "qualified_forward_dependency" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def first : CheckedClaim :=
  { name := "first", statement := "True", source := "test",
    requiredAssumptions := [],
    dependencies := [ResearchProject.qualifiedDependency "pkg" "second"],
    proposition := True, proof := True.intro }
def second : CheckedClaim :=
  { name := "second", statement := "True", source := "test",
    requiredAssumptions := [], dependencies := [], proposition := True,
    proof := True.intro }
def pkg : TheoryPackage :=
  TheoryPackage.empty "pkg" "test" |>.addClaim first |>.addClaim second
def badOrder : ResearchProject := ResearchProject.ofPackages "bad" [pkg]
example : badOrder.hasErrors = false := by native_decide'

expect_failure "duplicate_project_package" 'import LeanPhy.Workflow
open LeanPhy.Workflow
def p : TheoryPackage := TheoryPackage.empty "same" "test"
def duplicate : ResearchProject := ResearchProject.ofPackages "bad" [p, p]
example : duplicate.hasErrors = false := by native_decide'

expect_failure "variance_mismatch" 'import LeanPhy
open LeanPhy.Tensor
example {n : Nat} (T : Tensor3N n .up .up .down) : Tensor1N n .down :=
  contract12 T'

expect_failure "fourier_dimension_mismatch" 'import LeanPhy
open LeanPhy.Mathematics
example (x : Fin 2 → ℂ) : Fin 4 → ℂ :=
  FiniteFourierSystem.fourier4.forward x'

expect_failure "unitary_invariant_required" 'import LeanPhy
open LeanPhy.Quantum
example {n : Nat} (A : Operator n) : UnitaryOperator n :=
  { op := A, unitary := rfl }'

expect_failure "second_moment_scalar_mismatch" 'import LeanPhy
open LeanPhy.StatMech
example (p : FiniteDistribution 2) (f : Fin 2 → ℂ) : ℝ :=
  p.secondMoment f'

expect_failure "diagonal_state_observable_dimension_mismatch" 'import LeanPhy
open LeanPhy.Quantum
open LeanPhy.StatMech
example (p : FiniteDistribution 2) (f : Fin 3 → ℝ) : ℂ :=
  expectation (diagonalState p) (diagonalObservable f)'

expect_failure "finite_kernel_label_mismatch" 'import LeanPhy
open LeanPhy.StatMech
example {ι κ : Type} [Fintype ι] [Fintype κ]
    (K : FiniteKernel ι) (p : FiniteProbability κ) : FiniteProbability ι :=
  K.step p'

expect_failure "named_channel_completeness_required" 'import LeanPhy
open LeanPhy.Quantum
example {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
  (K : κ → NamedState ι) : NamedFiniteChannel ι :=
  namedChannelFromKraus K'

expect_failure "conductance_symmetry_required" 'import LeanPhy
open LeanPhy.StatMech
example {ι : Type} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (c : ι → ι → ℝ) (wp : ∀ i, 0 < w i)
    (cn : ∀ i j, 0 ≤ c i j) (rs : ∀ i, ∑ j, c i j = w i) :
    ConductanceModel ι :=
  { weight := w, conductance := c, weight_pos := wp,
    conductance_nonneg := cn, row_sum := rs }'

expect_failure "conductance_positive_weights_required" 'import LeanPhy
open LeanPhy.StatMech
example {ι : Type} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (c : ι → ι → ℝ) (cn : ∀ i j, 0 ≤ c i j)
    (sy : ∀ i j, c i j = c j i) (rs : ∀ i, ∑ j, c i j = w i) :
    ConductanceModel ι :=
  { weight := w, conductance := c, conductance_nonneg := cn,
    symmetric := sy, row_sum := rs }'

expect_failure "conductance_row_normalization_required" 'import LeanPhy
open LeanPhy.StatMech
example {ι : Type} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (c : ι → ι → ℝ) (wp : ∀ i, 0 < w i)
    (cn : ∀ i j, 0 ≤ c i j) (sy : ∀ i j, c i j = c j i) :
    ConductanceModel ι :=
  { weight := w, conductance := c, weight_pos := wp,
    conductance_nonneg := cn, symmetric := sy }'

expect_failure "dirichlet_requires_normalized_kernel" 'import LeanPhy
open LeanPhy.StatMech
example {ι : Type} [Fintype ι] (p : FiniteProbability ι)
    (transition : ι → ι → ℝ) (nonneg : ∀ i j, 0 ≤ transition i j)
    (f : ι → ℝ) :
    0 ≤ FiniteKernel.dirichletForm
      { transition := transition, nonneg := nonneg } p f f := by
  exact FiniteKernel.dirichletForm_nonneg _ p f'

expect_failure "dirichlet_laplacian_requires_detailed_balance" 'import LeanPhy
open LeanPhy.StatMech
example {ι : Type} [Fintype ι] (K : FiniteKernel ι)
    (p : FiniteProbability ι) (f g : ι → ℝ) :
    K.dirichletForm p f g =
      p.expectation (fun i => f i * K.laplacian g i) := by
  exact K.dirichletForm_eq_laplacian_pairing p f g'

expect_failure "response_commutation_certificate_required" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] [DecidableEq ι]
    (rho A B : Matrix ι ι ℂ) :
    commutatorResponse rho A B = 0 :=
  commutatorResponse_eq_zero_of_commute rho A B'

expect_failure "hamiltonian_hermitian_required" 'import LeanPhy
open LeanPhy.Quantum
example {n : Nat} (H : Operator n) : FiniteUnitary (Fin n) :=
  finiteHamiltonianFlow H rfl 1'

expect_failure "flow_invariant_commutation_required" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] [DecidableEq ι]
    (A O : Matrix ι ι ℂ) :
    (FiniteMatrixFlow.exponential A).IsInvariant O :=
  FiniteMatrixFlow.exponential_isInvariant_of_commute A O'

expect_failure "typed_channel_completeness_required" 'import LeanPhy
open LeanPhy.QuantumInfo
example (K : PUnit → Matrix (Fin 2) (Fin 1) ℂ) :
    TypedKrausChannel (Fin 1) (Fin 2) PUnit :=
  { op := K }'

expect_failure "typed_channel_label_mismatch" 'import LeanPhy
open LeanPhy.QuantumInfo
example (K : PUnit → Matrix (Fin 2) (Fin 1) ℂ) (rho : Matrix (Fin 1) (Fin 1) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  typedApplyKraus K rho'

expect_failure "path_endpoint_mismatch" 'import LeanPhy
open LeanPhy.Mathematics
example {V : Type} {x y z : V} (p : FinitePath V x y) (q : FinitePath V z z) :
    FinitePath V x z :=
  FinitePath.comp p q'

expect_failure "approximation_without_bound" 'import LeanPhy
open LeanPhy.Mathematics
example (x y : ℝ) : ErrorCertificate x y 0 :=
  ErrorCertificate.of_eq rfl'

expect_failure "cross_space_approximation_requires_decoder" 'import LeanPhy
open LeanPhy.Mathematics
example (x : ℝ) (y : Fin 2 → ℝ) : FiniteApproximation x y 0 := by
  exact ⟨ErrorCertificate.of_eq rfl⟩'

expect_failure "winding_without_integer_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {V : Type} [Fintype V] (link : V → ℤ) (step : Equiv.Perm V) :
    DiscreteCochain.WindingCertificate link step 0 :=
  ⟨rfl⟩'

expect_failure "plaquette_orientation_without_antisymmetry" 'import LeanPhy
open LeanPhy.Mathematics
example {V : Type} (α : V → V → ℤ) (x y z w : V) :
    Plaquette.flux α w z y x = -Plaquette.flux α x y z w := by
  exact Plaquette.flux_reverse α (fun _ _ => by rfl) x y z w'

expect_failure "step_residual_without_equation" 'import LeanPhy
open LeanPhy.Mathematics
example (x y : ℝ) : StepResidual x y 0 :=
  stepResidual_of_eq x y rfl'

expect_failure "hilbert_unitary_right_inverse_required" 'import LeanPhy
open LeanPhy.Mathematics
example (U : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :
    Hilbert.Unitary (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin 2)) :=
  { op := U, left_unitary := rfl }'

expect_failure "fermionic_wick_without_antisymmetry" 'import LeanPhy
open LeanPhy.FieldTheory
example {I A : Type} [CommRing A] (C : I → I → A)
    (i j k l : I) :
    FermionicWick.fourPoint C j i k l =
      -FermionicWick.fourPoint C i j k l := by
  exact FermionicWick.fourPoint_swap12 C (fun _ _ => by rfl) i j k l'

expect_failure "finite_divergence_without_local_equation" 'import LeanPhy
open LeanPhy.Mathematics
example {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (current : E → ℤ) (source : V → ℤ) :
    FiniteDivergence.ConservationCertificate tail head current source :=
  ⟨fun _ => rfl⟩'

expect_failure "markov_current_without_divergence_proof" 'import LeanPhy
open LeanPhy.StatMech
example {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : FiniteKernel ι) (p : FiniteProbability ι) :
    MarkovCurrentConservation K p :=
  ⟨fun _ => rfl⟩'

expect_failure "conservation_residual_without_bound" 'import LeanPhy
open LeanPhy.Mathematics
example {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (current : V → ℝ) (source radius : V → ℝ) :
    FiniteDivergence.ConservationError tail head (fun _ => 0) source radius :=
  ⟨fun _ => by positivity, fun _ => by rfl⟩'

expect_failure "representation_homomorphism_without_proof" 'import LeanPhy
open LeanPhy.Mathematics
example {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι]
    (R : FiniteMatrixRepresentation G ι) (g h : G) :
    R.rep (g * h) = R.rep g * R.rep h := by
  rfl'

expect_failure "unitary_representation_without_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    (R : FiniteMatrixRepresentation G ι) :
    UnitaryMatrixRepresentation G ι :=
  { toFiniteMatrixRepresentation := R, unitary := fun _ => rfl }'

expect_failure "chain_complex_boundary_certificate_required" 'import LeanPhy
open LeanPhy.Mathematics
example : FiniteChainComplex PUnit PUnit PUnit ℤ :=
  { boundary10 := fun _ _ => 0, boundary21 := fun _ _ => 0 }'

expect_failure "chain_cycle_hypothesis_required" 'import LeanPhy
open LeanPhy.Mathematics
example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (phi : C0 → A) (c : C1 → A) :
    FiniteChainComplex.pairing (K.coboundary0 phi) c = 0 :=
  K.exact_pairing_zero phi c'

expect_failure "chain_complex_coefficient_ring_required" 'import LeanPhy
open LeanPhy.Mathematics
example : FiniteChainComplex PUnit PUnit PUnit Nat :=
  { boundary10 := fun _ _ => 0, boundary21 := fun _ _ => 0,
    boundary_sq := by simp }'

expect_failure "graph_chain_coefficient_ring_required" 'import LeanPhy
open LeanPhy.Mathematics
example : FiniteChainAdapters.graphChainComplex (A := Nat)
    (fun _ : PUnit => PUnit.unit) (fun _ : PUnit => PUnit.unit) := by
  exact FiniteChainAdapters.graphChainComplex _ _'

expect_failure "cocycle_pairing_without_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (alpha : C1 → A) (b : C2 → A) :
    FiniteChainComplex.pairing alpha (K.boundary2 b) = 0 :=
  K.cocycle_pairing_boundary_zero alpha b'

expect_failure "exact_cycle_pairing_without_cycle" 'import LeanPhy
open LeanPhy.Mathematics
example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (phi : C0 → A) (c : C1 → A) :
    FiniteChainComplex.pairing (K.coboundary0 phi) c = 0 :=
  K.exact_pairing_cycle_zero phi c'

expect_failure "detailed_balance_stationarity_without_certificate" 'import LeanPhy
open LeanPhy.StatMech
example {ι : Type} [Fintype ι]
    (K : FiniteKernel ι) (p : FiniteProbability ι) : K.step p = p :=
  K.step_eq_of_detailedBalance p'

expect_failure "closed_surface_certificate_required" 'import LeanPhy
open LeanPhy.Mathematics
example {C0 C1 C2 A : Type} [Fintype C0] [Fintype C1] [Fintype C2]
    [CommRing A] (K : FiniteChainComplex C0 C1 C2 A)
    (alpha : C1 → A) (surface : C2 → A) :
    FiniteChainComplex.pairing (K.coboundary1 alpha) surface = 0 :=
  K.coboundary1_pairing_cycle2_zero alpha surface'

expect_failure "finite_path_partition_certificate_required" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (w : ι → ℂ) : FinitePathIntegral ι :=
  { weight := w }'

expect_failure "finite_rg_insertion_identity_required" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ) (O : κ → ℂ) :
    ∑ y, R.coarseWeight y * O y =
      ∑ x, R.fineWeight x * O x :=
  R.insertion_preserved O'

expect_failure "finite_pde_solution_certificate_required" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FiniteLinearPDE ι) (u : ι → ℝ) :
    EquationResidual (fun v => P.residual v) u 0 :=
  P.residual_zero u rfl'

expect_failure "finite_gradient_incidence_sum_required" 'import LeanPhy
open LeanPhy.Mathematics
example {V E : Type} [Fintype V] [Fintype E]
    (incidence : E → V → ℝ) : FiniteGradient V E :=
  { incidence := incidence }'

expect_failure "finite_rg_expectation_without_partition_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ) (O : κ → ℂ) :
    (R.coarsePathIntegral (by assumption)).expectation O =
      (R.finePathIntegral (by assumption)).expectation (fun x => O (R.coarse x)) := by
  exact R.expectation_preserved (by assumption) O'

expect_failure "finite_pde_uniqueness_without_coercivity" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FiniteLinearPDE ι)
    {u v : ι → ℝ} (hu : P.IsSolution u) (hv : P.IsSolution v) : u = v :=
  P.solution_unique_of_coercive (by assumption) hu hv'

expect_failure "finite_action_partition_certificate_required" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (S : ι → ℂ) :
    FinitePathIntegral.fromAction S (by assumption) := by
  exact FinitePathIntegral.fromAction S (by assumption)'

expect_failure "finite_expectation_error_without_denominator_bound" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P Q : FinitePathIntegral ι) (O : ι → ℂ)
    (hI : ErrorCertificate (P.insertion O) (Q.insertion O) 0)
    (hP : ErrorCertificate P.partition Q.partition 0) :
    FinitePathIntegral.ApproximationCertificate P Q O :=
  { insertionRadius := 0, partitionRadius := 0,
    insertion_nonneg := by positivity, partition_nonneg := by positivity,
    insertion_error := hI, partition_error := hP,
    exactLower := 0, approximateLower := 0,
    insertionUpper := 0, insertionUpper_nonneg := by positivity,
    approximate_insertion_upper := by positivity }'

expect_failure "finite_pointwise_error_without_nonnegativity" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P Q : FinitePathIntegral ι)
    (radius : ι → ℝ)
    (h : ∀ i, ErrorCertificate (P.weight i) (Q.weight i) (radius i)) :
    ErrorCertificate P.partition Q.partition (∑ i, radius i) :=
  FinitePathIntegral.ApproximationCertificate.partition_error_of_pointwise
    P Q radius (fun _ => by assumption) h'

expect_failure "observable_error_without_partition_lower_bound" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FinitePathIntegral ι)
    (O O2 : ι → ℂ)
    (C : FinitePathIntegral.ObservableApproximationCertificate O O2)
    (lower : ℝ) :
    ErrorCertificate (P.expectation O) (P.expectation O2)
      ((∑ i, ‖P.weight i‖ * C.radius i) / lower) :=
  C.expectation_error P O O2 lower (by assumption) (by assumption)'

expect_failure "rg_coarse_approximation_requires_denominator_bounds" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (Q : FinitePathIntegral κ) (O : κ → ℂ)
    (radius : κ → ℝ) (hr : ∀ y, 0 ≤ radius y)
    (hw : ∀ y, ErrorCertificate (R.coarseWeight y) (Q.weight y) (radius y))
    (insertionUpper : ℝ) (hinsertionUpper_nonneg : 0 ≤ insertionUpper)
    (hinsertion_upper : ‖Q.insertion O‖ ≤ insertionUpper) :
    FinitePathIntegral.ApproximationCertificate
      (R.coarsePathIntegral h) Q O :=
  FinitePathIntegral.FiniteRGStep.coarse_approximation_certificate
    R h Q O radius hr hw 1 1 (by positivity) (by positivity)
      (by assumption) (by assumption) insertionUpper hinsertionUpper_nonneg
      hinsertion_upper'

expect_failure "rg_coarse_approximation_requires_insertion_upper_bound" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (Q : FinitePathIntegral κ) (O : κ → ℂ)
    (radius : κ → ℝ) (hr : ∀ y, 0 ≤ radius y)
    (hw : ∀ y, ErrorCertificate (R.coarseWeight y) (Q.weight y) (radius y))
    (exactLower approximateLower : ℝ)
    (hexact_pos : 0 < exactLower) (happrox_pos : 0 < approximateLower)
    (hexact_lower : exactLower ≤ ‖(R.coarsePathIntegral h).partition‖)
    (happrox_lower : approximateLower ≤ ‖Q.partition‖) :
    FinitePathIntegral.ApproximationCertificate
      (R.coarsePathIntegral h) Q O :=
  FinitePathIntegral.FiniteRGStep.coarse_approximation_certificate
    R h Q O radius hr hw exactLower approximateLower hexact_pos happrox_pos
      hexact_lower happrox_lower 0 (by positivity) (by assumption)'

expect_failure "finite_boundary_uniqueness_without_coercivity" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FiniteLinearPDE ι)
    (B : FiniteBoundaryData ι) {u v : ι → ℝ}
    (hu : P.IsSolution u) (hv : P.IsSolution v)
    (huB : SatisfiesBoundary B u) (hvB : SatisfiesBoundary B v) : u = v :=
  P.solution_unique_of_boundary_coercive B (by assumption) hu hv huB hvB'

expect_failure "structured_pde_certificate_requires_residual" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FiniteEllipticProblem ι) (u : ι → ℝ)
    (hB : SatisfiesBoundary P.boundary u) : FiniteEllipticCertificate P u :=
  { residualRadius := 0, residual_nonneg := by positivity, boundary := hB }'

expect_failure "finite_pde_left_inverse_requires_left_inverse" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FiniteLinearPDE ι)
    (B : FiniteBoundaryData ι) (solve : (ι → ℝ) → (ι → ℝ)) :
    FinitePDELeftInverseCertificate P B :=
  { solve := solve, modulus := 0, modulus_nonneg := by positivity,
    lipschitz := by intro r s; positivity }'

expect_failure "finite_pde_left_inverse_requires_lipschitz" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FiniteLinearPDE ι)
    (B : FiniteBoundaryData ι) (solve : (ι → ℝ) → (ι → ℝ))
    (hleft : ∀ w, SatisfiesHomogeneousBoundary B w →
      solve (P.operator.mulVec w) = w) :
    FinitePDELeftInverseCertificate P B :=
  { solve := solve, modulus := 0, modulus_nonneg := by positivity,
    left_inverse := hleft }'

expect_failure "additive_left_inverse_requires_left_inverse" 'import LeanPhy
open LeanPhy.Mathematics
example {X Y : Type} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] (A : X →+ Y)
    (solve : Y → X) : AdditiveLeftInverseCertificate A :=
  { solve := solve, modulus := 0, modulus_nonneg := by positivity,
    lipschitz := by intro r s; positivity }'

expect_failure "additive_left_inverse_requires_lipschitz" 'import LeanPhy
open LeanPhy.Mathematics
example {X Y : Type} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] (A : X →+ Y)
    (solve : Y → X)
    (hleft : ∀ x, solve (A x) = x) :
    AdditiveLeftInverseCertificate A :=
  { solve := solve, modulus := 0, modulus_nonneg := by positivity,
    left_inverse := hleft }'

expect_failure "finite_boundary_error_requires_bound" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (B : FiniteBoundaryData ι)
    (u : ι → ℝ) : FiniteBoundaryResidualCertificate B u :=
  { radius := fun _ => 0, radius_nonneg := by intro i; positivity }'

expect_failure "joint_pde_certificate_requires_boundary_error" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P : FiniteEllipticProblem ι)
    (u : ι → ℝ) (h : P.IsSolution u) :
    FiniteEllipticApproximationCertificate P u :=
  { residualRadius := 0, residual_nonneg := by positivity,
    residual := P.equation.residual_zero u h.1 }'

expect_failure "joint_pde_zero_requires_boundary_zero" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    {P : FiniteEllipticProblem ι} {u : ι → ℝ}
    (C : FiniteEllipticApproximationCertificate P u)
    (hres : C.residualRadius = 0) : P.IsSolution u :=
  C.isSolution_of_zero hres (by assumption)'

expect_failure "finite_rg_fixed_point_without_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (h : (∑ y, R.fineWeight y) ≠ 0) (O : ι → ℂ) :
    (R.coarsePathIntegral h).expectation O =
      (R.finePathIntegral h).expectation O := by
  exact R.fixedPoint_expectation h (by assumption) O'

expect_failure "finite_rg_scaling_without_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (fineObs : ι → ℂ) (coarseObs : κ → ℂ) (lambda : ℂ) :
    (R.finePathIntegral h).expectation fineObs =
      lambda * (R.coarsePathIntegral h).expectation coarseObs := by
  exact R.expectation_scales h fineObs coarseObs lambda (by assumption)'

expect_failure "boundary_stability_requires_total_bound" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (P : FiniteEllipticProblem ι) :
    FiniteEllipticResidualStability P :=
  { equationModulus := 1, boundaryModulus := 1,
    equationModulus_nonneg := by positivity,
    boundaryModulus_nonneg := by positivity }'

expect_failure "normalized_expectation_requires_error" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (P Q : FinitePathIntegral ι)
    (O : ι → ℂ) :
    FinitePathIntegral.NormalizedExpectationCertificate P Q O :=
  { radius := 0, radius_nonneg := by positivity }'

expect_failure "real_action_lower_bound_requires_nonempty" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (S : ι → ℝ) (i₀ : ι) :
    Real.exp (-S i₀) ≤ ‖(FinitePathIntegral.fromRealAction S).partition‖ :=
  FinitePathIntegral.fromRealAction_partition_lower_bound S i₀'

expect_failure "cross_space_comparison_requires_error" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ : Type} [Fintype ι] [Fintype κ]
    (P : FinitePathIntegral ι) (Q : FinitePathIntegral κ)
    (O : ι → ℂ) (O2 : κ → ℂ) :
    FinitePathIntegral.ExpectationComparisonCertificate P Q O O2 :=
  { radius := 0, radius_nonneg := by positivity }'

expect_failure "cross_space_rg_requires_partition_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ τ : Type} [Fintype ι] [Fintype κ] [Fintype τ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (next : κ → τ) (O : τ → ℂ) :
  ((R.coarsen next).coarsePathIntegral (by assumption)).expectation O =
      (R.finePathIntegral (by assumption)).expectation
        (fun x => O (next (R.coarse x))) :=
  R.coarsen_expectation_preserved next (by assumption) O'

expect_failure "finite_evolution_requires_lipschitz" 'import LeanPhy
open LeanPhy.Mathematics
example {X : Type} [PseudoMetricSpace X] (f : X → X) :
    FiniteEvolutionStep X :=
  { step := f, modulus := 1, modulus_nonneg := by positivity }'

expect_failure "trajectory_requires_step_residual" 'import LeanPhy
open LeanPhy.Mathematics
example {X : Type} [PseudoMetricSpace X]
    (S : FiniteEvolutionStep X) (exact approximate : ℕ → X)
    (hExact : ∀ n, exact (n + 1) = S.step (exact n)) :
    S.TrajectoryCertificate exact approximate 0 (fun _ => 0) :=
  { initial_nonneg := by positivity,
    step_nonneg := by intro n; positivity,
    initial := ErrorCertificate.of_eq rfl,
    exact_step := hExact }'

expect_failure "connected_factorization_requires_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι) (O Q : ι → ℂ) :
    P.connectedCorrelator O Q = 0 :=
  P.connectedCorrelator_eq_zero_of_factorizes O Q (by assumption)'

expect_failure "finite_rg_scaling_composition_requires_intermediate_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ W : Type} [Fintype ι] [Fintype κ] [Fintype W]
    (R : FinitePathIntegral.FiniteRGStep ι κ) (next : κ → W)
    (fineObs : ι → ℂ) (middleObs : κ → ℂ) (coarseObs : W → ℂ)
    (lambda mu : ℂ)
    (h₁ : FinitePathIntegral.FiniteRGStep.ScalingCertificate
      R fineObs middleObs lambda) :
    FinitePathIntegral.FiniteRGStep.ScalingCertificate
      (R.coarsen next) fineObs coarseObs (lambda * mu) :=
  FinitePathIntegral.FiniteRGStep.ScalingCertificate.compose
    R next fineObs middleObs coarseObs lambda mu h₁ (by assumption)'

expect_failure "finite_positive_step_requires_nonnegativity" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (K : Matrix ι ι ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1) : FinitePositiveStep ι :=
  { kernel := K, row_sum := hrow }'

expect_failure "finite_positive_step_requires_row_normalization" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (K : Matrix ι ι ℝ)
    (hnonneg : ∀ i j, 0 ≤ K i j) : FinitePositiveStep ι :=
  { kernel := K, nonneg := hnonneg }'

expect_failure "finite_mass_conservation_requires_column_sum" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι] (K : FinitePositiveStep ι) :
    FinitePositiveStep.MassConservationCertificate K :=
  {}'

expect_failure "finite_npoint_rg_requires_partition_certificate" 'import LeanPhy
open LeanPhy.Mathematics
example {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (observables : List (κ → ℂ)) :
    (R.coarsePathIntegral (by assumption)).multiCorrelator observables =
      (R.finePathIntegral (by assumption)).multiCorrelator
        (observables.map (fun O => fun x => O (R.coarse x))) :=
  FinitePathIntegral.multiCorrelator_coarsen R (by assumption) observables'

expect_failure "finite_ward_requires_weight_symmetry" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι) (e : Equiv.Perm ι) (O : ι → ℂ) :
    P.expectation (fun i => O (e i)) = P.expectation O :=
  P.expectation_reindex_of_weightSymmetry e (by assumption) O'

expect_failure "finite_parabolic_trajectory_requires_step_residual" 'import LeanPhy
open LeanPhy.Mathematics
open LeanPhy.Mathematics.FinitePositiveStep
example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι)
    (exact approximate : ℕ → (ι → ℝ))
    (initialRadius : ℝ) (stepRadius : ℕ → ℝ)
    (hinit : UniformError (exact 0) (approximate 0) initialRadius)
    (hrec : ∀ n, exact (n + 1) = K.step (exact n)) :
    FinitePositiveStep.TrajectoryCertificate
      K exact approximate initialRadius stepRadius :=
  { initial_nonneg := by positivity,
    step_nonneg := by intro n; positivity,
    initial := hinit,
    exact_step := hrec }'

expect_failure "driven_trajectory_requires_source_recurrence" 'import LeanPhy
open LeanPhy.Mathematics
open LeanPhy.Mathematics.FinitePositiveStep
example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι)
    (source : ℕ → (ι → ℝ))
    (exact approximate : ℕ → (ι → ℝ))
    (initialRadius : ℝ) (stepRadius : ℕ → ℝ)
    (hinit : UniformError (exact 0) (approximate 0) initialRadius)
    (hstep : ∀ n, UniformError (K.drivenStep (approximate n) (source n))
      (approximate (n + 1)) (stepRadius n)) :
    FinitePositiveStep.DrivenTrajectoryCertificate K source exact approximate
      initialRadius stepRadius :=
  { initial_nonneg := by positivity,
    step_nonneg := by intro n; positivity,
    initial := hinit,
    step := hstep }'

expect_failure "schwinger_dyson_requires_weight_balance" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (P : FinitePathIntegral ι) (e : Equiv.Perm ι)
    (hinv : ∀ i, e (e i) = i) (jac : ι → ℂ) :
    FinitePathIntegral.InvolutiveVariation P :=
  { map := e, involutive := hinv, jacobian := jac }'

expect_failure "rg_fixed_point_defect_requires_radius" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (R : FinitePathIntegral.FiniteRGStep ι ι)
    (herr : ∀ y, ErrorCertificate (R.coarseWeight y) (R.fineWeight y) 0) :
    FinitePathIntegral.FiniteRGStep.FixedPointDefect R :=
  { error := herr }'

expect_failure "source_driven_trajectory_requires_source_error" 'import LeanPhy
open LeanPhy.Mathematics
open LeanPhy.Mathematics.FinitePositiveStep
example {ι : Type} [Fintype ι]
    (K : FinitePositiveStep ι)
    (exactSource approximateSource : ℕ → (ι → ℝ))
    (exact approximate : ℕ → (ι → ℝ))
    (initialRadius : ℝ) (sourceRadius stepRadius : ℕ → ℝ)
    (hinit : UniformError (exact 0) (approximate 0) initialRadius)
    (hrec : ∀ n, exact (n + 1) = K.drivenStep (exact n) (exactSource n))
    (hstep : ∀ n, UniformError
      (K.drivenStep (approximate n) (approximateSource n))
      (approximate (n + 1)) (stepRadius n)) :
    FinitePositiveStep.SourceDrivenTrajectoryCertificate K exactSource
      approximateSource exact approximate initialRadius sourceRadius stepRadius :=
  { initial_nonneg := by positivity,
    source_nonneg := by intro n; positivity,
    step_nonneg := by intro n; positivity,
    initial := hinit,
    exact_step := hrec,
    step := hstep }'

expect_failure "rg_defect_composition_requires_middle_weights" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (R S : FinitePathIntegral.FiniteRGStep ι ι)
    (first : FinitePathIntegral.FiniteRGStep.FixedPointDefect R)
    (second : FinitePathIntegral.FiniteRGStep.FixedPointDefect S) :
    FinitePathIntegral.FiniteRGStep.FixedPointDefect (R.coarsen S.coarse) :=
  FinitePathIntegral.FiniteRGStep.FixedPointDefect.compose
    R S (by assumption) first second'

expect_failure "reflection_certificate_requires_gram_factorization" 'import LeanPhy
open LeanPhy.Mathematics
example {ι α : Type} [Fintype ι] [Fintype α]
    (e : Equiv.Perm ι) : FiniteReflectionCertificate ι α :=
  { reflection := e }'

expect_failure "reflection_certificate_requires_involution" 'import LeanPhy
open LeanPhy.Mathematics
example {ι α : Type} [Fintype ι] [Fintype α]
    (e : Equiv.Perm ι) (G : FiniteGramKernel ι α) :
    FiniteReflectionCertificate ι α :=
  { reflection := e, gram := G }'

expect_failure "positive_path_requires_weight_nonneg" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (w : ι → ℝ) (hpart : 0 < ∑ i, w i) :
    FinitePositivePathIntegral ι :=
  { weight := w, partition_pos := hpart }'

expect_failure "positive_path_requires_partition_pos" 'import LeanPhy
open LeanPhy.Mathematics
example {ι : Type} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    FinitePositivePathIntegral ι :=
  { weight := w, weight_nonneg := hw }'

expect_failure "weighted_reflection_requires_involution" 'import LeanPhy
open LeanPhy.Mathematics
example {ι α : Type} [Fintype ι] [Fintype α]
    (e : Equiv.Perm ι) (G : FiniteWeightedGramKernel ι α) :
    FiniteWeightedReflectionCertificate ι α :=
  { reflection := e, gram := G }'

expect_failure "weighted_gram_requires_weight_nonneg" 'import LeanPhy
open LeanPhy.Mathematics
example {ι α : Type} [Fintype ι] [Fintype α]
    (w : α → ℝ) (feature : ι → α → ℝ) :
    FiniteWeightedGramKernel ι α :=
  { weight := w, feature := feature }'

expect_failure "energy_step_requires_one_step_bound" 'import LeanPhy
open LeanPhy.Mathematics
example {X : Type} (step : X → X) (energy : X → ℝ)
    (factor : ℝ) : FiniteEnergyStep X :=
  { step := step,
    energy := energy,
    energy_nonneg := by intro x; positivity,
    factor := factor,
    factor_nonneg := by positivity }'

expect_failure "state_map_intermediate_invariant_required" 'import LeanPhy
open LeanPhy.Mathematics
def firstMap : StateMap Nat Nat (fun _ => True) (fun n => n = 0) :=
  { toFun := fun _ => 0, preserves := by intro n _; rfl }
def secondMap : StateMap Nat Nat (fun n => n = 1) (fun _ => True) :=
  { toFun := fun _ => 0, preserves := by intro n _; trivial }
def invalidComposition : StateMap Nat Nat (fun _ => True) (fun _ => True) :=
  secondMap.compose firstMap'

expect_failure "approximate_model_state_lipschitz_required" 'import LeanPhy.Minimal
open LeanPhy.Mathematics
def idProcess : Process ℝ (fun _ => True) where
  toFun := id
  preserves := by intro _ _; trivial
def idModel : PhysicalModel ℝ where
  State := ℝ
  valid := fun _ => True
  step := idProcess
  Observable := Unit
  evaluate := fun x _ => x
def missingStateLipschitz : ApproximateModelMap idModel idModel where
  state := StateMap.identity ℝ (fun _ => True)
  pullback := id
  modulus := 1
  modulus_nonneg := by norm_num
  target_lipschitz := by intro x y; simpa using (show dist x y ≤ dist x y from le_rfl)
  oneStepRadius := fun _ => 0
  oneStepRadius_nonneg := by intro _; norm_num
  oneStep_error := by intro x _; exact ErrorCertificate.of_eq rfl
  observableRadius := fun _ _ => 0
  observableRadius_nonneg := by intro _ _; norm_num
  observable_error := by intro x _ _; exact ErrorCertificate.of_eq rfl
  observableModulus := fun _ => 1
  observableModulus_nonneg := by intro _; norm_num
  observable_lipschitz := by
    intro _
    exact { nonneg := by norm_num, bound := by intro x y; simpa using (show dist x y ≤ dist x y from le_rfl) }'

expect_failure "approximate_model_one_step_certificate_required" 'import LeanPhy.Minimal
open LeanPhy.Mathematics
def idProcess : Process ℝ (fun _ => True) where
  toFun := id
  preserves := by intro _ _; trivial
def idModel : PhysicalModel ℝ where
  State := ℝ
  valid := fun _ => True
  step := idProcess
  Observable := Unit
  evaluate := fun x _ => x
def missingOneStep : ApproximateModelMap idModel idModel where
  state := StateMap.identity ℝ (fun _ => True)
  stateModulus := 1
  stateModulus_nonneg := by norm_num
  state_lipschitz := by intro x y; simpa [StateMap.identity] using (show dist x y ≤ dist x y from le_rfl)
  pullback := id
  modulus := 1
  modulus_nonneg := by norm_num
  target_lipschitz := by intro x y; simpa using (show dist x y ≤ dist x y from le_rfl)
  oneStepRadius := fun _ => 0
  oneStepRadius_nonneg := by intro _; norm_num
  observableRadius := fun _ _ => 0
  observableRadius_nonneg := by intro _ _; norm_num
  observable_error := by intro x _ _; exact ErrorCertificate.of_eq rfl
  observableModulus := fun _ => 1
  observableModulus_nonneg := by intro _; norm_num
  observable_lipschitz := by
    intro _
    exact { nonneg := by norm_num, bound := by intro x y; simpa using (show dist x y ≤ dist x y from le_rfl) }'

expect_failure "approximate_model_observable_certificate_required" 'import LeanPhy.Minimal
open LeanPhy.Mathematics
def idProcess : Process ℝ (fun _ => True) where
  toFun := id
  preserves := by intro _ _; trivial
def idModel : PhysicalModel ℝ where
  State := ℝ
  valid := fun _ => True
  step := idProcess
  Observable := Unit
  evaluate := fun x _ => x
def missingObservable : ApproximateModelMap idModel idModel where
  state := StateMap.identity ℝ (fun _ => True)
  stateModulus := 1
  stateModulus_nonneg := by norm_num
  state_lipschitz := by intro x y; simpa [StateMap.identity] using (show dist x y ≤ dist x y from le_rfl)
  pullback := id
  modulus := 1
  modulus_nonneg := by norm_num
  target_lipschitz := by intro x y; simpa using (show dist x y ≤ dist x y from le_rfl)
  oneStepRadius := fun _ => 0
  oneStepRadius_nonneg := by intro _; norm_num
  oneStep_error := by intro x _; exact ErrorCertificate.of_eq rfl
  observableRadius := fun _ _ => 0
  observableRadius_nonneg := by intro _ _; norm_num
  observable_error := by intro x _ _; exact ErrorCertificate.of_eq rfl
  observableModulus := fun _ => 1
  observableModulus_nonneg := by intro _; norm_num'

expect_failure "rayleigh_self_adjoint_required" 'import LeanPhy
open LeanPhy.Mathematics
def badRayleigh : RayleighIntervalCertificate (1 : ℂ →L[ℂ] ℂ) 1 1 := by
  refine ⟨True.intro, ?_, ?_⟩
  · intro x
    simp [ContinuousLinearMap.reApplyInnerSelf_apply, one_apply_eq_self,
      inner_self_eq_norm_sq]
  · intro x
    simp [ContinuousLinearMap.reApplyInnerSelf_apply, one_apply_eq_self,
      inner_self_eq_norm_sq]'

expect_failure "positive_operator_quadratic_bound_required" 'import LeanPhy
open LeanPhy.Mathematics
def badPositive : PositiveOperatorCertificate (1 : ℂ →L[ℂ] ℂ) :=
  { selfAdjoint := IsSelfAdjoint.one _ }'

expect_failure "positive_spectrum_bridge_requires_complex_space" 'import LeanPhy
open LeanPhy.Mathematics
example : SpectrumRestricts (1 : ℝ →L[ℝ] ℝ) ContinuousMap.realToNNReal := by
  apply PositiveOperatorCertificate.spectrumRestricts_complex
  exact { selfAdjoint := IsSelfAdjoint.one _, quadratic_nonneg := by
    intro x
    simp [ContinuousLinearMap.reApplyInnerSelf_apply, one_apply_eq_self,
      inner_self_eq_norm_sq] }'

expect_failure "dominated_convergence_requires_integrable_bound" 'import LeanPhy
open LeanPhy.Mathematics MeasureTheory Filter
noncomputable section
abbrev μ : Measure Unit := Measure.dirac ()
def badDct : DominatedConvergenceCertificate μ
    (fun _ _ : Unit => (1 : ℂ)) (fun _ : Unit => (1 : ℂ))
    (fun _ : Unit => (1 : ℝ)) := by
  refine { measurable := ?_, dominated := ?_, pointwise_limit := ?_ }
  · intro n; exact measurable_const.aestronglyMeasurable
  · intro n; filter_upwards [] with a; simp
  · filter_upwards [] with a; exact tendsto_const_nhds'

expect_failure "normalized_limit_requires_nonzero_partition" 'import LeanPhy
open LeanPhy.Mathematics MeasureTheory Filter
noncomputable section
abbrev μ : Measure Unit := Measure.dirac ()
def badNormalized : NormalizedObservableConvergenceCertificate μ
    (fun _ _ : Unit => (1 : ℂ)) (fun _ : Unit => (1 : ℂ))
    (fun _ : Unit => (1 : ℂ)) (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => (1 : ℝ)) := by
  exact { weight_certificate := by
      refine { measurable := ?_, bound_integrable := ?_, dominated := ?_, pointwise_limit := ?_ }
      · intro n; exact measurable_const.aestronglyMeasurable
      · simpa using (integrable_const (μ := μ) (1 : ℝ))
      · intro n; filter_upwards [] with a; simp
      · filter_upwards [] with a; exact tendsto_const_nhds,
    insertion_certificate := by
      refine { measurable := ?_, bound_integrable := ?_, dominated := ?_, pointwise_limit := ?_ }
      · intro n; simpa using (measurable_const : Measurable (fun _ : Unit => (1 : ℂ))).aestronglyMeasurable
      · simpa using (integrable_const (μ := μ) (1 : ℝ))
      · intro n; filter_upwards [] with a; simp
      · filter_upwards [] with a; exact tendsto_const_nhds }'

expect_failure "mean_ergodic_requires_contractive_bound" 'import LeanPhy
open LeanPhy.Mathematics
def badMeanErgodic : MeanErgodicCertificate (0 : ℂ →L[ℂ] ℂ) := by
  exact {}'

expect_failure "lax_milgram_requires_coercivity" 'import LeanPhy
open LeanPhy.Mathematics
noncomputable section
abbrev scalarB : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
def badLaxMilgram : LaxMilgramCertificate scalarB := by
  exact {}'

expect_failure "contraction_requires_factor" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
def badContraction : ContractionCertificate (fun x : ℝ => x) (1 : NNReal) := by
  exact {}'

expect_failure "resolvent_requires_both_inverses" 'import LeanPhy
open LeanPhy.Mathematics
def badResolvent : ResolventCertificate (1 : ℂ →L[ℂ] ℂ) 1 := by
  exact ⟨0, by simp⟩'

expect_failure "resolvent_perturbation_requires_inverse_bound" 'import LeanPhy
open LeanPhy.Mathematics
def hA : ResolventCertificate (0 : ℂ →L[ℂ] ℂ) 2 := by
  apply resolvent_of_norm_bound
  simp
def hB : ResolventCertificate (1 : ℂ →L[ℂ] ℂ) 2 := by
  refine ⟨(1 : ℂ →L[ℂ] ℂ), ?_, ?_⟩ <;>
    ext x <;> simp [Algebra.algebraMap_eq_smul_one] <;> norm_num
example : ‖hA.inverse - hB.inverse‖ ≤ (1 : ℝ) := by
  exact resolvent_perturbation_bound hA hB
'

expect_failure "flow_bound_requires_operator_envelope" 'import LeanPhy
open LeanPhy.Mathematics
open LeanPhy.Mathematics.Hilbert
noncomputable section
def F : Hilbert.Flow (𝕜 := ℂ) (E := ℂ) where
  op := fun _ => 1
  zero := rfl
  add := by intro t s; rfl
def bad : FlowNormCertificate F (fun _ => (1 : ℝ)) := by
  exact { nonneg := by intro t; norm_num }'

expect_failure "duhamel_requires_forcing_integrability" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
open LeanPhy.Mathematics.Hilbert
open MeasureTheory
open scoped Interval
noncomputable section
def F : Hilbert.Flow (𝕜 := ℂ) (E := ℂ) where
  op := fun _ => 1
  zero := rfl
  add := by intro t s; rfl
def bad : VariationOfConstantsCertificate F (fun _ : ℝ => (0 : ℂ))
    (fun _ => (0 : ℂ)) 0 := by
  exact { endpoint_eq := by intro t; simp [F, Hilbert.Flow.evolve] }'

expect_failure "duhamel_requires_majorant_integrability" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
open LeanPhy.Mathematics.Hilbert
open MeasureTheory
open scoped Interval
noncomputable section
def F : Hilbert.Flow (𝕜 := ℂ) (E := ℂ) where
  op := fun _ => 1
  zero := rfl
  add := by intro t s; rfl
variable {bound majorant : ℝ → ℝ}
example (h : VariationOfConstantsCertificate F (fun _ : ℝ => (0 : ℂ))
    (fun _ => (0 : ℂ)) 0)
    (hF : FlowNormCertificate F bound)
    (hs : SourceNormCertificate (fun _ : ℝ => (0 : ℂ)) majorant)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖(0 : ℂ) - F.evolve t 0‖ ≤
      ∫ s in (0 : ℝ)..t, bound (t-s) * majorant s := by
  exact VariationOfConstantsCertificate.norm_error_le h hF hs ht'

expect_failure "neumann_requires_strict_norm_bound" 'import LeanPhy
open LeanPhy.Mathematics
example (A : ℂ →L[ℂ] ℂ) : ResolventCertificate A 1 := by
  apply resolvent_of_neumann
' 

expect_failure "operator_approximation_requires_zero_radius_limit" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics Filter
def badOperatorApprox : UniformOperatorApproximationCertificate
    (fun _ : ℕ => (ContinuousLinearMap.id ℝ ℝ))
    (ContinuousLinearMap.id ℝ ℝ) (fun _ => (0 : ℝ)) := by
  refine { nonneg := ?_, bound := ?_ }
  · intro n; norm_num
  · intro n; simp'

expect_failure "energy_certificate_requires_dissipation_nonneg" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics MeasureTheory
open scoped Interval
def badEnergy : EnergyDissipationCertificate
    (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => (0 : ℝ))
    (fun _ : ℝ => (0 : ℝ)) 0 1 := by
  refine { ordered := by norm_num, energy_nonneg := ?_,
    dissipation_integrable := ?_, forcing_integrable := ?_, balance_le := ?_ }
  · intro t; norm_num
  · simpa using (intervalIntegrable_const (μ := volume) (c := (0 : ℝ)) (a := (0 : ℝ)) (b := 1))
  · simpa using (intervalIntegrable_const (μ := volume) (c := (0 : ℝ)) (a := (0 : ℝ)) (b := 1))
  · simp'

expect_failure "unbounded_resolvent_requires_left_inverse" 'import LeanPhy
open LeanPhy.Mathematics
noncomputable def badDenseZero : DenseDomainOperator (𝕜 := ℂ) (E := ℂ) where
  domain := ⊤
  dense := by simpa using (dense_univ : Dense (Set.univ : Set ℂ))
  operator := (0 : (⊤ : Submodule ℂ ℂ) →ₗ[ℂ] ℂ)
def badInverse : ℂ →ₗ[ℂ] (⊤ : Submodule ℂ ℂ) :=
  LinearMap.codRestrict (⊤ : Submodule ℂ ℂ)
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (by intro y; simp)
def badUnboundedResolvent : DomainResolventCertificate badDenseZero 1 where
  inverse := badInverse
  right_inverse := by
    intro y
    change (1 : ℂ) • y - 0 = y
    simp'

expect_failure "domain_preserving_requires_domain_map" 'import LeanPhy
open LeanPhy.Mathematics
noncomputable def domainMap : DenseDomainOperator (𝕜 := ℂ) (E := ℂ) where
  domain := ⊤
  dense := by simpa using (dense_univ : Dense (Set.univ : Set ℂ))
  operator := (0 : (⊤ : Submodule ℂ ℂ) →ₗ[ℂ] ℂ)
def missingDomainMap : DenseDomainOperator.DomainPreserving domainMap where
  bounded := ContinuousLinearMap.id ℂ ℂ'

expect_failure "graph_bound_requires_bound" 'import LeanPhy
open LeanPhy.Mathematics
noncomputable def graphMap : DenseDomainOperator (𝕜 := ℂ) (E := ℂ) where
  domain := ⊤
  dense := by simpa using (dense_univ : Dense (Set.univ : Set ℂ))
  operator := (0 : (⊤ : Submodule ℂ ℂ) →ₗ[ℂ] ℂ)
def missingGraphBound : DenseDomainOperator.GraphBoundCertificate graphMap
    graphMap.operator 0 0 where
  a_nonneg := by norm_num
  b_nonneg := by norm_num'

expect_failure "self_adjoint_requires_adjoint_equality" 'import LeanPhy
open LeanPhy.Mathematics
noncomputable def selfAdjointMap : DenseDomainOperator (𝕜 := ℂ) (E := ℂ) where
  domain := ⊤
  dense := by simpa using (dense_univ : Dense (Set.univ : Set ℂ))
  operator := (0 : (⊤ : Submodule ℂ ℂ) →ₗ[ℂ] ℂ)
def missingAdjointEquality : DenseDomainOperator.SelfAdjointCertificate selfAdjointMap := {}'

expect_failure "renormalization_requires_limit" 'import LeanPhy
open LeanPhy.Mathematics
def badRenormalization : RenormalizationCertificate
    (fun _ : ℕ => (0 : ℝ)) (fun _ : ℕ => (0 : ℝ))
    (fun _ : ℕ => (0 : ℝ)) 0 where
  relation := by intro n; norm_num'

expect_failure "spectral_gap_requires_strict_contraction" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
def badGap : SpectralGapCertificate
    (0 : ℂ →L[ℂ] ℂ) (0 : ℂ →L[ℂ] ℂ) 1 where
  rho_nonneg := by norm_num
  rho_lt_one := by norm_num
'

expect_failure "polynomial_action_requires_eigenvector" 'import LeanPhy.Entry.Analysis
open LeanPhy.Mathematics
open Polynomial
example (A : ℂ →L[ℂ] ℂ) (v : ℂ) (p : Polynomial ℂ) :
    polynomialAction A p v = p.eval 0 • v := by
  apply polynomialAction_apply_eigenvector
'


expect_failure "second_order_requires_linear_closedness" 'import LeanPhy.Examples.Generated.HeisenbergSecondOrder
open LeanPhy.Generated
noncomputable section
example (a : Fin 9 → ℚ) (h : HeisenbergSecondOrder.obstructionValues a = 0) :
    LeanPhy.Mathematics.LieAlgebra ℚ (HeisenbergSecondOrder.Space × HeisenbergSecondOrder.Space × HeisenbergSecondOrder.Space) := by
  exact HeisenbergSecondOrder.secondOrderModel a h'

expect_failure "second_order_requires_obstruction_equations" 'import LeanPhy.Examples.Generated.HeisenbergSecondOrder
open LeanPhy.Generated
noncomputable section
example (a : Fin 9 → ℚ) (h : LeanPhy.Mathematics.LieCohomology.IsTwoCocycle HeisenbergSecondOrder.coefficients (HeisenbergSecondOrder.twoFrom a)) :
    LeanPhy.Mathematics.LieAlgebra ℚ (HeisenbergSecondOrder.Space × HeisenbergSecondOrder.Space × HeisenbergSecondOrder.Space) := by
  apply HeisenbergSecondOrder.secondOrderModel a
  exact ⟨h⟩'

expect_failure "second_order_obstructed_point_rejected" 'import LeanPhy.Examples.SecondOrderDeformationResearch
open LeanPhy.Examples.SecondOrderDeformationResearch LeanPhy.Generated
noncomputable section
example : HeisenbergSecondOrder.SecondOrderConditions (heisenbergFamily ![1,0,1,0,0]) := by
  decide'

expect_failure "second_order_zero_correction_is_not_enough" 'import LeanPhy.Examples.SecondOrderDeformationResearch
open LeanPhy.Examples.SecondOrderDeformationResearch LeanPhy.Generated LeanPhy.Mathematics.LieDeformation
set_option maxSynthPendingDepth 5
example : secondResidual (HeisenbergSecondOrder.twoFrom (cancellable 1 1)) 0 = 0 := by
  exact HeisenbergSecondOrder.secondOrderSolver.correction_cancels _ (by
    rw [HeisenbergSecondOrder.obstruction_coordinates]
    exact (cancellable_conditions 1 1).2)'

expect_failure "second_order_correction_sign_rejected" 'import LeanPhy.Examples.SecondOrderDeformationResearch
open LeanPhy.Examples.SecondOrderDeformationResearch LeanPhy.Generated
example : HeisenbergSecondOrder.correctionValues (cancellable 1 1) = ![0,0,0,-1,0,0,0,0,0] := by
  exact cancellable_correction 1 1'

expect_failure "second_order_cokernel_not_raw_jacobi" 'import LeanPhy.Examples.SecondOrderDeformationResearch
open LeanPhy.Examples.SecondOrderDeformationResearch LeanPhy.Generated LeanPhy.Mathematics.LieDeformation
open LeanPhy.Mathematics.LieCochainCoordinates
example : obstruction (HeisenbergSecondOrder.twoFrom (cancellable 1 1)) (e 0) (e 1) (e 2) = 0 := by
  exact cancellable_quadratic 1 1'


expect_failure "gauge_inverse_requires_quadratic_term" 'import LeanPhy.Mathematics.LieDeformationGauge
open LeanPhy.Mathematics.LieDeformation
example : (secondGauge (LinearMap.id : ℚ →ₗ[ℚ] ℚ) 0).symm (1,0,0) = (1,-1,0) := by
  norm_num [secondGauge_symm_apply]'

expect_failure "gauge_composition_requires_cross_term" 'import LeanPhy.Mathematics.LieDeformationGauge
open LeanPhy.Mathematics.LieDeformation
example : secondGauge (LinearMap.id : ℚ →ₗ[ℚ] ℚ) 0
    (secondGauge (LinearMap.id : ℚ →ₗ[ℚ] ℚ) 0 (1,0,0)) = (1,2,0) := by
  norm_num'

expect_failure "gauge_bracket_requires_coboundary_equation" 'import LeanPhy.Examples.Generated.HeisenbergSecondOrder
open LeanPhy.Generated.HeisenbergSecondOrder LeanPhy.Mathematics.LieDeformation
set_option maxSynthPendingDepth 5
example (ω η ν : C2) (φ ψ : Space →ₗ[ℚ] Space) (x y : Space × Space × Space) :
    secondGauge φ ψ (secondBracket ω ν x y) =
      secondBracket η (transportCorrection ω η φ ψ ν) (secondGauge φ ψ x) (secondGauge φ ψ y) := by
  apply secondGauge_map_bracket'

expect_failure "gauge_lift_requires_valid_correction" 'import LeanPhy.Examples.Generated.HeisenbergSecondOrder
open LeanPhy.Generated.HeisenbergSecondOrder LeanPhy.Mathematics.LieDeformation
set_option maxSynthPendingDepth 5
noncomputable section
example (ω η ν : C2) (E : Equivalence ω η) : SecondEquivalence ω ν η (E.secondCorrection 0 ν) := by
  exact E.liftSecond 0 ν'

expect_failure "normalized_obstruction_requires_closedness" 'import LeanPhy.Examples.Generated.HeisenbergSecondOrder
open LeanPhy.Generated.HeisenbergSecondOrder LeanPhy.Mathematics.LieDeformation
set_option maxSynthPendingDepth 5
example (ω : C2) : SecondExtendable ω ↔ representativeObstructionValues (reduction.project ω) = 0 := by
  exact normalized_extension_iff ω'

expect_failure "obstruction_invariance_requires_equivalence" 'import LeanPhy.Examples.Generated.HeisenbergSecondOrder
open LeanPhy.Generated.HeisenbergSecondOrder LeanPhy.Mathematics.LieDeformation
open LeanPhy.Mathematics.LieCohomology
set_option maxSynthPendingDepth 5
example (ω η : C2) (hω : IsTwoCocycle coefficients ω) (hη : IsTwoCocycle coefficients η) :
    secondOrderSolver.obstructionCoordinates ω = secondOrderSolver.obstructionCoordinates η := by
  apply secondOrderSolver.obstructionCoordinates_equivalence'

expect_failure "h3_is_not_the_cokernel_dimension" 'import LeanPhy.Examples.ThirdCohomologyResearch
open LeanPhy.Mathematics.LieCohomology LeanPhy.Generated
example : Module.finrank ℚ (H3 AffineFourThird.coefficients) = 2 := by
  rw [AffineFourThird.h3_finrank]
  norm_num'

expect_failure "three_cochain_requires_closedness" 'import LeanPhy.Examples.ThirdCohomologyResearch
open LeanPhy.Mathematics.LieCohomology LeanPhy.Generated
open LeanPhy.Examples.ThirdCohomologyResearch
example : IsThreeCocycle AffineFourThird.coefficients nonclosed := by
  exact False.elim (nonclosed_not_cocycle (by assumption))'

expect_failure "zero_h3_projection_requires_closedness" 'import LeanPhy.Examples.ThirdCohomologyResearch
open LeanPhy.Mathematics.LieCohomology LeanPhy.Generated
open LeanPhy.Examples.ThirdCohomologyResearch
example : IsThreeCoboundary AffineFourThird.coefficients nonclosed := by
  apply (AffineFourThird.third_boundary_iff nonclosed _).mpr
  exact nonclosed_projection_zero'

expect_failure "intrinsic_obstruction_is_quadratic" 'import LeanPhy.Examples.ThirdCohomologyResearch
open LeanPhy.Examples.ThirdCohomologyResearch LeanPhy.Generated
example : HeisenbergThird.intrinsicObstruction (HeisenbergThird.reduction.represent ![2,0,2,0,0]) =
    (2 : ℚ) • HeisenbergThird.intrinsicObstruction (HeisenbergThird.reduction.represent ![1,0,1,0,0]) := by
  simp [heisenberg_intrinsic_equations,funext_iff,Fin.forall_fin_succ]'

expect_failure "nonzero_h3_class_forbids_second_extension" 'import LeanPhy.Examples.ThirdCohomologyResearch
open LeanPhy.Mathematics.LieDeformation LeanPhy.Generated
open LeanPhy.Examples.ThirdCohomologyResearch
example : SecondExtendable (HeisenbergThird.reduction.represent ![1,0,1,0,0]) := by
  rw [HeisenbergThird.intrinsic_extension_iff _ (HeisenbergThird.reduction.represent_closed _)]
  simp [heisenberg_intrinsic_equations,funext_iff,Fin.forall_fin_succ]'

expect_failure "h3_coordinates_extension_requires_cocycle" 'import LeanPhy.Examples.Generated.HeisenbergThird
open LeanPhy.Mathematics.LieDeformation LeanPhy.Generated.HeisenbergThird
example (ω : C2) : SecondExtendable ω ↔ intrinsicObstruction ω = 0 := by
  exact intrinsic_extension_iff ω'

expect_failure "h3_class_invariance_requires_equivalence" 'import LeanPhy.Examples.Generated.HeisenbergThird
open LeanPhy.Mathematics.LieDeformation LeanPhy.Mathematics.LieCohomology
open LeanPhy.Generated.HeisenbergThird
example (ω η : C2) (hω : IsTwoCocycle coefficients ω) (hη : IsTwoCocycle coefficients η) :
    obstructionClass ω hω = obstructionClass η hη := by
  apply obstructionClass_of_class_eq ω η hω hη'

expect_failure "h3_scalar_coefficients_are_not_adjoint" 'import LeanPhy.Examples.Generated.AffineFourThird
open LeanPhy.Mathematics.LieDeformation LeanPhy.Generated.AffineFourThird
example (ω : C2) : Cochain algebra := ω'

expect_failure "parameter_h3_preserves_zero_coupling_dimension" 'import LeanPhy.Examples.ParameterizedObstructionResearch
open LeanPhy.Mathematics.LieCohomology LeanPhy.Generated
example : Module.finrank ℚ (H3 (HeisenbergThirdParameter.coefficients (K := ℚ) ![0] ⟨⟩)) = 2 := by
  rw [HeisenbergThirdParameter.h3_finrank]
  norm_num [HeisenbergThirdParameterThirdCE.dimension]'

expect_failure "parameter_h3_preserves_scalar_resonance" 'import LeanPhy.Examples.ParameterizedObstructionResearch
open LeanPhy.Mathematics.LieCohomology LeanPhy.Generated
example : Module.finrank ℚ (H3 (AffineFourThirdCharacter.coefficients (K := ℚ) ![1,1] ⟨⟩)) = 0 := by
  rw [LeanPhy.Examples.ParameterizedObstructionResearch.scalar_resonance_dimension]
  norm_num'

expect_failure "parameter_h3_requires_representation_equation" 'import LeanPhy.Examples.ParameterizedObstructionResearch
open LeanPhy.Generated
example : AffineFourThirdVector.Conditions (![1,2] : Fin 2 → ℚ) := by
  rw [LeanPhy.Examples.ParameterizedObstructionResearch.vector_validity_iff]
  norm_num'

expect_failure "parameter_h3_correction_requires_nonzero_coupling" 'import LeanPhy.Examples.ParameterizedObstructionResearch
open LeanPhy.Examples.ParameterizedObstructionResearch LeanPhy.Mathematics.LieDeformation
example : secondResidual (direction (0 : ℚ) 1 1) (displayedCorrection 0 1 1) = 0 := by
  apply displayedCorrection_cancels
  norm_num'

expect_failure "parameter_h3_extension_can_fail_at_degeneration" 'import LeanPhy.Examples.ParameterizedObstructionResearch
open LeanPhy.Examples.ParameterizedObstructionResearch LeanPhy.Mathematics.LieDeformation
example : SecondExtendable (direction (0 : ℚ) 1 1) := by
  rw [family_extension_iff]
  norm_num'

expect_failure "parameter_h3_normalized_solver_requires_closedness" 'import LeanPhy.Examples.Generated.HeisenbergThirdParameter
open LeanPhy.Generated.HeisenbergThirdParameter LeanPhy.Mathematics.LieDeformation
example (g : ℚ) (ω : C2 ![g] ⟨⟩) : SecondExtendable ω ↔
    representativeObstruction ![g] ⟨⟩ ((reduction ![g] ⟨⟩).project ω) = 0 := by
  exact normalized_extension_iff _ _ ω'

expect_failure "parameter_h3_model_requires_obstruction_zero" 'import LeanPhy.Examples.Generated.HeisenbergThirdParameter
open LeanPhy.Mathematics.LieCohomology LeanPhy.Generated.HeisenbergThirdParameter
example (g : ℚ) (ω : C2 ![g] ⟨⟩) (hω : IsTwoCocycle (coefficients ![g] ⟨⟩) ω) :
    LeanPhy.Mathematics.LieAlgebra ℚ (Space ℚ × Space ℚ × Space ℚ) := by
  exact intrinsicModel _ _ ω hω'

expect_failure "parameter_h3_class_comparison_keeps_fiber" 'import LeanPhy.Examples.Generated.HeisenbergThirdParameter
open LeanPhy.Generated.HeisenbergThirdParameter
example (g h : ℚ) (ω : C2 ![g] ⟨⟩) : C2 ![h] ⟨⟩ := by
  exact ω'

expect_failure "third_order_keeps_the_second_choice" 'import LeanPhy.Examples.ThirdOrderDeformationResearch
open LeanPhy.Mathematics.LieDeformation LeanPhy.Examples.ParameterizedObstructionResearch
open LeanPhy.Examples.ThirdOrderDeformationResearch
example : ThirdExtendable (direction (1 : ℚ) 1 1) (displayedCorrection 1 1 1) := by
  exact adjusted_second_extends 1 1 1 1 (by norm_num)'

expect_failure "third_order_zero_correction_fails" 'import LeanPhy.Examples.ThirdOrderDeformationResearch
open LeanPhy.Mathematics.LieDeformation LeanPhy.Examples.ParameterizedObstructionResearch
open LeanPhy.Examples.ThirdOrderDeformationResearch
example : thirdResidual (direction (1 : ℚ) 1 1) (adjustedSecond 1 1 1 1) 0 = 0 := by
  exact displayed_third_valid 1 1 1 1 (by norm_num)'

expect_failure "third_order_requires_second_jacobi" 'import LeanPhy.Mathematics.LieDeformationThirdObstruction
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology LeanPhy.Mathematics.LieDeformation
example {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {L : LieAlgebra R V}
    (ω ν : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω) :
    IsThreeCocycle (adjointLieModule L) (thirdObstructionCochain ω ν) := by
  exact thirdObstruction_isThreeCocycle ω ν hω'

expect_failure "third_order_requires_first_jacobi" 'import LeanPhy.Mathematics.LieDeformationThirdObstruction
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology LeanPhy.Mathematics.LieDeformation
example {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {L : LieAlgebra R V}
    (ω ν : Cochain L) (hν : secondResidual ω ν = 0) :
    IsThreeCocycle (adjointLieModule L) (thirdObstructionCochain ω ν) := by
  apply thirdObstruction_isThreeCocycle ω ν
  all_goals assumption'

expect_failure "third_order_model_requires_obstruction_zero" 'import LeanPhy.Mathematics.LieDeformationThirdObstruction
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology LeanPhy.Mathematics.LieDeformation
example {R V H : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup H] [Module R H]
    {L : LieAlgebra R V} (S : LieCohomology.ThirdReduction (adjointLieModule L) H)
    (ω ν : Cochain L) (hω : IsTwoCocycle (adjointLieModule L) ω) (hν : secondResidual ω ν = 0) :
    LieAlgebra R (ThirdJet V) := by
  exact LieDeformation.ThirdReduction.thirdModel S ω ν hω hν'

expect_failure "third_order_cannot_change_truncation" 'import LeanPhy.Examples.ThirdOrderDeformationResearch
open LeanPhy.Mathematics.LieDeformation LeanPhy.Examples.ParameterizedObstructionResearch
open LeanPhy.Examples.ThirdOrderDeformationResearch
example (x y : ThirdJet (HSpace ℚ)) :
    ((computedThirdModel 1 1 1 1 (by norm_num)).bracket x y).1 =
      secondBracket (direction 1 1 1) (displayedCorrection 1 1 1) x.1 y.1 := by
  exact computed_model_truncates 1 1 1 1 (by norm_num) x y'

expect_failure "third_order_correction_keeps_nonzero_coupling" 'import LeanPhy.Examples.ThirdOrderDeformationResearch
open LeanPhy.Mathematics.LieDeformation LeanPhy.Examples.ParameterizedObstructionResearch
open LeanPhy.Examples.ThirdOrderDeformationResearch
example : thirdResidual (direction (0 : ℚ) 1 1) (adjustedSecond 0 1 1 1) (displayedThird 0 1 1) = 0 := by
  apply displayed_third_valid
  norm_num'

expect_failure "third_order_obstruction_is_not_independent_of_second_choice" 'import LeanPhy.Examples.ThirdOrderDeformationResearch
open LeanPhy.Mathematics.LieDeformation LeanPhy.Examples.ParameterizedObstructionResearch
open LeanPhy.Examples.ThirdOrderDeformationResearch LeanPhy.Mathematics.LieCochainCoordinates
example : thirdObstructionCochain (direction (1 : ℚ) 1 1) (displayedCorrection 1 1 1) (e 0) (e 1) (e 2) =
    thirdObstructionCochain (direction (1 : ℚ) 1 1) (adjustedSecond 1 1 1 1) (e 0) (e 1) (e 2) := by
  rw [displayed_third_obstruction,adjusted_third_obstruction]
  norm_num [funext_iff,Fin.forall_fin_succ]'

expect_failure "joint_search_requires_first_order_closedness" 'import LeanPhy.Examples.ThirdOrderSearchResearch
open LeanPhy.Generated LeanPhy.Mathematics.LieDeformation
example : ThirdDirectionExtendable NonclosedThirdSearch.direction := by
  rw [NonclosedThirdSearch.search_exists_iff]
  refine ⟨?_,LeanPhy.Examples.ThirdOrderSearchResearch.nonclosed_zero_projection⟩
  assumption'

expect_failure "joint_search_detects_true_third_obstruction" 'import LeanPhy.Examples.ThirdOrderSearchResearch
open LeanPhy.Generated LeanPhy.Mathematics.LieDeformation
example : ThirdDirectionExtendable Filiform4ThirdObstructed.direction := by
  rw [Filiform4ThirdObstructed.search_exists_iff]
  refine ⟨Filiform4ThirdObstructed.direction_closed,?_⟩
  ext i; fin_cases i <;> norm_num [Filiform4ThirdObstructed.obstructionValues]'

expect_failure "joint_search_does_not_fix_the_old_second_choice" 'import LeanPhy.Examples.ThirdOrderSearchResearch
open LeanPhy.Generated LeanPhy.Mathematics.LieDeformation
example : ThirdExtendable HeisenbergThirdSearch.direction HeisenbergThirdSearch.secondCandidate := by
  exact HeisenbergThirdSearch.search_succeeds'

expect_failure "joint_search_second_order_is_insufficient" 'import LeanPhy.Examples.ThirdOrderSearchResearch
open LeanPhy.Generated LeanPhy.Mathematics.LieDeformation
example : ThirdDirectionExtendable Filiform4ThirdObstructed.direction := by
  exact Filiform4ThirdObstructed.second_order_succeeds'

expect_failure "joint_search_target_sign_is_required" 'import LeanPhy.Mathematics.LieDeformationThirdSearch
open LeanPhy.Mathematics LeanPhy.Mathematics.LieDeformation
example {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {L : LieAlgebra R V}
    (ω ν ρ : Cochain L) : jointDifferential ω (ν,ρ) = (obstructionCochain ω,0) ↔
      secondResidual ω ν = 0 ∧ thirdResidual ω ν ρ = 0 := by
  exact joint_equation_iff ω ν ρ'

expect_failure "joint_search_kernel_couples_the_corrections" 'import LeanPhy.Mathematics.LieDeformationThirdSearch
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology LeanPhy.Mathematics.LieDeformation
example {R V H : Type} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup H] [Module R H] {L : LieAlgebra R V} {ω : Cochain L} (S : JointReduction ω H)
    (ν ρ : Cochain L) (h : JointReduction.obstructionCoordinates S = 0) :
    secondResidual ω ν = 0 ∧ thirdResidual ω ν ρ = 0 ↔
      IsTwoCocycle (adjointLieModule L) (ν - (JointReduction.corrections S).1) ∧
      IsTwoCocycle (adjointLieModule L) (ρ - (JointReduction.corrections S).2) := by
  exact JointReduction.all_corrections_iff S ν ρ h'

expect_failure "joint_search_model_requires_zero_projection" 'import LeanPhy.Mathematics.LieDeformationThirdSearch
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology LeanPhy.Mathematics.LieDeformation
example {R V H : Type} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup H] [Module R H] {L : LieAlgebra R V} {ω : Cochain L} (S : JointReduction ω H)
    (hω : IsTwoCocycle (adjointLieModule L) ω) : LieAlgebra R (ThirdJet V) := by
  exact JointReduction.model S hω'

expect_failure "joint_search_nonexistence_requires_nonzero_projection" 'import LeanPhy.Mathematics.LieDeformationThirdSearch
open LeanPhy.Mathematics LeanPhy.Mathematics.LieDeformation
example {R V H : Type} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup H] [Module R H] {L : LieAlgebra R V} {ω : Cochain L} (S : JointReduction ω H)
    (h : JointReduction.obstructionCoordinates S = 0) : ¬ThirdDirectionExtendable ω := by
  exact JointReduction.no_model S h'

expect_failure "lie_ghost_cannot_lower_integer_degree" 'import LeanPhy.Examples.Generated.Sl2Ghost
open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Generated.Sl2Ghost
example {d : Int} {x : Ghosts} (hx : x ∈ degree d) : brst x ∈ degree (d - 1) := by
  exact brst_degree hx'

expect_failure "koszul_cannot_raise_integer_degree" 'import LeanPhy.GaugeTheory.GhostDegree
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial
example {d : Int} {x : GhostPolynomial ℚ 2} (hx : x ∈ degree d) :
    contract (LinearMap.proj (0 : Fin 2)) x ∈ degree (d + 1) := by
  exact contract_mem_degree _ hx'

expect_failure "char_two_parity_is_not_integer_degree" 'import LeanPhy.Examples.LieGhostResearch
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial
example : (1 : GhostPolynomial (ZMod 2) 1) ∈ degree 1 := by
  exact LeanPhy.Examples.LieGhostResearch.characteristic_two_degree_separation.1'

expect_failure "mixed_polynomial_has_no_single_degree" 'import LeanPhy.Examples.LieGhostResearch
open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Examples.LieGhostResearch
example : (1 + c 0) ∈ natDegree 1 := by
  exact generator_mem_natDegree (R := ℚ) (0 : Fin 3)'

expect_failure "lie_ghost_nonzero_scalar_not_exact" 'import LeanPhy.Examples.Generated.Sl2Ghost
open LeanPhy.Generated.Sl2Ghost
example : brst.IsExact 1 := by
  have h := scalar_exact 1
  simpa using h'

expect_failure "homogeneous_primitive_requires_previous_degree" 'import LeanPhy.GaugeTheory.GhostDegree
open LeanPhy.Mathematics LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial
example (L : LeanPhy.Mathematics.LieAlgebra ℚ (Fin 3 → ℚ)) {x : GhostPolynomial ℚ 3}
    (hx : x ∈ natDegree 2) :
    (∃ y, lieDifferential L y = x) ↔ ∃ y ∈ natDegree 2, lieDifferential L y = x := by
  exact homogeneous_exact_iff L hx'

expect_failure "ghost_h2_heisenberg_is_not_one_dimensional" 'import LeanPhy.Examples.GhostCohomology
open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Examples
example : Module.finrank ℚ (GhostH2 HeisenbergCohomology.algebra) = 1 := by
  rw [GhostCohomology.heisenberg_dimension]
  norm_num'

expect_failure "ghost_closed_pair_is_not_automatically_exact" 'import LeanPhy.Examples.GhostCohomology
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Examples
example : ∃ y, lieDifferential (LieGhostFamily.algebra (1 : ℚ) (-1)) y = generator 1 * generator 2 := by
  exact GhostCohomology.family_pair_closed (1 : ℚ) (-1) (by norm_num)'

expect_failure "ghost_parameter_dimension_retains_resonance" 'import LeanPhy.Examples.GhostCohomology
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Examples
example : Module.finrank ℚ (GhostH2 (LieGhostFamily.algebra (1 : ℚ) (-1))) = 0 := by
  rw [GhostCohomology.family_resonant]
  norm_num'

expect_failure "ghost_h2_characteristic_cannot_be_ignored" 'import LeanPhy.Examples.GhostCohomology
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Examples
example : Module.finrank (ZMod 2) (GhostH2 (LieGhostFamily.algebra (1 : ZMod 2) 1)) = 0 := by
  rw [GhostCohomology.characteristic_two_dimension]
  norm_num'

expect_failure "ghost_reduction_requires_closedness" 'import LeanPhy.GaugeTheory.LieGhostCohomology
open LeanPhy.Mathematics LeanPhy.Mathematics.LieCohomology
open LeanPhy.GaugeTheory.GhostPolynomial
set_option maxSynthPendingDepth 7
example (L : LeanPhy.Mathematics.LieAlgebra ℚ (Fin 3 → ℚ))
    (S : Reduction (trivialLieModule L : LieModule L ℚ) ℚ)
    (ω : LieCochain2 L (trivialLieModule L : LieModule L ℚ)) :
    (∃ y, lieDifferential L y = ghostTwo L ω) ↔ S.project ω = 0 := by
  exact ghostTwo_exact_iff_coordinates L S ω'

expect_failure "ghost_nonzero_class_requires_nontrivial_ring" 'import LeanPhy.Examples.GhostCohomology
open LeanPhy.GaugeTheory LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Examples
example : ¬∃ y, lieDifferential (LieGhostFamily.algebra (0 : ZMod 1) 0) y = generator 1 * generator 2 := by
  exact GhostCohomology.family_pair_not_exact 0 0'


expect_failure "matter_representation_law_required" 'import LeanPhy.Examples.GhostMatter
open LeanPhy.Mathematics LeanPhy.GaugeTheory
example : LieModule (LieGhostFamily.algebra (1 : ℚ) 1) ℚ :=
  { act := fun v m => v 1 * m
    act_add_left'"'"' := by intros; simp; ring
    act_smul_left'"'"' := by intros; simp; ring
    act_add_right'"'"' := by intros; ring
    act_smul_right'"'"' := by intros; simp; ring
    bracket_act'"'"' := by
      intro x y m
      simp [LieGhostFamily.algebra, LieGhostFamily.bracket]
      ring }
'

expect_failure "charged_matter_not_automatically_closed" 'import LeanPhy.Examples.GhostMatter
open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Examples
example : matterDifferential (GhostMatter.character (1 : ℚ) 1 1) (matterZero (1 : ℚ)) = 0 := by
  rw [GhostMatter.character_constant_closed_iff]
  norm_num'

expect_failure "matter_torsion_constant_not_exact" 'import LeanPhy.Examples.GhostMatter
open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Examples
example : ∃ y, matterDifferential (GhostMatter.character (1 : ZMod 6) 1 2) y = matterZero (3 : ZMod 6) := by
  rw [matterZero_exact_iff]
  decide'

expect_failure "matter_weight_nonzero_not_enough" 'import LeanPhy.Examples.GhostMatter
open LeanPhy.GaugeTheory.GhostPolynomial LeanPhy.Examples
example : matterDifferential (GhostMatter.character (1 : ZMod 6) 1 2) (matterZero (3 : ZMod 6)) ≠ 0 := by
  rw [GhostMatter.zero_divisor_constant_closed]
  decide'

expect_failure "matter_differential_does_not_preserve_degree" 'import LeanPhy.GaugeTheory.LieGhostMatter
open LeanPhy.Mathematics LeanPhy.GaugeTheory.GhostPolynomial
example {L : LieAlgebra ℚ (Fin 3 → ℚ)} (𝒨 : LieModule L ℚ)
    {x : MatterGhost ℚ 3 ℚ} (hx : x ∈ matterDegree 0) : matterDifferential 𝒨 x ∈ matterDegree 0 :=
  matterDifferential_mem_degree 𝒨 hx'

expect_failure "matter_one_closedness_requires_cocycle" 'import LeanPhy.GaugeTheory.LieGhostMatterCohomology
open LeanPhy.Mathematics LeanPhy.GaugeTheory.GhostPolynomial
example {L : LieAlgebra ℚ (Fin 3 → ℚ)} (𝒨 : LieModule L ℚ) (φ : LieCochain1 L 𝒨) :
    matterDifferential 𝒨 (matterOne 𝒨 φ) = 0 := by
  exact (matterOne_closed_iff 𝒨 φ).mpr'

cd "${BUILD_ROOT}"
lake env python3 "${PROJECT_ROOT}/scripts/run_negative_tests.py" \
  "${TMP_ROOT}" --jobs "${LEANPHY_NEGATIVE_JOBS:-8}" \
  --timeout "${LEANPHY_NEGATIVE_TIMEOUT:-600}"
