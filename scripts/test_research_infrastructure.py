#!/usr/bin/env python3
"""Exercise the compiled goal ledger and declaration index as downstream clients."""
import json
import os
from pathlib import Path
import subprocess
import unittest

ROOT = Path(os.environ.get('LEANPHY_BUILD_ROOT', Path(__file__).resolve().parents[1]))
BIN = ROOT / '.lake/build/bin'


def run(name, *args):
    return subprocess.run([str(BIN / name), *args], cwd=ROOT, text=True,
                          capture_output=True, timeout=90)


class ResearchInfrastructure(unittest.TestCase):
    def test_registered_target_history(self):
        result = run('leanphy_obligation_client', '--strict', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['open_obligation_count'], 0)
        self.assertEqual(project['claim_count'], 1)
        package = project['packages'][0]
        self.assertEqual(package['diagnostics'], [])
        history = package['resolved_obligations']
        self.assertEqual(len(history), 1)
        self.assertEqual(history[0]['obligation']['name'], 'residual bound')
        self.assertEqual(history[0]['obligation']['kind'], 'typed')
        self.assertEqual(history[0]['status'], 'proved_registered_target')
        self.assertEqual(history[0]['claim'], package['claims'][0]['name'])
        # An independent client must not advertise built-in-only flags.
        help_result = run('leanphy_obligation_client', '--help')
        self.assertEqual(help_result.returncode, 0, help_result.stderr)
        self.assertNotIn('--broad', help_result.stdout)
        builtin_help = run('leanphy_check', '--help')
        self.assertEqual(builtin_help.returncode, 0, builtin_help.stderr)
        self.assertIn('--broad', builtin_help.stdout)

    def test_evidence_does_not_close_external_goal(self):
        result = run('leanphy_obligation_client', '--open', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['claim_count'], 1)
        self.assertEqual(project['open_obligation_count'], 1)
        package = project['packages'][0]
        self.assertEqual(package['resolved_obligations'], [])
        self.assertEqual(package['open_obligations'][0]['kind'], 'external')
        strict = run('leanphy_obligation_client', '--open', '--strict')
        self.assertNotEqual(strict.returncode, 0)
        self.assertIn('remain open', strict.stderr)

    def test_duplicate_name_cannot_erase_second_goal(self):
        result = run('leanphy_obligation_client', '--duplicate', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['open_obligation_count'], 1)
        self.assertEqual(len(project['packages'][0]['resolved_obligations']), 1)
        strict = run('leanphy_obligation_client', '--duplicate', '--strict')
        self.assertNotEqual(strict.returncode, 0)
        self.assertIn('remain open', strict.stderr)

    def test_variational_research_preserves_analytic_obligations(self):
        result = run('leanphy_variational_client', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['claim_count'], 4)
        self.assertEqual(project['open_obligation_count'], 2)
        package = project['packages'][0]
        self.assertEqual(package['diagnostics'], [])
        self.assertEqual({o['name'] for o in package['open_obligations']},
                         {'smooth solutions', 'integrated charge'})
        self.assertEqual(package['resolved_obligations'], [])
        self.assertIn('off-shell candidate budget', {c['name'] for c in package['claims']})
        strict = run('leanphy_variational_client', '--strict')
        self.assertNotEqual(strict.returncode, 0)
        self.assertIn('remain open', strict.stderr)

    def test_source_client_retains_limit_and_dynamics_obligations(self):
        result = run('leanphy_source_client', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['claim_count'], 10)
        self.assertEqual(project['open_obligation_count'], 2)
        package = project['packages'][0]
        self.assertEqual(package['diagnostics'], [])
        self.assertEqual({o['name'] for o in package['open_obligations']},
                         {'thermodynamic limit', 'dynamical response'})
        self.assertTrue({'action coupling insertion', 'quantum Gibbs operator', 'thermal stationarity',
                         'quantum trace susceptibility', 'probe basis transport'} <=
                        {c['name'] for c in package['claims']})
        strict = run('leanphy_source_client', '--strict')
        self.assertNotEqual(strict.returncode, 0)
        self.assertIn('remain open', strict.stderr)

    def test_effective_client_preserves_validity_obligations(self):
        result = run('leanphy_effective_client', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['claim_count'], 14)
        self.assertEqual(project['open_obligation_count'], 3)
        package = project['packages'][0]
        self.assertEqual(package['diagnostics'], [])
        self.assertEqual({o['name'] for o in package['open_obligations']},
                         {'low-energy validity', 'Green functions and quantum matching',
                          'unitary low-energy dynamics'})
        self.assertTrue({'induced readout', 'reconstruction metric', 'inverse residual budget',
                         'coupled propagating residual', 'actual heavy first variation',
                         'propagating action matching', 'heavy source contacts',
                         'matched action error', 'heavy readout transport'} <=
                        {c['name'] for c in package['claims']})
        strict = run('leanphy_effective_client', '--strict')
        self.assertNotEqual(strict.returncode, 0)
        self.assertIn('remain open', strict.stderr)

    def test_fermion_client_keeps_physical_obligations(self):
        result = run('leanphy_fermion_client', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['claim_count'], 19)
        self.assertEqual(project['open_obligation_count'], 3)
        package = project['packages'][0]
        self.assertEqual(package['diagnostics'], [])
        self.assertEqual({o['name'] for o in package['open_obligations']},
                         {'interacting self-consistency', 'dynamical correlations',
                          'continuum and topology'})
        self.assertTrue({'constructed CAR', 'many-body Nambu equation', 'normal-ordering energy',
                         'many-body thermal state', 'orbital basis transport', 'parity string',
                         'actual vacuum Wick identity', 'two-mode vacuum Wick identity',
                         'multimode vacuum four-point function', 'multimode vacuum two-point function',
                         'arbitrary ordered vacuum moments', 'odd vacuum moments',
                         'vacuum contact terms', 'interaction vacuum readout'} <=
                        {c['name'] for c in package['claims']})
        strict = run('leanphy_fermion_client', '--strict')
        self.assertNotEqual(strict.returncode, 0)
        self.assertIn('remain open', strict.stderr)

    def test_dynamics_client_preserves_response_boundaries(self):
        result = run('leanphy_dynamics_client', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['claim_count'], 18)
        self.assertEqual(project['open_obligation_count'], 3)
        package = project['packages'][0]
        self.assertEqual(package['diagnostics'], [])
        self.assertEqual({o['name'] for o in package['open_obligations']},
                         {'general evolution existence and frequency response',
                          'controlled perturbation remainder', 'continuum limits'})
        self.assertTrue({'constructed many-body response', 'physical picture equivalence',
                         'noncommuting thermal derivative', 'moving probe response',
                         'normalization subtraction', 'finite frequency reconstruction',
                         'constructed continuous many-body pulse', 'general driven response',
                         'preparation and probe contacts', 'observed source interval'} <=
                        {c['name'] for c in package['claims']})
        strict = run('leanphy_dynamics_client', '--strict')
        self.assertNotEqual(strict.returncode, 0)
        self.assertIn('remain open', strict.stderr)

    def test_exploration_preserves_conditioned_and_negative_results(self):
        result = run('leanphy_exploration_client', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['claim_count'], 7)
        self.assertEqual(project['open_obligation_count'], 2)
        packages = project['packages']
        self.assertTrue(all(not p['diagnostics'] for p in packages))
        for p in packages[:2]:
            self.assertEqual(len(p['open_obligations']), 1)
            self.assertEqual(p['resolved_obligations'], [])
            current = [r for r in p['explorations'] if not r['historical']]
            self.assertEqual({r['outcome'] for r in current},
                             {'branch_goal_proved', 'branch_goal_refuted'})
            conditional = next(r for r in current if r['outcome'] == 'branch_goal_proved')
            self.assertTrue(conditional['conditions'])
        history = packages[0]['explorations']
        failed = [r for r in history if r['outcome'] == 'attempt_failed']
        self.assertEqual(len(failed), 1)
        self.assertTrue(failed[0]['historical'])
        self.assertIn('imaginary pairing phase', failed[0]['note'])
        strict = run('leanphy_exploration_client', '--strict')
        self.assertNotEqual(strict.returncode, 0)
        self.assertIn('remain open', strict.stderr)

    def test_exploration_revision_history_and_proved_coverage(self):
        result = run('leanphy_exploration_client', '--closed', '--strict', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['claim_count'], 3)
        self.assertEqual(project['open_obligation_count'], 0)
        for p in project['packages']:
            self.assertEqual(len(p['resolved_obligations']), 1)
            current = [r for r in p['explorations'] if not r['historical']]
            self.assertEqual(len(current), 1)
            self.assertEqual(current[0]['outcome'], 'branch_goal_proved')
            self.assertEqual(current[0]['conditions'], [])
        pairing, mass, covered = project['packages']
        for p, old, new in [(pairing, 'real-form-v1', 'hermitian-v2'),
                             (mass, 'all-masses-v1', 'invertible-v2')]:
            old_records = [r for r in p['explorations'] if r['revision'] == old]
            self.assertTrue(old_records)
            self.assertTrue(all(r['historical'] and r['superseded_by'].endswith('@' + new)
                                for r in old_records))
            self.assertIn('branch_goal_refuted', {r['outcome'] for r in old_records})
        self.assertIn('vanishes at m = 0', covered['claims'][0]['statement'])
        human = run('leanphy_exploration_client', '--closed')
        self.assertEqual(human.returncode, 0, human.stderr)
        self.assertIn('superseded by pairing ansatz@hermitian-v2', human.stdout)

    def test_matrix_certificates_consume_physics_and_preserve_open_domains(self):
        result = run('leanphy_matrix_certificate_client', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['claim_count'], 9)
        self.assertEqual(project['open_obligation_count'], 3)
        package = project['packages'][0]
        self.assertEqual(package['diagnostics'], [])
        self.assertEqual(len(package['resolved_obligations']), 1)
        self.assertEqual(package['resolved_obligations'][0]['obligation']['name'],
                         'finite heavy resolvent domain')
        self.assertEqual({o['name'] for o in package['open_obligations']},
                         {'physical model enclosure', 'unitary low-energy dynamics',
                          'large-system and continuum validity'})
        self.assertTrue({'rational data checked', 'effective Hamiltonian error',
                         'heavy source error', 'effective probe error', 'heavy reconstruction error'} <=
                        {c['name'] for c in package['claims']})
        strict = run('leanphy_matrix_certificate_client', '--strict')
        self.assertNotEqual(strict.returncode, 0)
        self.assertIn('remain open', strict.stderr)

    def test_actual_action_client_retains_boundary_and_solution_obligations(self):
        result = run('leanphy_action_evaluation_client', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['claim_count'], 9)
        self.assertEqual(project['open_obligation_count'], 4)
        package = project['packages'][0]
        self.assertEqual(package['diagnostics'], [])
        self.assertEqual(package['resolved_obligations'], [])
        self.assertEqual({o['name'] for o in package['open_obligations']},
                         {'on-shell stationarity without boundary conditions',
                          'solution existence and stability', 'spacetime boundary and charges',
                          'covariant and graded fields'})
        self.assertTrue({'integrated action derivative', 'interacting profile equation',
                         'fixed endpoint stationarity', 'interacting shift current',
                         'boundary counterexample', 'off-shell current drift'} <= {c['name'] for c in package['claims']})
        records = package['explorations']
        self.assertEqual(len(records), 2)
        self.assertEqual(records[-1]['outcome'], 'branch_goal_refuted')
        self.assertFalse(records[-1]['historical'])
        self.assertEqual(records[0]['outcome'], 'pending')
        self.assertTrue(records[0]['historical'])
        strict = run('leanphy_action_evaluation_client', '--strict')
        self.assertNotEqual(strict.returncode, 0)
        self.assertIn('remain open', strict.stderr)

    def test_fermion_word_client_keeps_state_and_cutoff_obligations(self):
        result = run('leanphy_fermion_word_client', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['claim_count'], 7)
        self.assertEqual(project['open_obligation_count'], 3)
        package = project['packages'][0]
        self.assertEqual(package['diagnostics'], [])
        self.assertEqual(package['resolved_obligations'], [])
        self.assertEqual({o['name'] for o in package['open_obligations']},
                         {'actual-state Wick theorem', 'bosonic cutoff boundaries',
                          'large-system performance and limits'})
        self.assertIn('quartic dynamics', {c['name'] for c in package['claims']})
        strict = run('leanphy_fermion_word_client', '--strict')
        self.assertNotEqual(strict.returncode, 0)
        self.assertIn('remain open', strict.stderr)

    def test_self_consistency_client_keeps_physical_obligations(self):
        result = run('leanphy_self_consistency_client', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['claim_count'], 11)
        self.assertEqual(project['open_obligation_count'], 4)
        package = project['packages'][0]
        self.assertEqual(package['diagnostics'], [])
        self.assertEqual({o['name'] for o in package['open_obligations']},
                         {'closure error and thermodynamic limit',
                          'critical and multiple branches', 'scalable numerical solvers and input uncertainty',
                          'noncommuting quantum self-consistency'})
        self.assertTrue({'actual readout error', 'temperature in linearization',
                         'stationarity counterexample', 'certified numerical solution',
                         'certified numerical readout'} <= {c['name'] for c in package['claims']})
        strict = run('leanphy_self_consistency_client', '--strict')
        self.assertNotEqual(strict.returncode, 0)
        self.assertIn('remain open', strict.stderr)

    def test_field_redefinition_client_keeps_equivalence_obligations(self):
        result = run('leanphy_field_redefinition_client', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['claim_count'], 13)
        self.assertEqual(project['open_obligation_count'], 4)
        package = project['packages'][0]
        self.assertEqual(package['diagnostics'], [])
        self.assertEqual({o['name'] for o in package['open_obligations']},
                         {'global inverse field charts',
                          'higher-order and derivative-dependent changes',
                          'multidimensional boundaries and graded fields',
                          'quantum measure and scattering'})
        self.assertTrue({'physical source transport', 'retained boundary variation',
                         'finite order distinction', 'Jacobian-transpose Euler transport',
                         'variational current transport', 'actual transformed action derivative',
                         'nonlinear shear equation domain', 'singular-map equation loss'}
                        <= {c['name'] for c in package['claims']})
        strict = run('leanphy_field_redefinition_client', '--strict')
        self.assertNotEqual(strict.returncode, 0)
        self.assertIn('remain open', strict.stderr)

    def test_finite_lattice_client_keeps_continuum_and_rg_obligations(self):
        result = run('leanphy_finite_lattice_client', '--project-json')
        self.assertEqual(result.returncode, 0, result.stderr)
        project = json.loads(result.stdout)
        self.assertEqual(project['claim_count'], 6)
        self.assertEqual(project['open_obligation_count'], 3)
        package = project['packages'][0]
        self.assertEqual(package['diagnostics'], [])
        self.assertEqual(package['resolved_obligations'], [])
        self.assertEqual({o['name'] for o in package['open_obligations']},
                         {'continuum Schwinger--Dyson bridge', 'physical RG flow',
                          'thermodynamic and critical limits'})
        claims = {c['name']: c for c in package['claims']}
        self.assertIn('normalized readout defect budget', claims)
        self.assertIn('two-stage RG error composition', claims)
        self.assertIn('unit-Jacobian', claims['symmetry to Ward insertion']['statement'])
        self.assertTrue(all(c['status'] == 'kernel_checked' for c in claims.values()))
        strict = run('leanphy_finite_lattice_client', '--strict')
        self.assertNotEqual(strict.returncode, 0)
        self.assertIn('remain open', strict.stderr)

    def test_index_real_types_sources_and_coverage(self):
        result = run('leanphy_index', '--json')
        self.assertEqual(result.returncode, 0, result.stderr)
        index = json.loads(result.stdout)
        entries = index['entries']
        self.assertEqual(index['entry_count'], len(entries))
        names = [e['name'] for e in entries]
        self.assertEqual(names, sorted(set(names)))
        by_name = {e['name']: e for e in entries}
        # Required public operations, not just an arbitrary catalogue-size target.
        expected = {
            'LeanPhy.Mathematics.RationalExp.enclose_contains': 'LeanPhy.Mathematics.RationalExp',
            'LeanPhy.StatMech.GibbsCertificate.sound': 'LeanPhy.StatMech.GibbsCertificate',
            'LeanPhy.StatMech.GibbsCertificate.feedback_residual': 'LeanPhy.StatMech.GibbsCertificate',
            'LeanPhy.StatMech.GibbsCertificate.solution_readout_error': 'LeanPhy.StatMech.GibbsCertificate',
            'LeanPhy.FieldTheory.PointTransformation.euler_pullback': 'LeanPhy.FieldTheory.EulerTransport',
            'LeanPhy.FieldTheory.PointTransformation.euler_recover': 'LeanPhy.FieldTheory.EulerTransport',
            'LeanPhy.FieldTheory.PointTransformation.euler_zero_iff_on_of_det_ne_zero': 'LeanPhy.FieldTheory.EulerTransport',
            'LeanPhy.FieldTheory.PointTransformation.boundary_pullback': 'LeanPhy.FieldTheory.EulerTransport',
            'LeanPhy.FieldTheory.PointTransformation.action_derivative_pullback': 'LeanPhy.FieldTheory.EulerTransport',
            'LeanPhy.FieldTheory.FermionicWick.moment': 'LeanPhy.FieldTheory.FermionicMoment',
            'LeanPhy.FieldTheory.FermionicWick.map_moment': 'LeanPhy.FieldTheory.FermionicMoment',
            'LeanPhy.FieldTheory.FermionVacuum.moment_eq': 'LeanPhy.FieldTheory.FermionVacuumWick',
            'LeanPhy.FieldTheory.FermionVacuum.moment_exchange': 'LeanPhy.FieldTheory.FermionVacuumWick',
            'LeanPhy.FieldTheory.FermionVacuum.word_expectation': 'LeanPhy.FieldTheory.FermionVacuumWick',
            'LeanPhy.FieldTheory.FermionVacuum.expression_expectation': 'LeanPhy.FieldTheory.FermionVacuumWick',
            'LeanPhy.FieldTheory.FermionWord.vacuumMoment': 'LeanPhy.FieldTheory.FermionVacuumWick',
            'LeanPhy.FieldTheory.FermionPolynomial.vacuumValue': 'LeanPhy.FieldTheory.FermionVacuumWick',
            'LeanPhy.FieldTheory.FermionVacuum.fourPoint': 'LeanPhy.FieldTheory.FermionVacuum',
            'LeanPhy.FieldTheory.FermionVacuum.certificate': 'LeanPhy.FieldTheory.FermionVacuum',
            'LeanPhy.FieldTheory.FiniteFermion.vacuumState': 'LeanPhy.FieldTheory.FermionVacuum',
            'LeanPhy.FieldTheory.FiniteFermion.annihilates_vacuum': 'LeanPhy.FieldTheory.FermionVacuum',
            'LeanPhy.Quantum.TimeDependent.Evolution.unitary': 'LeanPhy.Quantum.TimeDependentEvolution',
            'LeanPhy.Quantum.TimeDependent.Evolution.comparison': 'LeanPhy.Quantum.TimeDependentEvolution',
            'LeanPhy.Quantum.TimeDependent.Evolution.between_comp': 'LeanPhy.Quantum.TimeDependentEvolution',
            'LeanPhy.Quantum.TimeDependent.DrivenFamily.expectation_derivative': 'LeanPhy.Quantum.DrivenResponse',
            'LeanPhy.Quantum.TimeDependent.DrivenFamily.expectation_contacts': 'LeanPhy.Quantum.DrivenResponse',
            'LeanPhy.Quantum.TimeDependent.DrivenFamily.response_congr': 'LeanPhy.Quantum.DrivenResponse',
            'LeanPhy.Quantum.TimeDependent.pulseFamily_response': 'LeanPhy.Quantum.DrivenPulse',
            'LeanPhy.Quantum.Dynamics.finiteFrequencyResponse_inverse': 'LeanPhy.Quantum.FiniteFrequencyResponse',
            'LeanPhy.Mathematics.FinitePathIntegral.weight_symmetry_ward': 'LeanPhy.Mathematics.FiniteSchwingerDyson',
            'LeanPhy.FieldTheory.PointTransformation.pullback_sources': 'LeanPhy.FieldTheory.PointTransformation',
            'LeanPhy.FieldTheory.PointTransformation.pullback_compose': 'LeanPhy.FieldTheory.PointTransformation',
            'LeanPhy.FieldTheory.PointTransformation.pullback_inverse': 'LeanPhy.FieldTheory.PointTransformation',
            'LeanPhy.FieldTheory.PointTransformation.value_pullback': 'LeanPhy.FieldTheory.TransformationEvaluation',
            'LeanPhy.FieldTheory.PointTransformation.action_pullback': 'LeanPhy.FieldTheory.TransformationEvaluation',
            'LeanPhy.FieldTheory.PointTransformation.finiteProbability_pullback': 'LeanPhy.FieldTheory.TransformationEvaluation',
            'LeanPhy.FieldTheory.PointTransformation.action_infinitesimal_derivative': 'LeanPhy.FieldTheory.RedefinitionVariation',
            'LeanPhy.FieldTheory.PointTransformation.action_infinitesimal_on_shell': 'LeanPhy.FieldTheory.RedefinitionVariation',
            'LeanPhy.StatMech.SourceFeedback.feedback_dist_le': 'LeanPhy.StatMech.SourceFeedback',
            'LeanPhy.StatMech.SourceFeedback.contraction': 'LeanPhy.StatMech.SourceFeedback',
            'LeanPhy.StatMech.SourceFeedback.Envelope.automatic': 'LeanPhy.StatMech.FeedbackCertificate',
            'LeanPhy.StatMech.SourceFeedback.Envelope.solution_error_of_update': 'LeanPhy.StatMech.FeedbackCertificate',
            'LeanPhy.StatMech.SourceFeedback.Envelope.evaluated_observable_error': 'LeanPhy.StatMech.FeedbackCertificate',
            'LeanPhy.StatMech.SourceFeedback.functional_derivative': 'LeanPhy.StatMech.MeanFieldFunctional',
            'LeanPhy.StatMech.SourceFeedback.feedback_derivative': 'LeanPhy.StatMech.MeanFieldFunctional',
            'LeanPhy.StatMech.SourceFeedback.probability_energy': 'LeanPhy.StatMech.MeanFieldFunctional',
            'LeanPhy.FieldTheory.FermionWord.eval_normalize': 'LeanPhy.FieldTheory.FermionWord',
            'LeanPhy.FieldTheory.FermionWord.normalize_ordered': 'LeanPhy.FieldTheory.FermionWord',
            'LeanPhy.FieldTheory.FermionPolynomial.eq_of_compile_sub_eq_nil': 'LeanPhy.FieldTheory.FermionPolynomial',
            'LeanPhy.FieldTheory.FermionPolynomial.compile_ordered': 'LeanPhy.FieldTheory.FermionPolynomial',
            'LeanPhy.FieldTheory.FermionPolynomial.eq_of_local_certificate': 'LeanPhy.FieldTheory.FermionEmbedding',
            'LeanPhy.FieldTheory.InteractingFermion.observable_derivative_of_certificate': 'LeanPhy.FieldTheory.InteractingFermion',
            'LeanPhy.FieldTheory.IntervalAction.noether_drift_certificate': 'LeanPhy.FieldTheory.IntervalAction',
            'LeanPhy.Mathematics.PolynomialEvaluation.hasFDerivAt_eval': 'LeanPhy.Mathematics.PolynomialEvaluation',
            'LeanPhy.Mathematics.PolynomialIntegral.hasDerivAt_integral': 'LeanPhy.Mathematics.PolynomialIntegral',
            'LeanPhy.FieldTheory.FieldEvaluation.first_variation': 'LeanPhy.FieldTheory.FieldEvaluation',
            'LeanPhy.FieldTheory.CurveJet.evaluate_eulerLagrange': 'LeanPhy.FieldTheory.CurveJet',
            'LeanPhy.FieldTheory.IntervalAction.hasDerivAt_action_boundary': 'LeanPhy.FieldTheory.IntervalAction',
            'LeanPhy.FieldTheory.IntervalAction.stationary_of_euler': 'LeanPhy.FieldTheory.IntervalAction',
            'LeanPhy.FieldTheory.IntervalAction.noether_balance': 'LeanPhy.FieldTheory.IntervalAction',
            'LeanPhy.Examples.ActionEvaluationResearch.endpoint_cannot_be_discarded': 'LeanPhy.Examples.ActionEvaluationResearch',

            'LeanPhy.Mathematics.RationalMatrix.realize_mul': 'LeanPhy.Mathematics.RationalMatrix',
            'LeanPhy.Mathematics.RationalMatrix.norm_le': 'LeanPhy.Mathematics.RationalMatrix',
            'LeanPhy.Mathematics.MatrixCertificate.sound': 'LeanPhy.Mathematics.MatrixCertificate',
            'LeanPhy.Mathematics.ResidualInverse.inverse_norm_bound': 'LeanPhy.Mathematics.ResidualInverse',
            'LeanPhy.Mathematics.CertifiedElimination.effective_error': 'LeanPhy.Mathematics.CertifiedElimination',
            'LeanPhy.Mathematics.CertifiedElimination.readout_error': 'LeanPhy.Mathematics.CertifiedElimination',
            'LeanPhy.Quantum.CertifiedResolvent.excludes_spectrum': 'LeanPhy.Quantum.CertifiedResolvent',
            'LeanPhy.Generated.MatrixCertificates.ComplexHeavy.accepted': 'LeanPhy.Examples.Generated.ComplexHeavyCertificate',
            'LeanPhy.Workflow.Exploration.Branch.cover': 'LeanPhy.Workflow.Exploration',
            'LeanPhy.Workflow.Exploration.Branch.joinSplit': 'LeanPhy.Workflow.Exploration',
            'LeanPhy.Workflow.Exploration.Branch.transport': 'LeanPhy.Workflow.Exploration',
            'LeanPhy.Workflow.Exploration.Branch.reindex_proof': 'LeanPhy.Workflow.Exploration',
            'LeanPhy.Workflow.Exploration.Notebook.complete': 'LeanPhy.Workflow.Exploration',
            'LeanPhy.Workflow.Exploration.Notebook.revise': 'LeanPhy.Workflow.Exploration',
            'LeanPhy.Workflow.TheoryPackage.addExploration_preserves_goals': 'LeanPhy.Workflow.Core',
            'LeanPhy.Mathematics.Duhamel.hasDerivAt_perturbation': 'LeanPhy.Mathematics.Duhamel',
            'LeanPhy.Mathematics.Duhamel.conjugateVariation_eq_integral': 'LeanPhy.Mathematics.Duhamel',
            'LeanPhy.Quantum.Dynamics.state_derivative': 'LeanPhy.Quantum.DynamicalResponse',
            'LeanPhy.Quantum.Dynamics.state_expectation': 'LeanPhy.Quantum.DynamicalResponse',
            'LeanPhy.Quantum.Dynamics.expectation_perturbation_integral': 'LeanPhy.Quantum.DynamicalResponse',
            'LeanPhy.Quantum.Dynamics.step_response_derivative': 'LeanPhy.Quantum.DynamicalResponse',
            'LeanPhy.Quantum.ThermalPerturbation.thermal_expectation_perturbation': 'LeanPhy.Quantum.ThermalPerturbation',
            'LeanPhy.Quantum.ThermalPerturbation.response_of_commute': 'LeanPhy.Quantum.ThermalPerturbation',
            'LeanPhy.FieldTheory.FiniteFermion.modes': 'LeanPhy.FieldTheory.FiniteFermion',
            'LeanPhy.FieldTheory.FiniteFermion.ofOrder': 'LeanPhy.FieldTheory.FiniteFermion',
            'LeanPhy.FieldTheory.MultiModeCAR.antiNormal_eq': 'LeanPhy.FieldTheory.FermionBilinear',
            'LeanPhy.FieldTheory.MultiModeCAR.mix': 'LeanPhy.FieldTheory.FermionLinear',
            'LeanPhy.FieldTheory.MultiModeCAR.occupation_majorana': 'LeanPhy.FieldTheory.PhysicalMajorana',
            'LeanPhy.FieldTheory.FermionBdG.nambu_energy': 'LeanPhy.FieldTheory.FermionHamiltonian',
            'LeanPhy.FieldTheory.FermionBdG.nambu_equation': 'LeanPhy.FieldTheory.FermionHamiltonian',
            'LeanPhy.FieldTheory.FermionBdG.Coefficients.partner_equation': 'LeanPhy.FieldTheory.FermionBdG',
            'LeanPhy.FieldTheory.FermionBdG.quadratic_rotate': 'LeanPhy.FieldTheory.FermionBasis',
            'LeanPhy.Condensed.ComplexPairing.uniform_gap': 'LeanPhy.Condensed.ComplexPairing',
            'LeanPhy.Mathematics.FormalExpansion.Below.inverse': 'LeanPhy.Mathematics.FormalExpansion',
            'LeanPhy.Mathematics.FormalExpansion.effective_below': 'LeanPhy.Mathematics.FormalBlockElimination',
            'LeanPhy.Mathematics.BlockElimination.System.satisfies_iff': 'LeanPhy.Mathematics.BlockElimination',
            'LeanPhy.Mathematics.BlockElimination.System.readout_of_solution': 'LeanPhy.Mathematics.BlockElimination',
            'LeanPhy.Quantum.EnergyElimination.Model.eigen_equation_iff': 'LeanPhy.Quantum.EffectiveHamiltonian',
            'LeanPhy.Quantum.EnergyElimination.Model.normMetric_eq': 'LeanPhy.Quantum.EffectiveHamiltonian',
            'LeanPhy.FieldTheory.HeavyFieldElimination.action_eliminated': 'LeanPhy.FieldTheory.HeavyFieldElimination',
            'LeanPhy.FieldTheory.PropagatingHeavy.inverse_residual': 'LeanPhy.FieldTheory.PropagatingHeavy',
            'LeanPhy.FieldTheory.PropagatingHeavy.equation_reconstruct_order': 'LeanPhy.FieldTheory.PropagatingHeavy',
            'LeanPhy.FieldTheory.PropagatingHeavy.kinetic': 'LeanPhy.FieldTheory.PropagatingHeavy',
            'LeanPhy.FieldTheory.PropagatingHeavy.jetModel': 'LeanPhy.FieldTheory.HeavyFieldMatching',
            'LeanPhy.FieldTheory.PropagatingHeavy.Model.density_perturb': 'LeanPhy.FieldTheory.HeavyFieldMatching',
            'LeanPhy.FieldTheory.PropagatingHeavy.Model.density_matching': 'LeanPhy.FieldTheory.HeavyFieldMatching',
            'LeanPhy.FieldTheory.PropagatingHeavy.Model.effective_source_shift': 'LeanPhy.FieldTheory.HeavyFieldMatching',
            'LeanPhy.FieldTheory.PropagatingHeavy.Interval.evaluate_residual': 'LeanPhy.FieldTheory.HeavyFieldInterval',
            'LeanPhy.FieldTheory.PropagatingHeavy.Interval.action_matching': 'LeanPhy.FieldTheory.HeavyFieldInterval',
            'LeanPhy.FieldTheory.PropagatingHeavy.Interval.hasDerivAt_action': 'LeanPhy.FieldTheory.HeavyFieldInterval',
            'LeanPhy.FieldTheory.PropagatingHeavy.Interval.action_error': 'LeanPhy.FieldTheory.HeavyFieldInterval',
            'LeanPhy.FieldTheory.HeavyFieldElimination.eulerLagrange_effective': 'LeanPhy.FieldTheory.HeavyFieldElimination',
            'LeanPhy.Mathematics.EliminationError.effective_error': 'LeanPhy.Mathematics.EliminationError',
            'LeanPhy.Quantum.finiteThermalState_eq_exp': 'LeanPhy.Quantum.FiniteThermalState',
            'LeanPhy.Quantum.finiteThermalState_stationary': 'LeanPhy.Quantum.FiniteThermalState',
            'LeanPhy.Quantum.hasDerivAt_finiteThermalState_energy_temperature': 'LeanPhy.Quantum.FiniteThermalState',
            'LeanPhy.Mathematics.FiniteWeighted.hasDerivAt_expectation_score': 'LeanPhy.Mathematics.FiniteWeightedResponse',
            'LeanPhy.StatMech.SourceEnsemble.hasDerivAt_deriv_logPartition': 'LeanPhy.StatMech.SourceEnsemble',
            'LeanPhy.StatMech.SourceEnsemble.susceptibility_nonneg': 'LeanPhy.StatMech.SourceEnsemble',
            'LeanPhy.StatMech.hasDerivAt_finiteGibbs_parameter': 'LeanPhy.StatMech.GibbsResponse',
            'LeanPhy.StatMech.SourceEnsemble.expectation_source_error': 'LeanPhy.StatMech.ResponseBound',
            'LeanPhy.FieldTheory.FirstOrderLagrangian.hasDerivAt_finiteAction_expectation': 'LeanPhy.FieldTheory.FiniteActionResponse',
            'LeanPhy.Mathematics.FinitePathIntegral.hasDerivAt_sourceExpectation': 'LeanPhy.FieldTheory.FiniteSourceResponse',
            'LeanPhy.Quantum.thermalStateInBasis_eq_exp': 'LeanPhy.Quantum.FiniteThermalState',

            'LeanPhy.Quantum.pauliX_sq': 'LeanPhy.Quantum.Pauli',
            'LeanPhy.Condensed.bdg_sq': 'LeanPhy.Condensed.BCS',
            'LeanPhy.HighEnergy.ward_identity': 'LeanPhy.HighEnergy.Ward',
            'LeanPhy.Mathematics.ErrorCertificate.trans': 'LeanPhy.Mathematics.Approximation',
            'LeanPhy.Mathematics.ContractionCertificate.fixedPoint_unique': 'LeanPhy.Mathematics.Contraction',
            'LeanPhy.Workflow.TheoryPackage.resolveObligation': 'LeanPhy.Workflow.Core',
            'LeanPhy.Mathematics.PhysicalModel': 'LeanPhy.Mathematics.Model',
            'LeanPhy.FieldTheory.FirstOrderLagrangian.noether_residual_certificate': 'LeanPhy.FieldTheory.VariationalResidual',
            'LeanPhy.FieldTheory.FirstOrderLagrangian.first_variation': 'LeanPhy.FieldTheory.Variational',
            'LeanPhy.FieldTheory.FirstOrderLagrangian.eulerLagrange_quadraticAction': 'LeanPhy.FieldTheory.PolynomialAction',
            'LeanPhy.FieldTheory.FirstOrderLagrangian.canonicalStressTensor_off_shell': 'LeanPhy.FieldTheory.EnergyMomentum',
            'LeanPhy.FieldTheory.FirstOrderLagrangian.eulerLagrange_toMechanical': 'LeanPhy.Classical.VariationalBridge',
            # These operations are omitted from the selective Entry.Physics
            # closure but must be discoverable in the complete library index.
            'LeanPhy.Mathematics.commutatorResponse_eq_state_commutator': 'LeanPhy.Mathematics.FiniteResponse',
            'LeanPhy.Mathematics.PoissonAlgebra': 'LeanPhy.Mathematics.Poisson',
            'LeanPhy.Mathematics.FirstClassConstraintAlgebra.ConstraintMap.map_diracObservable': 'LeanPhy.Mathematics.ConstraintMap',
        }
        for name, module in expected.items():
            entry = by_name[name]
            self.assertEqual(entry['moduleName'], module)
            source = ROOT / entry['sourceFile']
            self.assertTrue(source.is_file(), entry)
            self.assertGreater(entry['line'], 0)
            self.assertLessEqual(entry['line'], len(source.read_text().splitlines()))
            self.assertTrue(entry['leanType'])
        self.assertEqual(by_name['LeanPhy.Mathematics.PhysicalModel']['kind'], 'structure')
        response_type = by_name['LeanPhy.Quantum.ThermalPerturbation.thermal_expectation_perturbation']['leanType']
        self.assertIn('HasDerivAt', response_type)
        self.assertNotIn('Commute', response_type)
        self.assertIn('Commute', by_name['LeanPhy.Quantum.ThermalPerturbation.response_of_commute']['leanType'])
        ward = by_name['LeanPhy.HighEnergy.ward_identity']
        self.assertEqual(ward['kind'], 'theorem')
        self.assertIn('slash', ward['leanType'])
        self.assertIn('LeanPhy.HighEnergy.vertexAmplitude_eq_slash', ward['proofDependencies'])
        for entry in entries:
            self.assertNotIn('sorryAx', entry['axioms'])
            self.assertNotIn('Lean.ofReduceBool', entry['axioms'])
            self.assertFalse(entry['name'].startswith('_private'))

    def test_index_imports_all_source_modules(self):
        modules = {str(p.relative_to(ROOT).with_suffix('')).replace('/', '.'): p
                   for p in (ROOT / 'LeanPhy').rglob('*.lean')}
        modules['LeanPhy'] = ROOT / 'LeanPhy.lean'
        modules['Clients.IndexMain'] = ROOT / 'Clients/IndexMain.lean'
        seen, pending = set(), ['Clients.IndexMain']
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            if name in modules:
                pending.extend(line.split()[1] for line in modules[name].read_text().splitlines()
                               if line.startswith('import '))
        self.assertEqual(set(modules) - seen, set())

    def test_index_filters_and_bad_options(self):
        result = run('leanphy_index', '--module', 'LeanPhy.Condensed',
                     '--query', 'BDG SQUARE', '--kind', 'theorem', '--json')
        self.assertEqual(result.returncode, 0, result.stderr)
        entries = json.loads(result.stdout)['entries']
        self.assertTrue(entries)
        self.assertTrue(all(e['moduleName'].startswith('LeanPhy.Condensed') for e in entries))
        self.assertTrue(all(e['kind'] == 'theorem' for e in entries))
        for args in [('--kind', 'unchecked'), ('--query',), ('--unknown',)]:
            self.assertNotEqual(run('leanphy_index', *args).returncode, 0)


if __name__ == '__main__':
    unittest.main()
