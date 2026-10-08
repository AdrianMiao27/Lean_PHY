#!/usr/bin/env python3
"""Exercise exact complex data, independent kernel checking and real physics consumers."""
import argparse
import copy
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import matrix_certificate as mc
from run_negative_tests import classify

ROOT = Path(__file__).resolve().parents[1]
BUILD_ROOT = ROOT
FIXTURE = ROOT / 'examples/matrix-certificates/complex-heavy.json'


def scalar(name, a=2, k='1/3', cap='1/3', residual='1/3', radius=0):
    return dict(name=name, nominal=dict(real=[[a]], imag=[[0]]),
                inverse=dict(real=[[k]], imag=[[0]]), inverse_bound=cap,
                residual_bound=residual, model_radius=radius)


class MatrixCertificateTests(unittest.TestCase):
    def compile(self, source):
        with tempfile.TemporaryDirectory(prefix='leanphy-matrix-certificate.') as folder:
            p = Path(folder) / 'Candidate.lean'
            p.write_text(source)
            return subprocess.run(['lake', 'env', 'lean', str(p)], cwd=BUILD_ROOT,
                                  text=True, capture_output=True, timeout=120)

    def assert_compiles(self, source):
        p = self.compile(source)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertNotIn('sorryAx', p.stdout + p.stderr)
        self.assertNotIn('Lean.ofReduceBool', p.stdout + p.stderr)

    def assert_rejected(self, source):
        p = self.compile(source)
        self.assertIsNone(classify(p.returncode, p.stdout + p.stderr), p.stdout + p.stderr)

    def test_rational_complex_precheck_and_reproducibility(self):
        raw = FIXTURE.read_bytes()
        data = json.loads(raw)
        digest = hashlib.sha256(raw).hexdigest()
        report = mc.report(data, digest)
        self.assertEqual(report['total_residual'], '1/2')
        self.assertEqual(report['inverse_norm_bound'], '1/2')
        self.assertEqual(report['inverse_error_bound'], '1/4')
        self.assertEqual(report['status'], 'candidate_requires_lean_check')
        self.assertEqual(report, json.loads(FIXTURE.with_suffix('.report.json').read_text()))
        self.assertEqual(mc.render(data, digest),
                         (ROOT / 'LeanPhy/Examples/Generated/ComplexHeavyCertificate.lean').read_text())

    def test_compiled_empty_scalar_and_nonnormal_data(self):
        empty = dict(name='Empty', nominal=dict(real=[], imag=[]), inverse=dict(real=[], imag=[]),
                     inverse_bound=0, residual_bound=0, model_radius=1)
        nonnormal = dict(name='Nonnormal', nominal=dict(real=[[3, 1], [0, 2]], imag=[[0, 1], [0, 0]]),
                         inverse=dict(real=[['1/3', '-1/6'], [0, '1/2']],
                                      imag=[[0, '-1/6'], [0, 0]]),
                         inverse_bound='2/3', residual_bound=0, model_radius='1/4')
        for data in [empty, scalar('Scalar'), nonnormal]:
            with self.subTest(name=data['name']):
                self.assertTrue(mc.precheck(data)[0])
                self.assert_compiles(mc.render(data) +
                    f'\n#print axioms LeanPhy.Generated.MatrixCertificates.{data["name"]}.valid\n')
        self.assertEqual(mc.report(nonnormal, 'test')['inverse_error_bound'], '2/15')

    def test_forged_inverse_residual_and_nominal_rejected_by_kernel(self):
        original = json.loads(FIXTURE.read_text())
        mutations = []
        for field, value in [('inverse_bound', '1/8'), ('residual_bound', 0), ('model_radius', 3)]:
            data = copy.deepcopy(original)
            data[field] = value
            mutations.append(data)
        changed_inverse = copy.deepcopy(original)
        changed_inverse['inverse']['real'][0][0] = '1/8'
        mutations.append(changed_inverse)
        changed_nominal = copy.deepcopy(original)
        changed_nominal['nominal']['real'][0][0] = 0
        mutations.append(changed_nominal)
        for data in mutations:
            with self.subTest(data=data):
                self.assertFalse(mc.precheck(data)[0])
                # Deliberately bypass the Python precheck: the Lean checker must reject.
                self.assert_rejected(mc.render(data))

    def test_strict_margin_and_signed_budget_rejections(self):
        bad = [scalar('Boundary', 1, 1, 1, 0, 1),
               scalar('NegativeRadius', 1, 1, 1, 0, -1),
               scalar('Singular', 0, 1, 1, 1, 0)]
        for data in bad:
            self.assertFalse(mc.precheck(data)[0])
            self.assert_rejected(mc.render(data))
        # Arbitrarily small positive margin is a valid exact rational premise.
        near = scalar('StrictInterior', 1, 1, 1, 0, '999/1000')
        self.assertTrue(mc.precheck(near)[0])
        self.assert_compiles(mc.render(near))

    def test_operator_norm_is_not_entrywise_max(self):
        data = dict(name='WrongNorm', nominal=dict(real=[[1, 0], [0, 1]], imag=[[0, 0], [0, 0]]),
                    inverse=dict(real=[[1, '1/4'], [0, 1]], imag=[[0, 0], [0, 0]]),
                    inverse_bound=1, residual_bound='1/4', model_radius=0)
        self.assertFalse(mc.precheck(data)[0])
        self.assert_rejected(mc.render(data))
        data['inverse_bound'] = '5/4'
        self.assertTrue(mc.precheck(data)[0])
        self.assert_compiles(mc.render(data))

    def test_parser_rejects_floats_shapes_and_source_injection(self):
        for value in [True, 0.25, None, '1/0', '1/2; axiom forged : False', 'nan']:
            with self.subTest(value=value), self.assertRaises(ValueError):
                mc.rational(value)
        self.assertEqual(mc.rational('0.125'), Q(1, 8))
        for change in [dict(name='Bad.Name'), dict(name='X\nend X'),
                       dict(inverse=dict(real=[[1, 2]], imag=[[0]])), dict(unexpected=True)]:
            data = scalar('Valid')
            data.update(change)
            with self.subTest(change=change), self.assertRaises(ValueError):
                mc.parse(data)
        with self.assertRaises(ValueError):
            mc.render(scalar('Valid'), 'x -/\naxiom forged : False')

    def test_cli_provenance_and_no_overwrite(self):
        with tempfile.TemporaryDirectory(prefix='leanphy-matrix-cli.') as folder:
            target = Path(folder) / 'Candidate.lean'
            report = Path(folder) / 'candidate.json'
            command = [sys.executable, str(ROOT / 'scripts/matrix_certificate.py'), str(FIXTURE),
                       '--output', str(target), '--report', str(report)]
            first = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(first.returncode, 0, first.stderr)
            self.assertEqual(json.loads(first.stdout)['status'], 'candidate_requires_lean_check')
            self.assertEqual(json.loads(report.read_text())['input_sha256'],
                             hashlib.sha256(FIXTURE.read_bytes()).hexdigest())
            original = target.read_bytes()
            second = subprocess.run(command, text=True, capture_output=True)
            self.assertNotEqual(second.returncode, 0)
            self.assertEqual(target.read_bytes(), original)
            bad = Path(folder) / 'bad.json'
            bad.write_text(json.dumps(scalar('Bad', 0, 1, 1, 1)))
            failed = subprocess.run([sys.executable, str(ROOT / 'scripts/matrix_certificate.py'),
                                    str(bad), '--output', str(target), '--force'],
                                   text=True, capture_output=True)
            self.assertNotEqual(failed.returncode, 0)
            self.assertEqual(target.read_bytes(), original)

    def test_checker_is_bound_to_actual_nominal_and_candidate(self):
        source = '''import LeanPhy.Examples.Generated.ComplexHeavyCertificate
open LeanPhy.Mathematics LeanPhy.Mathematics.MatrixCertificate
open LeanPhy.Generated.MatrixCertificates.ComplexHeavy
example : candidate.Accepted (RationalMatrix.zero 2 2) := accepted
'''
        self.assert_rejected(source)
        source = '''import LeanPhy.Examples.Generated.ComplexHeavyCertificate
open LeanPhy.Mathematics LeanPhy.Mathematics.MatrixCertificate
open LeanPhy.Generated.MatrixCertificates.ComplexHeavy
example : (checker nominal candidate).check { candidate with modelRadius := 4 } := by
  constructor
  · rfl
  · exact accepted
'''
        self.assert_rejected(source)

    def test_actual_model_enclosure_cannot_be_omitted(self):
        source = '''import LeanPhy.Examples.Generated.ComplexHeavyCertificate
open LeanPhy.Mathematics LeanPhy.Mathematics.MatrixCertificate
open LeanPhy.Generated.MatrixCertificates.ComplexHeavy
open scoped Matrix.Norms.Operator
example : (Matrix (Fin 2) (Fin 2) ℂ)ˣ :=
  candidate.unit nominal accepted 0
'''
        self.assert_rejected(source)
        source = '''import LeanPhy.Examples.MatrixCertificateResearch
open LeanPhy.Examples.MatrixCertificateResearch
example : (4 : ℂ) ∉ spectrum ℂ heavy := disk_excluded 4 (by norm_num)
'''
        self.assert_rejected(source)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--build-root', type=Path, default=ROOT)
    args, rest = parser.parse_known_args()
    BUILD_ROOT = args.build_root
    unittest.main(argv=[sys.argv[0]] + rest)
