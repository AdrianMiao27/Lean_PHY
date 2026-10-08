#!/usr/bin/env python3
"""Independent finite-table checks of actual feedback and its derivative.

Rational enumeration supplies candidate rates and uniform-state covariances.
Lean evaluates the finite envelopes and differentiates the actual Gibbs map.
Python arithmetic is test data, not a trusted proof or a numerical enclosure.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

from run_negative_tests import classify

ROOT = Path(__file__).resolve().parents[1]
BUILD_ROOT = ROOT
HEADER = '''import LeanPhy.StatMech.FeedbackCertificate
import LeanPhy.StatMech.MeanFieldFunctional
open LeanPhy.StatMech SourceFeedback
open scoped BigOperators NNReal Matrix
set_option maxHeartbeats 2000000
private theorem univ_three : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
'''


def rational(x):
    x = Fraction(x)
    return f'({x.numerator} / {x.denominator} : ℝ)'


def vector(values):
    return '![' + ', '.join(rational(x) for x in values) + ']'


def matrix(rows):
    return '![' + ', '.join(vector(row) for row in rows) + ']'


def cases():
    rng = random.Random(314159)
    # A nonsymmetric coupling and insertions with exact cancellations.
    yield [[1, 0, -1], [2, -1, 1]], [[Fraction(1, 8), Fraction(-1, 8)],
                                    [Fraction(1, 16), Fraction(1, 16)]]
    for count in range(7):
        n, d = 2 + count % 2, 2 + (count // 2) % 2
        yield [[rng.randrange(-2, 3) for _ in range(n)] for _ in range(d)], [
            [Fraction(rng.randrange(-3, 4), 16) for _ in range(d)] for _ in range(d)]


def declarations(number, a, k):
    return (f'namespace Case{number}\n'
            f'noncomputable def A : Fin {len(a)} → Fin {len(a[0])} → ℝ := {matrix(a)}\n'
            f'noncomputable def K : Fin {len(k)} → Fin {len(k)} → ℝ := {matrix(k)}\n')


class SelfConsistencyTests(unittest.TestCase):
    def compile(self, source):
        with tempfile.TemporaryDirectory(prefix='leanphy-self-consistency.') as folder:
            path = Path(folder) / 'Check.lean'
            path.write_text(HEADER + source)
            return subprocess.run(['lake', 'env', 'lean', str(path)], cwd=BUILD_ROOT,
                                  text=True, capture_output=True, timeout=180)

    def assert_compiles(self, source):
        result = self.compile(source)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn('sorryAx', result.stdout + result.stderr)
        self.assertNotIn('Lean.ofReduceBool', result.stdout + result.stderr)

    def test_finite_table_envelopes(self):
        source = []
        for c, (a, k) in enumerate(cases()):
            d, n = len(a), len(a[0])
            amplitude = max(abs(v) for row in a for v in row)
            coupling = max(sum(abs(sum(a[row][i] * k[row][col] for row in range(d)))
                               for col in range(d)) for i in range(n))
            source.append(declarations(c, a, k))
            source.append(f'''example : (Envelope.automatic A K).rate = {rational(2 * amplitude * coupling)} := by
  norm_num [Envelope.automatic, Envelope.rate, insertion, A, K,
    Finset.univ_fin2, univ_three, Real.norm_eq_abs]
end Case{c}
''')
        self.assert_compiles(''.join(source))

    def test_actual_feedback_jacobians(self):
        jobs = []
        for c, (a, k) in enumerate(cases()):
            d, n = len(a), len(a[0])
            source = [declarations(c, a, k)]
            for out in range(d):
                for col in range(d):
                    # Differentiate normalized finite weights at zero source:
                    # subtract the means; using raw moments gives a wrong result.
                    score = [sum(a[row][i] * k[row][col] for row in range(d)) for i in range(n)]
                    cov = (sum(Fraction(a[out][i]) * score[i] for i in range(n)) / n
                           - Fraction(sum(a[out]), n) * sum(score) / n)
                    source.append(f'''example : HasDerivAt (fun t => feedback (fun _ : Fin {n} => 0) A
    (fun _ => 0) K (SourceEnsemble.sourceLine (fun _ => 0)
      (fun b => if b = {col} then 1 else 0) t) {out}) {rational(cov)} 0 := by
  have hd := feedback_derivative (fun _ : Fin {n} => 0) A (fun _ => 0) K
    (fun _ => 0) (fun b => if b = {col} then 1 else 0) {out}
  norm_num [SourceFeedback.source, SourceEnsemble.probability, SourceEnsemble.action,
    SourceEnsemble.directionObservable, finiteGibbsProbability, finiteGibbsWeight,
    finitePartitionFunction, FiniteProbability.covariance, FiniteProbability.expectation,
    Fin.sum_univ_three, Fin.sum_univ_two, A, K] at hd
  norm_num [A, K]
  exact hd
''')
            source.append(f'end Case{c}\n')
            jobs.append(''.join(source))
        # Independent finite tables do not need to share one elaboration process.
        # Keep every direction; bound concurrent memory use and per-file time.
        with ThreadPoolExecutor(max_workers=2) as executor:
            list(executor.map(self.assert_compiles, jobs))

    def test_empty_order_type_and_single_configuration(self):
        self.assert_compiles('''example : (Envelope.automatic (fun _ : Fin 0 => fun _ : Unit => (0 : ℝ))
    (fun _ _ => 0)).rate = 0 := by simp [Envelope.automatic, Envelope.rate, insertion]
example (S : Unit → ℝ) (J : Unit → ℝ) (K : Unit → Unit → ℝ) (m : Unit → ℝ) :
    feedback S (fun _ : Unit => fun _ : Unit => (3 : ℝ)) J K m = fun _ => 3 := by
  funext a
  exact FiniteProbability.expectation_const _ 3
''')

    def test_unconnected_moment_is_rejected(self):
        # A constant observable has a nonzero raw second moment but zero response.
        result = self.compile('''example : HasDerivAt
    (fun t => feedback (fun _ : Unit => (0 : ℝ)) (fun _ : Unit => fun _ : Unit => (3 : ℝ))
      (fun _ => 0) (fun _ _ => 1) (fun _ => t) ()) 9 0 := by
  have hd := feedback_derivative (fun _ : Unit => (0 : ℝ))
    (fun _ : Unit => fun _ : Unit => (3 : ℝ)) (fun _ => 0) (fun _ _ => 1)
    (fun _ => 0) (fun _ => 1) ()
  simpa [SourceEnsemble.sourceLine, SourceEnsemble.directionObservable,
    FiniteProbability.covariance_const_left] using hd
''')
        self.assertIsNone(classify(result.returncode, result.stdout + result.stderr),
                          result.stdout + result.stderr)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--build-root', type=Path, default=ROOT)
    args, rest = parser.parse_known_args()
    BUILD_ROOT = args.build_root
    unittest.main(argv=[sys.argv[0]] + rest)
