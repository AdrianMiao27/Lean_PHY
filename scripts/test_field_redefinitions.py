#!/usr/bin/env python3
"""Independent rational evaluation of point maps and their gradient chain rule.

Python computes values and partial derivatives directly from monomial tables.
Lean evaluates the public density pullback on the same tables; random seeds are
fixed and coefficients exact. This tests variable dimensions and mixed terms.
"""
import argparse
from fractions import Fraction
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile
import unittest

from run_negative_tests import classify

ROOT = Path(__file__).resolve().parents[1]
BUILD_ROOT = ROOT
HEADER = '''import LeanPhy.FieldTheory.EulerTransport
open LeanPhy.FieldTheory FirstOrderLagrangian PointTransformation MvPolynomial
open scoped BigOperators Matrix
set_option maxHeartbeats 4000000
'''


def rat(x):
    x = Fraction(x)
    return f'({x.numerator} / {x.denominator} : ℝ)'


def polynomial(terms):
    pieces = []
    for coefficient, powers in terms:
        factors = [f'C {rat(coefficient)}']
        factors += [f'X {j} ^ {p}' for j, p in enumerate(powers) if p]
        pieces.append('(' + ' * '.join(factors) + ')')
    return ' + '.join(pieces) or '0'


def evaluate(terms, values):
    total = Fraction(0)
    for coefficient, powers in terms:
        term = Fraction(coefficient)
        for x, p in zip(values, powers):
            term *= x ** p
        total += term
    return total


def partial(terms, index):
    result = []
    for coefficient, powers in terms:
        if powers[index]:
            exponents = list(powers)
            exponents[index] -= 1
            result.append((coefficient * powers[index], exponents))
    return result


def multiply(left, right):
    result = {}
    for a, u in left:
        for b, v in right:
            powers = tuple(x + y for x, y in zip(u, v))
            result[powers] = result.get(powers, Fraction(0)) + a * b
    return [(c, p) for p, c in result.items() if c]


def substitute(terms, images, dimension):
    result = []
    for coefficient, powers in terms:
        term = [(coefficient, (0,) * dimension)]
        for image, exponent in zip(images, powers):
            for _ in range(exponent):
                term = multiply(term, image)
        result.extend(term)
    return result


def monomial(coefficient, dimension, indices):
    powers = [0] * dimension
    for i in indices:
        powers[i] += 1
    return Fraction(coefficient), tuple(powers)


def euler_value(density, q, v, acceleration):
    """Direct Euler differentiation of the expanded density at a curve jet."""
    n = len(q)
    point, tangent = q + v, v + acceleration
    return [evaluate(partial(density, b), point) - sum(
        evaluate(partial(partial(density, n + b), j), point) * tangent[j]
        for j in range(2 * n)) for b in range(n)]


def euler_cases():
    rng = random.Random(271828)
    dimensions = [(1, 1), (1, 2), (2, 1), (2, 2), (2, 3)]
    for old, new in dimensions:
        maps = [[monomial(1, new, [a % new]),
                 monomial(rng.choice([-2, -1, 1, 2]), new, [a % new, (a + 1) % new])]
                for a in range(old)]
        density = []
        for a in range(old):
            density += [monomial(Fraction(a + 1, 2), 2 * old, [old + a, old + a]),
                        monomial(-1, 2 * old, [a, a, a]),
                        monomial(a + 1, 2 * old, [a])]
        if old > 1:
            density += [monomial(Fraction(1, 2), 2 * old, [old, old + 1]),
                        monomial(2, 2 * old, [0, 1, 1]),
                        monomial(-1, 2 * old, [0, old + 1])]
        q = [Fraction(rng.randrange(-2, 3)) for _ in range(new)]
        v = [Fraction(rng.randrange(-2, 3)) for _ in range(new)]
        acceleration = [Fraction(rng.randrange(-2, 3)) for _ in range(new)]
        fields = [[(c, p + (0,) * new) for c, p in m] for m in maps]
        gradients = [[(c, tuple(p) + tuple(int(j == b) for j in range(new)))
                      for b in range(new) for c, p in partial(m, b)] for m in maps]
        pulled = substitute(density, fields + gradients, 2 * new)
        yield old, new, maps, density, pulled, q, v, acceleration


def density_polynomial(terms, fields):
    pieces = []
    for coefficient, powers in terms:
        factors = [f'C {rat(coefficient)}']
        for j, exponent in enumerate(powers):
            if exponent:
                slot = f'field {j}' if j < fields else f'gradient {j - fields} ()'
                factors.append(f'({slot}) ^ {exponent}')
        pieces.append('(' + ' * '.join(factors) + ')')
    return ' + '.join(pieces) or '0'


def cases():
    rng = random.Random(161803)
    for case in range(10):
        old, new, directions = 1 + case % 3, 1 + (case // 2) % 3, 1 + case % 2
        fields = [[(Fraction(rng.randrange(-3, 4), 2),
                    [rng.randrange(3) for _ in range(new)]) for _ in range(3)] for _ in range(old)]
        values = [Fraction(rng.randrange(-2, 3), 2) for _ in range(new)]
        gradients = [[Fraction(rng.randrange(-2, 3), 3) for _ in range(directions)] for _ in range(new)]
        yield old, new, directions, fields, values, gradients


class FieldRedefinitionTests(unittest.TestCase):
    def compile(self, source):
        with tempfile.TemporaryDirectory(prefix='leanphy-field-change.') as folder:
            p = Path(folder) / 'Check.lean'
            imports = re.findall(r'^import .+$', source, re.MULTILINE)
            body = re.sub(r'^import .+\n?', '', source, flags=re.MULTILINE)
            p.write_text('\n'.join(imports) + '\n' + HEADER + body)
            return subprocess.run(['lake', 'env', 'lean', str(p)], cwd=BUILD_ROOT,
                                  text=True, capture_output=True, timeout=180)

    def assert_compiles(self, source):
        result = self.compile(source)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn('sorryAx', result.stdout + result.stderr)
        self.assertNotIn('Lean.ofReduceBool', result.stdout + result.stderr)

    def test_independent_nonlinear_chain_rule(self):
        for c, (old, new, d, fields, values, gradients) in enumerate(cases()):
            source = f'namespace Case{c}\n'
            source += f'noncomputable def F : Fin {old} → MvPolynomial (Fin {new}) ℝ := !['
            source += ', '.join(polynomial(f) for f in fields) + ']\n'
            source += f'noncomputable def v : Fin {new} × Option (Fin {d}) → ℝ := fun p =>\n'
            source += '  p.2.elim (![' + ', '.join(rat(x) for x in values) + '] p.1)\n'
            source += '    (fun μ => ![' + ', '.join('![' + ', '.join(rat(x) for x in row) + ']'
                                                       for row in gradients) + '] p.1 μ)\n'
            old_values = [evaluate(f, values) for f in fields]
            old_gradients = [[sum(evaluate(partial(f, b), values) * gradients[b][mu]
                                  for b in range(new)) for mu in range(d)] for f in fields]
            # Mixed gradient/source interactions prevent a value-only substitution from passing.
            density = ' + '.join(f'(gradient ({a} : Fin {old}) ({mu} : Fin {d}) ^ 2 + '
                                 f'field {a} * gradient {a} {mu})'
                                 for a in range(old) for mu in range(d))
            expected = sum(old_gradients[a][mu] ** 2 + old_values[a] * old_gradients[a][mu]
                           for a in range(old) for mu in range(d))
            source += f'''example : MvPolynomial.eval v (pullback F ({density})) = {rat(expected)} := by
  norm_num [pullback, coordinate, potential, field, gradient, F, v,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
    Pi.single_apply, Fin.sum_univ_succ, map_ofNat]
end Case{c}
'''
            self.assert_compiles(source)

    def test_empty_field_and_direction_types(self):
        self.assert_compiles('''example (L : FirstOrderLagrangian ℝ (Fin 0) (Fin 0)) :
    pullback (fun a : Fin 0 => MvPolynomial.X a) L = L := pullback_identity L
example (r : ℝ) : pullback (fun _ : Unit => (C r : MvPolynomial (Fin 0) ℝ))
    (gradient () () : FirstOrderLagrangian ℝ Unit Unit) = 0 := by
  simp [pullback, coordinate, gradient]
''')

    def test_incorrect_gradient_is_rejected(self):
        result = self.compile('''example : MvPolynomial.eval
    (fun _ : Unit × Option Unit => (1 : ℝ))
    (pullback (fun _ : Unit => (X () ^ 2 : MvPolynomial Unit ℝ))
      (gradient () () : FirstOrderLagrangian ℝ Unit Unit)) = 1 := by
  norm_num [pullback, coordinate, potential, gradient, MvPolynomial.pderiv_pow]
''')
        self.assertIsNone(classify(result.returncode, result.stdout + result.stderr),
                          result.stdout + result.stderr)

    def test_independent_euler_covariance(self):
        # Expand the entire transformed density before differentiating; the
        # target covariance formula does not build the reference values.
        for old, new, maps, density, pulled, q, v, acceleration in euler_cases():
            with self.subTest(old=old, new=new):
                jac = [[evaluate(partial(m, b), q) for b in range(new)] for m in maps]
                old_q = [evaluate(m, q) for m in maps]
                old_v = [sum(row[b] * v[b] for b in range(new)) for row in jac]
                old_acceleration = [sum(jac[a][b] * acceleration[b] for b in range(new)) +
                                    sum(evaluate(partial(partial(m, b), c), q) * v[b] * v[c]
                                        for b in range(new) for c in range(new))
                                    for a, m in enumerate(maps)]
                old_euler = euler_value(density, old_q, old_v, old_acceleration)
                self.assertEqual(euler_value(pulled, q, v, acceleration),
                                 [sum(old_euler[a] * jac[a][b] for a in range(old))
                                  for b in range(new)])

    def test_kernel_euler_readouts(self):
        for k, (old, new, maps, density, pulled, q, v, acceleration) in enumerate(euler_cases()):
            expected = euler_value(pulled, q, v, acceleration)
            source = '''open scoped ContDiff
theorem derivation_ofNat {A : Type*} [CommRing A] [Algebra ℝ A]
    (D : Derivation ℝ A A) (n : ℕ) [n.AtLeastTwo] : D (ofNat(n) : A) = 0 :=
  D.map_natCast n
'''
            source += f'noncomputable def F : Fin {old} → MvPolynomial (Fin {new}) ℝ := !['
            source += ', '.join(polynomial(m) for m in maps) + ']\n'
            source += f'noncomputable def L : FirstOrderLagrangian ℝ (Fin {old}) Unit :=\n'
            source += density_polynomial(density, old) + '\n'
            for name, values in [('q', q), ('v', v), ('w', acceleration)]:
                source += f'noncomputable def {name} : Fin {new} → ℝ := !['
                source += ', '.join(rat(x) for x in values) + ']\n'
            source += f'noncomputable def profile (i : Fin {new}) (t : ℝ) := q i + v i*t + (w i/2)*t^2\n'
            for b, value in enumerate(expected):
                source += f'''theorem readout{b} : FieldEvaluation.euler (pullback F L)
    (fun _ : Unit => (1 : ℝ)) profile {b} 0 = {rat(value)} := by
  have hd (i : Fin {new}) : deriv (profile i) = fun t => v i + w i*t := by
    funext t
    unfold profile
    simp (disch := fun_prop) [deriv_fun_add, deriv_fun_mul, deriv_fun_pow]
    ring
  have hdd (i : Fin {new}) : deriv (deriv (profile i)) 0 = w i := by rw [hd]; simp
  rw [← CurveJet.evaluate_eulerLagrange (pullback F L) profile
    (by intro i; unfold profile; fun_prop) {b} 0]
  norm_num [CurveJet.evaluate, eulerLagrange, fieldPartial, momentum, lift,
    pullback, coordinate, potential, field, gradient, F, L, q, v, w,
    JetPolynomial.totalDerivative, JetPolynomial.jet, jetIndex, profile,
    iteratedDeriv_succ, Fin.sum_univ_succ, Pi.single_apply]
  all_goals simp only [map_ofNat, derivation_ofNat]
  all_goals norm_num [hd, hdd, q, v, w]
theorem transported{b} : (∑ a, FieldEvaluation.euler L (fun _ : Unit => (1 : ℝ))
    (transformed F profile) a 0 * jacobian F profile a {b} 0) = {rat(value)} :=
  (euler_pullback F L _ profile (by intro i; unfold profile; fun_prop) 0 {b}).symm.trans readout{b}
#print axioms transported{b}
'''
            with self.subTest(case=k, old=old, new=new):
                self.assert_compiles(source)

    def test_guide_snippets_compile(self):
        guide = (ROOT / 'docs/field-redefinitions.md').read_text()
        snippets = re.findall(r'```lean\n(.*?)\n```', guide, re.DOTALL)
        self.assertTrue(snippets)
        for k, snippet in enumerate(snippets):
            with self.subTest(snippet=k):
                self.assert_compiles(snippet)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--build-root', type=Path, default=ROOT)
    args, rest = parser.parse_known_args()
    BUILD_ROOT = args.build_root
    unittest.main(argv=[sys.argv[0]] + rest)
