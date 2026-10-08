#!/usr/bin/env python3
"""Compare vacuum readouts with independent occupation-state actions.

The oracle uses exact Gaussian integers and applies each probe to occupation
states. It does not use Wick factorization to obtain expected values. Lean
checks those values through the public, derived vacuum contraction operation.
"""
import argparse
from dataclasses import dataclass
import itertools
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BUILD_ROOT = ROOT


@dataclass(frozen=True)
class GI:
    re: int = 0
    im: int = 0

    def __add__(self, other):
        return GI(self.re + other.re, self.im + other.im)

    def __neg__(self):
        return GI(-self.re, -self.im)

    def __sub__(self, other):
        return self + -other

    def __mul__(self, other):
        return GI(self.re * other.re - self.im * other.im,
                  self.re * other.im + self.im * other.re)

    def lean(self):
        return f'(({self.re} : ℂ) + ({self.im} : ℂ) * Complex.I)'


ZERO, ONE = GI(), GI(1)


def expectation(probes):
    state = {0: ONE}
    for ann, cre in reversed(probes):
        out = {}
        for bits, amplitude in state.items():
            for mode, (a, c) in enumerate(zip(ann, cre)):
                coefficient = a if (bits >> mode) & 1 else c
                value = amplitude * coefficient
                if (bits & ((1 << mode) - 1)).bit_count() % 2:
                    value = -value
                dest = bits ^ (1 << mode)
                out[dest] = out.get(dest, ZERO) + value
        state = out
    return state.get(0, ZERO)


def contraction(p, q):
    return sum((a * c for a, c in zip(p[0], q[1])), ZERO)


def cases():
    rng = random.Random(161803)
    for n in range(5):
        for _ in range(8):
            yield n, [([GI(rng.randrange(-2, 3), rng.randrange(-2, 3)) for _ in range(n)],
                       [GI(rng.randrange(-2, 3), rng.randrange(-2, 3)) for _ in range(n)])
                      for _ in range(4)]


def lean_vector(values):
    return '![' + ', '.join(v.lean() for v in values) + ']' if values else 'Fin.elim0'


def multipoint_cases():
    rng = random.Random(271828)
    for n in range(5):
        for length in (0, 1, 3, 6):
            yield n, [([GI(rng.randrange(-2, 3), rng.randrange(-2, 3)) for _ in range(n)],
                       [GI(rng.randrange(-2, 3), rng.randrange(-2, 3)) for _ in range(n)])
                      for _ in range(length)]
    yield 1, [([ONE], [ONE])] * 8  # Repeated physical probes remain separate slots.
    yield 2, [([GI(rng.randrange(-1, 2), rng.randrange(-1, 2)) for _ in range(2)],
               [GI(rng.randrange(-1, 2), rng.randrange(-1, 2)) for _ in range(2)])
              for _ in range(8)]
    # Three annihilators followed by the same-order creators have odd crossing parity.
    units = [[ONE if i == j else ZERO for i in range(3)] for j in range(3)]
    yield 3, [(v, [ZERO] * 3) for v in units] + [([ZERO] * 3, v) for v in units]


def word_probes(n, word):
    return [(([ONE if i == mode else ZERO for i in range(n)], [ZERO] * n)
             if kind == 'ann' else
             ([ZERO] * n, [ONE if i == mode else ZERO for i in range(n)]))
            for kind, mode in word]


def lean_word(word):
    return '[' + ', '.join(f'{kind} {mode}' for kind, mode in word) + ']'


class FermionVacuumTests(unittest.TestCase):
    def compile(self, source):
        with tempfile.TemporaryDirectory(prefix='leanphy-vacuum-regression.') as folder:
            path = Path(folder) / 'Check.lean'
            path.write_text(source)
            return subprocess.run(['lake', 'env', 'lean', str(path)], cwd=BUILD_ROOT,
                                  capture_output=True, text=True, timeout=240)

    def test_exact_occupation_oracle(self):
        for n, (p, q, r, s) in cases():
            with self.subTest(n=n, p=p):
                self.assertEqual(expectation([p, q]), contraction(p, q))
                self.assertEqual(expectation([p, q, r, s]),
                                 contraction(p, q) * contraction(r, s) -
                                 contraction(p, r) * contraction(q, s) +
                                 contraction(p, s) * contraction(q, r))
        ann0, ann1 = ([ONE, ZERO], [ZERO, ZERO]), ([ZERO, ONE], [ZERO, ZERO])
        cre0, cre1 = ([ZERO, ZERO], [ONE, ZERO]), ([ZERO, ZERO], [ZERO, ONE])
        self.assertEqual(expectation([ann0, ann1, cre0, cre1]), GI(-1))
        majorana = ([ONE], [ONE])
        self.assertEqual(expectation([majorana] * 4), ONE)
        self.assertEqual(expectation([([GI(0, 1)], [ZERO]), ([ZERO], [ONE])]), GI(0, 1))

    def test_kernel_readouts_match_independent_data(self):
        source = ['import LeanPhy.FieldTheory.FermionVacuum',
                  'open LeanPhy.FieldTheory LeanPhy.FieldTheory.FiniteFermion',
                  'set_option maxHeartbeats 2000000']
        # Two independently generated quartets for each mode count, including zero.
        for k, (n, probes) in enumerate(cases()):
            if k % 8 >= 2:
                continue
            names = [f'p{k}_{j}' for j in range(4)]
            for name, (ann, cre) in zip(names, probes):
                source.append(f'noncomputable def {name} : FermionProbe (Fin {n}) :=\n'
                              f'  ⟨{lean_vector(ann)}, {lean_vector(cre)}⟩')
            ops = ' * '.join(f'{name}.operator (vacuumState {n}).car' for name in names)
            source.append(f'theorem readout{k} : (vacuumState {n}).expectation ({ops}) =\n'
                          f'    {expectation(probes).lean()} := by\n'
                          f'  rw [(vacuumState {n}).fourPoint {" ".join(names)}]\n'
                          f'  norm_num [FermionProbe.contraction, {", ".join(names)},\n'
                          '    Fin.sum_univ_succ, Complex.ext_iff]\n'
                          f'#print axioms readout{k}')
        result = self.compile('\n'.join(source))
        output = result.stdout + result.stderr
        self.assertEqual(result.returncode, 0, output)
        self.assertNotRegex(output, r'sorryAx|Lean\.ofReduceBool')
        self.assertEqual(len(re.findall(r"'readout\d+' depends on axioms:", output)), 10)

    def test_arbitrary_moments_match_occupation_actions(self):
        source = ['import LeanPhy.FieldTheory.FermionVacuumWick',
                  'open LeanPhy.FieldTheory LeanPhy.FieldTheory.FiniteFermion',
                  'set_option maxRecDepth 4096', 'set_option maxHeartbeats 8000000']
        corpus = list(multipoint_cases())
        self.assertEqual(expectation(corpus[-1][1]), GI(-1))
        self.assertEqual(expectation(corpus[-3][1]), ONE)
        for k, (n, probes) in enumerate(corpus):
            names = [f'mp{k}_{j}' for j in range(len(probes))]
            for name, (ann, cre) in zip(names, probes):
                source.append(f'noncomputable def {name} : FermionProbe (Fin {n}) :=\n'
                              f'  ⟨{lean_vector(ann)}, {lean_vector(cre)}⟩')
            ps = '[' + ', '.join(names) + ']'
            source.append(f'theorem multipoint{k} : (vacuumState {n}).moment {ps} =\n'
                          f'    {expectation(probes).lean()} := by\n'
                          f'  rw [(vacuumState {n}).moment_eq]\n'
                          '  norm_num [FermionicWick.moment_cons, FermionicWick.removals,\n'
                          '    FermionProbe.contraction, Fin.sum_univ_succ, Complex.ext_iff' +
                          (', ' + ', '.join(names) if names else '') + ']\n'
                          f'#print axioms multipoint{k}')
        result = self.compile('\n'.join(source))
        output = result.stdout + result.stderr
        self.assertEqual(result.returncode, 0, output)
        self.assertNotRegex(output, r'sorryAx|Lean\.ofReduceBool')
        self.assertEqual(len(re.findall(r"'multipoint\d+' depends on axioms:", output)), len(corpus))

    def test_unitary_transport_api(self):
        source = '''import LeanPhy.FieldTheory.FermionUnitaryWick
open LeanPhy.Quantum LeanPhy.FieldTheory LeanPhy.FieldTheory.FiniteFermion
open scoped Matrix
set_option maxHeartbeats 3000000
noncomputable example (U : FiniteUnitary (Occupation 2))
    (ps : List (FermionProbe (Fin 2))) :
    (FermionVacuum.transport U (vacuumState 2)).moment ps =
      FermionicWick.moment FermionProbe.contraction ps := by
  exact FermionVacuum.transport_moment_eq U (vacuumState 2) ps
'''
        result = self.compile(source)
        output = result.stdout + result.stderr
        self.assertEqual(result.returncode, 0, output)
        self.assertNotRegex(output, r'sorryAx|Lean\.ofReduceBool')

    def test_integer_words_and_expression_readouts(self):
        source = ['import LeanPhy.FieldTheory.FermionVacuumWick',
                  'open LeanPhy.FieldTheory LeanPhy.FieldTheory.FiniteFermion FermionWord',
                  'set_option maxRecDepth 4096', 'set_option maxHeartbeats 4000000']
        letters = [('ann', 0), ('ann', 1), ('cre', 0), ('cre', 1)]
        words = [list(w) for n in range(5) for w in itertools.product(letters, repeat=n)]
        rng = random.Random(314159)
        words += [[rng.choice(letters) for _ in range(length)] for length in (6, 8) for _ in range(8)]
        # Include nonzero long words in addition to the random sparse contractions.
        words += [[('ann', 0), ('cre', 0)] * 4,
                  [('ann', 0), ('ann', 1), ('cre', 0), ('cre', 1)] * 2]
        for k, word in enumerate(words):
            expected = expectation(word_probes(2, word))
            self.assertEqual(expected.im, 0)
            source.append(f'def w{k} : Word (Fin 2) := {lean_word(word)}\n'
                          f'theorem word{k} : (vacuumState 2).expectation\n'
                          f'    (FermionWord.eval (vacuumState 2).car w{k}) = ({expected.re} : ℂ) := by\n'
                          f'  rw [(vacuumState 2).word_expectation]\n'
                          f'  have h : vacuumMoment w{k} = {expected.re} := by decide +kernel\n'
                          '  rw [h]; norm_num\n')
        for k in range(8):
            terms = [(rng.randrange(-5, 6), rng.choice(words)) for _ in range(5)]
            value = sum(c * expectation(word_probes(2, word)).re for c, word in terms)
            table = '[' + ', '.join(f'({c}, {lean_word(word)})' for c, word in terms) + ']'
            source.append(f'def expr{k} : FermionPolynomial.Expression ℤ (Fin 2) := {table}\n'
                          f'theorem expression{k} : (vacuumState 2).expectation\n'
                          f'    (FermionPolynomial.eval (Int.castRingHom ℂ) (vacuumState 2).car expr{k}) =\n'
                          f'    ({value} : ℂ) := by\n'
                          '  rw [(vacuumState 2).expression_expectation]\n'
                          f'  have h : FermionPolynomial.vacuumValue expr{k} = {value} := by decide +kernel\n'
                          '  rw [h]; norm_num\n'
                          f'#print axioms expression{k}')
        result = self.compile('\n'.join(source))
        output = result.stdout + result.stderr
        self.assertEqual(result.returncode, 0, output)
        self.assertNotRegex(output, r'sorryAx|Lean\.ofReduceBool')
        self.assertEqual(len(re.findall(r"'expression\d+' depends on axioms:", output)), 8)

    def test_guide_snippets_compile(self):
        guide = (ROOT / 'docs/fermion-models.md').read_text()
        snippets = re.findall(r'```lean\n(.*?)\n```', guide, re.DOTALL)
        self.assertTrue(snippets)
        for k, snippet in enumerate(snippets):
            with self.subTest(snippet=k):
                result = self.compile(snippet)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--build-root', type=Path, default=ROOT)
    args, rest = parser.parse_known_args()
    BUILD_ROOT = args.build_root
    unittest.main(argv=[sys.argv[0]] + rest)
