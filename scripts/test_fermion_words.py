#!/usr/bin/env python3
"""Cross-check the exact CAR compiler against occupation-state actions.

Python produces comparison data only. Lean independently checks every identity
using the proved compiler; the dense oracle is an additional regression check.
"""
import argparse
from collections import defaultdict
from functools import lru_cache
import itertools
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

from run_negative_tests import classify

ROOT = Path(__file__).resolve().parents[1]
BUILD_ROOT = ROOT


@lru_cache(maxsize=None)
def reorder(word):
    """Bubble the first inversion, unlike Lean's right-to-left insertion."""
    for pos in range(len(word) - 1):
        a, b = word[pos:pos + 2]
        if a == b:
            return ()
        if a > b:
            result = defaultdict(int)
            swapped = word[:pos] + (b, a) + word[pos + 2:]
            for w, c in reorder(swapped):
                result[w] -= c
            if a[0] != b[0] and a[1] == b[1]:
                contracted = word[:pos] + word[pos + 2:]
                for w, c in reorder(contracted):
                    result[w] += c
            return tuple(sorted((w, c) for w, c in result.items() if c))
    return ((word, 1),)


def occupation_action(word, state):
    sign = 1
    for kind, mode in reversed(word):
        occupied = (state >> mode) & 1
        if occupied == (1 if kind == 0 else 0):
            return None, 0
        sign *= -1 if (state & ((1 << mode) - 1)).bit_count() % 2 else 1
        state ^= 1 << mode
    return state, sign


def lean_word(word, n):
    return '[' + ', '.join(f'{"cre" if k == 0 else "ann"} ({i} : Fin {n})'
                           for k, i in word) + ']'


HEADER = '''import LeanPhy.FieldTheory.InteractingFermion
import LeanPhy.FieldTheory.FermionEmbedding
open LeanPhy.FieldTheory FermionWord FermionPolynomial
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
'''


class FermionWordTests(unittest.TestCase):
    def compile(self, text):
        with tempfile.TemporaryDirectory(prefix='leanphy-fermion-words.') as folder:
            source = Path(folder) / 'Check.lean'
            source.write_text(HEADER + text)
            return subprocess.run(['lake', 'env', 'lean', str(source)], cwd=BUILD_ROOT,
                                  text=True, capture_output=True, timeout=180)

    def assert_compiles(self, text):
        result = self.compile(text)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn('sorryAx', result.stdout + result.stderr)
        self.assertNotIn('Lean.ofReduceBool', result.stdout + result.stderr)

    def test_exhaustive_small_words_against_occupation_actions(self):
        letters = tuple(itertools.product(range(2), range(2)))
        for length in range(5):
            for word in itertools.product(letters, repeat=length):
                for state in range(4):
                    out, value = occupation_action(word, state)
                    expected = {} if not value else {out: value}
                    actual = defaultdict(int)
                    for term, coeff in reorder(word):
                        dest, amp = occupation_action(term, state)
                        if amp:
                            actual[dest] += coeff * amp
                    self.assertEqual({k: v for k, v in actual.items() if v}, expected,
                                     (word, state))

    def test_kernel_checks_independent_reorderings(self):
        rng = random.Random(271828)
        letters = tuple(itertools.product(range(2), range(4)))
        words = [(), ((1, 0), (0, 0)), ((0, 1), (0, 0)),
                 ((1, 0), (1, 1), (0, 1), (0, 0))]
        words += [tuple(rng.choice(letters) for _ in range(rng.randrange(1, 13)))
                  for _ in range(64)]
        proofs = []
        for word in words:
            rhs = '[' + ', '.join(f'({coeff}, {lean_word(w, 4)})'
                                   for w, coeff in reorder(word)) + ']'
            proofs.append(f'example : compile (sub (term (1 : ℤ) {lean_word(word, 4)}) '
                          f'({rhs} : Expression ℤ (Fin 4))) = [] := by decide')
        self.assert_compiles('\n'.join(proofs))

    def test_sparse_labels_and_long_ordered_word(self):
        word = tuple((0, i) for i in range(16)) + tuple((1, i) for i in range(16))
        self.assert_compiles(f'''example : compile (term (3 : ℤ) {lean_word(word, 1024)}) =
  term 3 {lean_word(word, 1024)} := by decide
example : compile (scalar (0 : ℤ) : Expression ℤ (Fin 0)) = [] := by decide
''')

    def test_false_sign_and_missing_contraction_are_rejected(self):
        for lhs, rhs in [('[ann (0 : Fin 2), cre 0]', '[(-1, [cre 0, ann 0])]'),
                         ('[cre (1 : Fin 2), cre 0]', '[(1, [cre 0, cre 1])]')]:
            result = self.compile(f'example : compile (sub (term (1 : ℤ) {lhs}) {rhs}) = [] := by decide')
            self.assertIsNone(classify(result.returncode, result.stdout + result.stderr),
                              result.stdout + result.stderr)

    def test_adjoint_conjugates_and_reverses(self):
        self.assert_compiles('''example : FermionPolynomial.adjoint
    (term Complex.I [cre (0 : Fin 2), ann 1]) =
    term (-Complex.I) [cre 1, ann 0] := by
  simp [FermionPolynomial.adjoint, term, FermionWord.adjoint]
''')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--build-root', type=Path, default=ROOT)
    args, rest = parser.parse_known_args()
    BUILD_ROOT = args.build_root
    unittest.main(argv=[sys.argv[0]] + rest)
