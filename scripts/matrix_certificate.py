#!/usr/bin/env python3
"""Emit untrusted rational complex matrix data with a kernel-checked Lean acceptance goal.

The Python precheck is advisory. Only compilation of the emitted `accepted`
theorem and the public soundness bridge produces a mathematical certificate.
Floating-point JSON numbers are rejected; use exact rational/decimal strings.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import sys


def rational(value):
    if isinstance(value, bool) or not isinstance(value, (str, int)):
        raise ValueError('matrix entries and bounds must be integers or exact rational strings')
    if isinstance(value, str) and not re.fullmatch(r'[+-]?\d+(?:/\d+|\.\d+)?', value):
        raise ValueError(f'invalid exact rational: {value!r}')
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError(f'invalid rational: {value!r}') from error


def matrix(value, n=None):
    if not isinstance(value, dict) or set(value) != {'real', 'imag'}:
        raise ValueError('a complex matrix needs exactly real and imag arrays')
    re_part, im_part = value['real'], value['imag']
    if not isinstance(re_part, list) or not isinstance(im_part, list):
        raise ValueError('matrix parts must be row arrays')
    size = len(re_part) if n is None else n
    if len(re_part) != size or len(im_part) != size:
        raise ValueError('matrix dimensions do not match')
    parts = []
    for rows in (re_part, im_part):
        if any(not isinstance(row, list) or len(row) != size for row in rows):
            raise ValueError('matrix must be square with consistent row lengths')
        parts.append([[rational(x) for x in row] for row in rows])
    return size, parts


def parse(data):
    keys = {'name', 'nominal', 'inverse', 'inverse_bound', 'residual_bound', 'model_radius'}
    if not isinstance(data, dict) or set(data) != keys:
        raise ValueError('expected name, nominal, inverse and all three bounds')
    name = data['name']
    if (not isinstance(name, str) or not re.fullmatch(r'[A-Z][A-Za-z0-9_]*', name)
            or name in {'Type', 'Prop', 'Sort'}):
        raise ValueError('name must be a capitalized plain Lean identifier')
    n, a = matrix(data['nominal'])
    _, k = matrix(data['inverse'], n)
    bounds = tuple(rational(data[key]) for key in ['inverse_bound', 'residual_bound', 'model_radius'])
    return name, n, a, k, bounds


def rows(parts):
    re_part, im_part = parts
    return [sum((abs(x) + abs(y) for x, y in zip(r, i)), Fraction())
            for r, i in zip(re_part, im_part)]


def precheck(data):
    _, n, a, k, (cap, residual_cap, radius) = parse(data)
    ar, ai = a
    kr, ki = k
    rr = [[Fraction(i == j) - sum((ar[i][t] * kr[t][j] - ai[i][t] * ki[t][j]
           for t in range(n)), Fraction()) for j in range(n)] for i in range(n)]
    ri = [[-sum((ar[i][t] * ki[t][j] + ai[i][t] * kr[t][j]
           for t in range(n)), Fraction()) for j in range(n)] for i in range(n)]
    total = residual_cap + radius * cap
    valid = (cap >= 0 and residual_cap >= 0 and radius >= 0 and total < 1
             and all(x <= cap for x in rows(k))
             and all(x <= residual_cap for x in rows((rr, ri))))
    return valid, total, rows(k), rows((rr, ri))


def lean_rat(q):
    return f'({q.numerator} / {q.denominator} : ℚ)'


def lean_matrix(rows_):
    if not rows_:
        return '(fun i => Fin.elim0 i)'
    return '!![' + '; '.join(', '.join(lean_rat(q) for q in row) for row in rows_) + ']'


def render(data, digest='unspecified'):
    name, n, a, k, (cap, residual_cap, radius) = parse(data)
    if not re.fullmatch(r'[A-Za-z0-9_-]+', digest):
        raise ValueError('invalid provenance digest')
    return f'''import LeanPhy.Mathematics.MatrixCertificate

/- Generated exact data. Python output is untrusted until Lean checks `accepted`.
   Input digest: {digest}. -/
namespace LeanPhy.Generated.MatrixCertificates.{name}

open LeanPhy.Mathematics LeanPhy.Mathematics.MatrixCertificate

def nominal : RationalMatrix {n} {n} :=
  ⟨{lean_matrix(a[0])}, {lean_matrix(a[1])}⟩

def candidate : Candidate {n} where
  inverse := ⟨{lean_matrix(k[0])}, {lean_matrix(k[1])}⟩
  inverseBound := {lean_rat(cap)}
  residualBound := {lean_rat(residual_cap)}
  modelRadius := {lean_rat(radius)}

-- `decide` is reduced by the Lean kernel; no native decision axiom is used.
theorem accepted : candidate.Accepted nominal := by decide +kernel

theorem valid : Valid nominal candidate := sound nominal candidate accepted

def envelope : CertificateEnvelope (Candidate {n}) where
  metadata :=
    {{ producer := "matrix_certificate.py"
      format := "complex-rational-matrix-v1"
      digest := "{digest}"
      source := "exact matrix data with declared norm-ball radius" }}
  payload := candidate

def certificate : VerifiedCertificate (checker nominal candidate) :=
  verifyEnvelope (checker nominal candidate) envelope (by
    change candidate = candidate ∧ candidate.Accepted nominal
    exact ⟨rfl, accepted⟩)

end LeanPhy.Generated.MatrixCertificates.{name}
'''


def report(data, digest):
    name, n, _, _, bounds = parse(data)
    valid, total, krows, rrows = precheck(data)
    out = dict(name=name, dimension=n, input_sha256=digest,
               status='candidate_requires_lean_check',
               norm='linfinity_operator_with_rational_l1_complex_entry_bounds',
               exact_precheck=valid, inverse_row_bounds=list(map(str, krows)),
               residual_row_bounds=list(map(str, rrows)), total_residual=str(total),
               model_radius=str(bounds[2]))
    if valid:
        bound = bounds[0] / (1 - total)
        out.update(inverse_norm_bound=str(bound), inverse_error_bound=str(bound * total))
    return out


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--force', action='store_true')
    args = parser.parse_args(argv)
    try:
        raw = args.input.read_bytes()
        data = json.loads(raw)
        digest = hashlib.sha256(raw).hexdigest()
        summary = report(data, digest)
        if not summary['exact_precheck']:
            raise ValueError('candidate fails the exact rational precheck; no proof or output produced')
        source = render(data, digest)
        outputs = [args.output] + ([args.report] if args.report else [])
        if len({p.resolve() for p in outputs}) != len(outputs):
            raise ValueError('source and report destinations must differ')
        if args.input.resolve() in {p.resolve() for p in outputs}:
            raise ValueError('output cannot overwrite input')
        for path in outputs:
            if path.exists() and not args.force:
                raise ValueError(f'output exists: {path}; use --force to replace it')
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(source, encoding='utf-8')
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(summary, indent=2) + '\n', encoding='utf-8')
        print(json.dumps(summary))
        return 0
    except (ValueError, OSError) as error:
        print(f'matrix certificate error: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
