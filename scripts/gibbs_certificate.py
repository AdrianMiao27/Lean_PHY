#!/usr/bin/env python3
"""Emit exact data for kernel-checked Gibbs readouts or feedback residuals.

Input numbers are integers or exact rational/decimal strings. Python computes
advisory enclosures; generated Lean recomputes all of them. A common exponent
shift changes neither the model nor its normalized expectation. No output of a
floating-point solver is trusted, including its claimed convergence tolerance.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import json
from math import factorial
from pathlib import Path
import re
import sys
import time


def rational(x):
    if isinstance(x, bool) or not isinstance(x, (int, str)):
        raise ValueError('numbers must be integers or exact rational/decimal strings')
    if isinstance(x, str) and not re.fullmatch(r'[+-]?\d+(?:/\d+|\.\d+)?', x):
        raise ValueError('invalid exact rational')
    try:
        return Q(x)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError('invalid exact rational') from error


def array(x, size=None):
    if not isinstance(x, list) or (size is not None and len(x) != size):
        raise ValueError('inconsistent finite table dimensions')
    return [rational(v) for v in x]


def candidate(x):
    if not isinstance(x, dict) or set(x) != {'shift', 'depth', 'order', 'value', 'error'}:
        raise ValueError('candidate needs shift, depth, order, value and error')
    for key in ('depth', 'order'):
        if type(x[key]) is not int or not 0 <= x[key] <= 64:
            raise ValueError('depth/order must be integers between 0 and 64')
    if (x["order"] + 1) * 2**x["depth"] > 8192:
        raise ValueError("range reduction/order exceeds frontend rational-size budget")
    # This is a frontend resource limit, not a restriction of the Lean theorem.
    return {k: x[k] if k in ('depth', 'order') else rational(x[k]) for k in x}


def parse(data):
    if not isinstance(data, dict):
        raise ValueError('input must be an object')
    name, kind = data.get('name'), data.get('kind')
    if (not isinstance(name, str) or not re.fullmatch(r'[A-Z][A-Za-z0-9_]*', name)
            or name in {'Type', 'Prop', 'Sort'}):
        raise ValueError('name must be a capitalized plain Lean identifier')
    if kind == 'expectation':
        if set(data) != {'name', 'kind', 'exponents', 'observable', 'candidate'}:
            raise ValueError('expectation input needs exponents, observable and candidate')
        q = array(data['exponents'])
        O = array(data['observable'], len(q))
        return dict(name=name, kind=kind, q=q, O=[O], c=[candidate(data['candidate'])])
    if kind == 'feedback':
        if set(data) != {'name', 'kind', 'action', 'observables', 'bias', 'coupling',
                         'point', 'candidates', 'error'}:
            raise ValueError('feedback input needs action, observables, bias, coupling, point, candidates, error')
        S, J, m = array(data['action']), array(data['bias']), array(data['point'])
        n, d = len(S), len(J)
        if n == 0 or len(m) != d:
            raise ValueError('feedback requires a nonempty configuration set and matching point')
        if any(not isinstance(data[k], list) or len(data[k]) != d
               for k in ('observables', 'coupling', 'candidates')):
            raise ValueError('inconsistent feedback table dimensions')
        A = [array(row, n) for row in data['observables']]
        K = [array(row, d) for row in data['coupling']]
        cs = [candidate(c) for c in data['candidates']]
        source = [J[a] + sum((K[a][b] * m[b] for b in range(d)), Q()) for a in range(d)]
        q = [-S[i] + sum((source[a] * A[a][i] for a in range(d)), Q()) for i in range(n)]
        return dict(name=name, kind=kind, S=S, A=A, J=J, K=K, m=m, q=q, O=A,
                    c=cs, error=rational(data['error']))
    raise ValueError('kind must be expectation or feedback')


def enclose(x, depth, order):
    y = x / 2**depth
    n = order + 1
    center = sum((y**k / factorial(k) for k in range(n)), Q())
    radius = abs(y)**n * (n + 1) / (factorial(n) * n)
    for _ in range(depth):
        center, radius = center**2, radius * (2 * abs(center) + radius)
    return center, radius


def check(q, O, c):
    weights = [enclose(x - c['shift'], c['depth'], c['order']) for x in q]
    lower = sum((w - r for w, r in weights), Q())
    residual = (abs(sum((w * (a - c['value']) for (w, _), a in zip(weights, O)), Q()))
                + sum((r * abs(a - c['value']) for (_, r), a in zip(weights, O)), Q()))
    accepted = (all(abs(x - c['shift']) <= 2**c['depth'] for x in q)
                and lower > 0 and c['error'] >= 0 and residual <= c['error'] * lower)
    bits = max((max(abs(v.numerator).bit_length(), v.denominator.bit_length())
                for w in weights for v in w), default=0)
    return dict(accepted=accepted, partition_lower=str(lower), residual_upper=str(residual),
                required_error=str(residual / lower) if lower > 0 else None,
                max_rational_bits=bits)


def precheck(data):
    p = parse(data)
    checks = [check(p['q'], O, c) for O, c in zip(p['O'], p['c'])]
    accepted = all(c['accepted'] for c in checks)
    if p['kind'] == 'feedback':
        accepted = accepted and p['error'] >= 0 and all(
            c['value'] == m and c['error'] <= p['error'] for c, m in zip(p['c'], p['m']))
    return accepted, checks


def rat(x):
    return f'({x.numerator} / {x.denominator} : ℚ)'


def vector(xs):
    return '![' + ', '.join(xs) + ']' if xs else '(fun i => Fin.elim0 i)'


def values(xs):
    return vector([rat(x) for x in xs])


def lean_candidate(c):
    return ('{ shift := ' + rat(c['shift']) + ', depth := ' + str(c['depth']) +
            ', order := ' + str(c['order']) + ', value := ' + rat(c['value']) +
            ', error := ' + rat(c['error']) + ' }')


def render(data, digest='unspecified'):
    p = parse(data)
    if not re.fullmatch(r'[A-Za-z0-9_-]+', digest):
        raise ValueError('invalid provenance digest')
    n, name = len(p['q']), p['name']
    header = f'''import LeanPhy.StatMech.GibbsCertificate

/- Untrusted generated candidates; all numerical acceptance is kernel checked.
   Input digest: {digest}. -/
namespace LeanPhy.Generated.GibbsCertificates.{name}

open LeanPhy.Mathematics LeanPhy.StatMech
open GibbsCertificate
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

'''
    if p['kind'] == 'expectation':
        body = f'''def exponents : Fin {n} → ℚ := {values(p['q'])}
def observable : Fin {n} → ℚ := {values(p['O'][0])}
def candidate : Candidate := {lean_candidate(p['c'][0])}

theorem accepted : candidate.Accepted exponents observable := by decide +kernel

theorem valid : ErrorCertificate (candidate.value : ℝ)
    (GibbsCertificate.expectation exponents observable) (candidate.error : ℝ) :=
  sound candidate exponents observable accepted

def envelope : CertificateEnvelope Candidate where
  metadata :=
    {{ producer := "gibbs_certificate.py"
      format := "rational-gibbs-v1"
      digest := "{digest}"
      source := "exact exponent and observable tables" }}
  payload := candidate

def certificate : VerifiedCertificate (checker exponents observable candidate) :=
  verifyEnvelope (checker exponents observable candidate) envelope ⟨rfl, accepted⟩
'''
    else:
        d = len(p['J'])
        body = f'''def action : Fin {n} → ℚ := {values(p['S'])}
def observables : Fin {d} → Fin {n} → ℚ := {vector([values(row) for row in p['A']])}
def bias : Fin {d} → ℚ := {values(p['J'])}
def coupling : Fin {d} → Fin {d} → ℚ := {vector([values(row) for row in p['K']])}
def point : Fin {d} → ℚ := {values(p['m'])}
def candidates : Fin {d} → Candidate := {vector([lean_candidate(c) for c in p['c']])}
def error : ℚ := {rat(p['error'])}

-- Exponents are derived from this model in Lean, not copied from Python.
theorem accepted : ∀ a, (candidates a).Accepted
    (exponent action observables (feedbackSource bias coupling point)) (observables a) :=
  by decide +kernel

theorem error_nonneg : 0 ≤ error := by decide +kernel
theorem values_match : ∀ a, (candidates a).value = point a := by decide +kernel
theorem errors_fit : ∀ a, (candidates a).error ≤ error := by decide +kernel

theorem valid : ErrorCertificate (fun a => (point a : ℝ))
    (SourceFeedback.feedback (fun i => (action i : ℝ)) (fun a i => (observables a i : ℝ))
      (fun a => (bias a : ℝ)) (fun a b => (coupling a b : ℝ)) (fun a => (point a : ℝ)))
      (error : ℝ) :=
  feedback_residual action observables bias coupling point candidates error
    error_nonneg values_match errors_fit accepted

theorem solution_bound
    (e : SourceFeedback.Envelope (fun a i => (observables a i : ℝ)) (fun a b => (coupling a b : ℝ)))
    (hsmall : e.rate < 1) :
    ErrorCertificate (fun a => (point a : ℝ))
      (e.solution (fun i => (action i : ℝ)) (fun a => (bias a : ℝ)) hsmall)
      ((error : ℝ) / (1 - e.rate)) :=
  e.solution_error _ _ hsmall _ _ valid
'''
    return header + body + f'\nend LeanPhy.Generated.GibbsCertificates.{name}\n'


def report(data, digest):
    p = parse(data)
    ok, checks = precheck(data)
    return dict(name=p['name'], kind=p['kind'], configurations=len(p['q']),
                outputs=len(p['c']), input_sha256=digest,
                status='candidate_requires_lean_check', exact_precheck=ok,
                certificates=checks,
                boundary='finite rational inputs; no solver, closure or thermodynamic-limit guarantee')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--force', action='store_true')
    args = parser.parse_args(argv)
    started = time.monotonic()
    try:
        raw = args.input.read_bytes()
        data = json.loads(raw)
        digest = hashlib.sha256(raw).hexdigest()
        summary = report(data, digest)
        if not summary['exact_precheck']:
            raise ValueError('candidate fails exact precheck; no output produced')
        source = render(data, digest)
        paths = [args.output] + ([args.report] if args.report else [])
        if len({p.resolve() for p in paths}) != len(paths):
            raise ValueError('source and report destinations must differ')
        if args.input.resolve() in {p.resolve() for p in paths}:
            raise ValueError('output cannot overwrite input')
        for path in paths:
            if path.exists() and not args.force:
                raise ValueError(f'output exists: {path}; use --force to replace it')
        summary['source_bytes'] = len(source.encode())
        summary['generation_seconds'] = time.monotonic() - started
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(source)
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(summary, indent=2) + '\n')
        print(json.dumps(summary))
        return 0
    except (ValueError, OSError) as error:
        print(f'gibbs certificate error: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
