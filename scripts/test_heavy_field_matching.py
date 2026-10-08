#!/usr/bin/env python3
"""Compare coupled heavy-field expansions with independent exact differentiation.

SymPy differentiates concrete polynomial profiles in coordinate space. Lean
evaluates the public jet operations at the corresponding derivative data. The
oracle never supplies an equation, matching identity or trusted proof to Lean.
"""
import argparse
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile
import unittest

import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
BUILD_ROOT = ROOT
HEADER = '''import LeanPhy.FieldTheory.HeavyFieldInterval
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
open LeanPhy.FieldTheory LeanPhy.FieldTheory.PropagatingHeavy
open scoped Matrix ContDiff
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
@[simp] theorem deriv_num {R : Type} [CommRing R] [Algebra ℝ R]
    (D : Derivation ℝ R R) (n : ℕ) [n.AtLeastTwo] : D (ofNat(n)) = 0 := D.map_natCast n
'''

EXPAND = '''Model.field, reconstruct, inverseApprox, Finset.sum_range_succ,
    pow_succ, Module.End.mul_apply, LinearMap.sum_apply, Model.massOperator,
    massUnit, massHom, massMap, Model.kineticOperator, kinetic, gradientFlux,
    jetModel, Fin.sum_univ_succ, Derivation.leibniz, JetPolynomial.totalDerivative_jet,
    JetPolynomial.jet, JetPolynomial.totalDerivative, smul_eq_mul, Algebra.smul_def'''


INTERVAL_REGRESSION = r'''import LeanPhy.FieldTheory.HeavyFieldInterval
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open LeanPhy.FieldTheory LeanPhy.FieldTheory.PropagatingHeavy
open scoped ContDiff Matrix
noncomputable def bm : Model (JetPolynomial ℝ Unit Unit) Unit Unit :=
  jetModel 1 (by intro i j; cases i; cases j; rfl)
    (fun _ _ _ _ => 1) (by intros; rfl)
noncomputable def source : Unit → JetPolynomial ℝ Unit Unit := fun _ => JetPolynomial.jet () 0
def profile : Unit → ℝ → ℝ := fun _ t => t
theorem smooth : ∀ i, ContDiff ℝ ∞ (profile i) := fun _ => contDiff_id
theorem boundary_action : Interval.action profile smooth bm 1 0 1 0 source (bm.field 1 1 source) = 1/3 := by
  change (∫ t in (0:ℝ)..1, CurveJet.evaluate profile t (bm.density 1 0 source (bm.field 1 1 source))) = _
  have heval (t : ℝ) : CurveJet.evaluate profile t (bm.density 1 0 source (bm.field 1 1 source)) =
      1/2 - t^2/2 := by
    norm_num [Model.density, Model.gradientPair, pair, Model.field, reconstruct, inverseApprox,
      Module.End.mul_apply, LinearMap.sum_apply, Model.massOperator, massUnit, massHom,
      massMap, gradientFlux, bm, jetModel, source, CurveJet.evaluate, JetPolynomial.jet,
      JetPolynomial.totalDerivative, Derivation.leibniz, profile, iteratedDeriv_id,
      smul_eq_mul, Algebra.smul_def]
    have hd : deriv (profile ()) t = 1 := by change deriv id t = 1; simp
    rw [hd]
    ring
  simp_rw [heval]
  have hc : IntervalIntegrable (fun _ : ℝ => (1/2:ℝ)) MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  have hq : IntervalIntegrable (fun t : ℝ => t^2/2) MeasureTheory.volume 0 1 :=
    (show Continuous (fun t : ℝ => t^2/2) by fun_prop).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hc hq]
  simp only [div_eq_mul_inv, intervalIntegral.integral_mul_const]
  norm_num [integral_pow]
theorem boundary_effective : Interval.effectiveAction profile smooth bm 1 1 0 1 0 source = -1/6 := by
  change (∫ t in (0:ℝ)..1, CurveJet.evaluate profile t (bm.effective 1 1 0 source)) = _
  have heval (t : ℝ) : CurveJet.evaluate profile t (bm.effective 1 1 0 source) = -t^2/2 := by
    norm_num [Model.effective, pair, Model.field, reconstruct, inverseApprox,
      Module.End.mul_apply, LinearMap.sum_apply, Model.massOperator, massUnit, massHom,
      massMap, bm, jetModel, source, CurveJet.evaluate, JetPolynomial.jet,
      profile, smul_eq_mul, Algebra.smul_def]
    ring
  simp_rw [heval]
  simp only [div_eq_mul_inv, intervalIntegral.integral_mul_const, intervalIntegral.integral_neg]
  norm_num [integral_pow]
theorem boundary_residual (t : ℝ) : CurveJet.evaluate profile t (bm.residual 1 source (bm.field 1 1 source) ()) = 0 := by
  norm_num [Model.residual, equation, operator, Model.field, reconstruct, inverseApprox,
    Module.End.mul_apply, LinearMap.sum_apply, Model.massOperator, massUnit, massHom,
    massMap, Model.kineticOperator, kinetic, gradientFlux, bm, jetModel, source,
    CurveJet.evaluate, JetPolynomial.jet, JetPolynomial.totalDerivative,
    profile, iteratedDeriv_id, smul_eq_mul, Algebra.smul_def]

  change iteratedDeriv 2 id t = 0
  simp [iteratedDeriv_id]

theorem boundary_difference :
    Interval.action profile smooth bm 1 0 1 0 source (bm.field 1 1 source) -
      Interval.effectiveAction profile smooth bm 1 1 0 1 0 source = 1/2 := by
  rw [boundary_action, boundary_effective]
  norm_num
#print axioms boundary_action
#print axioms boundary_effective
#print axioms boundary_residual
#print axioms boundary_difference
'''

def rat(q):
    q = sp.Rational(q)
    return f'({q.p} / {q.q} : ℝ)'


def vector(xs):
    return '![' + ', '.join(xs) + ']'


def matrix(rows):
    return '!![' + '; '.join(', '.join(r) for r in rows) + ']'


def polynomial(expr, fields):
    pieces = []
    for powers, c in sp.Poly(expr, *fields).terms():
        factors = [f'MvPolynomial.C {rat(c)}']
        factors += [f'(JetPolynomial.jet {i} 0) ^ {p}' for i, p in enumerate(powers) if p]
        pieces.append('(' + ' * '.join(factors) + ')')
    return ' + '.join(pieces) or '0'


def cases():
    rng = random.Random(577215)
    for h, f, d, order in [(1, 1, 1, 0), (1, 1, 1, 1), (1, 1, 1, 3),
                            (2, 1, 1, 2), (2, 2, 1, 2), (2, 2, 2, 2), (3, 2, 1, 2)]:
        coords = sp.symbols(f't0:{d}')
        fields = sp.symbols(f'x0:{f}')
        profiles = [sp.Integer(i + 1) + sum((i + j + 1) * t + t * t / 2
                    for j, t in enumerate(coords)) for i in range(f)]
        if d > 1:
            profiles[-1] += coords[0] * coords[1]
        a = sp.Matrix(h, h, lambda i, j: rng.randrange(-1, 2) if i <= j else 0)
        mass = a * a.T + sp.eye(h)
        inv = mass.inv()
        z = sp.zeros(h * d)
        for p in range(h * d):
            for q in range(p, h * d):
                z[p, q] = z[q, p] = rng.randrange(-1, 2) + fields[(p + q) % f]
        source = sp.Matrix([fields[i % f] ** 2 + (i + 1) * fields[(i + 1) % f] + 1 for i in range(h)])
        replace = dict(zip(fields, profiles))
        z_actual, j_actual = z.subs(replace), source.subs(replace)
        epsilon = sp.Rational(1, h + 2)

        def kinetic(v):
            return sp.Matrix([sp.expand(sum(sp.diff(sum(z_actual[i*d+mu, j*d+nu] *
                   sp.diff(v[j], coords[nu]) for j in range(h) for nu in range(d)), coords[mu])
                   for mu in range(d))) for i in range(h)])

        term, solution = inv * j_actual, sp.zeros(h, 1)
        for k in range(order):
            solution -= epsilon ** k * term
            term = inv * kinetic(term)
        solution = solution.applyfunc(sp.expand)
        residual = mass * solution - epsilon * kinetic(solution) + j_actual
        effective = 7 + (solution.dot(j_actual)) / 2
        gradient = sum(z_actual[i*d+mu, j*d+nu] * sp.diff(solution[i], coords[mu]) *
                       sp.diff(solution[j], coords[nu]) for i in range(h) for j in range(h)
                       for mu in range(d) for nu in range(d))
        density = 7 + (solution.dot(mass * solution) + epsilon * gradient) / 2 + solution.dot(j_actual)
        at_origin = {t: 0 for t in coords}
        yield dict(h=h, f=f, d=d, order=order, fields=fields, profiles=profiles, coords=coords,
                   mass=mass, inv=inv, z=z, source=source, epsilon=epsilon,
                   solution=solution.subs(at_origin), residual=residual.subs(at_origin),
                   effective=effective.subs(at_origin), density=density.subs(at_origin))


def lean_case(c, k):
    h, f, d = c['h'], c['f'], c['d']
    out = [f'namespace Differential{k}', f'abbrev P := JetPolynomial ℝ (Fin {f}) (Fin {d})']
    out.append(f'noncomputable def mass : (Matrix (Fin {h}) (Fin {h}) ℝ)ˣ :=\n  ⟨' +
               matrix([[rat(v) for v in c['mass'].row(i)] for i in range(h)]) + ', ' +
               matrix([[rat(v) for v in c['inv'].row(i)] for i in range(h)]) + ',\n' +
               '    by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ],\n' +
               '    by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]⟩')
    nested = vector([vector([vector([vector([polynomial(c['z'][i*d+mu,j*d+nu], c['fields'])
                        for nu in range(d)]) for mu in range(d)]) for j in range(h)]) for i in range(h)])
    out.append(f'noncomputable def z : Fin {h} → Fin {h} → Fin {d} → Fin {d} → P := {nested}')
    out.append('noncomputable def model : Model P (Fin ' + str(h) + ') (Fin ' + str(d) + ') :=\n' +
               '  jetModel mass (by intro i j; fin_cases i <;> fin_cases j <;> rfl) z\n' +
               '    (by intro i j μ ν; fin_cases i <;> fin_cases j <;> fin_cases μ <;> fin_cases ν <;> rfl)')
    out.append(f'noncomputable def source : Fin {h} → P := ' +
               vector([polynomial(v, c['fields']) for v in c['source']]))
    samples = []
    for i, profile in enumerate(c['profiles']):
        branches = []
        for powers, coefficient in sp.Poly(profile, *c['coords']).terms():
            value = coefficient * sp.prod(sp.factorial(p) for p in powers)
            cond = ' ∧ '.join(f'p.2 {j} = {p}' for j, p in enumerate(powers))
            branches.append(f'if {cond} then {rat(value)} else ')
        samples.append(''.join(branches) + '0')
    out.append('noncomputable def sample : P →+* ℝ := MvPolynomial.eval (fun p => ' + vector(samples) + ' p.1)')
    eps, n = rat(c['epsilon']), c['order']
    for label, expr, values in [
        ('field', f'model.field {eps} {n} source', c['solution']),
        ('residual', f'model.residual {eps} source (model.field {eps} {n} source)', c['residual'])]:
        for i, value in enumerate(values):
            out.append(f'theorem {label}{i} : sample ({expr} {i}) = {rat(value)} := by\n' +
                       '  norm_num [sample, model, mass, z, source, Model.residual, equation, operator,\n' +
                       '    ' + EXPAND + ']\n' + f'#print axioms {label}{i}')
    # A separate computation of the original kinetic energy tests the matching signs.
    if k in (1, 3):
        for label, expr in [('effective', f'model.effective {eps} {n} 7 source'),
                            ('density', f'model.density {eps} 7 source (model.field {eps} {n} source)')]:
            out.append(f'theorem {label} : sample ({expr}) = {rat(c[label])} := by\n' +
                       '  norm_num [sample, model, mass, z, source, Model.effective, Model.density,\n' +
                       '    Model.gradientPair, pair, ' + EXPAND + ']\n' + f'#print axioms {label}')
    out.append(f'end Differential{k}')
    return '\n'.join(out)


class HeavyFieldMatchingTests(unittest.TestCase):
    def compile(self, source):
        with tempfile.TemporaryDirectory(prefix='leanphy-heavy-regression.') as folder:
            p = Path(folder) / 'Check.lean'
            p.write_text(source)
            return subprocess.run(['lake', 'env', 'lean', str(p)], cwd=BUILD_ROOT,
                                  capture_output=True, text=True, timeout=360)

    def assert_compiles(self, source):
        result = self.compile(source)
        output = result.stdout + result.stderr
        self.assertEqual(result.returncode, 0, output)
        self.assertNotRegex(output, r'sorryAx|Lean\.ofReduceBool')

    def test_independent_differential_models(self):
        for k, c in enumerate(cases()):
            with self.subTest(heavy=c['h'], light=c['f'], directions=c['d'], order=c['order']):
                self.assert_compiles(HEADER + lean_case(c, k))

    def test_actual_interval_and_boundary(self):
        t = sp.Symbol('t')
        reconstructed, source = -t, t
        residual = reconstructed - sp.diff(reconstructed, t, 2) + source
        density = (reconstructed**2 + sp.diff(reconstructed, t)**2) / 2 + reconstructed * source
        matched = reconstructed * source / 2
        self.assertEqual(residual, 0)
        self.assertEqual(sp.integrate(density, (t, 0, 1)), sp.Rational(1, 3))
        self.assertEqual(sp.integrate(matched, (t, 0, 1)), -sp.Rational(1, 6))
        self.assert_compiles(INTERVAL_REGRESSION)

    def test_guide_snippets_compile(self):
        guide = (ROOT / 'docs/effective-theory.md').read_text()
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
