#!/usr/bin/env python3
"""Independent Decimal oracles, kernel rejection checks and physical consumers.

High-precision Decimal.exp is used only to select independent test outputs.
Each Lean proof derives its own rigorous bound from exact rational input data.
"""
import argparse
import copy
from decimal import Decimal as D, localcontext
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile
import unittest

import gibbs_certificate as gc
from run_negative_tests import classify

ROOT = Path(__file__).resolve().parents[1]
BUILD_ROOT = ROOT
METRICS = []
FIXTURE = ROOT / 'examples/gibbs-certificates/biased-feedback.json'


def dec(q):
    q = Q(q)
    return D(q.numerator) / D(q.denominator)


def oracle(q, O):
    with localcontext() as ctx:
        ctx.prec = 80
        weights = [dec(x).exp() for x in q]
        return sum((w * dec(a) for w, a in zip(weights, O)), D()) / sum(weights)


def sample(name, q, O, shift=0, depth=0, order=12):
    value = format(oracle(q, O), '.6f')
    return dict(name=name, kind='expectation', exponents=list(map(str, q)),
                observable=list(map(str, O)),
                candidate=dict(shift=str(shift), depth=depth, order=order,
                               value=value, error='1/100000'))


def feedback_case(number, d, n):
    rng = random.Random(34000 + number)
    S = [Q(rng.randrange(-2, 3), 8) for _ in range(n)]
    A = [[Q(rng.randrange(-2, 3), 2) for _ in range(n)] for _ in range(d)]
    J = [Q(rng.randrange(-2, 3), 8) for _ in range(d)]
    K = [[Q(rng.randrange(-2, 3), 64 * max(d, 1)) for _ in range(d)] for _ in range(d)]
    with localcontext() as ctx:
        ctx.prec = 80
        point = [D(0)] * d
        for _ in range(35):
            source = [dec(J[a]) + sum((dec(K[a][b]) * point[b] for b in range(d)), D())
                      for a in range(d)]
            q = [-dec(S[i]) + sum((source[a] * dec(A[a][i]) for a in range(d)), D())
                 for i in range(n)]
            w = [x.exp() for x in q]
            point = [sum((w[i] * dec(A[a][i]) for i in range(n)), D()) / sum(w)
                     for a in range(d)]
        m = [format(x, '.6f') for x in point]
    return dict(name=f'Feedback{number}', kind='feedback', action=list(map(str, S)),
                observables=[list(map(str, row)) for row in A], bias=list(map(str, J)),
                coupling=[list(map(str, row)) for row in K], point=m, error='1/100000',
                candidates=[dict(shift=0, depth=1, order=10, value=v, error='1/100000') for v in m])


class GibbsCertificateTests(unittest.TestCase):
    def compile(self, source):
        with tempfile.TemporaryDirectory(prefix='leanphy-gibbs-check.') as folder:
            p, timing = Path(folder)/'Check.lean', Path(folder)/'time.json'
            p.write_text(source)
            wrapper = ('import subprocess,sys,time,resource,json; from pathlib import Path; '
                       't=time.monotonic(); p=subprocess.run(sys.argv[2:]); '
                       'Path(sys.argv[1]).write_text(json.dumps(dict(seconds=time.monotonic()-t, '
                       'max_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss))); '
                       'sys.exit(p.returncode)')
            result = subprocess.run([sys.executable, '-c', wrapper, str(timing),
                                     'lake', 'env', 'lean', str(p)],
                                    cwd=BUILD_ROOT, text=True, capture_output=True, timeout=240)
            record = json.loads(timing.read_text())
            METRICS.append(dict(test=self._testMethodName, source_bytes=len(source.encode()),
                                exit_code=result.returncode, **record))
            return result

    def assert_compiles(self, source):
        result = self.compile(source)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotRegex(result.stdout + result.stderr, r'sorryAx|Lean\.ofReduceBool|declaration uses `sorry`')

    def assert_rejected(self, source):
        result = self.compile(source)
        self.assertIsNone(classify(result.returncode, result.stdout + result.stderr),
                          result.stdout + result.stderr)

    def test_scalar_enclosures_against_independent_exp(self):
        pieces = ['import LeanPhy.Mathematics.RationalExp\nopen LeanPhy.Mathematics\n'
                  'set_option maxRecDepth 16384\nset_option maxHeartbeats 4000000\n']
        for i, (q, depth, order) in enumerate([(Q(0),0,0), (Q(-1),0,12), (Q(1),0,12),
                                               (Q(-1,3),0,10), (Q(7,4),1,12), (Q(-9,4),2,12)]):
            with localcontext() as ctx:
                ctx.prec = 80
                value = Q(format(dec(q).exp(), '.6f'))
            error = Q(1,100000)
            pieces.append(f'''theorem scalar{i} : RationalExp.Accepted {gc.rat(q)} {depth} {order}
    {gc.rat(value)} {gc.rat(error)} := by decide +kernel
#print axioms scalar{i}
''')
        pieces.append('#print axioms RationalExp.sound\n')
        self.assert_compiles(''.join(pieces))

    def test_normalized_readouts_against_independent_exp(self):
        rng = random.Random(777)
        cases = [sample('One', [Q(-1,2)], [Q(-3,2)]),
                 sample('Shifted', [Q(201,2),Q(199,2),Q(100)], [Q(-2),Q(1),Q(3)], 100),
                 sample('RangeReduced', [Q(5,2),Q(-3,2)], [Q(-1),Q(2)], depth=2)]
        for n in (2,3,4,6):
            cases.append(sample(f'Varied{n}', [Q(rng.randrange(-8,9),8) for _ in range(n)],
                                [Q(rng.randrange(-6,7),3) for _ in range(n)]))
        for data in cases:
            with self.subTest(name=data['name']):
                self.assertTrue(gc.precheck(data)[0])
                self.assert_compiles(gc.render(data) +
                    f'\n#print axioms LeanPhy.Generated.GibbsCertificates.{data["name"]}.valid\n')

    def test_variable_models_feed_actual_residual_and_solution(self):
        for j,(d,n) in enumerate([(1,2),(2,3),(3,4),(2,1),(0,2)]):
            data = feedback_case(j,d,n)
            self.assertTrue(gc.precheck(data)[0])
            p = gc.parse(data)
            for a,m in enumerate(p['m']):
                self.assertLess(abs(oracle(p['q'],p['O'][a])-dec(m)),dec(p['error']))
            self.assert_compiles(gc.render(data) +
                f'\n#print axioms LeanPhy.Generated.GibbsCertificates.{data["name"]}.solution_bound\n')

    def test_model_output_and_budget_mutations_rejected_by_kernel(self):
        good = json.loads(FIXTURE.read_text())
        mutations=[]
        for field,value in [('error',0),('value',0)]:
            data=copy.deepcopy(good); data['candidates'][0][field]=value; mutations.append(data)
        for field,value in [('bias',[0]),('coupling',[[1]]),('action',[2,0]),('point',[0])]:
            data=copy.deepcopy(good); data[field]=value; mutations.append(data)
        data=sample('WrongObservable',[Q(1,2),Q(-1,2)],[1,-1])
        data['observable']=[-1,1]; mutations.append(data)
        for data in mutations:
            self.assertFalse(gc.precheck(data)[0])
            self.assert_rejected(gc.render(data))  # Deliberately bypass Python rejection.

    def test_denominator_range_and_rounding_boundaries(self):
        cases = [sample('NoPartition',[0],[1],order=0),
                 sample('Empty',[0],[1]), sample('BadRange',[Q(3,2)],[1]),
                 sample('Rounded',[Q(1,2),Q(-1,2)],[1,-1]),
                 sample('NegativeBudget',[0],[1])]
        cases[0]['exponents']=['1'] # center = 1, radius = 2, no positive lower bound
        cases[1]['exponents']=[];cases[1]['observable']=[]
        cases[3]['candidate']['error']=0
        cases[4]['candidate']['error']=-1
        for data in cases:
            self.assertFalse(gc.precheck(data)[0])
            self.assert_rejected(gc.render(data))
        exact=sample('Constant',[Q(1,2),Q(-1,2)],[Q(-3),Q(-3)])
        exact['candidate']['error']=0
        self.assertTrue(gc.precheck(exact)[0]);self.assert_compiles(gc.render(exact))

    def test_parser_and_reproducible_fixture(self):
        data=json.loads(FIXTURE.read_text()); digest=hashlib.sha256(FIXTURE.read_bytes()).hexdigest()
        self.assertEqual(gc.render(data,digest),
            (ROOT/'LeanPhy/Examples/Generated/BiasedFeedbackCertificate.lean').read_text())
        for x in (True,0.25,None,'1/0','NaN','1; axiom bad : False'):
            with self.assertRaises(ValueError):gc.rational(x)
        for patch in (dict(name='A.B'),dict(name='X\nend X'),dict(point=[]),dict(action=[]),
                      dict(coupling=[[1,2]]),dict(unexpected=1)):
            invalid=copy.deepcopy(data);invalid.update(patch)
            with self.assertRaises(ValueError):gc.parse(invalid)
        bad=copy.deepcopy(data);bad['candidates'][0]['depth']=64
        with self.assertRaises(ValueError):gc.parse(bad)
        with self.assertRaises(ValueError):gc.render(data,'x -/\naxiom forged : False')

    def test_cli_provenance_and_output_preservation(self):
        with tempfile.TemporaryDirectory(prefix='leanphy-gibbs-cli.') as folder:
            output, report=Path(folder)/'Candidate.lean',Path(folder)/'report.json'
            cmd=[sys.executable,str(ROOT/'scripts/gibbs_certificate.py'),str(FIXTURE),
                 '--output',str(output),'--report',str(report)]
            run=subprocess.run(cmd,text=True,capture_output=True)
            self.assertEqual(run.returncode,0,run.stderr)
            info=json.loads(report.read_text())
            self.assertEqual(info['status'],'candidate_requires_lean_check')
            self.assertEqual(info['input_sha256'],hashlib.sha256(FIXTURE.read_bytes()).hexdigest())
            original=output.read_bytes()
            self.assertNotEqual(subprocess.run(cmd,capture_output=True).returncode,0)
            bad=Path(folder)/'bad.json';data=json.loads(FIXTURE.read_text());data['error']=0
            bad.write_text(json.dumps(data));cmd[2]=str(bad)
            self.assertNotEqual(subprocess.run(cmd+['--force'],capture_output=True).returncode,0)
            self.assertEqual(output.read_bytes(),original)

    def test_guide_snippets_compile(self):
        snippets=re.findall(r'```lean\n(.*?)```',(ROOT/'docs/numerical-gibbs.md').read_text(),re.S)
        self.assertGreaterEqual(len(snippets),2)
        for snippet in snippets:self.assert_compiles(snippet)


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--build-root',type=Path,default=ROOT)
    parser.add_argument('--report',type=Path)
    args,rest=parser.parse_known_args()
    BUILD_ROOT=args.build_root
    result=unittest.main(argv=[sys.argv[0]]+rest,exit=False).result
    if args.report:
        args.report.write_text(json.dumps(dict(success=result.wasSuccessful(),checks=METRICS),indent=2)+'\n')
    sys.exit(0 if result.wasSuccessful() else 1)
