#!/usr/bin/env python3
"""Real compiler regressions for imported, private and transitive audit coverage."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import audit_library as audit

ROOT = Path(__file__).resolve().parents[1]
BUILD_ROOT = ROOT


class AxiomAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='leanphy-audit-test.')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.env = {**os.environ, 'LEAN_PATH': str(self.root) + os.pathsep + os.environ.get('LEAN_PATH', '')}

    def compile(self, name, source, export=False):
        path = self.root / (name.replace('.', '/') + '.lean')
        path.parent.mkdir(parents=True, exist_ok=True); path.write_text(source)
        cmd = ['lake', 'env', 'lean', '-R', str(self.root)]
        if export:
            cmd += ['-o', str(path.with_suffix('.olean'))]
        cmd.append(str(path))
        result = subprocess.run(cmd, cwd=BUILD_ROOT, env=self.env, text=True,
                                capture_output=True, timeout=180)
        output = result.stdout + result.stderr
        return result.returncode, output

    def exported(self, name, source):
        code, output = self.compile(name, source, True)
        self.assertEqual(code, 0, output)

    def rejected(self, source, reason):
        code, output = self.compile('Consumer', source)
        self.assertEqual(code, 1, output)
        self.assertIn('LeanPhy dependency audit', output)
        self.assertIn(reason, output)
        self.assertNotIn('"status":"axiom_audit_passed"', output)

    def test_imported_private_and_other_namespace_declarations_counted(self):
        self.exported('GoodFixture', '''import LeanPhy.Verification
namespace OutsideLeanPhy
private theorem internal_fact : 2 + 2 = 4 := rfl
theorem ordinary_fact : True := True.intro
theorem conditional_fact (P : Prop) (h : P) : P := h
end OutsideLeanPhy
''')
        code, output = self.compile('Consumer', '''import GoodFixture
#leanphy_audit_modules [GoodFixture]
''')
        self.assertEqual(code, 0, output)
        report = audit.parse_summary(output)
        self.assertEqual(report['declarations_audited'], 3)
        self.assertEqual(report['theorems_audited'], 3)
        self.assertEqual(report['private_declarations_audited'], 1)
        self.assertEqual(report['defining_modules'], ['GoodFixture'])

    def test_unused_imported_private_axiom_is_rejected(self):
        self.exported('BadFixture', '''import LeanPhy.Verification
namespace CompletelyUnrelated
private axiom unused_assumption : False
end CompletelyUnrelated
''')
        self.rejected('import BadFixture\n#leanphy_audit_modules [BadFixture]\n',
                      'unused_assumption')

    def test_imported_proof_hole_is_rejected(self):
        self.exported('BadFixture', '''import LeanPhy.Verification
namespace Outside
theorem unfinished : False := by sorry
end Outside
''')
        self.rejected('import BadFixture\n#leanphy_audit_modules [BadFixture]\n', 'sorryAx')

    def test_imported_native_decide_is_rejected(self):
        self.exported('BadFixture', '''import Mathlib.Tactic
import LeanPhy.Verification
theorem computed : (List.range 20).length = 20 := by native_decide
''')
        # Lean 4.34 emits a per-declaration native_decide axiom, not necessarily
        # the older Lean.ofReduceBool name. The whitelist must reject either form.
        self.rejected('import BadFixture\n#leanphy_audit_modules [BadFixture]\n', '.native_decide.ax_')

    def test_external_axiom_in_theorem_type_is_rejected_transitively(self):
        self.exported('ExternalPremise', 'axiom hidden_value : Nat\n')
        self.exported('SelectedFixture', '''import ExternalPremise
import LeanPhy.Verification
theorem depends_in_type : hidden_value = hidden_value := rfl
''')
        self.rejected('import SelectedFixture\n#leanphy_audit_modules [SelectedFixture]\n', 'hidden_value')

    def test_current_module_audit_catches_local_and_private_proof_holes(self):
        self.rejected('''import LeanPhy.Verification
private theorem incomplete : False := by sorry
#leanphy_audit_module
''', 'sorryAx')

    def test_explicit_hypotheses_and_standard_foundations_are_accepted(self):
        code, output = self.compile('Consumer', '''import LeanPhy.Verification
theorem assumed (P : Prop) (h : P) : P := h
theorem extensional (P Q : Prop) (h : P ↔ Q) : P = Q := propext h
noncomputable def selected (α : Type) (h : Nonempty α) : α := Classical.choice h
#leanphy_audit_module
''')
        self.assertEqual(code, 0, output)
        summary = audit.parse_summary(output)
        self.assertGreaterEqual(summary['declarations_audited'], 3)
        self.assertEqual(set(summary['axioms_used']), {'propext', 'Classical.choice'})

    def test_empty_selection_and_missing_module_are_rejected(self):
        self.rejected('import LeanPhy.Verification\n#leanphy_audit_module\n', 'empty declaration selection')
        self.rejected('import LeanPhy.Verification\n#leanphy_audit_modules [MissingFixture]\n', 'is not loaded')

    def test_module_prefix_does_not_mean_string_prefix(self):
        self.exported('SelectedFixture', 'import LeanPhy.Verification\ntheorem fine : True := True.intro\n')
        self.exported('SelectedFixtureOther', 'axiom unselected : False\n')
        code, output = self.compile('Consumer', '''import SelectedFixture
import SelectedFixtureOther
#leanphy_audit_modules [SelectedFixture]
''')
        self.assertEqual(code, 0, output)
        self.assertEqual(audit.parse_summary(output)['declarations_audited'], 1)

    def make_project(self):
        (self.root/'LeanPhy').mkdir()
        (self.root/'LeanPhy/Verification.lean').write_bytes((ROOT/'LeanPhy/Verification.lean').read_bytes())
        (self.root/'LeanPhy.lean').write_text('import LeanPhy.Verification\n')
        (self.root/'LeanPhy/Unexported.lean').write_text('namespace Outside\nprivate theorem fact : True := True.intro\nend Outside\n')
        (self.root/'lean-toolchain').write_bytes((ROOT/'lean-toolchain').read_bytes())
        (self.root/'lakefile.toml').write_text('name = "LeanPhy"\n[[lean_lib]]\nname = "LeanPhy"\n')
        result = subprocess.run(['lake', 'update'], cwd=self.root, text=True, capture_output=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_release_driver_includes_unexported_modules_and_records_source_hashes(self):
        self.make_project()
        result = audit.run_audit(self.root, self.root, 180, self.root/'audit.log')
        self.assertIn('LeanPhy.Unexported', result['imported_source_modules'])
        self.assertIn('LeanPhy.Unexported', result['audit']['defining_modules'])
        self.assertEqual(result['source_sha256'], audit.snapshot(self.root))
        self.assertEqual(result['status'], 'library_axiom_audit_passed')

    def test_release_driver_rejects_an_unexported_module_axiom(self):
        self.make_project()
        (self.root/'LeanPhy/Unexported.lean').write_text('namespace Outside\nprivate axiom missed_by_umbrella : False\nend Outside\n')
        with self.assertRaisesRegex(ValueError, 'dependency audit failed'):
            audit.run_audit(self.root, self.root, 180, self.root/'audit.log')
        self.assertIn('missed_by_umbrella', (self.root/'audit.log').read_text())

    def test_snapshot_rejects_changed_added_and_missing_sources(self):
        self.make_project(); snapshot = audit.snapshot(self.root)
        p = self.root/'LeanPhy/Unexported.lean'; before = p.read_bytes()
        p.write_text('theorem changed : True := True.intro\n')
        with self.assertRaisesRegex(ValueError, 'snapshot mismatch'): audit.check_snapshot(self.root, snapshot)
        p.write_bytes(before)
        extra = self.root/'LeanPhy/Extra.lean'; extra.write_text('')
        with self.assertRaisesRegex(ValueError, 'snapshot mismatch'): audit.check_snapshot(self.root, snapshot)
        extra.unlink(); p.unlink()
        with self.assertRaisesRegex(ValueError, 'snapshot mismatch'): audit.check_snapshot(self.root, snapshot)

    def test_summary_parser_rejects_empty_missing_duplicate_and_untrusted_summaries(self):
        valid = dict(status='axiom_audit_passed', declarations_audited=1,
                     allowed_axioms=sorted(audit.FOUNDATIONS), axioms_used=[])
        line = audit.MARKER + json.dumps(valid)
        self.assertEqual(audit.parse_summary(line), valid)
        for output in ['', line+'\n'+line, audit.MARKER+json.dumps({**valid,'declarations_audited':0}),
                       audit.MARKER+json.dumps({**valid,'axioms_used':['sorryAx']}),
                       audit.MARKER+json.dumps({**valid,'allowed_axioms':[]})]:
            with self.subTest(output=output), self.assertRaises(ValueError): audit.parse_summary(output)

    def test_cli_rejects_existing_and_aliased_outputs_and_invalid_timeout(self):
        path = self.root/'keep.json'; path.write_text('preserve')
        cmd = [sys.executable, str(ROOT/'scripts/audit_library.py')]
        for args in [['--report',str(path)], ['--report',str(self.root/'same'),'--log',str(self.root/'same')],
                     ['--timeout','nan'], ['--timeout','0'], ['--timeout','inf']]:
            result = subprocess.run(cmd+args, text=True, capture_output=True, timeout=10)
            self.assertNotEqual(result.returncode, 0, result.stdout+result.stderr)
        self.assertEqual(path.read_text(), 'preserve')

    def test_compiler_timeout_is_failure(self):
        with self.assertRaises(subprocess.TimeoutExpired):
            audit.invoke([sys.executable, '-c', 'import time; time.sleep(10)'], self.root, 0.05)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--build-root', type=Path, default=ROOT)
    args, rest = parser.parse_known_args(); BUILD_ROOT = args.build_root
    unittest.main(argv=[sys.argv[0]]+rest)
