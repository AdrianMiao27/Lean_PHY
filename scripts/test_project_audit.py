#!/usr/bin/env python3
"""Exercise downstream research projects with real Lake builds and rejection cases."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import audit_project as audit

ROOT = Path(__file__).resolve().parents[1]
BUILD_ROOT = ROOT


class ProjectAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='leanphy-downstream-tests.')
        cls.base = Path(cls.temp.name)
        cls.project = cls.base/'research with spaces'
        result = subprocess.run([str(BUILD_ROOT/'.lake/build/bin/leanphy_init'), str(cls.project),
            '--name', 'downstream', '--profile', 'minimal', '--leanphy-path', str(BUILD_ROOT)],
            cwd=BUILD_ROOT, text=True, capture_output=True, timeout=30)
        if result.returncode:
            raise RuntimeError(result.stdout+result.stderr)
        # Reuse the exact already-installed dependency revisions without fetching.
        manifest = json.loads((BUILD_ROOT/'lake-manifest.json').read_text())
        manifest['name'] = 'downstream'
        for p in manifest['packages']:
            p['inherited'] = True
        manifest['packages'].insert(0, dict(type='path', scope='', name='LeanPhy',
            manifestFile='lake-manifest.json', inherited=False, dir=str(BUILD_ROOT), configFile='lakefile.toml'))
        (cls.project/'lake-manifest.json').write_text(json.dumps(manifest))
        (cls.project/'.lake').mkdir(exist_ok=True)
        (cls.project/'.lake/packages').symlink_to(BUILD_ROOT/'.lake/packages', target_is_directory=True)
        cls.original = {p: (cls.project/p).read_bytes() for p in ['Research.lean','Main.lean','lakefile.toml','lake-manifest.json']}

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def setUp(self):
        self.root = self.project
        for name in ['Research', 'src', 'other']:
            p = self.root/name
            if p.exists(): shutil.rmtree(p)
        for name, content in self.original.items():
            (self.root/name).write_bytes(content)
        for p in self.root.glob('result-*'):
            p.unlink()
        (self.root/'Research').mkdir()

    def source(self, name, text):
        p = self.root/name; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text)

    def cli(self, label='result-audit', script=False, timeout=240):
        report = self.root/(label+'.json'); log = self.root/(label+'.log')
        cmd = ['bash', str(self.root/'scripts/verify-leanphy.sh')] if script else [
            sys.executable, str(self.root/'scripts/audit_project.py'), '--project-root', str(self.root)]
        result = subprocess.run(cmd+['--report',str(report),'--log',str(log)],
            cwd=self.base, text=True, capture_output=True, timeout=timeout)
        return result, report, log

    def reject(self, expected, **kwargs):
        result, report, log = self.cli(**kwargs)
        output = result.stdout+result.stderr+(log.read_text() if log.exists() else '')
        self.assertNotEqual(result.returncode, 0, output)
        self.assertFalse(report.exists(), 'failure must not write a successful receipt')
        self.assertIn(expected, output)

    def test_scaffold_verifier_matches_source_and_zero_claim_report_is_preserved(self):
        self.assertEqual((self.root/'scripts/audit_project.py').read_bytes(), (ROOT/'scripts/audit_project.py').read_bytes())
        result, report, log = self.cli(script=True)
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        receipt = json.loads(report.read_text())
        self.assertEqual(set(receipt['modules']), {'Research','Main'})
        self.assertEqual(receipt['local_import_artifacts']['Main'][0][0],
                         str(self.root/'.lake/build/lib/lean/Main.olean'))
        self.assertEqual(receipt['status'], 'project_axiom_audit_passed')
        self.assertEqual(receipt['compiler_log_sha256'], audit.digest(log))
        projects = [json.loads(l) for l in result.stdout.splitlines() if l.startswith('{')]
        self.assertEqual(len(projects), 2)
        self.assertEqual(projects[0]['claim_count'], 0)
        self.assertEqual(projects[0]['open_obligation_count'], 1)

    def test_actual_physics_claim_and_physical_obligation_survive_project_verification(self):
        s = (self.root/'Research.lean').read_text()
        s = 'import LeanPhy.Quantum.Pauli\n'+s
        s = s.replace('def package : TheoryPackage :=', '''theorem pauli_product : LeanPhy.Quantum.pauliX * LeanPhy.Quantum.pauliY =
    Complex.I • LeanPhy.Quantum.pauliZ := LeanPhy.Quantum.pauliX_pauliY

def package : TheoryPackage :=''')
        s = s.replace('      "research project"\n', '''      "research project"
    |>.addTheoremWithAssumptions "Pauli product" "sigma_x sigma_y = i sigma_z"
      "Research.pauli_product" ["finite-model"] pauli_product
''')
        self.source('Research.lean', s)
        result, report, _ = self.cli(script=True)
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        self.assertGreater(json.loads(report.read_text())['audit']['theorems_audited'], 0)
        projects = [json.loads(l) for l in result.stdout.splitlines() if l.startswith('{')]
        self.assertEqual((projects[0]['claim_count'],projects[0]['open_obligation_count']), (1,1))
        self.assertEqual(projects[0]['status'], 'VERIFIED-CONDITIONAL')
        strict = subprocess.run(['lake','exe','downstream_check','--strict','--project-json'],
            cwd=self.root, text=True, capture_output=True, timeout=60)
        self.assertNotEqual(strict.returncode, 0)

    def test_unimported_module_in_other_namespace_is_built_and_audited(self):
        self.source('Research/Hidden.lean', 'namespace Elsewhere\nprivate theorem hidden : True := True.intro\nend Elsewhere\n')
        result, report, _ = self.cli()
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        data = json.loads(report.read_text())
        self.assertIn('Research.Hidden', data['modules'])
        self.assertIn('Research.Hidden', data['audit']['defining_modules'])
        self.assertGreaterEqual(data['audit']['private_declarations_audited'], 1)
        self.assertEqual(data['source_sha256'], audit.inventory(self.root)['source_sha256'])

    def test_unimported_private_axiom_is_rejected(self):
        self.source('Research/Hidden.lean', 'namespace Elsewhere\nprivate axiom missing_physics : False\nend Elsewhere\n')
        self.reject('missing_physics')

    def test_proof_hole_after_inline_audit_is_still_rejected(self):
        self.source('Research.lean', (self.root/'Research.lean').read_text()+'\ntheorem late_hole : False := by sorry\n')
        self.reject('sorryAx')

    def test_native_computation_in_unimported_module_is_rejected(self):
        self.source('Research/Native.lean', 'import Mathlib.Tactic\ntheorem result : (List.range 20).length = 20 := by native_decide\n')
        self.reject('.native_decide.ax_')

    def test_module_system_private_artifacts_are_included(self):
        self.source('Research/ModuleMode.lean', 'module\nprivate axiom hidden_module_assumption : False\n')
        self.reject('hidden_module_assumption')

    def test_executable_module_is_audited(self):
        self.source('Main.lean', (self.root/'Main.lean').read_text()+'\nprivate axiom executable_hole : False\n')
        self.reject('executable_hole')

    def test_broken_draft_fails_build_instead_of_disappearing(self):
        self.source('Research/Broken.lean', 'import MissingPhysicsModule\n')
        self.reject('MissingPhysicsModule')

    def test_nondefault_srcdir_is_derived_from_lake_configuration(self):
        for name in ['Research.lean','Main.lean']:
            target = self.root/'src'/name; target.parent.mkdir(exist_ok=True)
            (self.root/name).rename(target)
        config = (self.root/'lakefile.toml').read_text().replace('version = "0.1.0"','version = "0.1.0"\nsrcDir = "src"')
        self.source('lakefile.toml', config)
        result, report, _ = self.cli()
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        data = json.loads(report.read_text())
        self.assertEqual(data['source_directories'], ['src'])
        self.assertEqual(data['modules']['Research'], 'src/Research.lean')

    def test_source_change_during_compilation_rejects_receipt(self):
        self.source('Research/Mutation.lean', '''#eval IO.FS.writeFile "Research/Added.lean" "theorem added : True := True.intro\\n"
''')
        self.reject('changed during verification')

    def test_inventory_rejects_symlinks_duplicate_names_and_missing_configuration(self):
        self.source('Research/OK.lean', 'theorem good : True := True.intro\n')
        link = self.root/'Research/Link.lean'; link.symlink_to('OK.lean')
        with self.assertRaisesRegex(ValueError, 'symlinked Lean'): audit.inventory(self.root)
        link.unlink()
        (self.root/'Research/linked').symlink_to(self.base, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'symlinked source'): audit.inventory(self.root)
        (self.root/'Research/linked').unlink()
        self.source('other/Research.lean', 'theorem other : True := True.intro\n')
        with self.assertRaisesRegex(ValueError, 'duplicate module'): audit.inventory(self.root, [Path('.'),Path('other')])
        with self.assertRaisesRegex(ValueError, 'local, normalized'): audit.inventory(self.root,[self.base])
        self.source('lakefile.lean', '-- ambiguous configuration\n')
        try:
            with self.assertRaisesRegex(ValueError, 'exactly one'): audit.inventory(self.root)
        finally:
            (self.root/'lakefile.lean').unlink()

    def test_cli_preserves_outputs_and_rejects_invalid_timeouts(self):
        report = self.root/'result-keep.json'; report.write_text('keep')
        cmd = [sys.executable, str(self.root/'scripts/audit_project.py')]
        for args in [['--report',str(report)], ['--report',str(self.root/'same'),'--log',str(self.root/'same')],
                     ['--timeout','nan'],['--timeout','0'],['--timeout','inf']]:
            result = subprocess.run(cmd+args, cwd=self.root, text=True, capture_output=True, timeout=10)
            self.assertNotEqual(result.returncode, 0, result.stdout+result.stderr)
        self.assertEqual(report.read_text(), 'keep')

    def test_scaffold_refuses_missing_verifier_and_refreshes_copy_from_declared_dependency(self):
        dest = self.base/'resource copy'; dep = self.base/'fake dependency'; (dep/'scripts').mkdir(parents=True,exist_ok=True)
        exe = str(BUILD_ROOT/'.lake/build/bin/leanphy_init')
        cmd = [exe,str(dest),'--leanphy-path','../fake dependency']
        failed = subprocess.run(cmd,cwd=self.base,text=True,capture_output=True,timeout=30)
        self.assertNotEqual(failed.returncode,0); self.assertFalse(dest.exists())
        path = dep/'scripts/audit_project.py'; path.write_text('# version one\n')
        subprocess.run(cmd,cwd=self.base,check=True,capture_output=True,timeout=30)
        self.assertEqual((dest/'scripts/audit_project.py').read_text(),path.read_text())
        (dest/'notes.txt').write_text('keep research notes')
        path.write_text('# version two\n')
        self.assertNotEqual(subprocess.run(cmd,cwd=self.base,capture_output=True,timeout=30).returncode,0)
        subprocess.run(cmd+['--force'],cwd=self.base,check=True,capture_output=True,timeout=30)
        self.assertEqual((dest/'scripts/audit_project.py').read_text(),path.read_text())
        self.assertEqual((dest/'notes.txt').read_text(),'keep research notes')

    def test_all_profiles_generate_audited_projects_without_fabricated_claims(self):
        exe = str(BUILD_ROOT/'.lake/build/bin/leanphy_init')
        for profile in ['minimal','quantum','optics','fluid','physics','research']:
            dest = self.base/('profile-'+profile)
            subprocess.run([exe,str(dest),'--profile',profile,'--leanphy-path',str(BUILD_ROOT)],
                check=True,capture_output=True,timeout=30)
            source = (dest/'Research.lean').read_text()
            self.assertIn('#leanphy_audit_module',source)
            self.assertIn('|>.addPackage package)',source)
            self.assertIn('audit_project.py', (dest/'scripts/verify-leanphy.sh').read_text())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--build-root',type=Path,default=ROOT)
    args, rest = parser.parse_known_args(); BUILD_ROOT = args.build_root.resolve()
    unittest.main(argv=[sys.argv[0]]+rest)
