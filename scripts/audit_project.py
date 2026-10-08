#!/usr/bin/env python3
"""Build and audit local research modules, including files omitted by the main import.

Requires Python 3.11+ and a Lake project depending on LeanPhy. This standalone
file is copied into projects by leanphy_init. Dependency binaries and the
installed toolchain are trusted; the JSON receipt is provenance, not a proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time
import tomllib

MARKER = 'LeanPhy dependency audit: '
FOUNDATIONS = {'propext', 'Classical.choice', 'Quot.sound'}
IGNORED_DIRS = {'.lake', '.git', '.venv', '__pycache__'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_directories(root, explicit=()):
    configs = [p for p in [root/'lakefile.toml', root/'lakefile.lean'] if p.is_file()]
    if len(configs) != 1:
        raise ValueError('project must have exactly one lakefile.toml or lakefile.lean')
    if explicit:
        paths = [root/p for p in explicit]
    elif configs[0].suffix == '.toml':
        config = tomllib.loads(configs[0].read_text(encoding='utf-8'))
        base = root/config.get('srcDir', '.')
        targets = config.get('lean_lib', []) + config.get('lean_exe', [])
        if not targets:
            raise ValueError('Lake configuration declares no Lean libraries or executables')
        paths = [base/t.get('srcDir', '.') for t in targets]
    else:
        raise ValueError('lakefile.lean requires explicit --source-dir arguments')
    roots = sorted(set(p.absolute() for p in paths))
    for p in roots:
        if not p.resolve().is_relative_to(root) or p.resolve() != p:
            raise ValueError('source directories must be local, normalized, non-symlink paths')
        if not p.is_dir():
            raise ValueError(f'source directory does not exist: {p}')
    return roots, configs[0]


def inventory(root, explicit=()):
    directories, config = source_directories(root, explicit)
    modules = {}; files = {}
    for directory in directories:
        for here, dirs, names in os.walk(directory, followlinks=False):
            base = Path(here)
            kept = []
            for name in sorted(dirs):
                p = base/name
                if name in IGNORED_DIRS or name.startswith('.') or p in directories:
                    continue
                if p.is_symlink():
                    raise ValueError(f'symlinked source directory is not supported: {p}')
                kept.append(name)
            dirs[:] = kept
            for name in sorted(names):
                p = base/name
                if not name.endswith('.lean') or p == root/'lakefile.lean':
                    continue
                if p.is_symlink():
                    raise ValueError(f'symlinked Lean source is not supported: {p}')
                module = '.'.join(p.relative_to(directory).with_suffix('').parts)
                if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', module):
                    raise ValueError(f'unsupported Lean module path: {p}')
                if module in modules:
                    raise ValueError(f'duplicate module name across source directories: {module}')
                modules[module] = str(p.relative_to(root)); files[str(p.relative_to(root))] = digest(p)
    if not modules:
        raise ValueError('no local Lean source modules found')
    for p in [config, root/'lean-toolchain', root/'lake-manifest.json']:
        files[str(p.relative_to(root))] = digest(p)
    return dict(modules=dict(sorted(modules.items())), source_sha256=dict(sorted(files.items())),
                source_directories=[str(p.relative_to(root)) for p in directories])


def invoke(command, root, timeout):
    with subprocess.Popen(command, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          text=True, encoding='utf-8', errors='replace', start_new_session=True) as p:
        try:
            output, _ = p.communicate(timeout=timeout)
        except BaseException:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            p.communicate()
            raise
        return p.returncode, output


def lean_name(module):
    return '.'.join(f'«{part}»' for part in module.split('.'))


def parse_summary(output):
    matches = [line.split(MARKER, 1)[1] for line in output.splitlines() if MARKER in line]
    if len(matches) != 1:
        raise ValueError(f'expected one audit result, got {len(matches)}')
    summary = json.loads(matches[0])
    if summary.get('status') != 'axiom_audit_passed' or type(summary.get('declarations_audited')) is not int or summary['declarations_audited'] <= 0:
        raise ValueError('audit must succeed with a nonempty declaration selection')
    if set(summary.get('allowed_axioms', [])) != FOUNDATIONS or not set(summary.get('axioms_used', [])).issubset(FOUNDATIONS):
        raise ValueError('audit result violates the permitted foundations')
    return summary


def artifact_setup(root, modules, timeout, log):
    """Resolve by source file, then pin imports to those exact Lake artifacts.

    Executable roots such as Main can collide with dependency modules even in
    `lake lean`; use the per-source setup and artifact queries, not LEAN_PATH.
    """
    targets = [f'{path}:{facet}' for path in modules.values() for facet in ['setup','olean']]
    code, output = invoke(['lake','--log-level=error','--json','query',*targets], root, timeout)
    log.write(f'[resolved module artifacts]\n{output}\n'); log.flush()
    if code != 0:
        raise ValueError('could not resolve the built local module artifacts')
    values = [json.loads(line) for line in output.splitlines() if line.strip()]
    if len(values) != 2*len(modules):
        raise ValueError('Lake did not return one setup and artifact per local source')
    setup = dict(name='LeanPhyProjectAudit', isModule=False, importArts={}, dynlibs=[], plugins=[], options={})
    local = {}; hashes = {}
    for i, module in enumerate(modules):
        config, artifact = values[2*i:2*i+2]
        if not isinstance(config, dict) or config.get('name') != module or not isinstance(artifact,str):
            raise ValueError(f'Lake resolved a different module for {modules[module]}')
        path = (root/artifact).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            raise ValueError(f'local artifact is missing or outside the project: {path}')
        parts = [str(path)]
        ir = []
        if config.get('isModule'):
            parts += [str(path)+'.server',str(path)+'.private']
            ir = [str(path.with_suffix('.ir.sig')),str(path.with_suffix('.ir'))]
        for p in parts+ir:
            hashes[str(Path(p).relative_to(root))] = digest(Path(p))
        local[module] = [parts] + ([ir] if ir else [])
        for name, arts in config.get('importArts', {}).items():
            previous = setup['importArts'].get(name)
            if previous is not None and previous != arts:
                raise ValueError(f'conflicting dependency artifacts for module {name}')
            setup['importArts'][name] = arts
        for key in ['plugins','dynlibs']:
            for entry in config.get(key,[]):
                if entry not in setup[key]: setup[key].append(entry)
    for module, arts in local.items():
        previous = setup['importArts'].get(module)
        if previous is not None and previous != arts:
            raise ValueError(f'local module {module} conflicts with a dependency import')
        setup['importArts'][module] = arts
    return setup, local, hashes


def run_audit(root, log_path, timeout=1800, explicit=()):
    before = inventory(root, explicit)
    modules = list(before['modules'])
    source = 'import LeanPhy.Verification\n' + ''.join(f'import {lean_name(m)}\n' for m in modules)
    source += '\n#leanphy_audit_modules [' + ', '.join(lean_name(m) for m in modules) + ']\n'
    started = time.monotonic()
    with log_path.open('x', encoding='utf-8') as log:
        for label, command in [('toolchain', ['lake', 'env', 'lean', '--version']),
                               ('build all sources', ['lake', 'build', *before['modules'].values()])]:
            print(f'Project audit: {label} ({len(modules)} local modules)', flush=True)
            code, output = invoke(command, root, timeout)
            log.write(f'[{label}]\n{output}\n'); log.flush()
            if code != 0:
                raise ValueError(f'{label} failed (exit {code}); see {log_path}')
            if label == 'toolchain':
                version = output.strip()
        setup, local_artifacts, artifact_hashes = artifact_setup(root, before['modules'], timeout, log)
        setup_text = json.dumps(setup, sort_keys=True)
        with tempfile.TemporaryDirectory(prefix='leanphy-project-audit.') as tmp:
            p = Path(tmp)/'Audit.lean'; p.write_text(source, encoding='utf-8')
            setup_path = Path(tmp)/'setup.json'; setup_path.write_text(setup_text, encoding='utf-8')
            code, output = invoke(['lake','env','lean',str(p),'--setup',str(setup_path)], root, timeout)
        log.write(f'[declaration audit]\n{output}\n'); log.flush()
        if code != 0:
            raise ValueError(f'declaration audit failed (exit {code}); see {log_path}')
        summary = parse_summary(output)
    if inventory(root, explicit) != before:
        raise ValueError('project sources or configuration changed during verification')
    if any(digest(root/path) != value for path,value in artifact_hashes.items()):
        raise ValueError('local compiled artifacts changed during verification')
    return dict(status='project_axiom_audit_passed', audit=summary, **before,
                project_root=str(root), lean_version=version,
                local_import_artifacts=local_artifacts, artifact_sha256=artifact_hashes,
                module_setup_sha256=hashlib.sha256(setup_text.encode()).hexdigest(),
                verifier_sha256=digest(Path(__file__)),
                audit_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                compiler_log_sha256=digest(log_path), elapsed_seconds=round(time.monotonic()-started, 3),
                scope='all local Lean source files under the recorded source directories; transitive declaration dependencies',
                boundary='installed toolchain and imported dependency artifacts trusted; explicit hypotheses and physical obligations remain')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project-root', type=Path, default=Path.cwd())
    parser.add_argument('--source-dir', type=Path, action='append', default=[],
                        help='explicit source root relative to project (repeatable); otherwise use Lake TOML srcDir fields')
    parser.add_argument('--report', type=Path, help='new receipt path; never overwrites an existing file')
    parser.add_argument('--log', type=Path, help='new compiler log path; never overwrites an existing file')
    parser.add_argument('--timeout', type=float, default=1800)
    args = parser.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error('timeout must be positive and finite')
    try:
        outputs = [p.resolve() for p in (args.report, args.log) if p is not None]
        if len(outputs) != len(set(outputs)) or any(p.exists() for p in outputs):
            raise ValueError('report and log must be distinct new paths')
        log = args.log or Path(tempfile.mkdtemp(prefix='leanphy-project-audit-log.'))/'compiler.log'
        result = run_audit(args.project_root.resolve(), log, args.timeout, args.source_dir)
        if args.report:
            with args.report.open('x', encoding='utf-8') as f:
                json.dump(result, f, indent=2); f.write('\n')
        print(f'LeanPhy project dependency audit passed: {result["audit"]["declarations_audited"]} declarations '
              f'in {len(result["modules"])} local modules.')
        print(f'Compiler log: {log}')
        return 0
    except (ValueError, OSError, subprocess.TimeoutExpired) as error:
        print(f'LeanPhy project audit failed: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    # Make SIGTERM take the same child-process cleanup path as Ctrl-C.
    signal.signal(signal.SIGTERM, lambda _sig, _frame: sys.exit(143))
    sys.exit(main())
