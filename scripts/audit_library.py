#!/usr/bin/env python3
"""Build and audit every LeanPhy source module, including unexported modules.

The report records an observed compiler/audit run, not a proof of physical
validity. Dependency artifacts and the installed Lean toolchain remain trusted.
An explicit mirror must match the source snapshot both before and after checking.
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

ROOT = Path(__file__).resolve().parents[1]
MARKER = 'LeanPhy dependency audit: '
FOUNDATIONS = {'propext', 'Classical.choice', 'Quot.sound'}


def snapshot(root: Path) -> dict[str, str]:
    files = [root/'LeanPhy.lean', *sorted((root/'LeanPhy').rglob('*.lean')),
             root/'lean-toolchain', root/'lakefile.toml', root/'lake-manifest.json']
    if not (root/'LeanPhy/Verification.lean').is_file():
        raise ValueError('source tree is missing LeanPhy/Verification.lean')
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}


def module_names(hashes: dict[str, str]) -> list[str]:
    modules = [p[:-5].replace('/', '.') for p in hashes if p.endswith('.lean')]
    if any(not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', m) for m in modules):
        raise ValueError('a library source path cannot be represented as a Lean module name')
    return sorted(modules)


def check_snapshot(root: Path, expected: dict[str, str]) -> None:
    actual = snapshot(root)
    changed = sorted(p for p in actual.keys() | expected.keys() if actual.get(p) != expected.get(p))
    if changed:
        raise ValueError('source snapshot mismatch: ' + ', '.join(changed))


def invoke(command: list[str], cwd: Path, timeout: float) -> tuple[int, str]:
    """Terminate this run's compiler process group on timeout or interruption."""
    with subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
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


def parse_summary(output: str) -> dict:
    lines = [line.split(MARKER, 1)[1] for line in output.splitlines() if MARKER in line]
    if len(lines) != 1:
        raise ValueError(f'expected one completed audit summary; found {len(lines)}')
    summary = json.loads(lines[0])
    if summary.get('status') != 'axiom_audit_passed':
        raise ValueError('audit did not report success')
    if type(summary.get('declarations_audited')) is not int or summary['declarations_audited'] <= 0:
        raise ValueError('audit selected no declarations')
    if set(summary.get('allowed_axioms', [])) != FOUNDATIONS or not set(summary.get('axioms_used', [])).issubset(FOUNDATIONS):
        raise ValueError('audit changed its permitted foundations')
    return summary


def run_audit(source_root: Path, build_root: Path, timeout: float, log_path: Path) -> dict:
    hashes = snapshot(source_root)
    check_snapshot(build_root, hashes)
    modules = module_names(hashes)
    source = ''.join(f'import {m}\n' for m in modules) + '\n#leanphy_audit_library\n'
    started = time.monotonic()
    with log_path.open('x', encoding='utf-8') as log:
        for label, command in [('toolchain', ['lake', 'env', 'lean', '--version']),
                               ('build', ['lake', 'build', *modules])]:
            print(f'Auditing library: {label} ({len(modules)} source modules)', flush=True)
            code, output = invoke(command, build_root, timeout)
            log.write(f'[{label}]\n{output}\n'); log.flush()
            if code != 0:
                raise ValueError(f'{label} failed with exit status {code}; see {log_path}')
            if label == 'toolchain':
                version = output.strip()
        with tempfile.TemporaryDirectory(prefix='leanphy-library-audit.') as tmp:
            path = Path(tmp)/'Audit.lean'; path.write_text(source, encoding='utf-8')
            code, output = invoke(['lake', 'env', 'lean', str(path)], build_root, timeout)
            log.write(f'[audit]\n{output}\n'); log.flush()
        if code != 0:
            raise ValueError(f'dependency audit failed with exit status {code}; see {log_path}')
        summary = parse_summary(output)
    check_snapshot(source_root, hashes)
    check_snapshot(build_root, hashes)
    return dict(status='library_axiom_audit_passed', audit=summary,
                source_root=str(source_root), build_root=str(build_root),
                imported_source_modules=modules, source_sha256=hashes,
                driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                audit_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest(),
                lean_version=version, elapsed_seconds=round(time.monotonic()-started, 3),
                scope='all declarations in all library source modules; transitive axiom dependencies',
                boundary='observed local compiler run; imported dependency artifacts and toolchain trusted; no physical-validity claim')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, default=ROOT)
    parser.add_argument('--build-root', type=Path)
    parser.add_argument('--report', type=Path, help='new JSON report path; existing files are never replaced')
    parser.add_argument('--log', type=Path, help='new compiler log path; existing files are never replaced')
    parser.add_argument('--timeout', type=float, default=1800, help='seconds allowed per compiler/build invocation')
    args = parser.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error('timeout must be positive and finite')
    try:
        source_root = args.source_root.resolve(); build_root = (args.build_root or source_root).resolve()
        outputs = [p.resolve() for p in (args.report, args.log) if p is not None]
        if len(outputs) != len(set(outputs)):
            raise ValueError('report and log paths must differ')
        if any(p.exists() for p in outputs):
            raise ValueError('report/log output already exists; choose new paths')
        log_path = args.log or Path(tempfile.mkdtemp(prefix='leanphy-library-audit-log.'))/'compiler.log'
        result = run_audit(source_root, build_root, args.timeout, log_path)
        if args.report:
            with args.report.open('x', encoding='utf-8') as f:
                json.dump(result, f, indent=2); f.write('\n')
        audit = result['audit']
        print(f'LeanPhy full dependency audit passed: {audit["declarations_audited"]} declarations, '
              f'{audit["private_declarations_audited"]} private; {len(result["imported_source_modules"])} source modules.')
        print(f'Compiler log: {log_path}')
        return 0
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f'LeanPhy library audit failed: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
