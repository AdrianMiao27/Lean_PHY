#!/usr/bin/env python3
"""Run isolated negative Lean fixtures; infrastructure failures are not passes."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import threading


ERROR = re.compile(r"^.+:\d+:\d+: error(?:\([^\n]*\))?:", re.MULTILINE)
# A renamed API or malformed fixture must not masquerade as a rejected proof.
BROKEN_FIXTURE = re.compile(
    r"unknown (?:module prefix|identifier|constant|namespace)|"
    r"object file .* does not exist|failed to (?:import|load)|"
    r"unexpected (?:token|end of input)|invalid field|"
    r"not a field of structure|no such file or directory",
    re.IGNORECASE,
)
ACTIVE_GROUPS: set[int] = set()
ACTIVE_LOCK = threading.Lock()


def stop_active(_signum: int, _frame: object) -> None:
    with ACTIVE_LOCK:
        groups = list(ACTIVE_GROUPS)
    for group in groups:
        try:
            os.killpg(group, signal.SIGTERM)
        except ProcessLookupError:
            pass


def classify(returncode: int, output: str) -> str | None:
    if returncode == 0:
        return "invalid source unexpectedly compiled"
    if returncode != 1:
        return f"compiler failed with exit status {returncode}, not an elaboration rejection"
    if not ERROR.search(output):
        return "compiler failed without a source-located Lean error"
    if BROKEN_FIXTURE.search(output):
        return "broken import/API/syntax in fixture, not a verified safety rejection"
    return None


def check(source: Path, timeout: float) -> tuple[str, str | None, str]:
    try:
        with subprocess.Popen(
            ["lake", "env", "lean", str(source)], stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, encoding="utf-8",
            start_new_session=True,
        ) as process:
            with ACTIVE_LOCK:
                ACTIVE_GROUPS.add(process.pid)
            try:
                output, _ = process.communicate(timeout=timeout)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                output, _ = process.communicate()
                return source.stem, f"compiler timed out after {timeout:g}s", output
            finally:
                with ACTIVE_LOCK:
                    ACTIVE_GROUPS.discard(process.pid)
            return source.stem, classify(process.returncode, output), output
    except OSError as error:
        return source.stem, f"could not execute compiler: {error}", ""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sources", type=Path)
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--timeout", type=float, default=300)
    args = parser.parse_args()
    signal.signal(signal.SIGINT, stop_active)
    signal.signal(signal.SIGTERM, stop_active)
    if not 1 <= args.jobs <= 32 or args.timeout <= 0:
        parser.error("jobs must be in 1..32 and timeout must be positive")
    sources = sorted(args.sources.glob("*.lean"))
    if not sources:
        parser.error("no negative fixtures found")
    failures = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = [executor.submit(check, path, args.timeout) for path in sources]
        for future in as_completed(futures):
            label, error, output = future.result()
            if error is None:
                print(f"  [ok] rejected {label}", flush=True)
            else:
                failures += 1
                print(f"  [FAIL] {label}: {error}\n{output}", file=sys.stderr, flush=True)
    if failures:
        print(f"LeanPhy negative tests failed: {failures}/{len(sources)}.", file=sys.stderr)
        return 1
    print(f"LeanPhy negative elaboration tests passed. ({len(sources)} fixtures)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
