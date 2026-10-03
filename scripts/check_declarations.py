#!/usr/bin/env python3
"""Reject proof holes and custom axiom declarations outside Lean comments."""
from pathlib import Path
import re
import sys


def strip_comments(text: str) -> str:
    out = []
    i = 0
    block_depth = 0
    line = False
    string = False
    while i < len(text):
        if line:
            if text[i] == "\n":
                line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        if string:
            out.append(text[i])
            if text[i] == "\\" and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
            else:
                string = text[i] != '"'
                i += 1
            continue
        if text.startswith("--", i):
            line = True
            out.extend("  ")
            i += 2
        elif text.startswith("/-", i):
            block_depth = 1
            out.extend("  ")
            i += 2
        elif text[i] == '"':
            string = True
            out.append(text[i])
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


pattern = re.compile(r"\b(?:axiom|sorry|admit)\b")
failed = False
for root in (Path("LeanPhy"), Path("Main.lean"), Path("Prototype.lean"), Path("Check.lean")):
    paths = [root] if root.is_file() else sorted(root.rglob("*.lean"))
    for path in paths:
        clean = strip_comments(path.read_text(encoding="utf-8"))
        for match in pattern.finditer(clean):
            line = clean.count("\n", 0, match.start()) + 1
            print(f"{path}:{line}: forbidden token {match.group(0)}", file=sys.stderr)
            failed = True
if failed:
    raise SystemExit(1)
