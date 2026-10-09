#!/usr/bin/env python3
"""Fail if documentation narrates project history instead of describing the project.

Scans blueprint prose, Lean comments/docstrings, the home page and the README for wording
that refers to earlier versions of the project. References to earlier places in the same
text ("as we previously proved") are allowed by the allowlist below.
"""
import re, sys, pathlib

ROOTS = ["blueprint/src/sections", "Physicslib4", "home_page", "README.md"]
EXTS = {".tex", ".lean", ".md", ".html"}
SKIP = re.compile(r"(^|/)(scratch_|_site/)")
PATTERN = re.compile(
    r"[Rr]ecently completed|[Ff]ormerly|earlier version|earlier draft|[Ww]as withdrawn"
    r"|was once|has since been|is now a theorem|now (carries|supplies|consumes)"
    r"|\(new\)|\bnew (layer|block|subsection|node)\b|[Nn]ewest|\bblog\b"
    r"|left for later|for the time being|v4\.\d+\.\d+-rc\d|Mathlib \(at"
    r"|\bthe former Axiom|has been (removed|replaced|split|renamed)"
)
# Version statements are allowed in exactly these places.
VERSION = re.compile(r"\bv4\.\d+\.\d+\b")
VERSION_HOMES = {"blueprint/src/sections/sec10/introduction.tex", "home_page/index.md", "README.md"}

def files():
    for r in ROOTS:
        p = pathlib.Path(r)
        for f in ([p] if p.is_file() else p.rglob("*")):
            if f.is_file() and f.suffix in EXTS and not SKIP.search(str(f)):
                yield f

bad = []
for f in files():
    for n, line in enumerate(f.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
        if PATTERN.search(line):
            bad.append(f"{f}:{n}: temporal wording: {line.strip()[:120]}")
        if VERSION.search(line) and str(f) not in VERSION_HOMES:
            bad.append(f"{f}:{n}: version string outside its single home: {line.strip()[:120]}")
print("\n".join(bad) if bad else "OK: no temporal wording or stray version strings.")
sys.exit(1 if bad else 0)
