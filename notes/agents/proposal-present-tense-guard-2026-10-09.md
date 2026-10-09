# Proposal: keep the documentation in the present tense (Stage 8 of the 1.0 plan)

Date: 2026-10-09. Status: **proposal only.** Nothing below is applied. `.claude/CLAUDE.md` is the
user's file, and adding the CI step changes the repository's checks; both need the user's go-ahead.

## 1. CLAUDE.md rule

Proposed addition to `.claude/CLAUDE.md`, under "## Intent", after the `**Restriction:**` bullet:

```markdown
- Write documentation and comments (blueprint prose, Lean docstrings and comments, the home page,
  the README) in the present tense, describing what the project is. Do not narrate history:
  no "recently completed", "previously", "formerly", "now …", "no longer …", "(new)", or
  references to earlier versions, and never call the documentation a blog post. Record changes
  in `CHANGELOG.md` instead. References to earlier parts of the same text ("as we previously
  proved") are fine.
- State the targeted Lean and Mathlib versions only in `README.md`, `blueprint/src/sections/sec10/introduction.tex`
  and `home_page/index.md` ("Contributing"). Elsewhere, claims about what Mathlib provides carry no
  version.
```

## 2. CI check

### Script: `scripts/check_temporal_wording.py` (new file)

It scans `blueprint/src/sections`, `Physicslib4`, `home_page` and `README.md`, skipping
`scratch_*` files. It fails on two things:
- temporal wording, matched against a conservative pattern list that is deliberately narrower than
  the Stage 7 audit search, so that positional prose such as "as we previously proved" never
  triggers it;
- a `v4.x.y` version string outside the three designated homes.

Tested on 2026-10-09: it passes on `numina/release-1.0-docs`, and it fails, naming file and line,
on a planted "Recently completed" and a stray "Mathlib v4.31.0".

```python
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
```

### CI step: append to `.github/workflows/lean_action_ci.yml`, job `build`

```yaml
      - name: Check documentation is in the present tense
        run: python3 scripts/check_temporal_wording.py
```

### Notes

- The pattern list errs on the side of missing things rather than false alarms. Wording it does
  not match ("is no longer an option", "the decision has been taken") still depends on review and
  the CLAUDE.md rule.
- `notes/agents/` and `CHANGELOG.md` are outside its scope by design: both are historical records.
