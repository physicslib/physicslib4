# 1.0 pre-release review: shared brief for reviewers

Repository root: the current working directory (physicslib4). Lean 4 + Mathlib v4.34.1.
Project: formalization of algebraic QFT (Haag–Kastler axioms in Minkowski and curved spacetime,
GNS, spectral theorems, Stone's theorem, spacetime geometry). Read `.claude/CLAUDE.md` first.

## Hard rules

- **Read-only.** Do not modify any file in the repository except your own report file
  `notes/agents/review-1.0/<ID>.md`. No edits to `.tex`, `.lean`, `.md`, config. No git commands
  that change state. Scratch Lean experiments go in `/tmp` only (run from the repo root with
  `lake env lean /tmp/<file>.lean`), or use the `mcp__fuse__lean_*` tools (load them via
  ToolSearch, e.g. `select:mcp__fuse__lean_hover,mcp__fuse__lean_diagnostic_messages,mcp__fuse__lean_loogle`).
- Ignore `scratch_*` files and `notes/agents/` (other than this brief).
- **Write your report incrementally**: create the report file early and append findings as you go,
  so work survives an interruption. Finish with a summary section.
- Verify every finding against the current source before reporting it (quote the text or code).
  No speculative findings; if unsure, mark it `verdict: plausible` and say what would confirm it.

## Project conventions (findings if violated)

- The blueprint (`blueprint/src/sections/sec10/`) is the specification; Lean is checked against it.
- Definitions and the fields of axiom structures are design decisions: propose, never decide. Flag
  any finding that would change one as `protected: yes`.
- Only Chapter 10 is formalized; Chapters 1–9 are motivating context.
- Deliberate restrictions are recorded in the docstring on a line starting `**Restriction:**`.
- Documentation is in the present tense: no narrated history ("previously", "formerly", "now …",
  "no longer …", "(new)", "recently"), never "blog post". Positional references ("as we proved
  above") are fine. Lean/Mathlib versions appear only in `README.md`,
  `sec10/introduction.tex`, `home_page/index.md`.
- Blueprint tags `\lean{}`, `\leanok`, `\uses{}` must match the Lean code.

## What to probe (non-exhaustive; finding other kinds of issues is expected)

1. **Mathematical correctness of definitions** (blueprint and Lean): do they capture the intended
   notion? Look for vacuous or unsatisfiable conditions, junk-value traps (division by zero,
   `Classical.choose` on empty types, default values), wrong quantifier order, missing or
   superfluous hypotheses, universe restrictions, data vs. Prop confusion, conditions that make a
   structure trivially inhabited, mismatches with the standard literature (Haag, Hall,
   Reed–Simon, Murphy, Bratteli–Robinson, O'Neill, Hawking–Ellis), duplication of existing Mathlib
   notions.
2. **Blueprint–Lean harmony**: for each node in scope, compare the blueprint statement with the
   Lean signature (hypotheses, quantifiers, conclusion, generality, notation, names). Check
   `\uses{}` against what the Lean proof actually uses (missing or spurious edges), `\lean{}` names
   exist, `\leanok` is accurate, docstrings quote/paraphrase the blueprint faithfully and cite the
   right label.
3. **Theorem statements**: are they the right statements (not weakened or accidentally trivial)?
   Do hypotheses go unused (a sign of a wrong statement)?
4. **Prose quality** (blueprint, docstrings, comments, home page): clarity, awkward or convoluted
   constructions, run-on sentences, grammar, typos, undefined symbols, inconsistent notation or
   terminology across blueprint / Lean / web, LaTeX problems, wrong cross-references, stale or
   false claims, process text addressed to formalizers ("Do not re-derive…"), redundancy,
   present-tense violations.
5. **Lean code quality**: missing/inaccurate module and declaration docstrings, Mathlib naming
   conventions, unused hypotheses/variables/imports, dead or duplicate code, private helpers that
   duplicate Mathlib, `set_option` uses (especially `maxHeartbeats`,
   `backward.isDefEq.respectTransparency`), fragile proofs, unexplained `erw`/`convert`, bad
   `@[simp]` attributes, instance diamonds, deprecated API, file organization, linter warnings
   (use `mcp__fuse__lean_diagnostic_messages`).
6. **Home-page pages in scope**: item numbers, titles, Lean names and links consistent with the
   blueprint; descriptions accurate.

## Report format (`notes/agents/review-1.0/<ID>.md`)

Header: ID, scope, files read (with line ranges), date. Then findings, each as:

```
### <ID>-<n>. <short title>
- severity: blocker | major | minor | nit
- category: definition-correctness | statement-correctness | blueprint-lean-mismatch | stale-claim |
  uses-tags | prose | notation | lean-docstring | lean-style | lean-structure | home-page | other
- location: path:line (and the paired path:line, if a mismatch)
- protected: yes | no
- verdict: confirmed | plausible
- evidence: short quote(s)
- proposed fix: concrete
```

End with: counts by severity and category, the top 5 issues, and cross-cutting patterns you saw
(themes that a staged fix plan should group). Your final message back to the orchestrator: the
report path, the counts, and the top 5, in under 300 words.
