# Pre-commit checklist for Lean work in physicslib4

Standing routine for the orchestrator and any specialist landing Lean changes.
Added 2026-09-18 after `lake lint` was found never to have been run: commits
`0ac363f` (previous session) and this session's commits all landed without it, and
the repo currently fails `lake lint` with 9 pre-existing errors.

## Run before every commit

1. `lake build` — must succeed. Note this also runs Mathlib's in-elaboration
   linters, because `lakefile.toml` sets `weak.linter.mathlibStandardSet = true`.
   That is NOT the same as step 2.
2. `lake lint` — the environment-linter pass (`lintDriver = "batteries/runLinter"`
   in `lakefile.toml`). Checks `unusedArguments`, `simpNF`, docstrings and 11 others.
   **Compare the error count against the pre-change baseline; do not just eyeball it.**
3. `lean_verify` on each new/changed theorem — axioms must be only `propext`,
   `Classical.choice`, `Quot.sound`. Anything else, especially `sorryAx`, is a stop.
4. `grep -c sorry` on each touched file — count must not rise.
5. `python3 ~/.claude/lean-kit/lean_guard.py check` — no protected changes.
   Two flags for untracked `.claude/CLAUDE.md` and `.claude/lean-policy.json` are
   pre-existing noise, present since before 2026-09-17; confirm they are not in the
   commit rather than assuming.
6. `lake exe mk_all` — only needed when a **new file** is added; adding declarations
   to an existing file does not require it. Always inspect `git diff Physicslib4.lean`
   afterwards rather than committing it blind: `mk_all` globs the tree and would add
   any `scratch_*.lean` to the root import list, which `.claude/CLAUDE.md` says to ignore.
7. `lake exe checkdecls blueprint/lean_decls` — after any `\lean{}` tag change.
   (`leanblueprint checkdecls` is a wrapper around this; the wrapper is not always on
   PATH. Regenerate `blueprint/lean_decls` with `leanblueprint web` first, or the check
   passes vacuously against a stale file.)

## Pitfalls actually hit

- **Never pipe a check into `tail`/`head` and read the exit code.** `lake lint | tail`
  reports `tail`'s status, not lint's. This produced a false "exit 0" on 2026-09-18 when
  `lake lint` was really exiting 1. Redirect to a file and check `$?`, or use `PIPESTATUS`.
- `lake lint` exits **1** when it reports errors, so it is CI-usable as-is.
- `ripgrep` is not installed on this machine: `lean_local_search` and `lean_verify`'s
  source-scan half degrade. Use `grep`.

## Not enforced automatically

There is no pre-commit hook (`.git/hooks/` has only stock `.sample` files) and no CI
workflow running lint. `.git/*`, `.github/*`, `.claude/*` and `CLAUDE.md` are protected
by `.claude/lean-policy.json`, so agents cannot add that enforcement — it must come from
a human. Suggested text to add to `.claude/CLAUDE.md` under `## Build`:

    - `lake lint` before committing; it exits 1 on findings. Current baseline: 9
      pre-existing `unusedArguments` errors. Do not let the count rise.
