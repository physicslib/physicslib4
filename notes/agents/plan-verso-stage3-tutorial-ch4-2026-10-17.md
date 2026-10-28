# Plan: tutorial chapter 4, "Doing it yourself"

Follows chapters 1–3 (`413c929`, `97568b2`, `a98e8c3`). The audience, style rules, exercise format
and writer–reviewer–your-read process are the same as for chapters 1–3.

## Decisions recorded (2026-10-17)

1. Worked project: try option A (a state on the trivial net's quasilocal algebra) first; fall back to
   option B (pullback along a local inclusion) if A is not feasible.
2. The contribution process is the README's (a branch, a pull request against `main`, passing checks,
   an approving review), plus a `CHANGELOG.md` entry for notable changes.
3. AI-assisted tools are left out.
4. The Contributing sections of `README.md` and `home_page/index.md` are shortened to point to
   chapter 4.

## Goal

Chapters 1–3 are read in the browser. Chapter 4 moves the reader onto their own machine. A reader
finishes able to:

- build the library;
- run and change the tutorial's examples;
- state a new result, find the API they need, and prove it;
- record it in the blueprint the way the project does;
- open a pull request that passes CI.

Chapter 2 defers "running the exercises locally" to this chapter, and chapter 3 points here for a
project: building a state on a net's quasilocal algebra with `GNS.State.comp`.

## Sections

1. **Setting up.**
   - Install Lean through elan, then `git clone`.
   - `lake exe cache get` (Mathlib's prebuilt files), then `lake build`. Say how long each step takes.
   - VS Code with the Lean 4 extension, and the infoview: goals, hovers, errors.
   - Opening a library file and the tutorial's own Lean files. Running a chapter's exercise by copying
     it into a scratch file.
   - Builds on the Contributing steps in `home_page/index.md` and `README.md`, which this section
     replaces or expands. Keep the two in agreement.
2. **How the project is organised.**
   - The blueprint is the specification; the Lean is checked against it.
   - Only Chapter 10 is formalised.
   - The directory layout: `Physicslib4/`, `blueprint/src/`, `web/`, `home_page/`.
   - Conventions:
     - definitions and axiom structures are design decisions: propose changes, don't just make them;
     - `**Restriction:**` lines record deliberate restrictions;
     - documentation is written in the present tense;
     - the build has no `sorry`.
3. **From an idea to a statement.**
   - Start from the blueprint: write the informal statement with `\label`, `\uses` and, once the Lean
     exists, `\lean` and `\leanok`.
   - Translate it into a Lean statement with `sorry`, in the right file and namespace.
   - Check that the statement means what you intend before proving it.
4. **Finding the API.**
   - `#check`, `exact?`, `apply?` and `rw?`.
   - Loogle, for searching by the shape of a type.
   - The API docs, and the blueprint's links to the Lean.
   - Searching the Mathlib sources.
   - A worked search for a lemma this library uses, showing each tool's output.
5. **Proving it.**
   - Working interactively: read the goal, take a step, repeat.
   - Breaking a proof into lemmas.
   - Common errors: type class problems, universe mismatches, coercions. Each with an example the
     reader has already met in chapters 2–3.
6. **The worked project.** A state on a net's quasilocal algebra, built with `GNS.State.comp`
   (`GNS/ExtremeState.lean:489`, which needs a `*`-homomorphism into an algebra that has a state).
   - Carried out in full in the chapter: the statement, the search for the API, the proof, and how it
     would be recorded in the blueprint.
   - Option A: for the trivial net, if a `*`-homomorphism from `trivialHaagKastlerNet.quasilocal` to ℂ
     can be built, or obtained from the library. **Feasibility unknown; the writer checks this first.**
   - Option B, as a fallback: pull back a state along a local inclusion $`\iota_{\mathbf{B}}`$, or
     along the covariance map, which uses only API that certainly exists.
7. **Checking and contributing.**
   - The checks CI runs, and how to run them locally:
     - `lake build` and `lake lint`;
     - `checkdecls` for the blueprint's Lean names;
     - `scripts/check_temporal_wording.py`;
     - `leanblueprint web` and `pdf`;
     - the Verso site and tutorial build.
   - A branch, a pull request against `main`, and review.
   - Where to ask for help: the Lean Zulip and the repository's issues.
8. **Where to go next.**
   - Open directions in the blueprint and the `**Restriction:**` lines (each names what it waits on).
   - The reference manual, once it exists.
   - Further reading, pointing back to chapter 2's list.

Each section ends with one or two exercises with collapsible solutions. Exercises that need a local
setup say so. Target length: 4,000–5,000 words.

## Notes and risks

- **Running the examples in CI.** Commands such as `lake build` can't run in the browser, so they
  appear as plain code blocks. Lean examples are still checked by Verso.
- **Keeping commands current.** Commands and versions must stay true. The Lean and Mathlib version
  appears only in the three places the project allows, so the chapter refers to `lean-toolchain`
  instead of naming a version.
- **Local tooling.** The lean-kit guard and the agent tooling are local to the maintainer. They are
  not part of the contributor workflow, and the chapter does not mention them.
- **Agreement with other docs.** The Contributing text in `README.md` and `home_page/index.md` must
  agree with section 1. The plan is to make those two point to chapter 4.

## Questions for you

1. **Worked project:** try option A (a state on the trivial net's quasilocal algebra) and fall back to
   B if it isn't feasible, or go straight to B?
2. **Contribution process:** is the README's process (branch, pull request against `main`, passing
   checks, one approving review) the one to teach? Is there anything else contributors must do, such
   as recording changes in `CHANGELOG.md`?
3. **AI-assisted proving:** the tools exist, but the chapter currently leaves them out. Should it
   mention them in one paragraph, or leave them out?
4. **README and home page:** should their Contributing steps be shortened to point to chapter 4?
