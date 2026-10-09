# Plan: remove backward-looking wording for the 1.0 release

Date: 2026-10-08. Proposed branch: `numina/release-1.0-docs` off `numina/aqft-in-lean`.
Status: **done 2026-10-09 (Stage 8 proposal awaiting approval; no tag, not pushed).**

## Decisions (user, 2026-10-08)

- **D1 approved:** keep positional references ("as we previously proved", "recall", "we are now
  in a position").
- **D2 approved:** add `CHANGELOG.md`, with a "Pre-1.0 development notes" section for the
  history removed from the docs.
- **D3 not approved, replaced.** A warning, note or remark whose referent is an earlier version
  of the project is removed entirely, not restated. This covers "an earlier version of this
  blueprint claimed …", and any caution that exists only because something was once wrong. The
  reader cannot reach that referent without git history or the CHANGELOG. Mathematical content
  that stands on its own and is needed by the surrounding text stays, stated plainly with no
  reference to the past. The retraction may be recorded in the CHANGELOG (D2).
- **D4 approved:** design rationale for rejected alternatives stays, rewritten as present-tense
  "Design note" text.
- **D5 replaced.** No wording may call the documentation a "blog post", in any tense. The
  documentation is referred to as what it is: "this blueprint", "this chapter", "Section~\ref{…}",
  or "the project web page" / "the home page" for the website. Sentences that point to a
  blog post ("As proven in this blog post", "In a subsequent blog post we will detail …") are
  rewritten to point at the corresponding part of the blueprint, or removed.
- **D6 replaced.** All version-dated tool claims are removed ("Mathlib (at `v4.31.0-rc1`) …" and
  the like); any claim that is still true is restated undated. Each form of documentation states
  the targeted versions in exactly one place:
  - **code:** `README.md` (Lean toolchain and Mathlib v4.34.1, as pinned by `lean-toolchain` and
    `lakefile.toml`);
  - **blueprint:** one sentence in the Chapter 10 introduction (`sec10/introduction.tex`);
  - **web:** one line on the home page (`index.md`, in "Contributing").

  Stage 7 checks by grep that no other version string remains in docstrings, blueprint prose or
  home-page text. The Mathlib version strings in `lake-manifest.json`, `lakefile.toml`,
  `lean-toolchain` and CI configuration are configuration, not documentation, and are untouched.
- **D7 approved:** `notes/agents/` is out of scope.
- **D8 replaced.**
  - The "Recently completed" blocks on `index.md` are replaced by a present-tense "Highlights"
    section with new content, not the current text. It has exactly four highlights:
    1. the Haag–Kastler axioms for Minkowski spacetime;
    2. the Haag–Kastler axioms for Lorentzian (curved) spacetime;
    3. the spectral theorem for bounded self-adjoint operators;
    4. the spectral theorem for unbounded self-adjoint operators.

    Each highlight is a short present-tense description with its blueprint nodes and principal Lean
    declarations.
  - The axioms-page change list becomes "Design notes".
  - "(new)" and "a new layer" (and similar) are dropped from the section pages.
- **No v1.0 tag.** Other changes must land before 1.0. Stage 9 is merge only: no tag, and no
  push unless asked.

## Goal

Present the documentation and code comments as a first-time reader meets them at 1.0. They
should describe what the project *is*, in the present tense, with no narration of how it got
there. This covers the blueprint (all chapters), Lean docstrings and comments, and the home page.

The change is prose only. No Lean statement, definition, proof, blueprint label, `\lean{}`,
`\uses{}` or `\leanok` changes.

## What counts as "backward-looking"

The distinction that matters is temporal versus positional.

- **Remove or rewrite (temporal).** Text that refers to an earlier *version* of the project, or to
  a change between versions:
  - change notices: "Recently completed: …", "The new §10.4 …", "(new)", "a new subsection",
    "is now a theorem", "now carries / supplies / consumes …", "no longer …";
  - history: "previously carried …", "formerly …", "was withdrawn", "an earlier version of this
    blueprint claimed …", "the former Axiom 4", "Two changes … for readers coming from an earlier
    version";
  - process narration: "the decision has been taken", "an option still under consideration",
    "This node previously carried …".
- **Keep (positional).** References to an earlier *place* in the same text, which are ordinary
  mathematical prose: "as we previously proved", "recall that …", "we are now in a position to …".
  The grep finds many of these (`spectral-theorems.tex` alone has eight "previously proved"). They
  are deliberately left alone. See D1 for an optional tightening.
- **Rewrite in the present tense (rationale).** Design rationale stays, because it is useful to
  every reader, but it is stated as a fact about the design, not as a decision story.
  - Example: "\emph{The rejected alternative, and why it is rejected.} The alternative was …"
    becomes "\emph{Design note: why the quasilocal algebra is constructed rather than assumed.}
    One could instead …".

## Size (measured 2026-10-08)

A grep for typical temporal phrases ("recently", "previously", "earlier version", "no longer",
"formerly", "withdrawn", "is now", "the new", "an earlier", "the former" and similar) finds about
110 matches in 30 files. Some are positional and stay.

- **Blueprint:** about 59 matches in 13 files. They concentrate in
  `sec10/haag-kastler-axioms.tex` (17), `sec10/spectral-theorems.tex` (9, mostly positional),
  `sec10/spacetime.tex` (7), `sec10/unbounded-spectral-theorems.tex` (6) and the curved chapter
  (4). Chapters 0 and 9 have a few each, mostly positional.
- **Lean:** about 25 matches in 12 files, mostly `AQFT/HaagKastler/{QuasilocalAlgebra,Net}.lean`
  and `AQFT/HaagKastlerCurved/Net.lean`. Examples: "This structure formerly carried its own
  `inclusion` family …", "the former Axiom 4".
- **Home page:** about 26 matches in 5 files. Examples:
  - `index.md`: "Recently completed: …" (three blocks) and the status prose;
  - `axioms.md`: "Three changes to the axioms are worth calling out for readers coming from an
    earlier version";
  - `sec10-*.md`: "(new)", "a new layer", "a new subsection".
- **Related time-relative wording:**
  - Version-dated tool claims, e.g. `Spacetime/Basic.lean`: "Mathlib (at `v4.31.0-rc1`) does not
    provide …", although the project now pins v4.34.1.
  - The blog-post origin of the text: Chapter 10 says "As proven in this blog post …" and "In a
    subsequent blog post we will detail these axioms".
  - "Formalization note" paragraphs, some of which narrate history ("This node previously
    carried …"). Others are useful present-tense notes and stay.

The grep is only a seed. Wording such as "That was withdrawn", "the decision has been taken" or
"is no longer an option" varies too much to match, so Stage 1 is a full read of the affected files.

## Decisions needed

**D1. Positional references.**
- (a) **Recommended:** keep "as we previously proved", "recall", "we are now in a position" and
  similar. They are standard mathematical writing, not history.
- (b) Also tighten them to explicit cross-references ("by Lemma~\ref{…}") wherever the target is
  a labelled node. This means more edits but crisper text.

**D2. Preserve the history somewhere.**
- (a) **Recommended:** add a top-level `CHANGELOG.md`. Its "Pre-1.0 development notes" section
  collects the substantive history removed from the docs, for example:
  - Axiom 4 split into the existence theorem and the bridge principle;
  - isotony supplying its embeddings as data;
  - Axiom 3 restated in a common containing diamond;
  - positive energy lifted to unbounded generators;
  - Stone's theorem added.

  Returning readers can still find it, and the docs stay clean. A "1.0" entry starts the
  changelog proper.
- (b) No changelog; rely on git history.

**D3. Retracted claims.** Example: "An earlier version of this blueprint claimed that any two
C*-norms on a *-algebra coincide, which is that false statement."
- **Recommended:** keep the mathematical warning in the present tense ("A *-algebra can carry
  more than one C*-norm; the full and reduced norms on ℂ[F₂] are an example …"), drop the history,
  and record the retraction in the CHANGELOG (D2).

**D4. Design rationale for rejected alternatives.**
- (a) **Recommended:** keep it as a present-tense "Design note".
- (b) Remove it, leaving only the chosen construction.

**D5. Blog-post wording.** Two time-relative sentences come from the blog origin:
"As proven in this blog post, these sharpened axioms entail the original axioms …" and "In a
subsequent blog post we will detail these axioms."
- **Recommended:** replace the forward reference with a cross-reference to Chapter 9 or §10.7,
  where the curved axioms now live. Keep the link to the blog post only as a citation ("as shown in
  [blog post]"), without "this" or "subsequent".
- Stage 1 lists every blog-related sentence for you to approve.

**D6. Version-dated tool facts.** Example: "Mathlib (at `v4.31.0-rc1`) does not provide …".
- **Recommended:** re-check each claim against the pinned Mathlib.
  - Where it is still true: state it undated, but name the pinned version once in the README or
    blueprint introduction ("the project builds against Mathlib v4.34.1").
  - Where it is no longer true (for example, the Mathlib v4.34.1 covariant-derivative API): rewrite
    to describe the current situation.

**D7. `notes/agents/`.** Plans, audits and scout memos are inherently historical. Some are
committed, some untracked.
- (a) **Recommended:** out of scope for the rewrite. They are internal working records. Either
  keep them, or move them out of the release branch (an `internal` branch, or delete with git
  history as the record). Your call on which.
- (b) Rewrite them too. Not recommended, because their whole purpose is history.

**D8. Home-page structure.** The landing page has "Recently completed" blocks (density theorem,
Stone's theorem, inverse musical isomorphism) and the axioms page has a "changes worth calling out"
list.
- **Recommended:**
  - replace the blocks with a present-tense "Highlights" section that describes three or four
    notable results as facts, without "recently";
  - turn the axioms-page list into "Design notes" (isotony as data, Axiom 3 in a containing diamond,
    Axiom 4 as a bridge principle plus existence theorem), stated as how the axioms are, not how
    they changed;
  - drop "(new)" and "a new layer" from the section pages;
  - the substance moves to `CHANGELOG.md` (D2).

## Stages

Each stage is committed on the branch. No Lean code or blueprint statement changes, which is
checked in Stage 7.

### Stage 1: inventory (read-only)

- One agent per area (blueprint Chapter 10, blueprint Chapters 0–9, Lean, home page) reads every
  file that has a seed match, plus a skim of the remaining files in the area, so that phrasing the
  grep cannot catch is found too.
- The output is `notes/agents/inventory-backward-looking-2026-10-08.md`: a table of file:line, the
  quoted phrase, a category (change notice / history / process / retraction / rationale /
  version-dated / blog / positional-keep) and a proposed action (delete / present-tense rewrite /
  keep / to CHANGELOG).
- You review the inventory by category, plus every item in Chapters 0–9, which are your text.

### Stage 2: CHANGELOG (if D2(a))

- Write `CHANGELOG.md` from the inventory items marked "to CHANGELOG", grouped by topic:
  axioms, operator theory, spacetime geometry, documentation. Link to the relevant blueprint
  labels.
- Present tense for the 1.0 entry; past tense is natural inside the pre-1.0 notes.

### Stage 3: blueprint, Chapter 10 (writer, then reviewer)

- Per file, in decreasing order of density: `haag-kastler-axioms.tex`, `spacetime.tex`,
  `unbounded-spectral-theorems.tex`, `haag-kastler-axioms-in-curved-spacetime.tex`,
  `spectral-theorems.tex`, then the rest.
- Apply the inventory actions: present-tense rewrites, rationale as "Design note", retraction
  warnings per D3, blog wording per D5.
- Labels, statements, `\lean`, `\uses` and `\leanok` must not change.
- The reviewer checks that:
  1. no temporal wording remains;
  2. no mathematical content was lost or changed;
  3. no statement or proof text changed apart from history sentences inside proofs;
  4. the "Formalization note" paragraphs that stay are present tense.

### Stage 4: blueprint, Chapters 0–9 (your text)

- Proposals only, with exact old → new wording for each item, collected in a memo.
- Applied after your approval, as was done for Chapter 5 in the Axiom 3 plan.
- Positional wording is kept, per D1.

### Stage 5: Lean docstrings and comments

- `lean-simplifier`, docstrings and comments only. Mathlib style: describe what the declaration
  is and why it is shaped that way, never what it used to be.
- Re-check each version-dated Mathlib claim against `.lake/packages/mathlib` (D6).
- The diff must touch only `/-! … -/`, `/-- … -/` and `--` lines. A script checks this by
  comparing the files with comments stripped.

### Stage 6: home page and other repository docs

- `index.md`, `axioms.md`, `guide.md` and the section pages, per D8.
- `README.md`: check it, and name the pinned Lean and Mathlib versions once, per D6.
- `home_page/_config.yml` descriptions.
- Rebuild locally with Jekyll and check links, as in earlier refreshes.

### Stage 7: verification

- `lake build`, `lake lint`, `checkdecls`, a PDF build (no errors, no overfull lines) and a web
  build.
- A comment-stripped diff of `Physicslib4/` against the branch point must be empty: no code
  changed.
- A blueprint check that the set of labels and every `\lean` / `\uses` / `\leanok` line is
  unchanged since the branch point, by script.
- A final grep with the seed patterns plus an allowlist of the kept positional phrases, so every
  remaining match is accounted for.

### Stage 8: keep it that way

- Add one rule to `.claude/CLAUDE.md` (your file; proposal only): "Write documentation and comments
  in the present tense, describing what is. Record changes in `CHANGELOG.md`, not in the docs."
- Optional: a small CI step that runs the seed grep with the allowlist and fails on new temporal
  wording.

### Stage 9: merge and release

- Merge into `numina/aqft-in-lean`.
- **Do not tag v1.0** (user decision: other changes come first). Push and the PR to `main` only
  when asked.

## Risks

- **Losing information.** History that is also substance can be lost, e.g. "the former Axiom 4
  conflated a bridge principle with an existence claim". Mitigation: the inventory marks every
  deletion, D2 keeps it in the CHANGELOG, and the Stage 3 reviewer checks for lost content.
- **Chapters 0–9 are your text.** They are proposal-only.
- **False positives.** Positional wording is kept per D1, and the Stage 7 allowlist makes every
  kept phrase explicit.

## Estimate

- Stage 1: 4 parallel read-only agents.
- Stages 3–6: about 110 seeded items plus whatever the read-through finds. Most are one-sentence
  rewrites; perhaps 15 are paragraph-level, such as the home-page blocks, the "rejected
  alternative" note and the retracted-claim note.
- Stages 7–8 are mechanical.

## Progress log

(empty)
- 2026-10-09, Stage 1 done: five read-only inventories in `notes/agents/inventory-1.0/`
  (A–E, about 214 action items; summary and open decisions in `inventory-1.0/README.md`). Coverage gap:
  `spectral-theorems.tex` and the second half of `unbounded-spectral-theorems.tex` were only
  grep-checked; re-read before Stage 3. Several stale or false doc statements were found (listed in
  the README) and will be corrected in the present tense in Stages 3, 5 and 6.
- 2026-10-09, The four user-approved Chapter 5/9 edits applied (20670c2): prologue "as we have seen
  previously" removed; "not yet available in Mathlib" → "that Mathlib does not provide"; stray
  "Clarification." deleted; "As shown in earlier in this blueprint" → Section~\ref{sctn:all-observables-of-interest}.
  Stage 4 therefore has no remaining Chapter 0–9 items.
- 2026-10-09, Stage 2 done: `CHANGELOG.md` (repository root) with "Unreleased" and "Pre-1.0
  development notes", grouped as axioms, quasilocal algebra, operator theory, spacetime geometry,
  toolchain, and documentation/web page, built from the five inventories' "To CHANGELOG" lists
  (file:line pointers dropped; current labels and Lean names kept).
- 2026-10-09, Stage 3 done: four parallel writers rewrote Chapter 10 (haag-kastler-axioms; curved +
  general covariance + GNS + introduction; spacetime + Stone; bounded + unbounded spectral after a
  full re-read that found 4 more items). The single blueprint version sentence was added to
  `sec10/introduction.tex` (Lean and Mathlib v4.34.1). The stale "not yet formalized" claim was
  removed, and a false Mathlib claim at spacetime.tex ≈1772 was corrected. Reviewer REVISE → four
  fixes applied (design-note count, two Mathlib paths, "composition", an orphaned sentence).
  Checks: no \label/\lean/\uses/\leanok/\begin/\end line changed (git diff check), validate shows
  only the 14 pre-existing conv: errors, PDF builds with no errors and no overfull lines, web
  builds. Stage 4 has nothing left (Chapters 0–9 were done in 20670c2).
- 2026-10-09, Stage 5 done: three lean-simplifier agents rewrote docstrings and comments in 30 files
  (AQFT/HaagKastler + AQFT top level; HaagKastlerCurved, GNS, Analysis, Operators, Spectral;
  Spacetime, Geometry). The third agent hit its turn limit during its final grep; the orchestrator
  completed that check. Factual corrections: HaagKastlerNet bundles Axioms 2, 3 and 5 (no Axiom 4
  field; Axiom 6 not adopted), GNS `H : Type u`, `isBasisSet_smul` is an interface field,
  `IsScalarTower ℝ ℂ (A →L[ℂ] ℂ)` resolves (only `LocallyConvexSpace` is missing), KMS strip-
  Liouville is proved, LorentzCone sign lemma exists, stale "towards …" titles fixed. Leftover
  "-- (extracted by Fuse golfer)" markers removed everywhere. Checks: a comment-stripped
  comparison against HEAD shows code unchanged in all 30 files; no Lean/Mathlib version strings
  remain in Physicslib4/; build and lint clean; residue = 3 positional uses (CStarCompletion "the
  former" = first of two items; QuasilocalAlgebra quotes the blueprint's "as previously proven").
- 2026-10-09, Stage 6 done:
  - index.md: the three "Recently completed" blocks are replaced by a new "## Highlights" section,
    placed before Formalisation status, with exactly the four D8 entries (Minkowski HK axioms;
    Lorentzian HK axioms; bounded spectral theorem, Thm 162; unbounded spectral theorem, Thm 285),
    each with sections, item numbers and principal Lean names. The Axiom 5 remark is undated. The
    single web version line is in Contributing.
  - axioms.md: the change list is now "## Design notes" (three present-tense notes).
  - guide.md: duplicate lead-in removed; Definition 678 → 677.
  - Section pages: all change notices removed ("(new)", "A new layer", "A new block", "now …",
    "earlier versions …", "Axiom 4 is now split"); the sec10-6 bicommutant typo is fixed; the
    "Mathlib lacks / itself has only / does not supply" remarks are dropped in favour of
    project-centric wording.
  - mathjax.html and the _config.yml comments are fixed.
  - README: present-tense heading and wording, the single code version line (v4.34.1) in Getting
    Started, "started June 2026" removed (it is in the CHANGELOG). The forward-looking "Scope"
    section is kept.
  - Jekyll builds 11 pages with no broken links; all 665 entries check.
- 2026-10-09, Stage 7 done (verification against branch point c0e1c24):
  - lake build and lake lint clean.
  - Comment-stripped comparison: code unchanged in all 30 changed Lean files.
  - Blueprint: the same 662 labels, no `\lean`/`\uses`/`\leanok`/`\label`/`\proves`/`\begin`/`\end`
    line changed in any file (proof blocks included).
  - PDF has 0 errors, 0 overfull boxes and 0 undefined references; web builds; checkdecls passes;
    Jekyll builds 11 pages with no broken links (Stage 6).
  - Version strings: exactly three, one per form (sec10/introduction.tex, home_page/index.md,
    README.md).
  - Final wording search: 23 hits, all positional or logical (e.g. "as we previously proved",
    "we are now in a position", "the former … the latter").
  - Fixed: `QuasilocalAlgebra.lean`'s quotation of `def:quasilocal-algebra` was stale ("As
    previously proven …"); it now quotes the current statement.
  - Noted, not changed: several module docstrings paraphrase their blueprint statement in Lean
    notation rather than quoting verbatim. They contain no temporal wording.
- 2026-10-09, Stage 8 done (proposal only): `notes/agents/proposal-present-tense-guard-2026-10-09.md`
  contains the CLAUDE.md wording (present tense; versions in three places), the script
  `scripts/check_temporal_wording.py` (tested: passes on the branch, fails on planted violations)
  and the CI step for lean_action_ci.yml. None of it is applied, pending the user's approval.
- 2026-10-09, Stage 9: merged into numina/aqft-in-lean. No tag, no push.
- 2026-10-09, Stage 8 applied: scripts/check_temporal_wording.py + CI step committed on numina/aqft-in-lean; CLAUDE.md rule added locally (.claude/ is untracked).
