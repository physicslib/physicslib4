# Tutorial chapter 2 ("Lean in brief"): progress log

Plan: `notes/agents/plan-verso-stage3-tutorial-ch2-2026-10-16.md`. Chapter file:
`web/Tutorial/LeanInBrief.lean`, included after chapter 1 in `web/Tutorial.lean`.

## Step 0: infrastructure (2026-10-16)

- **Lean blocks in the manual genre.** The chapter needs `open Verso.Genre.Manual.InlineLean` for the
  `lean`, `leanOutput` and `signature` code blocks. Blocks elaborate in the chapter module's own
  environment, so the chapter imports the library modules it uses (`import
  Physicslib4.AQFT.HaagKastler.Net`, etc.), as the website's `FrontPage.lean` does; no `leanInit`
  is needed. Declarations persist between blocks (`keep` defaults to true), so `open` in one block
  applies to the later ones, and exercise names must be unique (use `example`).
- **(a) `sorry`.** A plain ```` ```lean ```` block containing `sorry` builds: the manual genre
  makes non-error messages silent, so the "declaration uses `sorry`" warning does not fail the
  build; it is rendered as a wavy underline with a hover. `lean (name := x)` followed by
  ```` ```leanOutput x ```` shows the message text below the block (the build fails if the text
  differs, so the output stays current). A block that must fail uses `lean +error`; the build then
  fails if no error occurs. Tested: all three.
- **(b) Proof states.** Verso renders every tactic as a toggle (`Highlighted.tactics`): clicking
  it shows the goal *after* that tactic; this is the reference manual's mechanism. To show them
  without a click, a new `goals` directive in `web/Tutorial/Meta.lean` wraps a Lean block and sets
  the HTML option `codeOptions.visibleProofStates := .all`. Its CSS hides the redundant states of
  nested tactics (each rule of `rw [a, b]`) and the state at `by` (which repeats the statement).
  Tested on a three-tactic and a four-tactic proof; screenshots checked in headless Chrome.
- **Declarations that stay current.** `#check` + `leanOutput` (exact match, fails on drift);
  `{docstring Name}` renders a structure with its signature, docstring and fields (options
  `+hideStructureConstructor`, `+hideFields`); the `signature` code block checks a hand-wrapped
  signature against the declaration. For a `def` whose value is a `Prop`, an `example ... ↔ ... :=
  Iff.rfl` restates the body with readable line breaks and fails if the definition changes.
  `#print` output is not wrapped to the code width (`format.width` has no effect on messages), so
  it is avoided for long declarations.
- **Line length.** Verso warns on code lines over 60 columns (`verso.code.warnLineLength`); the
  chapter keeps code within 60 columns.
- **(c) Build time.** Elaborating the chapter file with the library import takes about 7.5 s
  (`lake env lean`), against 2.5 s for chapter 1: about 5 s more, mostly loading the library and
  Mathlib `.olean` files. The library itself is not rebuilt (`path = ".."`).

## Sections

| Section | Words (prose, approx.) | Build |
|---|---|---|
| Introduction | 157 | OK |
| 1. What a proof assistant does | 459 | OK (`+error` block, `sorry` warning, `#print axioms` output) |
| 2. Types and terms | 658 | OK (`#check` prints signatures in binder form; outputs adjusted) |
| 3. Propositions and proofs | 632 | OK (`≪[M, t]` needs parentheses before `∧`) |
| 4. Tactic proofs | 1022 | OK (both worked proofs in `goals` blocks; solutions too) |
| 5. Structures and type classes | 927 (plus rendered docstrings) | OK (`{docstring}` for LocalNet, Isotony, HaagKastlerNet; universe aside) |
| 6. Definitions that are propositions | 633 | OK (`signature` blocks; `Iff.rfl` restatements; State docstring; fixed one 62-column line in section 1) |
| 7. Mathlib and finding things | 604 | OK |
| 8. Further reading | 126 | OK (sections 7 and 8 written and built together) |

## Final state (2026-10-16)

- Reread for correctness and style, trimmed to about 4,500 prose words (5,040 counting every word
  inside inline code and maths). Per section, with inline code and maths counted as one word each:
  intro 157, 1: 432, 2: 587, 3: 526, 4: 771, 5: 864, 6: 496, 7: 522, 8: 126.
- Worked proofs (section 4, both in `goals` blocks): `LocalNet.mul_comm_algebra_empty` as
  `apply EquivLike.injective U.emptyEquivComplex; rw [map_mul, map_mul]; exact mul_comm _ _`
  (`EquivLike.injective` rather than the library's `.injective`, whose goal shows `toRingEquiv`);
  `causalDiamond_subset_of` with the library's proof (`intro`, `rw … at hx ⊢`, `rcases`, `exact`).
- Exercises: 11 (sections 1–7: 1, 1, 1, 2, 2, 2, 2), 9 of them in Lean with a `sorry` statement and
  a checked solution.
- `lake build` and `lake exe generate-tutorial --output _out/tutorial` succeed; the chapter has no
  warnings (`lake env lean Tutorial/LeanInBrief.lean`).

## For the reviewer

- `{docstring}` shows the library's own docstrings, written for developers (the `HaagKastlerNet.U`
  field text about universe polymorphism and bundling). The labels `def:local-algebras` etc. are
  highlighted as Lean code (`def` as a keyword) by the Markdown-to-Lean rendering, and long field
  types (e.g. `instCStarAlgebra`) are clipped at the box edge.
- `#check` outputs of more than 60 columns are shown unwrapped (message width is not configurable
  per block).
- The library's causal precedence `≺[M, t]` is the transitive closure of causal geodesic segments;
  chapter 1 defines `p ≺ q` to include `q = p`. The chapter makes no claim that depends on the
  difference, but a reader comparing the two may notice it.
- The `goals` directive (`web/Tutorial/Meta.lean`) relies on Verso's HTML classes (`.tactic`,
  `.tactic-state`) and on the `data-binding` of the `by` keyword; a Verso upgrade may need it
  adjusted. `web/README.md` does not yet mention it (outside this task's file list).

## Revision after review (`notes/agents/review-tutorial-ch2-2026-10-16.md`), 2026-10-16

- Group 1 (README, `Meta.lean`, sections 2–4), build OK:
  - `web/README.md`: `goals` in the layout and in "Writing the tutorial" (with an example), a note
    on the Lean blocks (`sorry`, `+error`, `leanOutput`, `-show`, 60 columns), chapter 2 in the
    layout.
  - `Meta.lean`: comment naming the Verso markup the `goals` CSS relies on;
    `pre.lean-output { white-space: pre-wrap; overflow-wrap: anywhere; }` on the `exercise`
    extension, so long `#check` outputs wrap.
  - Section tags and `{ref}` links for the "section N" cross-references.
  - §2: chronological vs causal diamond reconciled with chapter 1; `Carrier` introduced as a field;
    vector field as a section; varied the reminder opening.
  - §3, ≺ now reflexive in the library (user decision): one paragraph saying `≺` is reflexive
    (`causallyPrecedes_refl`, the case `p = q`) and that `IsCausalTrip` is the strict version,
    pinned by a checked `causallyPrecedes_iff_eq_or_isCausalTrip` example (needs parentheses around
    `p ≺[M, t] q` before `↔`). The chapter made no irreflexivity claim elsewhere. The review's ≺
    item (chapter 1 changes, "p ≺ p is false") is superseded and not applied; chapter 1 unchanged.
  - §4: `rw` wording, `constructor` sees through membership, `x · x`, a `simp` example, note on the
    library's first step in worked proof 1, "second exercise of chapter 1" and the causal-diamond
    remark in worked proof 2, the dot-notation display note in the `intro` bullet, forward
    reference for `[CStarAlgebra A]`, varied "Recall that".
  - Worked causal proof and both §4 exercises rebuilt against the reflexive `≺`: they elaborate
    unchanged (the proof uses only transitivity and `mem_causalDiamond`).
- Group 2 (sections 5–7), build OK:
  - The `{docstring}` boxes for `LocalNet`, `Isotony`, `HaagKastlerNet` and `GNS.State` in §5–6
    are replaced by plain, hand-wrapped excerpts of each `structure … where` (no docstrings), each
    pinned by a hidden `lean -show` block: one `example` per field type and a constructor
    (`⟨…⟩`) check that fails if a field is added, removed or retyped. This also removes the
    `HaagKastlerNet` docstring's "proofs of Axioms 2, 3 and 5" contradiction (no library change).
  - One `{docstring Isotony}` box kept, in §7 "Searching", to illustrate docstrings and the
    blueprint label.
  - §5: "only the diamonds (the empty one among them)"; `Type*` explained; `StarModule` added to the
    `CStarAlgebra` parents; "In algebra, a structure is …" opening.
  - Output wrapping: the selector must be `pre.hl.lean.lean-output` (Verso's `.hl.lean
    { white-space: pre }` outranks `pre.lean-output`); checked in a screenshot.
- Not applied: the `#print axioms` line breaks (Lean's exact output; the reviewer also says leave
  it). The review's ≺ item (superseded by the user's decision; chapter 1 unchanged).
- Correction to the earlier log: `lake env lean Tutorial/LeanInBrief.lean` cannot check for
  warnings here (it aborts on `MD4Lean.parse`, with no output, which the earlier grep read as
  "no warnings"). The full `lake build` log (replayed by `lake build Tutorial.LeanInBrief`) shows no
  warnings for the chapter.
- Words: about 4,670 counting inline code and maths as one word each (5,255 raw).
- Final: `lake build` and `lake exe generate-tutorial --output _out/tutorial` succeed; screenshots of
  §3–5 checked (wrapped outputs, goal states from the reflexive `≺`, excerpts).
