# Review: tutorial chapter 4 "Doing it yourself" (2026-10-17)

Scope: `web/Tutorial/DoingItYourself.lean` (line numbers below refer to it unless stated), the
Contributing sections of `README.md` and `home_page/index.md` (`git diff`), and the rendered HTML.

Checks run: `cd web && lake build && lake exe generate-tutorial --output _out/tutorial` (exit 0);
the unchecked claims tested in a scratch file outside the repo with `lake env lean` (the
`mul_comm` error of exercise 1, the `exact?` suggestion of the section 4 exercise, the faithfulness
solution); Loogle queried; library, Mathlib and leanblueprint sources read.

## 1. Lean and mathematics

The worked project is correct and correctly explained. `Q₀ := trivialHaagKastlerNet.quasilocal`
uses only the fields `ι`, `ι_injective` and `dense_range` of `QuasilocalAlgebra`
(`Physicslib4/AQFT/HaagKastler/QuasilocalAlgebra.lean`), so the argument does not depend on how
`HaagKastlerNet.quasilocal` is built. Local images lie in `ℂ·1` (`AlgHomClass.commutes`), `ℂ·1` is a
finite-dimensional subspace and so closed (`Submodule.closed_of_finiteDimensional`, whose
hypotheses the text states correctly: Hausdorff TVS, complete nontrivially normed field), density
then gives `Q₀.carrier = ℂ·1`, injectivity follows from `1 ≠ 0` (through `ι_injective`), and
`identityState.comp (StarAlgEquiv.ofBijective _ _).symm.toStarAlgHom` is a state
(`GNS.State.comp`, `Physicslib4/GNS/ExtremeState.lean:489`, pulls back along any unital
*-homomorphism, as described). All Lean blocks build. The uniqueness solution (section 6) and the
covariance-invariance solution (section 8) are correct and checked by the build. `GNS.State` has a
`FunLike` instance (`GNS/Basic.lean:68`), so `DFunLike.ext` does give `ω = trivialNetState`.
`IsInvariantState` (`QuasilocalIntertwiner.lean:528`) is the first conjunct of `IsVacuumState`
(`VacuumState.lean:125`), so "the first half of the vacuum conditions" is accurate.
`nonempty_haagKastlerNet` is stated at `.{0}`, `trivialBasisSet` is `I⁺(0) ∩ I⁻(0)`,
`trivialQuasilocalAlgebra` has carrier `ℂ`, `exists_starAlgHom_extend_of_dense` exists
(`Analysis/CStarDenseExtend.lean:38`), Stone's theorem exists (`Spectral/Stone/Theorem.lean:209`):
the declarations match their descriptions.

- **1.1 (should fix), line 612.** "This is `AlgHomClass.commutes`, read backwards". The proof
  uses `AlgHomClass.commutes (Q₀.ι hB) a` forwards, without `.symm`. Replace lines 611–625 with:
  "The algebra of every diamond is `ℂ`, so an element `a` of it is a number, and `ι` sends it to
  $`a\mathbf{1}`. This is `AlgHomClass.commutes` applied to `ι`:" [code block unchanged] "The
  lemma's left side is `ι (algebraMap ℂ ℂ a)`, which is `ι a` by definition; on the right, Lean
  accepts `a` as a complex number, although its type is the algebra of `B`, because the two types
  are equal by definition."
- **1.2 (should fix), lines 496–499.** "When the search fails, the message says `failed to
  synthesize`. Chapter 3 met this with `mul_comm`…" disagrees with the section 1 exercise, whose
  (correct, verified) error is `typeclass instance problem is stuck` / `CommMagma ?m`. Replace with:
  "When the search fails, the message says `failed to synthesize`; when Lean does not yet know the
  type to search on, it says `typeclass instance problem is stuck`, as in the first exercise of
  {ref "doing-it-yourself-setup"}[section 1]."
- **1.3 (should fix), lines 866–877, exercise of section 7.** If the reader has also added the
  blueprint entry of section 6 ("Recording it"), `checkdecls` fails as well: the `\lean{…}` names
  are in a file that is never compiled. Either add to the statement "You have not touched the
  blueprint yet." or add to the solution: "If the blueprint entry of section 6 is already in place,
  `checkdecls` fails too: its `\lean{…}` names are declared in a file that is not built."
- **1.4 (nit), lines 263–264.** `\leanfile` is this project's macro, a no-op for leanblueprint
  (`blueprint/src/macros/common.tex:22–26`). Write "(and `\leanfile{…}`, this project's own
  addition, with their file)".

## 2. Accuracy of instructions

CI description (section 7) matches `.github/workflows/lean_action_ci.yml` step by step (lean-action
`build`, `lint`, `mk_all-check`; checkdecls over the grep'd `\lean{}` names; the temporal-wording
script; the conditional Verso build with the root-relative-URL check), and `blueprint.yml` (main
only; builds, lints, builds Verso site and tutorial, docgen-action with blueprint and homepage,
deploys). `lake build` building only what `Physicslib4.lean` imports is right (`defaultTargets =
["Physicslib4"]`, default roots). `check_temporal_wording.py` does flag "is now proved" (pattern
`\b(is|are) now (proved|…)`). Contribution process = README's plus a `CHANGELOG.md` line under
"Unreleased" (that heading exists). No Lean/Mathlib version, no maintainer-local or AI tooling in
the chapter.

- **2.1 (error), lines 835–845.** `leanblueprint checkdecls` is listed before `leanblueprint web`.
  It runs `lake exe checkdecls blueprint/lean_decls`, and `blueprint/lean_decls` is written by the
  web build (leanblueprint `client.py`: "Requires to build the project and the blueprint first").
  On a fresh clone it fails; otherwise it checks a stale list. Fix:
  ```
  leanblueprint web
  leanblueprint pdf
  leanblueprint checkdecls
  ```
  and the sentence after it: "build the blueprint into `blueprint/web/` and `blueprint/print/`,
  and then check the `\lean{…}` names against the build (`checkdecls` reads the list of names that
  `leanblueprint web` writes)."
- **2.2 (error), line 435.** `grep -rn "theorem closed_of_finiteDimensional"
  .lake/packages/mathlib/Mathlib` finds nothing: the declaration is written `theorem
  Submodule.closed_of_finiteDimensional` (`Mathlib/Topology/Algebra/Module/FiniteDimension.lean:531`).
  Fix: `grep -rn "closed_of_finiteDimensional" .lake/packages/mathlib/Mathlib` (first hit is the
  declaration).
- **2.3 (should fix), line 835.** leanblueprint also needs Graphviz (its `pygraphviz` dependency)
  for the dependency graph. Write: "The blueprint needs `leanblueprint`, a Python package (`pip
  install leanblueprint`; it needs Graphviz for the dependency graph and a LaTeX installation for
  the PDF; its README gives the details per system)."
- **2.4 (should fix), `README.md:53`.** Getting Started still says `lake exe cache get!`; the
  chapter says `get`. See 3d.
- Checked and fine: Loogle query `IsClosed, Submodule, FiniteDimensional` returns 11 hits with
  `Submodule.closed_of_finiteDimensional` third ("among the first results" is accurate);
  `exact?` suggestion `exact FaithfulSMul.algebraMap_injective ℂ A` verified; elan one-liner;
  Lake/`lake-manifest.json` description; `web/` build commands match `web/README.md` and CI.

## 3. Writer's flagged points

- **3a. Build times (should fix), lines 64–68, 117–118.** No measurement backs "a few minutes" or
  "several minutes to some tens of minutes"; CI logs for recent runs are not retrievable here.
  Proposed wording without invented precision:
  "* `lake exe cache get` downloads Mathlib's compiled files, several gigabytes: minutes on a fast
    connection, longer on a slow one. Without it, `lake build` would compile Mathlib itself, which
    takes hours.
   * `lake build` then compiles the library's hundred-odd files. The first time takes a while
    (tens of minutes on a laptop is normal); later builds recompile only the files that changed
    and those that import them."
  and for `web/`: "The first `lake build` in `web/` compiles Verso, the tool that renders these
  pages, and the native code of the modules it links, and takes a while." Better still: time one
  clean build (`rm -rf .lake/build && time lake build`) on an ordinary laptop and state that range.
- **3b. Restrictions.** Confirmed: `grep -rn "Restriction:" Physicslib4` returns nothing. Section 2's
  generic description is accurate and adequate, but two things need fixing:
  - **(error), lines 201–203.** The example is "…waiting on Stone's theorem", while line 178 tells
    the reader the library contains Stone's theorem. A reader sees a contradiction. Present the form
    instead of a concrete case: "For example, a line of the form `**Restriction:** the generator is
    required to be bounded; the intended form allows an unbounded self-adjoint generator, and is
    waiting on <the missing result>.`" or pick a hypothetical that names no existing result, e.g.
    "…waiting on the spectral theorem for unbounded normal operators" only if that is genuinely
    absent (it is not verified here; prefer the template form). Also the rendered example shows
    "*Restriction:*" as bold text rather than the literal docstring syntax; put it in code
    (`` `**Restriction:**` ``) so the reader sees what to type.
  - **(should fix), lines 895–897.** "a search for that string lists them, and each is a ready-made
    project" implies some exist. Replace: "_Restrictions._ A declaration that is less general than
    intended says so in a `**Restriction:**` line, naming what it waits on; `grep -rn
    "Restriction:" Physicslib4` lists them, and each is a ready-made project. The search can come
    back empty, when every declaration has its intended general form."
- **3c. `web/README.md` (should fix).** The Layout list names `AQFTInBrief.lean` and
  `LeanInBrief.lean` but neither `WorkedExamples.lean` (chapter 3) nor the new file. After the
  line `- \`Tutorial/LeanInBrief.lean\`: chapter 2, "Lean in brief".` add exactly:
  ```
  - `Tutorial/WorkedExamples.lean`: chapter 3, "Worked examples".
  - `Tutorial/DoingItYourself.lean`: chapter 4, "Doing it yourself".
  ```
  Also check whether "chapter 1, "AQFT in brief" (in preparation)" is still accurate now that
  chapter 1 is committed (`413c929`); if not, drop " (in preparation)".
- **3d. `cache get` vs `get!`.** Mathlib's `cache get` downloads only the files missing locally
  and unpacks them; `get!` re-downloads every file, overwriting what is there (useful only for a
  corrupted or interrupted cache). `get` is right for normal setup, and it is what CI
  (`lean_action_ci.yml`, `blueprint.yml`), `web/README.md` and the chapter use. Unify on `get`:
  - `README.md:53`: `lake exe cache get    # download prebuilt dependencies`;
  - `.claude/CLAUDE.md:7`: `lake exe cache get`, then `lake build` (maintainer's file; a proposal,
    not an agent edit);
  - `home_page/index.md` no longer lists the command (its `get!` step is removed by the diff), so
    nothing there. Keep the chapter's parenthetical on `get!` as is.

## 4. Prose and style

Overall crisp, present tense, pitched right for the audience, and it does not re-explain chapters
1–3. `check_temporal_wording.py` does not scan `web/` (ROOTS excludes it), so I read for history
wording by hand: none found apart from 4.2.

- **4.1 (should fix).** "As you will recall" appears three times (lines 164, 359, 520). Vary two:
  line 359 "Chapter 2 ({ref "lean-in-brief-mathlib"}[section 7]) listed several ways to find them;
  here each is applied to one of the three."; line 520 "Recall the aside on universes in
  {ref "lean-in-brief-structures"}[chapter 2, section 5]: a structure such as …".
- **4.2 (nit), line 18.** "The first three chapters were read in the browser." Prefer "The first
  three chapters are written to be read in the browser."
- **4.3 (nit), home_page/index.md diff.** "add a result to the blueprint and the Lean" reads
  oddly; use README's "add a result to the blueprint and the library".
- **4.4 (nit), source wrapping.** Prose lines over 100 columns: 133, 218, 675, 789, 932 (170
  columns). Rewrap.

## 5. Rendering

Build and generation succeed. The chapter is at `web/_out/tutorial/html-multi/Doing-it-yourself/`,
so the new README/home page links `…/tutorial/Doing-it-yourself/` resolve once deployed. Ten
collapsible `<details>` solutions (ten exercises), five `goals` blocks (57 goal panels), 19 KaTeX
maths spans, cross-chapter refs resolve (`Worked-examples/#worked-examples-gns`,
`Lean-in-brief/#lean-in-brief-mathlib`, etc.), no root-relative URLs, highlighted names link to
their anchors (`#trivialNetState`, `#Q___`).

- **5.1 (should fix), Lean lines over the 60-column rule of `web/README.md`.** Line 689 (63 cols)
  and 723 (61). Fix:
  ```
  theorem trivial_bijective :
      Function.Bijective
        (StarAlgHom.ofId ℂ Q₀.carrier) := by
  ```
  and
  ```
  example (z : ℂ) :
      trivialNetState
        (algebraMap ℂ Q₀.carrier z) = z := by
  ```
  (Lines 378–380, 512, 558 are Lean output in `leanOutput` blocks and cannot be wrapped; 512 is
  the long `Hint:` line, acceptable.)
- **5.2 (nit).** The Restriction example renders as bold "Restriction:" (see 3b).

## Verdict and top 5

Verdict: **ready after small fixes.** The mathematics and Lean are sound and well explained; the
instructions are accurate apart from two command errors. Counts: 3 errors, 10 should fix (3d is the same item as 2.4), 5 nits.

1. Reorder the blueprint commands: `leanblueprint web`, `pdf`, then `checkdecls` (2.1).
2. Fix the grep for `closed_of_finiteDimensional` (2.2).
3. Replace the Stone's-theorem Restriction example, which contradicts line 178, and reword the
   section 8 "Restrictions" bullet for the case of none (3b).
4. Unify on `lake exe cache get` in `README.md:53` (and propose it for `.claude/CLAUDE.md:7`);
   add the chapter 3 and 4 lines to `web/README.md` (3c, 3d).
5. Correct "read backwards" (1.1), reconcile `failed to synthesize` vs `stuck` (1.2), and make the
   section 7 exercise unambiguous about `checkdecls` (1.3).
