# Reference manual, stage 0: progress log

Infrastructure for the reference manual as a second Verso manual-genre book at `/manual/` (plan:
`plan-verso-reference-manual-2026-10-17.md`, "Infrastructure"). Appended after each step.

## Step 0: reconnaissance (2026-10-17)

- The tutorial's setup (`verso-stage3-progress.md`): `Tutorial/Theme.lean` holds the stylesheet
  (`tutorialCss`), the `RenderConfig` and the `replaceHeader` extra step; `Tutorial/Meta.lean` the
  directives; `Site/Links.lean` `navLinksFrom siteRoot tutorialRoot`, with the Reference manual
  link at `siteRoot ++ "manual/"` (the website's stub page `Site/Manual.lean`).
- The rule that wraps long Lean messages (`pre.hl.lean.lean-output`) sits in the `extraCss` of the
  `exercise` block extension, so it reaches only books that use `exercise`. The manual has no
  exercises: the rule moves into the shared stylesheet.
- `{docstring}` (Verso `v4.35.0`, `VersoManual/Docstring.lean`) takes the flags `hideFields`
  (all fields), `hideStructureConstructor`, `allowMissing` and `label := "..."`. Field types are
  pretty-printed at `format.width` 40. Fields inherited from a parent structure carry
  `data-inherited-from` on their `section.subdocs`, so CSS can hide them; there is no flag for it.
- API docs (doc-gen4, deployed): a declaration `N` of module `A.B.C` is at
  `docs/A/B/C.html#N`, the anchor being the full name, e.g.
  `docs/Physicslib4/AQFT/HaagKastler/LocalAlgebras.html#Physicslib4.AQFT.HaagKastler.LocalNet` and
  `docs/Physicslib4/AQFT/HaagKastler/EinsteinCausality.html#Physicslib4.AQFT.HaagKastler.HaagKastlerNet.einstein_causality`
  (both checked: page 200, anchor present). `docs/find/?pattern=N#doc` also resolves by name.

## Step 1: shared theme, book scaffold (2026-10-17)

- New `web/Book/Theme.lean` (lean_lib `Book`, globs `Book.+`): the shared stylesheet `bookCss`
  (formerly `Tutorial.tutorialCss`, plus the `lean-output` wrapping rule moved out of the `exercise`
  extension, plus wrapping of field types in `{docstring}` boxes), `themeCss`,
  `config (description)` and `replaceHeader (header)`. `Tutorial/Theme.lean` and `Manual/Theme.lean`
  are thin instances (description, header with their own nav entry active).
- `Site/Links.lean`: `navLinksFrom tutorialRoot manualRoot`; `manualPath = "../manual/"`,
  `siteFromBook = "../site/"` (was `siteFromTutorial`), `manualNavLinks`, and `apiDocsUrl module decl`.
  `Site/Manual.lean` (stub page) and its route removed; `Site.header` takes no path (no website page
  has an active nav entry).
- New `web/Manual.lean` (title page), `web/Manual/HaagKastler.lean` (placeholder chapter, file name
  `Haag-Kastler-axioms-in-Minkowski-spacetime/`, set with `file :=`; the default slug was
  `The-Haag___Kastler-...`), `web/ManualMain.lean` (`generate-manual`), lean_lib `Manual` and
  lean_exe `generate-manual` added to `web/lakefile.toml` and its default targets.
- `web/Book/Meta.lean`: role `{apiDocs Name}[text]` (empty text: the name in code type). The name
  is resolved at build time; the module comes from `env.getModuleIdxFor?`.

## Step 2: declaration display, draft chapter `Manual/FeatureTests.lean` (2026-10-17)

- `{docstring Physicslib4.AQFT.HaagKastler.LocalNet}`: a box labelled "structure" with the
  signature, the docstring, "Constructor" and "Fields" (each field with its type and docstring).
  Builds without `allowMissing`.
- Truncation: field types are pretty-printed at width 40 but a single long application does not
  break, and the box cut it off at the right edge (`HaagKastlerNet.localCommutativity :
  Physicslib4.AQFT.HaagKastler.LocalCommutativity self.U self.isotony`). Fixed in `bookCss`: field
  lines wrap with a hanging indent. Names in field types are printed fully qualified.
- Inherited fields (`Physicslib4.GNS.State extends A →L[ℂ] ℂ`): Verso hides them by default and
  lists the parent under "Extends" with a checkbox that shows them. No directive needed (an
  `ownFields` directive was tried and dropped). `+hideFields` hides all fields,
  `+hideStructureConstructor` the constructor (the `(x := true)` form is deprecated).
- Docstring Markdown code spans are elaborated as Lean: `` `def:local-algebras` `` renders with
  `def` highlighted as a keyword. A point for the docstring pass.
- `#check HaagKastlerNet.einstein_causality` (under `open Physicslib4 AQFT HaagKastler in`) with
  `leanOutput`: Verso prints messages at width 120 whatever `format.width` is (SubVerso uses
  `Std.Format.defWidth`); the shared `pre.hl.lean.lean-output` rule wraps them in the text column.
- API-doc links checked live (page 200, anchor present) for `LocalNet`, `einstein_causality`, and
  the Mathlib class `CStarAlgebra` (`docs/Mathlib/Analysis/CStarAlgebra/Classes.html#CStarAlgebra`).

## Step 3: paths (2026-10-17)

- Website nav "Reference manual" and the tutorial's go to `../manual/`; the manual's wordmark to
  `../site/`, its Tutorial link to `../tutorial/`.
- Served `/tmp/srv/physicslib4/{site,tutorial,tutorial-draft,manual,manual-draft}` on port 8765 and
  crawled from each root (`/tmp/check_urls2.py`): 300 local URLs (401 with the drafts), all 200 except
  the known `-verso-search/xref.json` crawler artefact (the browser resolves it against `<base>`).
  No root-relative `href`/`src` in any output.

## Step 4: CI, .gitignore (2026-10-17)

- `blueprint.yml`: step "Build the Verso site, tutorial and manual into home_page" also runs
  `generate-manual --output _out/manual` and copies `html-multi` to `../home_page/manual`.
- `lean_action_ci.yml`: step "Build the Verso site, tutorial and manual" also builds the manual;
  the root-relative URL check covers `_out/manual/html-multi`. Change filter unchanged (`web/`).
- `.gitignore`: `home_page/manual/`. Both YAML files parse.
- Jekyll pass-through (`/tmp/jk/home_page`, bundle from stage 3): `_site/manual` identical to the
  input except the extra `-verso-search/licenses.html`, as for the tutorial.

## Step 5: README, rebuild, screenshots (2026-10-17)

- `web/README.md`: three documents; layout (`Book/`, `Manual/`, `ManualMain.lean`); "Writing the
  reference manual" (chapter files, `file :=`, the `{docstring}` / `#check` + `leanOutput` /
  `apiDocs` conventions); build and view commands for the manual; sub-path and CI sections.
  `scripts/check_temporal_wording.py` passes.
- Clean rebuild: `lake build` (7281 jobs), `generate-site`, `generate-tutorial`, `generate-manual`
  (about 4 s each), plus both `--draft` builds. No root-relative URLs; crawl as in step 3, all 200.
  The tutorial renders as before (exercise boxes, wrapped Lean output).
- Screenshots of the placeholder chapter, 1440x900: `notes/agents/verso-manual-light.png`,
  `notes/agents/verso-manual-dark.png` (headless Chrome, `preferredColorScheme` 1 / 0).
- Not done: CI timing of the manual build (to check after the first run); nothing committed.
