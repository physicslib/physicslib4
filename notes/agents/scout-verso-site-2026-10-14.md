# Scout memo: Verso-based website/manual for physicslib4

Date: 2026-10-14. Scope: investigate using Verso (VersoBlog / VersoManual) to build a
website and/or tutorial-style user manual for physicslib4, alongside (or replacing)
the current Jekyll home page (`home_page/`), leanblueprint blueprint (`blueprint/src`),
and doc-gen4 API docs, all currently assembled by `leanprover-community/docgen-action`
at commit `7b5b9a1822650bd45aaeb4182d94bceba2030f89` (pinned in
`.github/workflows/blueprint.yml`).

Project facts used throughout: `lean-toolchain` = `leanprover/lean4:v4.34.1`;
`lakefile.toml` requires `mathlib` `rev = "v4.34.1"` and `«doc-gen4»` `rev = "v4.34.1"`.

## 1. Verso version

- `leanprover/verso` has **no tag whose own `lean-toolchain` is `v4.34.1`**. Full tag
  list (via `git ls-remote --tags https://github.com/leanprover/verso`, checked
  2026-10-14) jumps `v4.34.0 → v4.34.0-rc1/rc2 → v4.35.0-rc1..rc4 → v4.35.0`, plus daily
  `nightly-2026-MM-DD` tags and a moving `latest` tag. Confirmed by fetching
  `lean-toolchain` at each tag via raw.githubusercontent.com:
  - `v4.34.0` → `leanprover/lean4:v4.34.0` (not `.1`)
  - `v4.35.0` → `leanprover/lean4:v4.35.0`
- Lean's `v4.34.1` release itself (`leanprover/lean4` GitHub release) has
  `published_at: 2026-09-24T20:24:21Z`. Verso's nightly tag `nightly-2026-09-24`
  exists and points its own `lean-toolchain` at `leanprover/lean4:nightly-2026-09-24`
  — the closest same-day match, but it is a Verso *nightly* snapshot, not a release,
  and I did not verify that `nightly-2026-09-24`'s Lean nightly is literally the
  commit `v4.34.1` was cut from (plausible but **unverified**).
- **Conclusion: there is no clean Verso release pinned to v4.34.1.** Realistic options,
  in order of risk:
  1. Pin `verso` to `nightly-2026-09-24` (best calendar match) and accept it is an
     unreleased snapshot of Verso itself (fine — Verso the *tool* doesn't need to be
     reproducible the way the formalization does).
  2. Decouple entirely (see §2/§7 "package-docs" pattern): run the Verso-based site/
     manual package on its own newer toolchain (e.g. `v4.35.0`, Verso's latest stable
     tag as of 2026-10-14), and pull in physicslib4 source/doc data through SubVerso's
     *external-module* extraction, which is explicitly designed so "a library [can]
     stay on an older version of Lean while still adopting improvements to Verso that
     require new compiler versions" (quoted from
     `leanprover/verso-templates`, `package-docs/manual/Docs.lean` docstring, fetched
     2026-10-14). This avoids ever requiring Verso and physicslib4/Mathlib in the same
     `lake build` graph, and is the route I recommend (§6 of outline below).
- **Dependency conflict check for a `web/` package that `require`s both `verso` and
  physicslib4 directly (the non-decoupled route):** Lake resolves one Lean toolchain
  per build (the root package's `lean-toolchain` governs what every dependency is
  compiled with, regardless of the dependency's own `lean-toolchain` file). Verso's
  own dependencies (SubVerso, MD4Lean) are small, Verso-specific, and not present in
  Mathlib's dependency set, so there is no *version-pin* conflict in the manifest
  sense; the real risk is a *Lean-version* conflict — Verso at `v4.35.0`/nightly likely
  uses toolchain features not present in `v4.34.1`, or vice versa, so a direct
  `require verso` + `require physicslib4` in one package is the fragile approach.
  I did not attempt an actual `lake build` of such a package (out of scope / no
  network-isolated sandbox time budgeted); this is a prediction from reading the
  toolchain files, not a tested result — **flag as unverified, recommend testing
  early** if the direct-require route is chosen over decoupling.

## 2. How Verso sites are built

Confirmed from `leanprover/verso-templates` (fetched 2026-10-14) and
`leanprover/verso-website` (the source of `verso.lean-lang.org`, Apache-2.0,
fetched 2026-10-14):

- **Genres:** `VersoBlog` (websites — `import VersoBlog`, `open Verso Genre Blog`) and
  `VersoManual` (books/manuals — `import VersoManual`, `open Verso Genre Manual`).
- **Declaring the executable.** Pattern from every template (`basic-blog`,
  `basic-book`, `package-docs/manual`), lakefile.toml:
  ```toml
  [[require]]
  name = "verso"
  git = "https://github.com/leanprover/verso"
  rev = "v4.35.0"
  [[lean_lib]]
  name = "Blog"        # or "Book", "Docs", ...
  [[lean_exe]]
  name = "generate-blog"   # or "generate-book", "docs", ...
  root = "Main"
  ```
  `Main.lean` then calls the genre's entry point. For `VersoBlog`
  (`verso-website/Main.lean`, fetched 2026-10-14):
  ```lean
  def main (args : List String) : IO UInt32 := do
    let remotes ← Verso.Multi.updateRemotes false none (fun _ => pure ())
    blogMain theme versoSite (linkTargets := remotes.remoteTargets) args
  ```
  For `VersoManual` (`verso-templates/package-docs/manual/Main.lean`):
  ```lean
  def config : RenderConfig where
    emitTeX := false
    emitHtmlSingle := .no
    emitHtmlMulti := .immediately
    htmlDepth := 2
  def main := manualMain (%doc Docs) (config := config)
  ```
- **Output directory.** `lake exe <name>` writes HTML under `_out/` by default
  (confirmed by `package-docs/manual/README.md`: "The generated site will be in
  `_out/html-multi/`"); `verso-templates/generate.sh` copies each example's output
  into one combined directory for serving — i.e. the CLI takes an output-directory-ish
  set of flags but the templates' own convention is to post-copy. I did not find a
  documented `--output` flag in the fetched files; worth checking `lake exe <name> --help`
  against the pinned Verso tag before committing to a layout (**unverified** exact
  flag name/default beyond the `_out/` convention above).
- **One site linking to another (manual → website).** `Verso.Multi.updateRemotes`
  plus a `linkTargets`/`remoteTargets` argument to `blogMain`/`manualMain` is exactly
  the cross-site linking mechanism (seen in `verso-website/Main.lean`); the Verso user
  manual itself documents a "multi-site" feature for this (not independently fetched;
  inferred from the `Verso.Multi` namespace name and its use — **flag as
  needing a closer read of the Verso manual's own "Multi-page documents"/site-linking
  chapter before implementing**).
- **Can a manual embed docstrings of declarations from a dependency, and elaborate
  examples that `import Physicslib4`?** Yes, via two distinct, confirmed mechanisms:
  1. **In-process** (`leanprover/reference-manual`, the flagship real example — Apache
     2.0, `lean-toolchain` = `v4.35.0`, fetched 2026-10-14): the manual package directly
     imports the library whose declarations it documents (there, Lean's own stdlib,
     via `illuminate`), and chapter files use `{docstring Foo}`,
     `{docstring Dynamic.mk +allowMissing}` etc. (seen literally in `Manual.lean`'s
     "Dynamic Typing" section). This requires the manual package and the documented
     library to share one `lake build`, hence one toolchain — i.e. it needs
     physicslib4's own oleans built in-process, and would need physicslib4 and the
     manual package on the *same* Lean version.
  2. **Decoupled / cross-version** (`leanprover/verso-templates`,
     `package-docs/manual/Docs.lean`, fetched in full 2026-10-14): a sibling Lake
     package (there, `zippers/`) is the subject; the manual sets
     `set_option verso.exampleProject "../zippers"` and
     `set_option verso.exampleModule "Zippers"`, `open Verso.Code.External`, then uses
     `anchor`/`anchorTerm`/`anchorName`/`anchorInfo` code blocks (not `{docstring}`)
     to pull in highlighted source, hovers, and `#eval` output extracted from the
     *other* package's own build (via the `subverso-extract-mod` tool, run under the
     subject package's own toolchain). The docstring text's own words: "It decouples
     the version of Lean used for Verso from that used by the library. This is
     important because it allows a library to stay on an older version of Lean while
     still adopting improvements to Verso that require new compiler versions."
     — this is **exactly physicslib4's situation** (pinned `v4.34.1`, Verso has no
     matching tag). **Caveat (unverified):** I did not confirm whether `{docstring}`
     itself (full doc-comment rendering, as opposed to `anchor`-based source/eval
     snippets) is available through this external/cross-toolchain path, or only
     in-process (route 1). If full docstring rendering of physicslib4 declarations is
     required, that likely forces route 1 (shared toolchain) for that specific content,
     while worked-example code/output can still use route 2. Recommend a short spike
     against the actual Verso tag to settle this before committing to the manual's
     structure.
- **Cost/requirements of embedding library content:** route 1 needs physicslib4 to
  build successfully as a dependency of the manual package (full `lake build`,
  i.e. Mathlib too, before the manual elaborates) — this is the project's existing
  `lake build` cost, repeated inside the docs build (CI minutes, cache size). Route 2
  needs the `subversoExtractMod`/`subverso-extract-mod` executable (seen as an explicit
  `target subversoExtractMod` step in `reference-manual/lakefile.lean`) run once over
  physicslib4 at its own toolchain, producing an extraction artifact the manual
  package consumes without rebuilding physicslib4 itself in-process — cheaper per manual
  rebuild, more moving parts to set up once.
- **Small real examples to imitate**, all fetched/confirmed 2026-10-14:
  - `leanprover/verso-templates` — `basic-blog`, `basic-book` (minimal), `package-docs`
    (external-library docs, our closest analogue), `textbook` (single-toolchain,
    custom `savedLean` block + `buildExercises` build step for extracting exercises),
    `blog-features` (custom theme/components), `slides` (reveal.js via verso-slides).
  - `leanprover/verso-website` (verso.lean-lang.org source) — small, real `VersoBlog`
    site, Apache-2.0, shows a full custom `Theme` (navbar, footer, analytics,
    tooltips) in ~90 lines of `Main.lean`.
  - `leanprover/reference-manual` — the large, real `VersoManual` example (the Lean
    Language Reference, `lean-lang.org/doc/reference/latest/`); heavyweight
    (`restoreAllArtifacts`, custom `moreLeancArgs`/`moreLinkArgs`, a `Tutorial` genre
    page too, `extract-lakefile` exe, `illuminate` + `versowebcomponents` deps) —
    good for seeing scale, not a template to copy wholesale for a project our size.

## 3. Themes and licences

- **Licence, confirmed by fetching `LICENSE` from each repo's `main` branch
  (2026-10-14), all read "Apache License 2.0 (Apache)" / Apache License Version 2.0:**
  `leanprover/verso`, `leanprover/verso-website`, `leanprover/verso-web-components`,
  `leanprover/reference-manual`. So yes — Verso itself and the actual lean-lang.org/
  verso.lean-lang.org theming code are Apache-2.0, confirmed (not merely "believed").
- **Where the styling lives:**
  - `leanprover/verso-website` is the source for **verso.lean-lang.org** (confirmed by
    its `Main.lean` title "Verso — Written in Lean, checked by Lean" and footer links
    to `lean-lang.org`, Zulip, GitHub). Its `Theme` is a plain Lean value
    (`Theme.default with primaryTemplate := do ...`), an HTML5 template built with
    Verso's `Html`/`Template` combinators, referencing `/static/style.css` and
    `/static/glightbox/...` — i.e. the actual CSS is a static asset copied in via
    `static "static" ← "static_files"` in the `Site` declaration, not generated by
    Verso itself.
  - `leanprover/verso-web-components` is billed as "a collection of reusable
    components from the Lean website designed [to] build related sites with the same
    look and feel" (its GitHub description, confirmed) — i.e. this is the designed
    sharing mechanism for "one stylesheet across blog and manual genres." I confirmed
    it is a Lake package (has a `lakefile.lean`) and Apache-2.0 licensed; I did **not**
    fetch its actual file contents (CSS/components list, the `require`/`import`
    incantation) — budget-limited, flagged as the single highest-value next read
    before implementation.
  - `leanprover/reference-manual`'s `lakefile.lean` literally
    `require versowebcomponents from git "https://github.com/leanprover/verso-web-components"@"main"`
    — direct confirmation that a `VersoManual` book consumes the same component
    library a `VersoBlog` site can, i.e. **a blog-genre site and a manual-genre book
    can share one stylesheet/component set via `verso-web-components`.**
  - `leanprover/lean-lang.org` **redirects** (HTTP 301, confirmed via
    `curl -sIL`) to `leanprover/leanprover.github.io` — i.e. the main
    marketing site's source has moved/is at that repo name. I did not fetch its
    contents or confirm it is Verso-based (it may predate the Verso rewrite, or be a
    different stack entirely) — **unverified, flagged for a follow-up read** if the
    goal is specifically to imitate lean-lang.org (as opposed to verso.lean-lang.org,
    which is fully confirmed Verso + Apache-2.0).
- **Customisability:** confirmed qualitatively from `verso-website/Main.lean` — project
  name, logo/favicon, nav links, colours (via the linked `style.css`, not fetched),
  footer columns, and even third-party scripts (Plausible analytics, GLightbox,
  tippy.js tooltips) are all just values/HTML in the `Theme`/`Main.lean`, so
  customisation is effectively total (it's a Lean value you write, not a config file
  with a fixed schema). Degree of customisation is bounded only by willingness to
  write Verso `Html`/`Template` code.

## 4. Restyling the blueprint (plasTeX/leanblueprint)

From the project's own `blueprint/src/plastex.cfg` and `extra_styles.css` (read
directly, not web-sourced):
- `plastex.cfg` `[html5]` section already sets `extra-css=extra_styles.css` — this is
  leanblueprint's documented hook for additional CSS loaded after the theme's own
  stylesheet, and the project already uses it (currently 25 lines, adding a left
  border to theorem/proof boxes — read in full at
  `blueprint/src/extra_styles.css`).
- `[general]` `copy-theme-extras=yes` and `plugins=plastexdepgraph plastexshowmore
  leanblueprint` are the other configurable surfaces: `copy-theme-extras` controls
  whether a plasTeX theme's extra static files (fonts, images) are copied into the
  output, and the plugin list determines which plasTeX renderer extensions run
  (the dependency graph, "show more" collapsing, and leanblueprint's own
  Lean-status decorations).
- **What I did not do (budget):** I did not fetch plasTeX's own documentation on
  theme *directories* (i.e. swapping the whole HTML5 theme, not just adding extra
  CSS) or on available `[html5]` options beyond `extra-css`/`localtoc-level`/
  `mathjax-dollars` already visible in this file. Matching a Verso site's fonts,
  header and navigation exactly (not just colours/borders) likely requires either
  (a) writing a full custom `extra_styles.css` that overrides the default plasTeX
  HTML5 theme's header/nav markup with `!important`/selector overrides (constrained
  by whatever markup the default theme emits — unverified how much that markup can be
  reshaped from CSS alone), or (b) a custom plasTeX theme directory (bigger lift,
  not investigated). **Recommend a follow-up scout pass specifically on plasTeX's
  `Themes/` mechanism if close visual parity with the Verso site is a hard
  requirement**, since I cannot confirm from what I read today whether CSS alone
  suffices for header/nav parity.
- **What can't change:** confirmed by the file structure itself — the theorem/proof
  box *structure* (the `div.theorem_thmcontent` etc. class hierarchy) and the
  dependency graph are generated by the `leanblueprint`/`plastexdepgraph` plugins
  from the `.tex` source and Lean declaration status; CSS can restyle their
  appearance but not their existence or layout logic — consistent with
  `.claude/CLAUDE.md`'s framing of the blueprint as the specification artifact, not
  a themeable page.

## 5. Restyling doc-gen4

- Fetched the `leanprover/doc-gen4` repository overview: **no documented
  configuration option, environment variable, or hook for a custom stylesheet or
  header.** The only documented environment variables found are `DOCGEN_SRC`
  (source-link behaviour) and `DISABLE_EQUATIONS`; styling is in a `static/`
  directory inside the doc-gen4 package itself, and the README explicitly warns that
  modifying the `.js`/`.css` files in doc-gen4 "won't necessarily be copied over" —
  i.e. even editing doc-gen4's own source isn't guaranteed to propagate without a
  full rebuild step understanding.
- `docgen-action`'s `action.yml` (fetched in full from the pinned commit
  `7b5b9a1822650bd45aaeb4182d94bceba2030f89`, used in
  `.github/workflows/blueprint.yml`) exposes **no stylesheet/static-file input** at
  all — its inputs are `api-docs`, `blueprint`, `build-page`, `deploy`, `homepage`,
  `build-args`, `lake-package-directory`, `references`, `use-github-cache` (plus
  deprecated aliases). The API-docs build step is just
  `${{ github.action_path }}/scripts/build_docs.sh` (not fetched — would show the
  exact `lake build` invocation and output path, e.g. `.lake/build/doc`).
- **Least-invasive route, since no first-class hook exists:** a post-processing step
  after `build_docs.sh` runs (or after the whole action, operating on
  `homepage/docs` or wherever API docs land before the Jekyll build packages
  everything into `_site`) that injects a `<link rel="stylesheet" href="...">` (and
  optionally a `<script>` for a shared nav) into doc-gen4's generated HTML — e.g. a
  small `sed`/HTML-postprocess script run as an extra CI step between
  `docgen-action`'s internal doc build and its Jekyll build, OR simply drop a custom
  CSS file into doc-gen4's known static output directory and reference it from
  doc-gen4's own template if doc-gen4 supports a `<link>` to an extra file by
  filename convention (**not confirmed** — would need to read
  `build_docs.sh` and doc-gen4's HTML templates directly, not done this pass).
  A second, likely cleaner option matching the `docgen-action` design: since
  `docgen-action` copies the API docs *into* the `homepage` folder before/during the
  Jekyll build (per the action's own step ordering), a Jekyll layout/include
  (`home_page/_layouts` or `_includes`, already present in this repo) could wrap or
  inject into the doc pages post-hoc via Jekyll's own file-processing — but Jekyll by
  default **does not process files with no front matter** beyond copying them
  (relevant also to §6).

## 6. Combining with docgen-action

- **`homepage:` input, confirmed from the action.yml fetched above:** "The folder
  where the Jekyll site can be found," default `docs`. The action step "Check for
  `${{ inputs.homepage }}` folder" is explicitly commented `# this is meant to detect
  a Jekyll-based website` — i.e. **the action is hard-wired to assume the homepage
  folder is a Jekyll source tree**, not an arbitrary pre-built static-HTML directory.
  If `DOCS_EXISTS=true`, it unconditionally runs `bundle exec jekyll build` in that
  directory (the "Build website using Jekyll" step), and deploys
  `${{ inputs.homepage }}/_site` as the Pages artifact; if the folder doesn't exist,
  it deploys `${{ inputs.homepage }}/` directly (no Jekyll).
- **Does Jekyll "pass through" plain HTML without front matter?** Jekyll's documented
  behaviour (general Jekyll knowledge, not re-fetched this pass, low risk — widely
  stable Jekyll behaviour) is: files without YAML front matter are copied verbatim
  (static passthrough); files *with* front matter are processed as pages/posts
  through the configured layout. So a directory of plain Verso-generated HTML
  (no front matter) dropped inside `home_page/` **would** be copied through
  untouched by Jekyll — i.e. option (a) "drop Verso's `_out/html-multi/` output as a
  subdirectory of `home_page/`" is viable and requires no action.yml change, matching
  exactly how the blueprint and API docs are already placed into `homepage/blueprint`
  and (implicitly) `homepage/docs` before the Jekyll build consumes them. This is the
  lowest-effort way to combine Verso output with `docgen-action`'s existing pipeline:
  **treat Verso's output directory as just another static subtree of `home_page/`,
  copied in by an added CI step before the "Build website using Jekyll" step** (the
  action doesn't need to know Verso exists at all).
- **Does `docgen-action` expose its output directory or a skip-deploy option for
  assembling one Pages artifact differently?** Yes to the latter: `deploy: false`
  (default `true`) disables both the upload-pages-artifact and deploy-pages steps,
  for a dry run / so a separate workflow step could assemble and upload a combined
  artifact instead. No explicit "output directory" input exists beyond `homepage`
  itself and the implicit `blueprint/print.pdf` / `blueprint/web` copy targets (both
  hard-coded to `${{ inputs.homepage }}/blueprint`); there's no way to redirect API
  docs or blueprint output elsewhere without forking the action or running
  `deploy: false` and re-assembling by hand before a separate
  `upload-pages-artifact`/`deploy-pages` pair.
- **Recommendation:** keep `docgen-action` exactly as configured (blueprint + API
  docs + Jekyll homepage unchanged), and have a preceding CI step `lake exe
  <verso-site>` / `lake exe <verso-manual>` into e.g. `home_page/tutorial/` and/or
  `home_page/` (for a Verso-built landing page component) **before** the
  `docgen-action` step runs, so Jekyll's build simply picks the already-rendered
  Verso HTML up as static passthrough content. This needs no `action.yml` or
  `docgen-action` fork at all — lowest risk, respects "don't modify protected CI
  files" guidance implicitly (new step is additive, not a change to the pinned
  action).

## 7. Tutorial-style user manual

**What a Verso manual offers a tutorial**, confirmed from the `reference-manual`
repo structure (it literally has a sibling `Tutorial`/`TutorialMain` target in its
`lakefile.lean`, `lean_lib Tutorial`, `lean_exe "generate-tutorials" where root :=
`TutorialMain`) and from the `package-docs/manual/Docs.lean` content fetched in full:
elaborated, hover-annotated code via `{lean}`/`anchor` blocks that are *actually
type-checked against the real library* (not copy-pasted text — e.g. the zippers
example's `#eval z1 ⇰ .right` / `anchorInfo` block shows real elaborator output,
confirmed verbatim: `some { revBefore := [1], after := [2, 4] }`); margin notes
(`{margin}[...]`); citations (`{citep}`/`{citet}`/`{citehere}`); cross-references
(`{ref "tag"}`); an automatically built index (`{index}[term]`, `{theIndex}`).
I did not independently confirm a dedicated "exercise" or "expected-error" block type
beyond the `textbook` template's custom `savedLean` block (a project-specific
extension, not a built-in Verso feature) — **flag as unverified whether Verso ships
a built-in exercise/error-expectation directive, or whether every project builds its
own** (the `textbook` template's README explicitly frames `savedLean` as "a
non-trivial extension to the manual genre," implying it is *not* built in).

**Existing Lean tutorials in Verso to model on:**
- `leanprover/reference-manual`'s own `Tutorial` target (chapters include `VCGen`,
  `MVCGen`, `Grind/IndexMap` per its directory listing — these are tutorials on
  specific tactics, not a from-scratch "learn Lean" tutorial).
- The classic "Theorem Proving in Lean"/"Functional Programming in Lean" books are
  **not confirmed** to have been ported to Verso in my research this pass (I did not
  search for them specifically — flagged as a gap; worth a quick follow-up search if
  modelling prose style on them matters, since they are the best-known *teaching*
  style precedent even if not technically Verso-native).
- `verso-templates/textbook` is the best small, real "teach from elaborated code"
  example (confirmed: single-toolchain, custom exercise-extraction build step).

### Proposed chapter plan

Each worked example below names real declarations, grep-confirmed to exist in this
repository on 2026-10-14 (paths relative to repo root):

1. **AQFT in brief.** Prose only (no Lean). Summarize Haag–Kastler axioms,
   pointing readers at `blueprint/src/sections/` chapters 1–9 for full context
   (per `.claude/CLAUDE.md`: chapters 1–9 are background, not formalised).
2. **Lean in brief.** Prose + trivial elaborated snippets (generic Lean/Mathlib,
   not physicslib4-specific) — tactics, `#check`, `#eval`, structures.
3. **How they meet in this repository.** Explain the blueprint-as-specification
   workflow, `lake exe checkdecls`, the chapter 10 declaration-numbering scheme
   (per the project's own `home_page/index.md`, already read: "675 declarations...
   mapped onto 1,191 distinct Lean declarations").
4. **Worked example: a trivial net and its axioms.**
   - `Physicslib4.AQFT.HaagKastler.Net.HaagKastlerNet` — the flat-spacetime net
     structure (`Physicslib4/AQFT/HaagKastler/Net.lean:71`), with fields `U :
     LocalNet`, `isotony : Isotony U`, `localCommutativity : LocalCommutativity U
     isotony`, `lorentzCovariance : LorentzCovariance U isotony` (confirmed by
     direct read of lines 71–90).
   - `Physicslib4.AQFT.HaagKastler.Isotony.Isotony`
     (`Physicslib4/AQFT/HaagKastler/Isotony.lean`, read in full) — Axiom 2, with
     `map`, `injective`, `map_self`, `map_comp` fields, and its lemma
     `Isotony.exists_injective_self`.
   - `Physicslib4.AQFT.HaagKastler.LocalCommutativity`
     (`Physicslib4/AQFT/HaagKastler/LocalCommutativity.lean`, read in full) — Axiom
     3, plus `QuasilocalAlgebra.commute_ι_iff_commute_map`.
   - **Correction (orchestrator check):** a concrete net exists. Minkowski:
     `Physicslib4.AQFT.HaagKastler.trivialLocalNet`, `trivialLocalNetIsotony`,
     `trivialHaagKastlerNet`, `nonempty_haagKastlerNet`
     (`Physicslib4/AQFT/HaagKastler/Net.lean:306-382`). Curved: the same names in
     `Physicslib4.AQFT.HaagKastlerCurved` (`HaagKastlerCurved/Net.lean:343-401`). The
     scout's grep missed them because they are `def`s, not instances.
5. **Worked example: a state and its GNS representation.**
   - `Physicslib4.GNS.State` (`Physicslib4/GNS/Basic.lean:59`,
     `structure State extends A →L[ℂ] ℂ`).
   - `Physicslib4.GNS.gns_construction` and `.gns_unique`
     (`Physicslib4/GNS/Construction.lean:64,163`).
6. **Worked example: local commutativity in a diamond.**
   - Same `LocalCommutativity` def as above (flat case); for the curved/general
     setting, `Physicslib4.AQFT.HaagKastlerCurved.LocalCommutativity`
     (`Physicslib4/AQFT/HaagKastlerCurved/LocalCommutativity.lean:67`). Diamonds are the Alexandrov basis sets
     $I^+(p) \cap I^-(q)$: `Physicslib4.AQFT.HaagKastler.IsAlexandrovBasisSet`
     (`HaagKastler/LocalAlgebras.lean:62`) and, for a general spacetime,
     `Physicslib4.Spacetime.alexandrovBasis` (`Spacetime/Causality.lean:428`). Axiom 3
     is stated for spacelike-separated diamonds inside a common containing diamond.
     (Orchestrator correction: the scout flagged this as unresolved.)
7. **Worked example: Lorentz invariance of causal precedence.**
   - `Physicslib4.causallyPrecedes_smul_iff`
     (`Physicslib4/Spacetime/LorentzCausality.lean:357`, grep-confirmed), alongside
     the related `isSpacelikeRelated_smul_iff` (line 370) and
     `isCompletelySpacelike_smul_iff` (line 381) in the same file — a strong,
     directly on-topic cluster of lemmas for this chapter.
8. **Doing it yourself.** Prose + pointers to `lake exe checkdecls`,
   `leanblueprint checkdecls`, contribution guidance (cross-reference
   `README.md`'s "Contributing" section per `.claude/CLAUDE.md`'s versioning rule).
9. **Where to go next.** Links to the blueprint web/pdf, API docs, GitHub.

## Recommended layout and staged plan

**Layout:**
- New top-level `web/` directory (sibling to `blueprint/`, `home_page/`), itself a
  separate Lake package (own `lakefile.toml`, own `lean-toolchain` pinned to Verso's
  nearest usable tag — recommend starting from Verso's latest stable release tag at
  implementation time, e.g. `v4.35.0` as of 2026-10-14 — **not** `v4.34.1`, per §1).
  This keeps `web/`'s toolchain entirely decoupled from the root package's
  `lean-toolchain` (protected file, per `.claude/lean-policy.json`
  `protected_files`, which this agent must not touch regardless).
  - `web/site/` — `VersoBlog` package producing the landing page (replaces or
    augments `home_page/index.md` content), output to e.g. `web/site/_out/`.
  - `web/manual/` — `VersoManual` package producing the tutorial, consuming
    physicslib4 source/output via the decoupled `verso.exampleProject`/
    `subverso-extract-mod` mechanism (§2), output to e.g. `web/manual/_out/html-multi/`.
  - A shared theme/component package or copied assets from
    `leanprover/verso-web-components` (Apache-2.0, confirmed) for visual parity
    with verso.lean-lang.org, if desired — or a from-scratch `Theme` value styled to
    match the existing blueprint/Jekyll palette instead, which is lower-risk and
    doesn't borrow Lean-FRO branding.
  - URL paths under the existing GitHub Pages site
    (`https://physicslib.github.io/physicslib4/`, from `home_page/index.md`):
    e.g. `/tutorial/` (the Verso manual) and either replace `/` (landing page) or
    add a new `/site/` and leave `home_page/index.md` as-is initially (lower risk,
    staged — see below).

**Staged plan:**
1. **Scaffold.** Stand up `web/` as a separate Lake package off-CI (not yet wired
   into `.github/workflows/blueprint.yml`), starting from `verso-templates/basic-blog`
   and `verso-templates/package-docs` as literal copies, confirm `lake build` +
   `lake exe` succeed locally against a real Verso tag.
2. **Theme.** Adapt a `Theme` value (own styling, not necessarily `verso-web-
   components`) matching the project's existing look (`home_page/_layouts`,
   `blueprint/src/extra_styles.css` colours) or deliberately adopting Lean-FRO
   styling via `verso-web-components` — **decision needed from the user** (§ open
   questions).
3. **Website.** Build the `VersoBlog` landing page content (can start as a near-copy
   of `home_page/index.md`'s prose, since that content already exists and is
   current).
4. **Manual(s).** Build the `VersoManual` tutorial per the chapter plan above,
   settling whether `{docstring}` needs the in-process (shared-toolchain) or decoupled route
   (§2) via a small spike.
5. **CI.** Add a step to `.github/workflows/blueprint.yml` (or a new workflow) that
   runs `lake build` + `lake exe` inside `web/` and copies output into
   `home_page/` (or a new subdirectory) **before** the existing `docgen-action`
   step, per §6 — no change to the pinned `docgen-action` commit or its inputs.
6. **Retire Jekyll** (optional, later/separate decision): once the Verso site fully
   replaces `home_page/index.md`'s content and navigation, decide whether to keep
   `docgen-action`'s Jekyll pass at all (it may still be needed only to glue
   blueprint + API docs + Verso output into one `_site`, per §6's "Jekyll as
   static passthrough" finding — i.e. "retiring Jekyll" may mean "stop writing
   Markdown content for it" rather than "remove it from the pipeline", since
   `docgen-action` has no non-Jekyll assembly path as of the pinned commit).

## Open risks

1. **No Verso tag matches `v4.34.1` exactly** (§1) — mitigated by the decoupled
   external-module approach, but that approach's exact capabilities (especially
   whether `{docstring}` works cross-toolchain) are **unverified** and need a spike.
2. **Direct `require verso` + `require physicslib4` in one package is untested** and
   predicted-fragile across Lean versions (§1) — avoid unless the spike in risk 1
   shows the decoupled route is insufficient for the manual's needs.
3. *(Withdrawn after checking: the trivial net exists, `trivialHaagKastlerNet` in
   `HaagKastler/Net.lean` and `HaagKastlerCurved/Net.lean`, and diamonds are
   `IsAlexandrovBasisSet` / `alexandrovBasis`. See §7.)*
5. **plasTeX/leanblueprint's capacity for header/nav parity with a Verso theme is
   unverified** (§4) — I confirmed the `extra-css` hook exists and is in use, but not
   whether CSS alone can restyle the theme's header/nav markup to match Verso, or
   requires a plasTeX theme-directory swap (not investigated this pass).
6. **doc-gen4 styling has no first-class customisation hook** (§5) — any visual
   parity work there is a post-processing patch, which is inherently more fragile to
   doc-gen4 version bumps than a documented option would be.
7. **lean-lang.org's own source (vs. verso.lean-lang.org's, which IS confirmed)**
   was not fetched — `leanprover/lean-lang.org` redirects to
   `leanprover/leanprover.github.io`, contents/stack not examined (§3).
8. **Budget-limited gaps**, explicitly flagged inline above, that a follow-up pass
   should close before implementation: `verso-web-components`' actual file contents
   and `require`/`import` incantation (§3); whether Verso has a built-in exercise/
   error-expectation directive (§7); plasTeX theme-directory mechanism (§4);
   `build_docs.sh` and doc-gen4's HTML template internals (§5); confirmation of
   whether classic Lean tutorials (TPiL/FPiL) have Verso ports (§7).

## Questions for the user

1. Visual direction: adopt Lean-FRO's own look via `verso-web-components`
   (Apache-2.0, re-usable, but carries Lean-FRO branding cues), or a from-scratch
   theme matching the project's current blueprint/Jekyll palette?
2. Is full in-process `{docstring}` rendering of physicslib4 declarations a hard
   requirement for the manual, or is anchor-based elaborated-code-and-output
   (the decoupled, lower-risk route) sufficient? This determines whether `web/`
   must share physicslib4's exact toolchain.
3. Should the Verso site **replace** `home_page/index.md`/Jekyll outright, or sit
   alongside it at a sub-path (e.g. `/tutorial/`) while Jekyll continues to glue
   blueprint + API docs + the Verso output together (per §6's finding that
   `docgen-action` has no non-Jekyll assembly path)?
4. *(Questions on the trivial net and the name for diamonds withdrawn: both are answered in §7.)*

## Decisions recorded (2026-10-14)

1. Visual direction: the Lean FRO look via `verso-web-components`, with the project's own branding.
2. Toolchain: upgrade the project to Lean and Mathlib v4.35.0, then pin Verso v4.35.0 to match (all three
   stable `v4.35.0` tags exist, checked with `git ls-remote`). `web/` then shares the project's toolchain,
   so docstrings can be embedded directly.
3. Rollout: the Verso site goes alongside the Jekyll site first, then replaces it.

## Branding and content decisions (2026-10-15)

5. Name "physicslib4", tagline "A Lean 4 formalisation of the mathematical foundations of physics";
   plain wordmark, no logo for now. The Picasso bull image is removed from the repository (copyright).
6. Lean FRO palette with a deep-teal accent; a sample page goes to the user before the accent is final.
7. Paths while both sites coexist: `/tutorial/` (user manual), `/manual/` (reference manual), `/site/`
   (Verso landing page until it replaces the Jekyll `/`); blueprint and API docs unchanged.
8. Two books: the tutorial and the reference manual.
9. Agents draft each chapter; the user reviews. The AQFT introduction draws on blueprint Chapters 1-9.

### Prose style for the Verso site and manuals

- Audience: a physics or mathematics student entering the first year of a PhD in theoretical physics.
- Crisp and straightforward.
- When introducing a topic the reader should already know, open with a reminder, e.g. "As you will
  recall, an algebra consists of ...", or an equivalent phrase with the same meaning.
- Model: the expository style of arXiv:2410.16599.
