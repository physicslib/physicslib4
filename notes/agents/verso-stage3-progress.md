# Verso stage 3: progress log

Infrastructure for the tutorial as its own Verso manual-genre book at `/tutorial/` (plan:
`plan-verso-stage3-tutorial-ch1-2026-10-15.md`). Appended after each step.

## Step 0: reconnaissance (2026-10-15)

- Verso `v4.35.0` (`304b856`) ships `VersoManual`; example books in `test-projects/textbook` and
  `test-projects/package-manual`: a root `#doc (Manual)` file that pulls chapters in with
  `{include 1 Module}`, and a `main := manualMain (%doc Root) (config := ...)`.
- `manualMain --output DIR` writes the multi-page HTML to `DIR/html-multi/`. Each page carries a
  relative `<base href>` and `relativize` rewrites root-relative `href`/`src` to relative ones.
- Theming: the manual's page template (`VersoManual/Html.lean`, `page`) is fixed; there is no theme
  hook like the blog genre's `Theme`. Available: `extraHead`, `extraCss`, `extraJs`, `extraCssFiles`,
  `extraJsFiles`, `extraContents` (inside `<main>`), `logo`, `logoLink`, and `extraSteps` run after the
  HTML is written. Its `<header>` holds only the book title.
- Maths: `$`…`` (inline) and `$$`…`` (display), rendered by bundled KaTeX (feature on by default:
  `-verso-data/katex/katex.{css,js}`, `math.js`, fonts).
- Collapsible blocks: no manual-genre directive (the blog genre has one; `VersoManual` uses `<details>`
  only internally). To be built.
- Figures: no figure directive in the manual genre. To be built (block extension rendering raw `Html`).
- Citations: `citet`, `citep`, `citehere` roles with `Citable` = `InProceedings`, `Thesis`, `ArXiv`,
  `Article` (no book type). `citet`/`citep` render the reference as a margin note; `citehere` inline.
  No collected bibliography page.

## Step 1: tutorial book scaffold (2026-10-15)

- `web/lakefile.toml`: `lean_lib Tutorial` (globs `Tutorial`, `Tutorial.+`) and `lean_exe generate-tutorial`
  (root `TutorialMain`), both default targets. Same Verso `v4.35.0` and toolchain; no manifest change.
- New: `web/TutorialMain.lean`, `web/Tutorial.lean` (title page "physicslib4 tutorial", includes the chapters),
  `web/Tutorial/AQFTInBrief.lean` (placeholder chapter, one present-tense paragraph),
  `web/Tutorial/FeatureTests.lean` (`draft := true`, built only with `--draft`), `web/Tutorial/Meta.lean`,
  `web/Tutorial/Papers.lean`, `web/Tutorial/Theme.lean`.
- `generate-tutorial --output DIR` writes `DIR/html-multi/` in about 3 s. `htmlDepth := 1`: one HTML page per
  chapter (sections are anchors on the chapter page). This is a one-line setting in `Tutorial/Theme.lean`.

## Step 2: shared theme (2026-10-15)

- The manual genre's page template is fixed, so the blog `Theme` cannot be reused as a whole. Shared Lean code
  instead: `Site.Theme` now has `headerWith home links isActive` and `footerWith home links` (the website's
  `header`/`footer` are instances); `Site.Links` has `navLinksFrom siteRoot tutorialRoot`, `navLinks`
  (website) and `tutorialNavLinks` (tutorial).
- `Tutorial.Theme`: one stylesheet `-verso-data/physicslib4.css` = `Site.colorTheme.toCSS` + vwc `navbar.css`
  + `Site.siteCss` + `tutorialCss` (in that order, so overrides win; separate CSS files came out in HashSet
  order and vwc's active-nav colour beat the teal one). `tutorialCss` maps `--verso-*` variables to the
  tokens (fonts, text, ToC, tooltips and tactic states in dark mode), positions the site header as the
  manual's fixed header (`--verso-header-height: 4.5rem`), restyles the manual search box (its script
  appends it to the first `<header>`, so it sits at the right of the site header), shows the book title
  at the top of the ToC (the manual normally shows it in the header), and colours the ToC triangle.
- vwc `dark.js` (theme switch, stored in `localStorage`, so shared with the website on the same origin) and
  `navbar.js` (hover highlight) as `extraJsFiles`; the favicon override as inline JS, as on the website.
  Favicon and Apple touch icon copied from `static_files/` (`extraFilesHtml`); Google Fonts link in `extraHead`.
- Header: `Tutorial.replaceHeader`, an `ExtraStep` run after the HTML is written, replaces the manual's
  `<header>…</header>` with `Site.headerWith "../site/" tutorialNavLinks (· == "Tutorial")`; it fails the
  build if a page has no `<header>`. The book has no footer (the manual's previous/next links end each page).
- `Site/Diagram.lean` imports only `Verso.Output.Html` (was `VersoBlog`), so the tutorial can use it.

## Step 3: features (2026-10-15)

- Maths: Verso's KaTeX (bundled, no CDN). `\mathfrak{U}(\mathbf{B})`, `I^+(p)\cap I^-(q)` inline and
  `\langle \Omega, \pi(a)\Omega\rangle` displayed all render; every page links `-verso-data/katex/katex.css`,
  `katex.js`, `math.js`; the 60 font files are emitted and the browser loads the needed ones (200).
- Collapsible: no manual-genre directive, so `Tutorial.Meta` defines `exercise` (teal-ruled box labelled
  "Exercise") and `solution` (`<details class="solution">`, collapsed, summary "Solution").
- Figure: `:::figure "diamond"` + caption renders `Site.diamondDiagram` in a `<figure>`; light/dark colours
  follow the CSS classes from `siteCss`. Unknown names are an elaboration error.
- Citations: Verso's `citet`/`citep` (author–year with a numbered margin note holding the full reference)
  and `citehere` (full reference inline), with `Article` (Haag–Kastler 1964, Brunetti–Fredenhagen–Verch 2003)
  and `ArXiv` (Grossi 2024, arXiv:2410.16599) entries in `Tutorial/Papers.lean`. No book type (Haag's *Local
  Quantum Physics*) and no collected bibliography: further reading is a plain Markdown list. `citep` adds its
  own leading space; Verso leaves a space between a margin-note marker and following punctuation.
- Tests kept in the draft-only chapter `Feature tests`, which doubles as a markup example for the writer.

## Step 4: paths, website links (2026-10-15)

- `Site/Tutorial.lean` stub removed (and its route); website Tutorial nav and "Read the tutorial" go to
  `../tutorial/`; the tutorial's wordmark goes to `../site/`, Reference manual to `../site/manual/`.
- Served `/tmp/srv/physicslib4/{site,tutorial,tutorial-draft}` with `python3 -m http.server 8765`; a crawler
  (`/tmp/check_urls2.py`, prefix `/physicslib4/`) starting from the site and from the tutorial: 109 local
  URLs, all 200. Its one 404 (`tutorial/-verso-search/xref.json`) is an artefact: the crawler resolves
  `fetch("xref.json")` against the script, the browser against `<base>`; the server log shows the browser's
  `/physicslib4/tutorial/xref.json` 200. No root-relative `href`/`src` in either output.
- Jekyll pass-through (`/tmp/jk/home_page`, as in stage 2): `_site/tutorial` identical to the input except an
  extra `-verso-search/licenses.html` rendered from `licenses.md` (harmless).

## Step 5: CI, .gitignore, README (2026-10-15)

- `blueprint.yml`: step renamed "Build the Verso site and tutorial into home_page"; adds
  `generate-tutorial --output _out/tutorial`, copies `html-multi` to `../home_page/tutorial`, removes
  `.lake` and `_out`. Tested locally (copy identical).
- `lean_action_ci.yml`: step "Build the Verso site and tutorial" builds both into `_out/`; the root-relative
  URL check covers `_out/site` and `_out/tutorial/html-multi`. Change filter unchanged (`web/` covers it).
- `.gitignore`: `home_page/tutorial/`. Both YAML files parse. `web/README.md` rewritten for both documents.
  `scripts/check_temporal_wording.py` passes.

## Step 6: screenshots and review (2026-10-15)

- `notes/agents/verso-tutorial-light.png`, `notes/agents/verso-tutorial-dark.png` (1440 wide; the page is
  shorter than the 900 px viewport, so full height is 900).
- Critical look: header, accent and dark mode match the website; the ToC lists the chapter twice (book
  contents and the chapter's own contents, standard manual layout); content column is left-aligned with the
  right margin reserved for margin notes; on phones (390 px) there are two burger icons, the manual's ToC
  toggle at the left and the site menu at the right; the search box is hidden below 1024 px, where the vwc
  header switches to its mobile menu.
