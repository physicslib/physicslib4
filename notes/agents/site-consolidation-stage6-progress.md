# Site consolidation stage 6: API docs restyle, progress log (2026-10-29)

## Step 1: survey of doc-gen4's output

Working copy: `/tmp/docsdev/physicslib4/` (copy of the CI artifact of run 40863239158), 5,904 HTML
pages under `docs/`, 724 MB.

- Every page except `navbar.html` and `find/index.html` starts its body with
  `<input id="nav_toggle" type="checkbox"><header>…</header>`. The header holds the hamburger label
  for the module tree on narrow screens (`label[for=nav_toggle]`, shown below 1000px), the title
  "Documentation", the page name (`h2.header_filename`) and `form#search_form` (input `q`,
  `#search_button` whose onclick sets `form.action` to `<SITE_ROOT>search.html`).
- `search.js` (module) finds `#search_form` and its input, appends `#autocomplete_results` to the
  form, and on Enter clicks the selected result or `#search_button`. It does not care where the
  form is. No other script refers to the header.
- Theme: `color-scheme.js` is loaded only in `navbar.html` (the module tree, an iframe in
  `nav.nav`). It reads `localStorage.theme` (`light`/`dark`/`system`), sets `data-theme` on the
  iframe's and the parent's `<html>`, and un-hides the picker `#settings` at the foot of the tree.
  `style.css` keys its variables (`--header-bg`, `--body-bg`, `--code-bg`, `--text-color`,
  `--link-color`, kind colours, `--header-height: 3em`) on `:root`, `prefers-color-scheme` and
  `[data-theme=light|dark]`.
- Layout: header `position: fixed`, height `--header-height`; `main` and the two side columns
  (`nav.nav`, `nav.internal_nav`) are offset by `--header-height + 1em`; anchors use
  `scroll-margin-top: --fragment-offset`. doc-gen4's bare `header`, `header > *` and `nav` rules
  would also hit the shared header's `<header>` and `<nav class="navbar">`, so they are reset.
- Fonts: Lato (body), JuliaMono (code), from cdnjs `@import`s.
- `find/index.html` is a redirect page with no body content; `src/` holds no HTML.

## Step 2: before screenshots

`docs-restyle/before-1280-{light,dark}-kms.png` (`Physicslib4/AQFT/KMS.html`, served from
`/tmp/docsdev` on port 8792, headless Chromium via playwright-core in `/tmp/pw`).

## Step 3: implementation

- `web/docs-theme/site-header.html`: third copy of the shared header (from
  `blueprint/src/webtheme/site-header.html`; SVGs copied byte for byte, diff checked), "API docs"
  active, links absolute under `/physicslib4/`, a `SEARCH_FORM` slot after the wordmark, and in place
  of the blueprint's table-of-contents button a `<label for="nav_toggle">` that opens doc-gen4's
  module list on narrow screens.
- `web/docs-theme/physicslib4-docs.css`: tokens and header rules copied from
  `blueprint/src/extra_styles.css` (sections 1–2), then: header fixed; doc-gen4's bare
  `header`/`nav` rules undone on it; search form (18rem, shrinks to 6rem), autocomplete below the
  header; doc-gen4's variables mapped on `html:root` (beats its `:root`/`[data-theme]`); fonts
  Open Sans / Fira Code (JuliaMono as fallback for glyphs); definitions in teal; side columns;
  doc-gen4's picker `#settings` hidden.
- `web/docs-theme/physicslib4-docs.js`: the site class (`dark-theme`) is the source; sets
  `data-theme` and `localStorage.theme` from it, and the class and `data-theme` of the module-list
  frame (or, inside the frame, of the parent), on every class change.
- `scripts/restyle_api_docs.py`: bytes-level rewrite, parallel (`ProcessPoolExecutor`), marker
  `<meta name="physicslib4-restyle">` for idempotence, assets copied in; fails if no page has
  doc-gen4's top bar.
- First run on the copy: 5,902 pages + `navbar.html` restyled, `find/index.html` left (redirect
  page), 1.0s wall (8 processes).

## Step 4: fixes after the first browser run

- Phone (390px): the module-list button and ☰ sat at x=273.05 (blueprint 269.86), the row
  overflowing by 3.19px; on <=700px the wordmark's right margin is 0.5rem (its box is unchanged) and
  the search box takes the room left (108.8px).
- The page name went nowhere: the internal nav comes between the header and `<main>`; the script
  now inserts it after the first `<main>`. Aligned with the text (8px padding).
- doc-gen4's phone module list was offset 21px to the right (its own `margin-left: 1em`); reset.

## Step 5: verification (fresh copy of the artifact's `docs/`, script run, `/tmp/pw/docs_after.js`)

Header, identical on site / manual / blueprint / docs module page / docs index, light and dark:
- 1280x800: header 1280x72 at 0,0, 16px Open Sans; wordmark 48,22.06 121.05x26.88, 22.4px
  Open Sans 600; links x/width 661.5/85.0, 754.5/156.3, 918.8/95.6, 1022.4/89.6, 1120.0/52.0,
  1180.0/52.0, all 14.4px; background rgba(249,251,253,.81) light, rgba(24,24,24,.85) dark.
  Search box (docs only) at 193.05,17.50, 200.14x36.
- 390x844: header 390x72, wordmark 24,22.05; button group 269.86,4.30 96.14x62.39 (as the
  blueprint's, which also has two buttons; site and manual 313.86 with one); search box
  153.05, 108.81x36.

Function:
- Search: typing `kmsStrip` gives 15 autocomplete results (panel 193,72, 416px wide, directly
  under the header); Enter opens `search.html?q=kmsStrip` with 15 results; ArrowDown + Enter
  opens `KMS.html#Physicslib4.AQFT.kmsStripInterior`.
- Anchor `#Physicslib4.AQFT.kmsStrip`: declaration top at 87.9px, below the 72px header;
  its source link points at GitHub (`…/KMS.lean#L50-L51`).
- Module list: current entry bold and scrolled into view; clicking `PositiveEnergy` opens it in the
  page. doc-gen4's picker hidden (`display: none`).
- MathJax: 22 `mjx-container`s on `Mathlib/Analysis/MeanInequalities.html`.
- Theme: the header switch on a docs page gives class `dark-theme`, `data-theme=dark`,
  `theme-local=dark`, `theme=dark`, body rgb(18,18,18), and the frame dark too; the manual then
  opens dark; switching back on the manual opens the docs light, frame light.
- Phone: the module-list button opens doc-gen4's list full width below the header.
- No page errors.

Idempotence: second run reports 5,903 already restyled, 0 rewritten; checksums of all files
identical before and after. Runtime on all 5,904 pages: 1.0s (8 processes), 2.2s with `--jobs 1`.

Screenshots (JPEG, 960px wide): `docs-restyle/before-1280-{light,dark}-kms.jpg`,
`after-1280-{light,dark}-kms.jpg`, `after-1280-light-search.jpg`, `after-390-light-kms.jpg`,
`after-390-light-modules-open.jpg`.

## Step 6: workflow, documentation

- `.github/workflows/blueprint.yml`: the commented hook is replaced by step "Restyle the API docs"
  (`python3 scripts/restyle_api_docs.py _site/docs`) between "Assemble the site" and "Upload the
  site"; layout comment updated. YAML parsed (Ruby `YAML.load_file`; step order checked).
- `web/README.md`: `docs-theme/` in the layout, section "The API docs" (the third copy of the
  header), CI step 6. `CHANGELOG.md`: entry.
- `python3 scripts/check_temporal_wording.py`: OK.

## Not matched / open

- Header links are root-relative `/physicslib4/…` (as requested, and as `web/redirects/404.html`),
  not `https://physicslib.github.io/physicslib4/…` as in the blueprint copy; they need the site
  served under `/physicslib4/`.
- doc-gen4's colour-scheme picker (dark/system/light) is hidden rather than kept: the header's switch
  is the one switch. doc-gen4's declaration-kind colours (theorem green, structure orange, axiom
  red) keep doc-gen4's light and dark values; definitions and instances use the teal accent.
- doc-gen4's style.css still `@import`s Lato and JuliaMono (JuliaMono remains the fallback for
  glyphs Fira Code lacks).
- Not yet checked on a CI run (plan: branch build if possible, otherwise `main`).
