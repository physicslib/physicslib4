# Verso site, stage 1: progress log

Local only, no CI. Package lives in `web/`. Appended after each step.

## Step 0: reconnaissance (2026-10-15)

- Verso tag `v4.35.0` = commit `304b856`; its own `lean-toolchain` is `v4.35.0`. Deps: Cli `c24fe60`,
  illuminate `f77493b`, plausible `dfa4f38`, MD4Lean `31907cc`, subverso `892d6dc`.
- `verso-web-components` has tag `v4.35.0` (`lean-toolchain` `v4.35.0`; its manifest pins verso `304b856`,
  i.e. Verso `v4.35.0`). `main` has moved on to `v4.36.0-rc1`, so pin the tag, not `main`.
- Template: `verso-templates/basic-blog` (lakefile.toml, `lean_lib Blog`, `lean_exe generate-blog`).
- The vwc theme (`Verso.Web.theme`) hard-codes the Lean logo in `NavBar.render` and `Footer.render`.
  To keep a plain wordmark and no Lean branding, the site reuses vwc's `head`, CSS, JS and the
  `ThemeConfig` design tokens (copied from `leanprover/reference-manual` `Tutorial/Meta/Theme.lean`),
  with its own header/footer markup using vwc's CSS classes.
- Overlap with the root manifest (physicslib4 at v4.35.0): plausible, Cli, MD4Lean are the same revs
  in both; illuminate and subverso are Verso-only. No version conflict expected; to be tested.

## Step 1: package scaffold (2026-10-15)

- Created `web/lean-toolchain` (`leanprover/lean4:v4.35.0`), `web/lakefile.toml` (requires `verso` @ `v4.35.0`,
  `versowebcomponents` @ `v4.35.0`, `physicslib4` from `..`), `web/.gitignore` (`/.lake/`, `/_out/`).
- `lake update` in `web/`: **resolved with no conflict.** Manifest: verso `304b856`, versowebcomponents `a1eb0c3`,
  mathlib `56a0058` (same as root), doc-gen4 `0e1ffe2`, subverso `892d6dc`, illuminate `f77493b`, Cli `c24fe60`,
  plausible `dfa4f38`, MD4Lean `31907cc`. Mathlib post-update hook fetched the cache (all files already local).
  Root `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` untouched (git status confirms).


## Step 2: site sources, build and render (2026-10-15)

- `web/Main.lean` (`generate-site` exe, `blogMain`), `web/Site.lean`, `web/Site/Theme.lean` (vwc CSS/JS/head and
  design tokens; own header/footer with a text wordmark; teal `--color-primary` `#0f766e`, dark `#0d9488`),
  `web/Site/FrontPage.lean` (title, tagline, paragraph, blueprint and API-docs links, elaborated example).
- Elaborated example works in-process: `import Physicslib4.AQFT.HaagKastler.Net`, `leanInit` + `lean` block with
  `#check Physicslib4.AQFT.HaagKastler.trivialHaagKastlerNet`, and a `leanOutput` block that Verso checks against
  the real output (`... : Physicslib4.AQFT.HaagKastler.HaagKastlerNet`).
- `lake build` in `web/`: 6714 jobs, about 2 minutes (Verso and vwc compiled; physicslib4 oleans reused from
  `../.lake/build`, not rebuilt). `lake exe generate-site --output _out/site` writes `index.html`, `-verso-data/`
  (all 16 referenced CSS/JS files present) and `-verso-docs.json`. Served with `python3 -m http.server`; all
  assets return 200; headless-Chrome screenshot checked.
- Known nit: vwc's `head` always emits `<link rel="apple-touch-icon" href="apple-touch-icon.png">`, which 404s
  (no logo by design). Favicon links point at `data:,`.
- `web/README.md`, `web/.gitignore` written. Nothing committed.

## Step 3: redesign brief received; why the example had no highlighting (2026-10-15)

User feedback: too minimal, no visible highlighting, lede too long, nav needs Tutorial and Reference manual.

Findings (compared live lean-lang.org and verso.lean-lang.org HTML/CSS, vwc sources):
- Verso does emit highlighted markup (`.hl.lean` with `.keyword`/`.const`/`.var` token spans, hover data in
  `-verso-docs.json`, tippy/popper loaded). But Verso's `verso-vars.css` sets
  `--verso-code-keyword-color`, `--verso-code-const-color`, `--verso-code-var-color` all to
  `var(--verso-code-color)` (black): by default keywords are only bold and variables only italic.
  Both Lean sites keep that monochrome look, and vwc's `code-gallery.css` even forces
  `.hl.lean span { color: var(--color-text) !important }`.
- Our snippet (`#check <one constant>`) had no binders and one keyword, so it rendered as plain black
  text: nothing to make bold or italic, and outside any framed component.
- The frame on lean-lang.org is vwc's `codeGallery` block component (tabs, 2px primary border, caption
  footer), which is not a directive; it needs a small directive wrapper to be used from Verso markup.
- Fix: set the Verso code-colour variables (teal keywords, amber constants, italic variables; dark-mode
  values), override the gallery's forced monochrome, show a real statement with binders in a
  `codeGallery`, and keep hovers (Verso's built-in tippy + docs JSON).

## Step 4: landing-page redesign built (2026-10-15)

- New files: `web/Site/Links.lean`, `web/Site/Components.lean` (directives `hero`, `landingSection`, `gallery`
  wrapping vwc `codeGallery`, `features` using vwc `learnCard`/`cardGrid`; buttons via vwc `button`),
  `web/Site/Diagram.lean` (inline SVG causal diamonds, CSS-class colours), `web/Site/Tutorial.lean`,
  `web/Site/Manual.lean` (stubs at `/tutorial/`, `/manual/`), `web/static_files/{apple-touch-icon,favicon}.png`
  ("p4" tile, rendered with headless Chrome). `Theme.lean`, `FrontPage.lean`, `Main.lean`, `Site.lean`, README updated.
- Page: hero (wordmark, tagline, the one sentence, buttons Read the tutorial / Blueprint / API docs, diagram with
  caption); "Checked by Lean" code gallery with two tabs (`causallyPrecedes_smul_iff` restated as an `example`
  with local notations 𝕄 and ≺ set up in a hidden block; `Nonempty HaagKastlerNet.{0}` from
  `trivialHaagKastlerNet`); six feature cards linking to the `sec10-*.html` guide pages; About section.
- Nav (header and footer, same order): Tutorial, Reference manual, Blueprint, API docs (+ GitHub, theme switch).
- 404s fixed: `apple-touch-icon.png` now exists; vwc `dark.js` rewrote the favicon to `/static/favicon-*.ico`, so an
  inline script after the footer redefines `updateFaviconForSystemTheme` as a no-op.
- Checks: all local `href`/`src` on the three pages resolve; 19 hoverable tokens, `-verso-docs.json` served (200).
  Screenshots: `notes/agents/verso-landing-light.png`, `notes/agents/verso-landing-dark.png`.
- Nits left: the active nav pill uses vwc's background tint (bluish); card footer label "OPEN" is fixed by vwc's
  `learnCard`; hovers verified by markup and served JSON, not by an interactive hover in a browser.

## Step 5: four tweaks (2026-10-15)

- Feature cards: own markup (`features` in `Site/Components.lean`, `.feature-card*` in `siteCss`) replaces vwc
  `learnCard`; whole card is one link, §10 tags kept, teal "Read more →".
- Nav: active item tint overridden to teal (`rgba(15,118,110,0.12)`; dark `rgba(45,212,191,0.16)` with `#5eead4`
  text); dark `--color-hover` (hover pill) is a teal tint.
- New `centeredSection` directive: "Checked by Lean" and "About" headings and paragraphs centred, max width
  42rem; code box unchanged.
- Rebuilt and regenerated; all local links/assets resolve. Full-height screenshots (page height 2566 px,
  measured) refreshed: `notes/agents/verso-landing-light.png`, `notes/agents/verso-landing-dark.png`.
