# Blueprint restyle: progress log (2026-10-28)

## Step 1: mechanism survey

- leanblueprint 0.0.20, plasTeX 3.1, plastexdepgraph 0.0.5, plastexshowmore 0.0.2 (`.venv`).
- plasTeX themes (`[general] theme`, `extra-templates`): only one theme directory is loaded, and
  its extras (styles, js, `symbol-defs.svg`) are copied from it; a project theme therefore has to
  duplicate plasTeX's default theme files. Templates in an `extra-templates` root are loaded before
  the theme, so the theme's `default-layout.jinja2` overrides them.
- Package template directories (`PackageTemplateDir`, as used by leanblueprint and
  plastexdepgraph) are loaded after the theme, so they override the layout. A local plasTeX
  package is found through `[general] packages-dirs` in `plastex.cfg`.
- The dependency graph page is rendered from plastexdepgraph's `templates/dep_graph.html`, which
  the package option `tpl=` replaces.

## Step 2: before screenshots

- Served `/tmp/srv/physicslib4/{site,tutorial,manual,blueprint}` on port 8791 (8765 is taken by
  another process). Script `/tmp/pw/bp.js` (playwright-core, headless Chromium).
- Before: blueprint header 1280x34 (index), 1280x48 (chapter), 1280x47 (dependency graph), grey
  `#f2f2f2`, Times body text; site and manual header 1280x72, wordmark at x=48, links at
  661.5 / 754.5 / 918.8 / 1022.4, 14.4px. Screenshots `blueprint-restyle/before-*.png`.

## Step 3: implementation

- `blueprint/src/webtheme/physicslib4web.py`: plasTeX package (loaded by `\usepackage{physicslib4web}`
  in `web.tex`, found through `packages-dirs=webtheme` in `plastex.cfg`); registers
  `webtheme/templates/` (layouts) and the theme script, and puts `site-header.html` in
  `rendererdata['html5']['site_header']`.
- `webtheme/templates/{default,document}-layout.jinja2`: plasTeX's default layouts with the header
  replaced, fonts/icon/theme script in the head, the document title at the top of the TOC.
- `webtheme/dep_graph.html`: plastexdepgraph's template with the same header, selected by
  `tpl=webtheme/dep_graph.html` on `\usepackage{blueprint}` (blueprint.sty ignores options).
- `webtheme/physicslib4-theme.js`: light/dark switch, same localStorage keys as the website.
- `blueprint/src/physicslib4web.sty`: empty LaTeX stub; plasTeX compiles the web version's
  pictures (tikz-cd) with real LaTeX and the web.tex preamble, which failed with
  "File `physicslib4web.sty' not found" without it.
- `extra_styles.css`: tokens, header, page, boxes, dependency graph.
- Build: OK, warnings identical to before (includegraphics, PostScript specials).

## Step 4: fixes after the first screenshots

- Theorem boxes had no border: plasTeX's class is `<kind>_thmwrapper theorem-style-<style>`, so
  `[class$=_thmwrapper]` never matched; `[class*=_thmwrapper]` does.
- TOC: theme-white's `li.current { font-weight: 700 }` was inherited by the sub-entries; reset.
- Dependency graph: node dialog moved below the header; multi-declaration "Lean" tooltip in teal.

## Step 5: verification (clean rebuild, `rm -rf blueprint/web && leanblueprint web`)

- Build exit 0; warnings identical to the build before the change.
- Header, 1280x800, light and dark, site / manual / blueprint index / chapter / dependency graph:
  header 1280x72, wordmark 48,22.06 121.05x26.88 at 22.4px Open Sans 600; links
  Tutorial 661.5/85.0, Reference manual 754.5/156.3, Blueprint 918.8/95.6, API docs 1022.4/89.6,
  GitHub 1120.0/52.0, theme 1180.0/52.0, all 14.4px; background rgba(249,251,253,.81) light,
  rgba(24,24,24,.85) dark. Identical on all five pages.
- 390x844: header 390x72, wordmark 24,22.05 on all pages; the ☰ button keeps its place, and on
  pages with a TOC the TOC button sits left of it (toggle group 269.86..366, site 313.86..366).
- Interaction: theme switch (class + `theme-local`), L∃∀N dialog with the doc links, proof
  expand, 16109 MathJax containers, no page errors; phone TOC and navigation menu open; dependency
  graph renders 695 nodes with leanblueprint's status colours (#1cac78, #9cec8b, #b0eca3, #a3d6ff,
  green/blue borders), legend and node dialog work.
- Links: absolute under https://physicslib.github.io/physicslib4/. Relative `../site/` would
  resolve from every blueprint page (all pages sit in one directory) when deployed side by side,
  but not in `leanblueprint serve` (root is blueprint/web) or from disk, so absolute is used,
  as the Verso documents do for the blueprint and API docs.
- PDF: `latexmk -g` on print.tex rebuilds; `print.fls` references none of the new files.
- Pre-existing, not changed: the title page shows the title twice (`\maketitle` in web.tex and
  in the content).
- Docs: `web/README.md` section "The web blueprint"; CHANGELOG entry. `check_temporal_wording.py` OK.
- Screenshots: `blueprint-restyle/{before,after}-<width>-<mode>-<page>[-header].png`, plus
  `after-1280-light-bp-{theorem-box,theorem-proof,lean-modal,proof-open,depgraph-legend,depgraph-node}.png`,
  `after-390-light-bp-{toc-open,nav-open}.png`.
- Risk: CI's docgen-action installs leanblueprint/plasTeX itself; the copied layouts follow
  plasTeX 3.1 / plastexdepgraph 0.0.5 and would need refreshing if those templates change.
