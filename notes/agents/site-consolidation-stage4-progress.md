# Site consolidation, stage 4: the site moves to `/`

Plan: `plan-site-consolidation-2026-10-29.md`, stage 4. Redirect table: `audit-jekyll-content-2026-10-29.md`.
Decisions applied: `guide.html` → manual conventions chapter (`#conventions-blueprint`);
`axioms.html` → manual Haag–Kastler chapter (per plan); `index.html` is not redirected.

## Step 0: survey (2026-10-29)

- Website-relative paths live in `web/Site/Links.lean` (`tutorialPath`, `manualPath`,
  `manualChapterUrl`, `siteFromBook`) and two gallery caption links in `web/Site/FrontPage.lean`
  (lines 54, 67).
- Book-to-book links (`../tutorial/…` in `Manual/*.lean`, `Manual.lean`) stay correct: both books
  remain at `/tutorial/` and `/manual/`.
- `blueprint/src/webtheme/site-header.html`: wordmark points at `…/physicslib4/site/`.
- `.github/workflows/lean_action_ci.yml`: the root-relative check greps `_out/site`, the local output
  directory, which does not change; left alone. Its comment (line 70) and its error message (line 84)
  mention `/physicslib4/site/`: stage 5 updates them.

## Step 1: paths

- `web/Site/Links.lean`: `tutorialPath = "tutorial/"`, `manualPath = "manual/"` (website-relative);
  new `tutorialFromBook = "../tutorial/"`, `manualFromBook = "../manual/"` for the books' nav;
  `manualChapterUrl slug = manualPath ++ slug ++ "/"`; `siteFromBook = "../"`. Module docstring
  rewritten for the new layout.
- `web/Site/FrontPage.lean`: the two gallery caption links `../manual/…` → `manual/…`.
- `blueprint/src/webtheme/site-header.html`: wordmark → `https://physicslib.github.io/physicslib4/`.
- No other `site/` link outside `notes/`, `.github/` and `web/README.md` (README in step 4).
- `.github/` untouched (see step 0).

## Step 2: redirects and 404

`web/redirects/` mirrors the Pages root. 11 redirect pages (meta refresh 0, `rel=canonical` to the
absolute target, `noindex`, one present-tense line with a link; relative URLs):
`guide.html` → `manual/Conventions-and-design-decisions/#conventions-blueprint`;
`axioms.html` → `manual/Haag-Kastler-axioms-in-Minkowski-spacetime/`; `sec10-1`…`sec10-7` → the
chapters of the audit table; `sec10-8-general-covariance.html` → the curved chapter's
"General covariance relates nets…" section; `site/index.html` → `../`. Anchors checked against the
generated manual HTML (`conventions-blueprint`, the §10.8 section id).

`web/redirects/404.html`: self-contained (inline tokens and header CSS, sections 1–2 of
`blueprint/src/extra_styles.css`; inline theme script from `physicslib4-theme.js`; the blueprint
header copy without the TOC button and with no active entry), every link an absolute
`/physicslib4/…` path; links home, tutorial, manual, blueprint, API docs. Generated once by a
throwaway script in `/tmp`; the files are plain static HTML.

## Step 3: local test

- `lake build` in `web/` succeeded; `generate-site`, `generate-tutorial`, `generate-manual` into
  fresh `_out/`. `leanblueprint web` from `.venv/bin` (local blueprint build).
- Assembled `/tmp/srv/physicslib4/`: site at the root, `tutorial/`, `manual/`, `blueprint/`, then
  `web/redirects/.` copied over the root. Served by a small Python server that answers misses with
  `404.html` (as GitHub Pages does). Crawler honours `<base href>`, maps
  `https://physicslib.github.io/physicslib4/…` to the local server, checks every `href`/`src` and
  fragment.
- Found during the crawl and fixed: the blueprint favicon pointed at
  `https://physicslib.github.io/physicslib4/site/favicon.png` in
  `blueprint/src/webtheme/dep_graph.html`, `templates/document-layout.jinja2`,
  `templates/default-layout.jinja2` → `…/physicslib4/favicon.png`. Blueprint rebuilt.
- Final crawl: 407 pages (root 1, tutorial 104, manual 289, blueprint 13), 27010 internal links,
  1 broken: `/physicslib4/blueprint.pdf` from the landing page (the PDF is not built locally; stage 5
  must place it at the artifact root). 99 links to `/physicslib4/docs/` not checked (not built
  locally). Missing fragments: 3108 Verso chapter tags in the books' tables of contents
  (`Chapter/#gns` etc.; Verso emits no matching id, unaffected by this stage) and 1 JS-drawn
  dependency-graph node; no other.
- Redirects: all 11 pages, plus `site/` and `site` (server adds the slash), land on their target with
  status 200, fragments present (`#conventions-blueprint`, the §10.8 section id).
- 404: served for `/physicslib4/nonexistent`, `/physicslib4/a/b/c/missing.html`,
  `/physicslib4/manual/No-such-chapter/`; its links resolve from every depth (docs 404 locally only).
  Headless-Chrome screenshot shows the header and the link list styled as the site.
- Root-relative check of `lean_action_ci.yml` on the new `_out/`: no hits.

## Step 4: README and wording check

- `web/README.md`: Layout lists `redirects/` (the 11 redirect pages and `404.html`); "Build and view
  locally" assembles the published layout (site at the root, books, optional blueprint, redirects
  over the root); "Served from a sub-path" describes the root layout and the `Site.*` path names.
- `python3 scripts/check_temporal_wording.py`: OK.

## For stage 5

- Assemble the artifact: Verso site at the root, `tutorial/`, `manual/`, `blueprint/`,
  `blueprint.pdf` (the landing page links `/physicslib4/blueprint.pdf`), `docs/`, then copy
  `web/redirects/.` over the root (it supplies `404.html` and `site/index.html`).
- `web/README.md` "Continuous integration" still describes the Jekyll deployment (`home_page/site`,
  `/physicslib4/site/`); rewrite it with the workflow.
- `.github/workflows/lean_action_ci.yml`: comment (line 70) and error message (line 84) name
  `/physicslib4/site/`.
- `.gitignore` line 14 `home_page/site/` becomes obsolete with the new workflow.
- Not committed (per instructions).
