# Site consolidation, stage 3: progress log (2026-10-29)

## Item 1: Conventions chapter gaps (done, before build)

- `web/Manual/Conventions.lean`, "How the blueprint and the Lean fit together": removed the
  `guide.html` sentence; added a paragraph "_Chapters 1 to 9._" with one bullet per blueprint
  chapter 1–9 (linking `blueprint/chptr-*.html`, file names taken from the local `blueprint/web/`),
  each naming the axiom and the point it settles; added that items 1–12 are background results
  quoted there and that Chapters 1–9 have no Lean declaration.
- Replaced the "section pages" sentence (`sec10-5-spacetime.html`) with: the web blueprint links
  every entry to its declarations, the dependency graph shows each entry's status, and each manual
  chapter opens its subsections with the entries they cover.

## Item 2: links to Jekyll pages (done, before build)

- Manual "Where to look" footers (GNS ×2, Spectral, Unbounded, Stone, Spacetime, HaagKastler,
  Curved ×2): the section-page links are removed; the sentence now says each entry of the linked
  blueprint section links to its Lean declarations (retargeted to the blueprint, which was already
  linked beside them).
- Conventions ×2: see item 1 (`guide.html` replaced by the chapter map; `sec10-5` sentence
  retargeted to the web blueprint and dependency graph).
- `Site/FrontPage.lean` gallery caption links: `sec10-5-spacetime.html` → `../manual/Spacetime-and-geometry/`,
  `sec10-6-haag-kastler.html` → `../manual/Haag-Kastler-axioms-in-Minkowski-spacetime/`. The gallery
  link is a plain-text block of the markup, so it cannot call `manualChapterUrl`; the docstring of
  `manualChapterUrl` and `web/README.md` now say so (stage 4 must update these two paths too).
- `Tutorial/DoingItYourself.lean`: the `home_page/` bullet is removed; the `web/` bullet describes the
  website, tutorial and manual.
- Total: 13 links + 1 bullet.

## Build, serve, crawl, wording check

- `lake build`, `generate-site`, `generate-tutorial`, `generate-manual`: all succeed (only the existing
  module-system warning on `Manual/Spacetime.lean`). Output dirs deleted first.
- Served under `/tmp/srv/physicslib4/{site,tutorial,manual}`; crawler `/tmp/crawl3/crawl.py`, 460 pages.
  - Missing pages: 0.
  - Links to Jekyll pages (`/physicslib4/`, `index.html`, `guide.html`, `axioms.html`, `sec10-*.html`): 0.
  - Links into the published blueprint, checked against the local `blueprint/web/` files and ids
    (including the nine new chapter links): 0 broken.
  - Unresolved fragments: 13 distinct targets, all a chapter page's own tag
    (`…/Bounded-spectral-theory/#spectral`, `…/AQFT-in-brief/#aqft-in-brief`, …) from Verso's
    table of contents. The pages load at the top; Verso emits no id for a chapter's own heading in
    `html-multi`. Not caused by this stage.
- Gallery caption links on the landing page render as `../manual/Spacetime-and-geometry/` and
  `../manual/Haag-Kastler-axioms-in-Minkowski-spacetime/`.
- `python3 scripts/check_temporal_wording.py`: OK.
- Grep of `web/` for Jekyll-page links afterwards: none (only `publishedRoot`, a prefix, and the
  blueprint chapter file `chptr-original-haag-kastler-axioms.html`, which matches `axioms.html`
  by suffix).
