# Plan: retire the Jekyll home page in favour of the Verso site

Completes decision 3 of `scout-verso-site-2026-10-14.md` ("alongside first, then replace"). The Verso
website (`/site/`), tutorial (`/tutorial/`) and reference manual (`/manual/`) are complete and
reviewed.

## Decisions recorded (2026-10-28)

1. Timing: merge the current branch to `main` first, so `/site/`, `/tutorial/`, `/manual/` and the
   restyled blueprint go live alongside Jekyll; switch only after they are seen working.
2. Landing-page counts: generated at build time by a small script, never maintained by hand.
3. Version statement: `README.md` alone. When Jekyll is removed, the statements in `home_page/index.md`
   and `blueprint/src/sections/sec10/introduction.tex` go, `VERSION_HOMES` becomes README only, and
   the project rule in `.claude/CLAUDE.md` is updated to match (the user approved that edit).
4. Redirects from the old URLs are kept indefinitely.
5. Deployment: option (b). Assemble the Pages artifact in the workflow (API docs, the blueprint, which
   is already built in its own step, the Verso outputs at the root); this also allows restyling the
   API docs. Jekyll and `docgen-action`'s deployment are removed.

## Current state

- **Jekyll.** `home_page/` holds the Jekyll site: `index.md`, `guide.md`, `axioms.md` and the eight
  section pages `sec10-*.md`, about 1,470 lines, plus `_config.yml`, layouts, includes, assets,
  `404.html` and the Gemfile.
- **Deployment.** `.github/workflows/blueprint.yml` builds the three Verso outputs into
  `home_page/site/`, `home_page/tutorial/` and `home_page/manual/`. `docgen-action` then builds the
  blueprint, the API docs and the Jekyll site (`homepage: home_page`), and deploys everything as one
  Pages artifact.
- **Coexistence.** Today the Jekyll page is `/` and the Verso site is `/site/`.

## Where each piece of Jekyll content goes

| Jekyll content | Destination |
|---|---|
| `index.md` Overview, Explore, Highlights | the Verso landing page, which already has a hero, feature cards and About; add a Highlights section |
| `index.md` Formalisation status | a short status section on the landing page, with no hand-maintained counts (see question 2) |
| `index.md` Useful links, Acknowledgements | landing page footer or an About section |
| `index.md` Contributing | already points to tutorial chapter 4; keep a one-line pointer |
| `index.md` version statement | the landing page's Contributing pointer, or the README only (see question 3) |
| `guide.md` | tutorial chapter 4 and the manual; drop what they already cover |
| `axioms.md` | already covered by the manual's Minkowski and curved chapters plus the conventions chapter; drop it |
| `sec10-*.md` section pages | replaced by the manual (decision recorded 2026-10-17) and the blueprint's own index |

A short audit stage (stage 1) checks this mapping line by line, so nothing is lost silently.

## Deployment options

- **(a) Keep `docgen-action`.** Put the Verso site's HTML at the root of the homepage directory and
  let Jekyll copy it through. This was tested for `/site/`, `/tutorial/` and `/manual/`.
  - Needs: a minimal `_config.yml`, no layouts, and checking that Jekyll leaves the root
    `index.html` alone.
  - Smallest change.
- **(b) Assemble the Pages artifact ourselves.**
  - Build the API docs and blueprint as `docgen-action` does, or run `docgen-action` without its
    deploy step if it allows that.
  - Copy the Verso output to the root, then use `actions/upload-pages-artifact` and `deploy-pages`.
  - Removes Jekyll entirely, at the cost of maintaining the build steps that `docgen-action` hides.

**Recommended: (a) first**, and keep (b) in reserve in case `docgen-action` interferes.

## Link continuity

External links point to `/physicslib4/index.html`, `guide.html`, `axioms.html` and
`sec10-*.html`. Each of these gets a small redirect page (an HTML meta-refresh with a canonical link)
to its new home:

- `sec10-1-gns.html` → `manual/GNS/`, and similarly for the other section pages;
- `guide.html` → `tutorial/`;
- `axioms.html` → `manual/Haag-Kastler…/`.

`/site/` also redirects to `/`. Redirects are cheap, and they keep links from papers and posts
working.

## Other changes

- **Paths.** The site moves from `/site/` to `/`. Its links to the books change from `../tutorial/`
  to `tutorial/`, and the books' links back change from `../site/` to `../`. The root-relative-URL
  check and the CI path filters are updated to match.
- **Version-statement rule.** The project rule names `home_page/index.md` as one of the three places
  for the Lean and Mathlib version. It moves to the new home (the landing page or README).
  - `.claude/CLAUDE.md` is yours to edit.
  - The agent updates `VERSION_HOMES` in `scripts/check_temporal_wording.py` to match.
- **Removal.**
  - Delete the Jekyll sources: section pages, `guide.md`, `axioms.md`, layouts, includes, assets and
    the Gemfile.
  - Keep `404.html`, rewritten in the Verso style, and the redirect pages.
  - The renumbering stage that every blueprint change needed goes away. Item numbers then live only
    in the blueprint and the manual's links.
- **`CHANGELOG.md`:** one entry.

## Stages

1. **Content audit**, read-only. Map every paragraph of the Jekyll pages to its destination or mark it
   dropped, then list the gaps.
2. **Landing page.** Add Highlights, status, links and acknowledgements to the Verso site; move the
   site to the root paths; update the cross-links between site, tutorial and manual. Build and serve
   locally under `/physicslib4/`.
3. **Redirects and 404.** Generate the redirect pages and the new 404, and test them locally.
4. **CI.** Switch `blueprint.yml` to option (a), and update the path filters and the URL check. Test
   with a local Jekyll pass-through build.
5. **Rules.**
   - You update the version-statement rule in `.claude/CLAUDE.md`.
   - The agent updates `VERSION_HOMES`, `README.md` and `CHANGELOG.md`.
6. **Remove the Jekyll sources.** Then a full local check: crawl every page and link under
   `/physicslib4/`.
7. **Merge to `main`, and verify the live site.** This is the first real deployment of the Verso pages,
   so check every top-level URL and a sample of redirects.

Each stage is one agent run with a progress log, sized to fit the session budget.

## Questions for you

1. **Timing.** Retire Jekyll before 1.0, or tag 1.0 with both sites and switch afterwards? Doing it
   first means 1.0 ships with the new site, but the Verso pages have never been deployed live.
   - A middle path: merge the current branch to `main` first, so `/site/`, `/tutorial/` and
     `/manual/` go live alongside Jekyll, and switch only after they are seen working.
2. **Counts on the landing page.** Today's numbers (declarations by kind, Lean names, pages) need
   regenerating after every blueprint change. Options:
   - drop them;
   - keep a few totals generated at build time by a small script;
   - link to the blueprint's own progress view.

   (Recommended: drop them or generate them; never maintain them by hand.)
3. **Where the version statement lives:** the landing page, or `README.md` only?
4. **Redirects:** keep them indefinitely, or for a fixed period?
