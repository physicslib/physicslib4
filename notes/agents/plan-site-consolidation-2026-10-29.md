# Plan: site consolidation (API docs style, links, audit, retiring Jekyll)

Supersedes the stage list of `plan-retire-jekyll-2026-10-28.md`; its recorded decisions still hold:
- merging to `main` first is done (#48–#50), and the Verso pages are live;
- counts are generated at build time;
- the version is stated in `README.md` alone;
- redirects are kept indefinitely;
- deployment uses option (b), assembling the Pages artifact ourselves.

## Decisions recorded (2026-10-29)

1. Feature cards link to the top of each reference-manual chapter.
2. doc-gen4's search moves into the shared header on the API docs pages (its own top bar is folded
   away, keeping search, navigation and the theme switch working).
3. The first full run of the API docs restyle may be on `main`.

## Goals (from the user, 2026-10-29)

1. **API docs (`/docs/`) styled like the rest of the site.** The same fonts and colours, and the same
   shared header as the website, tutorial, manual and blueprint, with "API docs" marked as the
   current page and doc-gen4's content below it.
2. **A content audit** of the Jekyll pages before anything is removed.
3. **The website's "What is formalised" cards** link to the matching reference-manual chapter, for
   example the Haag–Kastler card to `/manual/Haag-Kastler-axioms-in-Minkowski-spacetime/#…`.
4. **Retire the Jekyll home page,** so the Verso site is at `/`.

## Stages

Each stage is one agent run with a progress log, sized for the session budget, and ends in a commit.

1. **Feature-card links.** Point the six cards on the Verso landing page at the reference-manual
   chapters. Use the chapter's anchor for its main section, taken from the generated HTML (verified,
   not guessed).
   - Write the link through one helper that knows where the site lives, so that moving the site from
     `/site/` to `/` in stage 4 changes the paths in one place.
   - Build, serve and crawl locally.
   - Independent and small, so it goes first.
2. **Content audit,** read-only. Map every paragraph of `home_page/index.md`, `guide.md`, `axioms.md`
   and the eight `sec10-*.md` pages to its destination: the landing page, the tutorial, the manual,
   the blueprint, or dropped with a reason. List the gaps. The output is a memo; you decide on the
   gaps.
3. **The landing page takes over `index.md`.**
   - Add what the audit assigns to it: Highlights, a status section, useful links and
     acknowledgements.
   - Generate the counts at build time: a small script reads the built blueprint (declarations by
     kind, Lean names) and writes a data file that the Verso page reads.
   - Fill whatever gaps you approved in the tutorial or manual.
4. **Move the site to `/`.**
   - The Verso website is generated at the root of the Pages output.
   - Update the links between the website, tutorial and manual: `tutorial/` and `manual/` instead
     of `../tutorial/`, and `../` instead of `../site/`. This includes the blueprint header copy and
     the stage 1 helper.
   - Write the redirect pages: `sec10-*.html` to the matching manual chapters, `guide.html` to the
     tutorial, `axioms.html` to the manual's axiom chapter, and `/site/` to `/`.
   - Write a new `404.html` in the site style.
   - Test everything locally under `/physicslib4/`.
5. **Deployment, option (b).** Rewrite `.github/workflows/blueprint.yml` to assemble the Pages artifact
   itself:
   - the Lean build;
   - the API docs, with doc-gen4 run as `docgen-action` runs it (the docbuild package), keeping the
     swap step;
   - the pinned blueprint step;
   - the Verso outputs at the root;
   - `actions/upload-pages-artifact` and `actions/deploy-pages`.

   Jekyll and `docgen-action`'s deployment are removed, and so is the `ubuntu-24.04` pin. The API
   docs step leaves a hook for stage 6.
6. **API docs restyle.** A post-processing script runs over doc-gen4's HTML in the workflow.
   - It inserts the shared header, with "API docs" marked current, on every page.
   - It adds a stylesheet that maps doc-gen4's own CSS variables and fonts to the site's: fonts,
     colours, teal accent, light and dark mode.
   - doc-gen4's search, navigation tree, declaration anchors and source links must keep working.
   - Develop it locally against a sample of the live `/docs/` pages, downloaded, rather than a local
     doc-gen4 build, which builds docs for all of Mathlib and takes hours. Then check a full run on a
     branch build if possible, and otherwise on `main`, with the old pages still served until it
     succeeds.
7. **Rules and text.**
   - Remove the version statements from `home_page/index.md` (deleted with Jekyll) and from
     `blueprint/src/sections/sec10/introduction.tex`.
   - `VERSION_HOMES` becomes `README.md` only.
   - Update the rule in `.claude/CLAUDE.md` (approved).
   - Add a `CHANGELOG.md` entry, and update `README.md` where it points to the home page.
8. **Remove the Jekyll sources and verify.**
   - Delete `home_page/`'s Jekyll files (layouts, includes, assets, Gemfile, `_config.yml`, the
     Markdown pages), keeping only what stage 4 still needs.
   - Remove the home-page renumbering from future blueprint work, since item numbers then live only
     in the blueprint.
   - Run a full local crawl of every page and link.
9. **Merge and check live.** A pull request into `main`, merged once CI passes. Then check every
   top-level URL, the redirects, the API docs with the new header, and the dark mode across all five
   kinds of page.

Order and dependencies:
- **1 and 2** are independent and can go first.
- **3** follows 2.
- **4** follows 3.
- **5** follows 4.
- **6** needs the hook from 5.
- **7 and 8** come last, before 9.

## Questions for you

1. **Card anchors.** Link each card to the top of its chapter, or to the chapter's "Main definitions and
   theorems" section, which is the closest to your `#haag-kastler` example?
2. **doc-gen4's own top bar.** It has search and a theme switch. Keep it below the shared header,
   restyled, or fold its search into the shared header? Keeping it is safer; folding it in is
   cleaner.
3. **Testing the API docs restyle.** Is a first full run on `main` acceptable, given the old pages stay
   live until a run succeeds?
