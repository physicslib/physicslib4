# physicslib4 website, tutorial and reference manual

Three documents written with [Verso](https://github.com/leanprover/verso):

- the website: the physicslib4 landing page, in Verso's website (`VersoBlog`) genre, styled with
  [verso-web-components](https://github.com/leanprover/verso-web-components), the components behind
  lean-lang.org;
- the tutorial: a book in Verso's manual (`VersoManual`) genre, with one chapter per file;
- the reference manual: a second manual-genre book, with one chapter per section of Chapter 10 of
  the blueprint.

All three share one look: the verso-web-components design tokens with a deep-teal accent, and the
same header with the "physicslib4" wordmark and the navigation About, Tutorial, Roadmap, Get involved,
Reference manual, Blueprint, API docs.

This directory is a Lake package of its own. It requires physicslib4 from `..`, so the Lean
examples on the page are elaborated against the library itself.

## Layout

- `lakefile.toml`, `lean-toolchain`: the package and its pinned Verso and verso-web-components versions.
- `Main.lean`: the site structure and the `generate-site` executable.
- `Site/Links.lean`: the tagline, the navigation links of the website and the books, and the URLs
  of the blueprint and API docs (`apiDocsUrl` for one declaration).
- `Site/Theme.lean`: the website theme (header, footer, design tokens, accent colour, code colours).
  The header, the design tokens and the stylesheet are also used by the books.
- `Site/Components.lean`: the page directives (hero, sections, code gallery, feature cards, `pageToc`,
  `anchoredHeading`, and the Get Involved page's `sideFigure`, `contributeSteps`, `contributeCards` and
  `callout`),
  built on verso-web-components.
- `Site/Diagram.lean`: the causal-diamond diagram, as inline SVG.
- `Site/FrontPage.lean`: the landing page.
- `Site/About.lean`, `Site/Roadmap.lean`, `Site/GetInvolved.lean`: the About, Roadmap and Get Involved
  pages, at `about/`, `roadmap/` and `get-involved/`.
- `Book/Theme.lean`: what the two books share: their stylesheet (the website's, plus `bookCss`, which
  restyles the manual genre), their HTML configuration `Book.config` and `Book.replaceHeader`,
  which puts the website header on every page.
- `Book/Meta.lean`: the role `apiDocs`, a link to the API docs of a declaration.
- `TutorialMain.lean`: the `generate-tutorial` executable.
- `Tutorial.lean`: the tutorial's title page; it includes the chapters.
- `Tutorial/AQFTInBrief.lean`: chapter 1, "AQFT in brief".
- `Tutorial/LeanInBrief.lean`: chapter 2, "Lean in brief".
- `Tutorial/WorkedExamples.lean`: chapter 3, "Worked examples".
- `Tutorial/DoingItYourself.lean`: chapter 4, "Doing it yourself".
- `Tutorial/FeatureTests.lean`: a draft-only chapter showing the markup for maths, exercises,
  figures and citations; built only with `--draft`.
- `Tutorial/Meta.lean`: the directives `exercise`, `solution` (collapsible), `figure`, and `goals`,
  which shows the proof state after every tactic of the Lean block it wraps.
- `Tutorial/Papers.lean`: the works cited with the manual genre's `citet`, `citep` and `citehere`.
- `Tutorial/Theme.lean`: the tutorial's configuration and header, built from `Book/Theme.lean`.
- `ManualMain.lean`: the `generate-manual` executable.
- `Manual.lean`: the reference manual's title page; it includes the chapters.
- `Manual/GNS.lean`: "The GNS construction" (blueprint Section 10.1).
- `Manual/Spectral.lean`: "Bounded spectral theory" (blueprint Section 10.2).
- `Manual/Unbounded.lean`: "Unbounded operators and their spectral theorem" (blueprint
  Section 10.3).
- `Manual/Stone.lean`: "Stone's theorem" (blueprint Section 10.4).
- `Manual/Spacetime.lean`: "Spacetime and geometry" (blueprint Section 10.5).
- `Manual/HaagKastler.lean`: "The Haag–Kastler axioms in Minkowski spacetime" (blueprint
  Section 10.6).
- `Manual/Curved.lean`: "The axioms in curved spacetime and general covariance" (blueprint
  Sections 10.7–10.8).
- `Manual/Conventions.lean`: "Conventions and design decisions", the library's conventions and
  design decisions, each stated once with links to where it matters.
- `Manual/NotProved.lean`: "Appendix: what the library does not prove", the standard facts the
  chapters mark as not proved, in one list.
- `Manual/FeatureTests.lean`: a draft-only chapter showing `{docstring}`, `#check` and `apiDocs`;
  built only with `--draft`.
- `Manual/Theme.lean`: the manual's configuration and header, built from `Book/Theme.lean`.
- `docs-theme/`: the header, stylesheet and theme script that `scripts/restyle_api_docs.py` puts on
  the API docs; see "The API docs" below.
- `static_files/`: the "p4" wordmark icons (favicon and Apple touch icon), used by all three.
- `redirects/`: static pages copied over the root of the published site, with the same paths as
  there, so that links to these addresses keep working. `guide.html`, `axioms.html`, the eight
  `sec10-*.html` section pages and `site/index.html` each hold a page that redirects at once
  (`<meta http-equiv="refresh">`, with `<link rel="canonical">` and a link) to its place in the
  reference manual or, for `site/`, to the website at `../`. Their URLs are relative. `404.html` is the
  site's "page not found" page: GitHub Pages serves it at any depth, so it is self-contained (the
  design tokens, header rules and theme script of the web blueprint, inlined) and its links are
  absolute paths under `/physicslib4/`.

## Writing the tutorial

A chapter is a module `Tutorial/<Name>.lean` with a `#doc (Manual) "<Title>" =>` document, included
from `Tutorial.lean` with `{include 1 Tutorial.<Name>}`. Each chapter is one HTML page.

- Maths: `` $`\mathfrak{U}(\mathbf{B})` `` inline and `` $$`\langle \Omega, \pi(a)\Omega\rangle` ``
  displayed, rendered by KaTeX, which Verso bundles (stylesheet, script and fonts in
  `-verso-data/katex/`, no CDN).
- Exercises: an `exercise` directive, with the solution in a nested `solution` directive, which is
  an HTML `<details>` element, collapsed until opened.

  ```
  :::::exercise
  Statement.

  ::::solution
  Solution.
  ::::
  :::::
  ```
- Figures: `:::figure "diamond"` followed by the caption and `:::` shows the causal-diamond diagram
  of the landing page (`Site/Diagram.lean`). Further diagrams are added to `Tutorial.diagrams`.
- Proof states: Verso shows the goal after a tactic when the reader clicks it. To show every goal
  without a click, as in a worked proof, wrap the Lean block in `goals`:

  ````
  :::goals
  ```lean
  example (a b : ℕ) : a + b = b + a := by
    rw [Nat.add_comm]
  ```
  :::
  ````
- Lean code: a chapter that elaborates library code imports the library modules it needs and
  opens `Verso.Genre.Manual.InlineLean`. A `lean` block containing `sorry` builds (the warning is
  shown, not fatal); `lean +error` marks a block that must fail; `leanOutput name` after
  `lean (name := name)` shows a message and fails the build if it changes; `lean -show` checks code
  without displaying it. Code lines are kept within 60 columns.
- Citations: `{citet haagKastler1964}[]` gives "Haag and Kastler (1964)" and
  `{citep brunettiFredenhagenVerch2003}[]` "(Brunetti, Fredenhagen, and Verch, 2003)", each with the
  full reference as a numbered margin note; `{citehere grossi2024}[]` gives the full reference
  inline. `citep` supplies its own leading space, so write it directly after the preceding word. The
  manual genre has types for articles, conference papers, theses and arXiv preprints but not for
  books, and it builds no collected bibliography: books, and a further-reading list, are written as
  ordinary Markdown lists with links.

## Writing the reference manual

A chapter is a module `Manual/<Name>.lean`, included from `Manual.lean` with
`{include 1 Manual.<Name>}`; each chapter is one HTML page. A chapter gives its page a readable file
name in its metadata (`file := "Haag-Kastler-axioms-in-Minkowski-spacetime"`); otherwise the name is
made from the title, with `___` for an en dash. The markup of the tutorial applies (maths, Lean
blocks, citations; the directives of `Tutorial.Meta` are available by importing it). Declarations
are shown in two ways, both elaborated against the library, so a renamed declaration breaks the
build:

- Definitions and structures: `{docstring Physicslib4.AQFT.HaagKastler.LocalNet}` on a line of its
  own shows a box with the signature, the docstring and, for a structure, the constructor and the
  fields with their types and docstrings. Fields inherited from a parent structure are hidden; the
  parent is listed under "Extends" with a checkbox that shows them. `+hideFields` and
  `+hideStructureConstructor` drop the fields and the constructor. Field types that do not fit wrap
  with a hanging indent. The docstring is rendered as Markdown, and its code spans are highlighted
  as Lean. Code spans are elaborated in the chapter's own scope, not the declaration's, so a name
  written relative to a library namespace (`QuasilocalAlgebra`, `HaagKastlerNet.quasilocal`) is
  resolved and linked only if the chapter opens that namespace: a chapter therefore opens the
  namespaces of the declarations it shows, before `#doc` (`open Physicslib4.AQFT.HaagKastler`).
  Field names and file names in code spans stay unresolved and are shown as plain code. A
  highlighted structure name or field name links to the anchor of the structure's constructor
  (`…___mk`) in the docstring box, not to the structure or the field; the hover text names the
  right declaration. This is Verso's behaviour and affects every structure shown.
- Theorems: `#check` in a named `lean` block, with its output in a `leanOutput` block and the
  manual's own prose around it. Verso prints messages 120 columns wide; longer lines wrap at the
  width of the text column. Opening the namespace shortens the names:

  ````
  ```lean (name := checkEinstein)
  open Physicslib4 AQFT HaagKastler in
  #check HaagKastlerNet.einstein_causality
  ```

  ```leanOutput checkEinstein
  ...
  ```
  ````

- Links to the API docs: `{apiDocs Physicslib4.AQFT.HaagKastler.LocalNet}[]` shows the name in code
  type, `{apiDocs Physicslib4.AQFT.HaagKastler.LocalNet}[the local net]` the given text. The link is
  `Site.apiDocsUrl`: doc-gen4's page of the declaring module, anchored by the full name, for example
  `https://physicslib.github.io/physicslib4/docs/Physicslib4/AQFT/HaagKastler/LocalAlgebras.html#Physicslib4.AQFT.HaagKastler.LocalNet`.
  It works for Mathlib declarations too.

A chapter that uses library declarations imports the library modules it needs and opens
`Verso.Genre.Manual.InlineLean` and `Book`.

## Build and view locally

From the repository root:

```sh
cd web
lake exe cache get        # Mathlib build cache, first time only
lake build                # the three executables
lake exe generate-site --output _out/site
lake exe generate-tutorial --output _out/tutorial            # writes _out/tutorial/html-multi/
lake exe generate-tutorial --draft --output _out/tutorial-draft   # with the draft-only chapters
lake exe generate-manual --output _out/manual                # writes _out/manual/html-multi/
lake exe generate-manual --draft --output _out/manual-draft       # with the draft-only chapters
cd ..
```

The first `lake build` also builds physicslib4 if `../.lake` has no up-to-date build. A book's
generator adds to its output directory without clearing it, so delete the directory first after
renaming a chapter. The website links to the books through `tutorial/` and `manual/`, and the books
link back through `../`, so view them in the published layout, the website at the root:

```sh
rm -rf /tmp/srv && mkdir -p /tmp/srv/physicslib4
cp -R web/_out/site/. /tmp/srv/physicslib4/
cp -R web/_out/tutorial/html-multi /tmp/srv/physicslib4/tutorial
cp -R web/_out/manual/html-multi /tmp/srv/physicslib4/manual
cp -R blueprint/web /tmp/srv/physicslib4/blueprint   # optional, after `leanblueprint web`
cp blueprint/print/print.pdf /tmp/srv/physicslib4/blueprint.pdf   # optional, after `leanblueprint pdf`
cp -R web/redirects/. /tmp/srv/physicslib4/
python3 -m http.server -d /tmp/srv
```

and open <http://localhost:8000/physicslib4/>, <http://localhost:8000/physicslib4/tutorial/> and
<http://localhost:8000/physicslib4/manual/>. (`cp -R dir/. target/` copies the contents of `dir`;
the tutorial and manual targets are new directories, so `cp -R` creates them.) `http.server` answers
a missing page with its own error page, not `404.html`; open
<http://localhost:8000/physicslib4/404.html> to see the latter.

`.lake/` and `_out/` are ignored by git.

## Served from a sub-path

The website is published at the root of the project site, <https://physicslib.github.io/physicslib4/>,
the tutorial at <https://physicslib.github.io/physicslib4/tutorial/> and the reference manual at
<https://physicslib.github.io/physicslib4/manual/>, beside the blueprint (`/physicslib4/blueprint/`,
with `/physicslib4/blueprint.pdf`) and the API docs (`/physicslib4/docs/`). The pages of
`redirects/` are copied over the root. The generated pages
contain no root-relative URLs: each page carries a relative `<base href>` pointing at the root of its
document (`./` on the website's landing page; in a book `./` on the title page and `./../` on a
chapter), and every local link and asset is relative to it. The website's Tutorial and Reference
manual links go to `tutorial/` and `manual/` (`Site.tutorialPath`, `Site.manualPath`); in each book
the wordmark goes to `../` (`Site.siteFromBook`) and the link to the other book to `../tutorial/` or
`../manual/` (`Site.tutorialFromBook`, `Site.manualFromBook`). They therefore work under any prefix,
provided the URL ends in `/` (GitHub Pages redirects `/physicslib4` to `/physicslib4/`). The feature
cards link to the top of reference-manual chapters through `Site.manualChapterUrl`
(`manual/<chapter>/`); the caption links of the code gallery, plain text in `Site/FrontPage.lean`,
write the same paths directly. Links to the
blueprint and the API docs are absolute (`Site/Links.lean`).

The books use the manual genre's own page layout (title in the table of contents, search box,
previous and next links). `Book.replaceHeader`, a build step run after the HTML is written, swaps
the manual genre's header for the website header, with the book's own entry active. The books have
no footer.

## The web blueprint

The web blueprint (`leanblueprint web`, published at
<https://physicslib.github.io/physicslib4/blueprint/>) carries the same header, fonts, colours and
light and dark theme. It is built by plasTeX, not Verso, so the header is kept in a second copy:

- `blueprint/src/webtheme/site-header.html`: the header, with Blueprint as the active entry. Its
  links are absolute URLs under `https://physicslib.github.io/physicslib4/`, so they also work in
  `leanblueprint serve` and in a blueprint opened from disk; the Blueprint entry is `index.html`.
- `blueprint/src/webtheme/physicslib4web.py`: a plasTeX package, loaded by `web.tex` and found
  through `packages-dirs` in `plastex.cfg`, which puts the header on the chapter pages, the title
  page (the layouts in `webtheme/templates/`) and the dependency graph page (`webtheme/dep_graph.html`,
  selected by the `tpl=` option of the `blueprint` package). `blueprint/src/physicslib4web.sty` is
  its empty LaTeX counterpart, needed because plasTeX draws the pictures of the web version with
  LaTeX and the preamble of `web.tex`.
- `blueprint/src/webtheme/physicslib4-theme.js`: the theme switch, with the website's
  `localStorage` keys, so the three documents and the blueprint show the same theme.
- `blueprint/src/extra_styles.css`: the design tokens and the header rules of `Site.headerCss`,
  then the blueprint's own pages, theorem boxes, table of contents and dependency graph.

A change to the header in `Site/Theme.lean` (`headerWith`, `headerCss`) or to the design tokens is
copied to these files. The PDF (`print.tex`) loads none of them.

The layouts in `webtheme/` are copies of plasTeX's own, so CI builds the blueprint with the versions
pinned in `blueprint/requirements.txt` (step "Build the blueprint" in
`.github/workflows/blueprint.yml`). Raising a pin needs a local `leanblueprint web` check first.

## The API docs

The API docs (doc-gen4, published at <https://physicslib.github.io/physicslib4/docs/>) carry the
same header, fonts, colours and light and dark theme. doc-gen4 has no theme mechanism, so
`scripts/restyle_api_docs.py DOCS_DIR` (Python 3, standard library only) rewrites its HTML after the
build. On every page it puts the header in place of doc-gen4's top bar, moves doc-gen4's search form
(with its autocomplete and its results page) into the header between the wordmark and the links,
and moves the module name to the top of a module page's text. Every page and the module list
(`navbar.html`, a frame) load the site's fonts and three files the script copies into `DOCS_DIR`.
The header is kept in a third copy:

- `docs-theme/site-header.html`: the header, with API docs as the active entry and links absolute
  under `/physicslib4/`, so that they work at any depth under `docs/`. In place of the blueprint's
  table-of-contents button it has the button for doc-gen4's module list on narrow screens (a label
  for doc-gen4's checkbox `nav_toggle`); the line `SEARCH_FORM` marks where the search form goes.
- `docs-theme/physicslib4-docs.css`: the design tokens and header rules, copied from
  `blueprint/src/extra_styles.css`, then doc-gen4's own CSS variables, fonts and colours mapped to
  the site's, and doc-gen4's rules for bare `header` and `nav` elements undone on the header.
- `docs-theme/physicslib4-docs.js`: keeps doc-gen4's colour scheme (the attribute `data-theme` and
  the key `theme`, read by doc-gen4's `color-scheme.js`) and the module-list frame in step with the
  site's theme, which `blueprint/src/webtheme/physicslib4-theme.js` (also copied) sets. doc-gen4's
  own colour-scheme picker at the foot of the module list is hidden: the header's switch takes its
  place.

A change to the header or the design tokens is copied to these files as well. The script marks the
pages it rewrites and leaves marked pages alone, so a second run changes nothing; it takes about a
second on the 5,904 pages of the API docs. To check it locally, run it on a copy of the API docs
placed at `/tmp/srv/physicslib4/docs` in the layout of "Build and view locally".

## Continuous integration

- `.github/workflows/blueprint.yml` (pushes to `main`, and manual runs) builds and publishes the
  whole site. Its `build` job:
  1. builds and lints physicslib4 with `lean-action`;
  2. step "Build the Verso site, tutorial and manual": runs `lake exe cache get`, `lake build`,
     `lake exe generate-site --output _out/site`, `lake exe generate-tutorial --output _out/tutorial`
     and `lake exe generate-manual --output _out/manual` in `web/`, then removes `web/.lake` to free
     disk space;
  3. builds the blueprint PDF and web version (`leanblueprint pdf`, `leanblueprint web`) in a
     TeX Live container, with the versions pinned in `blueprint/requirements.txt`;
  4. builds the API docs with doc-gen4 the way `leanprover-community/docgen-action` does: a
     `docbuild/` Lake package requiring physicslib4 from `../` and doc-gen4 at the tag matching
     `lean-toolchain`, sharing `../.lake/packages`, built with `lake build Physicslib4:docs` into
     `docbuild/.lake/build/doc`; the API docs of the dependencies are cached, keyed by
     `lake-manifest.json`. Swap and memory overcommit are switched on first, for doc-gen4's many
     `git` processes;
  5. step "Assemble the site": copies `web/_out/site/.` to `_site/`, `web/_out/tutorial/html-multi`
     to `_site/tutorial`, `web/_out/manual/html-multi` to `_site/manual`, `blueprint/web` to
     `_site/blueprint`, `blueprint/print/print.pdf` to `_site/blueprint.pdf` and the API docs to
     `_site/docs`, then `web/redirects/.` over `_site/`;
  6. step "Restyle the API docs": runs `python3 scripts/restyle_api_docs.py _site/docs` (see "The
     API docs"); it rewrites the copy in `_site/`, so the cached doc-gen4 output is not changed;
  7. uploads `_site/` with `actions/upload-pages-artifact`, which leaves out names starting with `.`.

  The `deploy` job publishes the artifact with `actions/deploy-pages`, on
  `main` only; a manual run on another branch builds and uploads the artifact without deploying
  it. The local check in "Build and view locally" uses the same copy commands.
- `.github/workflows/lean_action_ci.yml` (every push and pull request, when `web/`, the library or the
  toolchain changes), step "Build the Verso site, tutorial and manual": the same builds into
  `web/_out/`, with no deployment, followed by a check that no page of the three uses a
  root-relative `href` or `src`.

In both, `lake exe cache get` only unpacks Mathlib from the cache that `lean-action` has already
downloaded, and the physicslib4 build in `../.lake/build` is reused through the `path = ".."`
dependency, so neither Mathlib nor physicslib4 is rebuilt. `lake build` compiles Verso and
verso-web-components, and the native code of the modules that the three executables link (including
Mathlib's), which accounts for most of its time.
