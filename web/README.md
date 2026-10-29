# physicslib4 website, tutorial and reference manual

Three documents written with [Verso](https://github.com/leanprover/verso):

- the website: the physicslib4 landing page, in Verso's website (`VersoBlog`) genre, styled with
  [verso-web-components](https://github.com/leanprover/verso-web-components), the components behind
  lean-lang.org;
- the tutorial: a book in Verso's manual (`VersoManual`) genre, with one chapter per file;
- the reference manual: a second manual-genre book, with one chapter per section of Chapter 10 of
  the blueprint.

All three share one look: the verso-web-components design tokens with a deep-teal accent, and the
same header with the "physicslib4" wordmark and the navigation Tutorial, Reference manual,
Blueprint, API docs.

This directory is a Lake package of its own. It requires physicslib4 from `..`, so the Lean
examples on the page are elaborated against the library itself.

## Layout

- `lakefile.toml`, `lean-toolchain`: the package and its pinned Verso and verso-web-components versions.
- `Main.lean`: the site structure and the `generate-site` executable.
- `Site/Links.lean`: the tagline, the navigation links of the website and the books, and the URLs
  of the blueprint and API docs (`apiDocsUrl` for one declaration).
- `Site/Theme.lean`: the website theme (header, footer, design tokens, accent colour, code colours).
  The header, the design tokens and the stylesheet are also used by the books.
- `Site/Components.lean`: the landing-page directives (hero, sections, code gallery, feature cards),
  built on verso-web-components.
- `Site/Diagram.lean`: the causal-diamond diagram, as inline SVG.
- `Site/FrontPage.lean`: the landing page.
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
- `static_files/`: the "p4" wordmark icons (favicon and Apple touch icon), used by all three.

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
renaming a chapter. The three documents link to each other through `../site/`, `../tutorial/` and
`../manual/`, so view them side by side, as they are published:

```sh
rm -rf /tmp/srv && mkdir -p /tmp/srv/physicslib4   # start clean: cp -R into an existing directory nests the copy
cp -R web/_out/site /tmp/srv/physicslib4/site
cp -R web/_out/tutorial/html-multi /tmp/srv/physicslib4/tutorial
cp -R web/_out/manual/html-multi /tmp/srv/physicslib4/manual
python3 -m http.server -d /tmp/srv
```

and open <http://localhost:8000/physicslib4/site/>, <http://localhost:8000/physicslib4/tutorial/> and
<http://localhost:8000/physicslib4/manual/>.

`.lake/` and `_out/` are ignored by git.

## Served from a sub-path

The website is published at <https://physicslib.github.io/physicslib4/site/>, the tutorial at
<https://physicslib.github.io/physicslib4/tutorial/> and the reference manual at
<https://physicslib.github.io/physicslib4/manual/>, under the project site that also hosts the
blueprint (`/physicslib4/blueprint/`) and the API docs (`/physicslib4/docs/`). The generated pages
contain no root-relative URLs: each page carries a relative `<base href>` pointing at the root of its
document (`./` on the website's landing page; in a book `./` on the title page and `./../` on a
chapter), and every local link and asset is relative to it. The website's Tutorial and Reference
manual links go to `../tutorial/` and `../manual/`; in each book the wordmark goes to `../site/` and
the link to the other book to `../tutorial/` or `../manual/`. They therefore work under any common
prefix, provided the URL ends in `/` (GitHub Pages redirects `/physicslib4/site` to
`/physicslib4/site/`). The feature cards link to the top of
reference-manual chapters through `Site.manualChapterUrl` (`../manual/<chapter>/`); the caption links
of the code gallery, plain text in `Site/FrontPage.lean`, write the same paths directly. Links to the
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
pinned in `blueprint/requirements.txt` (its own step in `.github/workflows/blueprint.yml`, not
docgen-action's unpinned install). Raising a pin needs a local `leanblueprint web` check first.

## Continuous integration

- `.github/workflows/blueprint.yml` (pushes to `main`), step "Build the Verso site, tutorial and
  manual into home_page": after `lean-action` has built physicslib4, it runs `lake exe cache get`,
  `lake build`, `lake exe generate-site --output ../home_page/site`, `lake exe generate-tutorial
  --output _out/tutorial` and `lake exe generate-manual --output _out/manual` in `web/`, copies
  `_out/tutorial/html-multi` and `_out/manual/html-multi` to `home_page/tutorial/` and
  `home_page/manual/`, then removes `web/.lake` and `web/_out`. The next step, `docgen-action`,
  builds the blueprint and the API docs into `home_page/` and runs Jekyll there. The Verso files have
  no front matter and no names starting with `_`, `.`, `#` or `~`, so Jekyll copies them unchanged to
  `_site/site/`, `_site/tutorial/` and `_site/manual/`, which are deployed as `/physicslib4/site/`,
  `/physicslib4/tutorial/` and `/physicslib4/manual/`. (Jekyll also renders each book's
  `-verso-search/licenses.md` as an extra `licenses.html` beside it.) `home_page/site/`,
  `home_page/tutorial/` and `home_page/manual/` are ignored by git.
- `.github/workflows/lean_action_ci.yml` (every push and pull request, when `web/`, the library or the
  toolchain changes), step "Build the Verso site, tutorial and manual": the same builds into
  `web/_out/`, with no deployment, followed by a check that no page of the three uses a
  root-relative `href` or `src`.

In both, `lake exe cache get` only unpacks Mathlib from the cache that `lean-action` has already
downloaded, and the physicslib4 build in `../.lake/build` is reused through the `path = ".."`
dependency, so neither Mathlib nor physicslib4 is rebuilt. `lake build` compiles Verso and
verso-web-components, and the native code of the modules that the three executables link (including
Mathlib's), which accounts for most of its time.
