# physicslib4 website and tutorial

Two documents written with [Verso](https://github.com/leanprover/verso):

- the website: the physicslib4 landing page and a stub reference-manual page, in Verso's website
  (`VersoBlog`) genre, styled with
  [verso-web-components](https://github.com/leanprover/verso-web-components), the components behind
  lean-lang.org;
- the tutorial: a book in Verso's manual (`VersoManual`) genre, with one chapter per file.

Both share one look: the verso-web-components design tokens with a deep-teal accent, and the same
header with the "physicslib4" wordmark and the navigation Tutorial, Reference manual, Blueprint,
API docs.

This directory is a Lake package of its own. It requires physicslib4 from `..`, so the Lean
examples on the page are elaborated against the library itself.

## Layout

- `lakefile.toml`, `lean-toolchain`: the package and its pinned Verso and verso-web-components versions.
- `Main.lean`: the site structure and the `generate-site` executable.
- `Site/Links.lean`: the tagline, the navigation links of the website and the tutorial, and the URLs
  of the blueprint and API docs.
- `Site/Theme.lean`: the website theme (header, footer, design tokens, accent colour, code colours).
  The header, the design tokens and the stylesheet are also used by the tutorial.
- `Site/Components.lean`: the landing-page directives (hero, sections, code gallery, feature cards),
  built on verso-web-components.
- `Site/Diagram.lean`: the causal-diamond diagram, as inline SVG.
- `Site/FrontPage.lean`: the landing page. `Site/Manual.lean`: the reference-manual stub page.
- `TutorialMain.lean`: the `generate-tutorial` executable.
- `Tutorial.lean`: the tutorial's title page; it includes the chapters.
- `Tutorial/AQFTInBrief.lean`: chapter 1, "AQFT in brief" (in preparation).
- `Tutorial/LeanInBrief.lean`: chapter 2, "Lean in brief".
- `Tutorial/FeatureTests.lean`: a draft-only chapter showing the markup for maths, exercises,
  figures and citations; built only with `--draft`.
- `Tutorial/Meta.lean`: the directives `exercise`, `solution` (collapsible), `figure`, and `goals`,
  which shows the proof state after every tactic of the Lean block it wraps.
- `Tutorial/Papers.lean`: the works cited with the manual genre's `citet`, `citep` and `citehere`.
- `Tutorial/Theme.lean`: the tutorial's configuration and styles, built from `Site/Theme.lean`.
- `static_files/`: the "p4" wordmark icons (favicon and Apple touch icon), used by both.

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

## Build and view locally

From the repository root:

```sh
cd web
lake exe cache get        # Mathlib build cache, first time only
lake build                # both executables
lake exe generate-site --output _out/site
lake exe generate-tutorial --output _out/tutorial            # writes _out/tutorial/html-multi/
lake exe generate-tutorial --draft --output _out/tutorial-draft   # with the draft-only chapters
cd ..
```

The first `lake build` also builds physicslib4 if `../.lake` has no up-to-date build. The website
and the tutorial link to each other through `../tutorial/` and `../site/`, so view them side by side,
as they are published:

```sh
rm -rf /tmp/srv && mkdir -p /tmp/srv/physicslib4   # start clean: cp -R into an existing directory nests the copy
cp -R web/_out/site /tmp/srv/physicslib4/site
cp -R web/_out/tutorial/html-multi /tmp/srv/physicslib4/tutorial
python3 -m http.server -d /tmp/srv
```

and open <http://localhost:8000/physicslib4/site/> and <http://localhost:8000/physicslib4/tutorial/>.

`.lake/` and `_out/` are ignored by git.

## Served from a sub-path

The website is published at <https://physicslib.github.io/physicslib4/site/> and the tutorial at
<https://physicslib.github.io/physicslib4/tutorial/>, under the project site that also hosts the
blueprint (`/physicslib4/blueprint/`) and the API docs (`/physicslib4/docs/`). The generated pages
contain no root-relative URLs: each page carries a relative `<base href>` pointing at the root of its
document (on the website `./` on the landing page and `.././` on `manual/`; in the tutorial `./` on
the title page and `./../` on a chapter), and every local link and asset is relative to it. The
website's Tutorial link and "Read the tutorial" button go to `../tutorial/`; the tutorial's wordmark
and Reference manual link go to `../site/` and `../site/manual/`. Both therefore work under any
common prefix, provided the URL ends in `/` (GitHub Pages redirects `/physicslib4/site` to
`/physicslib4/site/`). Links to the blueprint, the API docs and the blueprint guide pages are absolute
(`Site/Links.lean`).

The tutorial uses the manual genre's own page layout (title in the table of contents, search box,
previous and next links). `Tutorial.replaceHeader`, a build step run after the HTML is written,
swaps the manual genre's header for the website header. The book has no footer.
## Continuous integration

- `.github/workflows/blueprint.yml` (pushes to `main`), step "Build the Verso site and tutorial into
  home_page": after `lean-action` has built physicslib4, it runs `lake exe cache get`, `lake build`,
  `lake exe generate-site --output ../home_page/site` and `lake exe generate-tutorial --output
  _out/tutorial` in `web/`, copies `_out/tutorial/html-multi` to `home_page/tutorial/`, then removes
  `web/.lake` and `web/_out`. The next step, `docgen-action`, builds the blueprint and the API docs
  into `home_page/` and runs Jekyll there. The Verso files have no front matter and no names starting
  with `_`, `.`, `#` or `~`, so Jekyll copies them unchanged to `_site/site/` and `_site/tutorial/`,
  which are deployed as `/physicslib4/site/` and `/physicslib4/tutorial/`. (Jekyll also renders the
  search component's `-verso-search/licenses.md` as an extra `licenses.html` beside it.)
  `home_page/site/` and `home_page/tutorial/` are ignored by git.
- `.github/workflows/lean_action_ci.yml` (every push and pull request, when `web/`, the library or the
  toolchain changes), step "Build the Verso site and tutorial": the same builds into `web/_out/`, with
  no deployment, followed by a check that no page of either uses a root-relative `href` or `src`.

In both, `lake exe cache get` only unpacks Mathlib from the cache that `lean-action` has already
downloaded, and the physicslib4 build in `../.lake/build` is reused through the `path = ".."`
dependency, so neither Mathlib nor physicslib4 is rebuilt. `lake build` compiles Verso and
verso-web-components, and the native code of the modules that the two executables link (including
Mathlib's), which accounts for most of its time.
