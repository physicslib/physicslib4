# physicslib4 website

The physicslib4 landing page, written with [Verso](https://github.com/leanprover/verso)'s website
(`VersoBlog`) genre and styled with
[verso-web-components](https://github.com/leanprover/verso-web-components), the components behind
lean-lang.org. The accent colour is deep teal.

This directory is a Lake package of its own. It requires physicslib4 from `..`, so the Lean
examples on the page are elaborated against the library itself.

## Layout

- `lakefile.toml`, `lean-toolchain`: the package and its pinned Verso and verso-web-components versions.
- `Main.lean`: the site structure and the `generate-site` executable.
- `Site/Links.lean`: the tagline, the navigation links and the URLs of the blueprint and API docs.
- `Site/Theme.lean`: the theme (header, footer, design tokens, accent colour, code colours).
- `Site/Components.lean`: the landing-page directives (hero, sections, code gallery, feature cards),
  built on verso-web-components.
- `Site/Diagram.lean`: the causal-diamond diagram, as inline SVG.
- `Site/FrontPage.lean`: the landing page. `Site/Tutorial.lean`, `Site/Manual.lean`: stub pages.
- `static_files/`: the "p4" wordmark icons (favicon and Apple touch icon).

## Build and view locally

From the repository root:

```sh
cd web
lake exe cache get        # Mathlib build cache, first time only
lake build
lake exe generate-site --output _out/site
cd ..
python3 -m http.server -d web/_out/site
```

Then open <http://localhost:8000/>. The first `lake build` also builds physicslib4 if `../.lake`
has no up-to-date build.

`.lake/` and `_out/` are ignored by git.

## Served from a sub-path

The site is published at <https://physicslib.github.io/physicslib4/site/>, under the project site that
also hosts the blueprint (`/physicslib4/blueprint/`) and the API docs (`/physicslib4/docs/`). The
generated pages contain no root-relative URLs: each page carries a relative `<base href>` (`./` on the
landing page, `.././` on `tutorial/` and `manual/`), and every in-site link and asset (`-verso-data/`,
`-verso-docs.json`, the icons, `tutorial/`, `manual/`) is relative to it. The site therefore works under
any prefix, provided the URL ends in `/` (GitHub Pages redirects `/physicslib4/site` to
`/physicslib4/site/`). Links to the blueprint, the API docs and the blueprint guide pages are absolute
(`Site/Links.lean`).

To check the sub-path locally:

```sh
mkdir -p /tmp/srv/physicslib4
cp -R web/_out/site /tmp/srv/physicslib4/site
python3 -m http.server -d /tmp/srv
```

and open <http://localhost:8000/physicslib4/site/>.

## Continuous integration

- `.github/workflows/blueprint.yml` (pushes to `main`), step "Build the Verso site into
  home_page/site": after `lean-action` has built physicslib4, it runs `lake exe cache get`, `lake build`
  and `lake exe generate-site --output ../home_page/site` in `web/`, then removes `web/.lake`. The next
  step, `docgen-action`, builds the blueprint and the API docs into `home_page/` and runs Jekyll there.
  The Verso files have no front matter and no names starting with `_`, `.`, `#` or `~`, so Jekyll copies
  them unchanged to `_site/site/`, which is deployed as `/physicslib4/site/`. `home_page/site/` is
  ignored by git.
- `.github/workflows/lean_action_ci.yml` (every push and pull request), step "Build the Verso site":
  the same build into `web/_out/site`, with no deployment, followed by a check that no page uses a
  root-relative `href` or `src`.

In both, `lake exe cache get` only unpacks Mathlib from the cache that `lean-action` has already
downloaded, and the physicslib4 build in `../.lake/build` is reused through the `path = ".."`
dependency, so neither Mathlib nor physicslib4 is rebuilt. `lake build` compiles Verso and
verso-web-components, and the native code of the modules that `generate-site` links (including
Mathlib's), which accounts for most of its time.
