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
