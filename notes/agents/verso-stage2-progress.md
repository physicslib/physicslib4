# Verso site, stage 2: progress log

Sub-path deployment and CI. Appended after each step.

## Step 0: centre "What is formalised" (2026-10-15)

- `web/Site/FrontPage.lean`: the "contents" section uses `centeredSection` instead of `landingSection`, so its
  heading is centred like "Checked by Lean" and "About" (the feature grid is unaffected; only the title and
  direct `<p>` children are centred). Rebuilt (`lake build`, 6728 jobs, about 20 s) and regenerated.

## Step 1: sub-path audit (2026-10-15)

- Generated HTML uses no root-relative URLs. Every page carries a relative `<base href>` (`./` on the landing
  page, `.././` on `tutorial/` and `manual/`), and every local `href`/`src` is relative to it: `-verso-data/*.css`,
  `-verso-data/*.js`, `favicon.png`, `apple-touch-icon.png`, `tutorial/`, `manual/`, the wordmark `./`. The hover
  data is loaded by `fetch("-verso-docs.json")`, which also resolves against the base. CSS `url()`s are Google
  Fonts only; the two sourcemaps are siblings of their scripts. The only root-relative strings are vwc `dark.js`'s
  `/static/favicon-*.ico`, which the site's inline script already disables. So no Verso base-URL option is needed
  and no source change was made; nav links to Tutorial and Reference manual already go to the in-site stubs.
- Test: copied `_out/site` to `/tmp/srv/physicslib4/site/`, served `/tmp/srv` with `python3 -m http.server 8765`.
  A crawler (`/tmp/check_site_urls.py`, not kept in the repo) follows every `href`/`src`/`url()`/`fetch`/
  sourcemap from the three pages, resolving HTML references against `<base>`: 24 local URLs, all 200, all under
  `/physicslib4/site/`. Headless Chrome loads of the three pages: every request 200 (server log), including
  `-verso-docs.json`. Blueprint, API-docs and `sec10-*.html` links are absolute `https://physicslib.github.io/physicslib4/...`.
- Caveat: `<base href="./">` needs the trailing slash; `/physicslib4/site` (no slash) is redirected by GitHub Pages
  (and by `http.server`, 301) to `/physicslib4/site/`.

## Step 2a: Jekyll pass-through test (2026-10-15)

- `docgen-action` at the pinned commit `7b5b9a1`: if `home_page/` exists it copies the blueprint into
  `home_page/blueprint/`, doc-gen4 output into `home_page/docs/`, then runs `JEKYLL_ENV=production bundle exec
  jekyll build` in `home_page/` (Ruby 3.1, bundler cache) and uploads `home_page/_site`. Nothing in it touches
  other subdirectories of `home_page/`, so a `home_page/site/` written beforehand is picked up by Jekyll.
- Local run, in a copy (`/tmp/jk/home_page`, so the tracked `Gemfile.lock` is untouched): the committed lockfile
  (github-pages 226, Jekyll 3.9.2, nokogiri 1.13.6 for x86_64-linux) does not install on this Mac (Ruby 3.4.1,
  arm64: nokogiri 1.13.6 native build fails; Docker daemon not running). Resolved afresh in the copy instead:
  github-pages 232, Jekyll 3.10.0. Static-file handling is the same in both Jekyll 3.x versions.
- With `web/_out/site` copied to `home_page/site/`, `JEKYLL_ENV=production bundle exec jekyll build`: `diff -r site
  _site/site` reports no difference; SHA-256 of all 24 files identical. None of the Verso files has front matter;
  the `-verso-data/` and `-verso-docs.json` names start with `-`, which Jekyll does not exclude (it excludes
  `_`, `.`, `#`, `~` prefixes). Serving `_site` as `/physicslib4/`, the crawler finds 24 local URLs under
  `/physicslib4/site/`, all 200.

## Step 2b: fresh `web/` build, as in CI (2026-10-15)

- Moved `web/.lake` aside and ran the CI commands from scratch in `web/`. `lake exe cache get`: clones the
  dependencies, then "Decompressing 9030 already-cached file(s)", "No files to download" (it reuses
  `~/.cache/mathlib`, which in CI is filled by `lean-action`'s cache step), 1 min 38 s in all. `lake build`:
  6728 jobs, 2 min 46 s; no `.olean` rebuilt for Mathlib or Physicslib4 (0 `Built Physicslib4.*` lines; the
  2884 `Built Mathlib.*` lines are all `:c.o`, native objects that the `generate-site` executable links, about
  0.13 s each). `generate-site`: 4 s; output identical to the earlier build. The old `web/.lake` was then deleted.
- Disk: `web/.lake/packages/mathlib` is a second Mathlib copy (about 7 GB with build), separate from the root's.

## Step 2c: CI edits (2026-10-15)

- `.github/workflows/blueprint.yml`: new step "Build the Verso site into home_page/site" between "Build and lint
  project" (`lean-action`) and "Compile blueprint and documentation" (`docgen-action`). Runs in `web/`:
  `lake exe cache get`, `lake build`, `lake exe generate-site --output ../home_page/site`, then `rm -rf .lake` to
  free the second Mathlib copy before doc-gen4 runs. Tested locally that `--output ../home_page/site` produces
  output identical to `_out/site`.
- `.github/workflows/lean_action_ci.yml`: new last step "Build the Verso site": same build into `web/_out/site`, no
  deploy, then fails if any HTML has a root-relative `href`/`src` (`grep -E '(href|src)="/[^/]'`; none today).
  `permissions: contents: read` unchanged.
- No new actions (only `run` steps), so nothing new to pin. Both files parse as YAML (Ruby `YAML.load_file`).
- `.gitignore`: `home_page/site/` (checked with `git check-ignore`).

## Step 3: README (2026-10-15)

- `web/README.md`: sections "Served from a sub-path" and "Continuous integration". Temporal-wording check passes.
- Expected extra CI time per workflow: about 6 to 12 min (clone of the `web/` dependencies including a Mathlib
  checkout, cache unpack, Verso compile and Mathlib native objects on a 4-core runner; local Apple-silicon
  figure is 4.5 min). To be confirmed by the first runs; disk headroom in `blueprint.yml` (docgen's Mathlib API
  docs after the Verso step) likewise.
