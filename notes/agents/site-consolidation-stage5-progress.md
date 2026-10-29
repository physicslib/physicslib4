# Site consolidation, stage 5: the workflow assembles and deploys the Pages artifact

Plan: `plan-site-consolidation-2026-10-29.md`, stage 5 (deployment option (b)). Inputs: the "For
stage 5" notes of `site-consolidation-stage4-progress.md`.

## Step 1: survey (2026-10-29)

- `docgen-action` at `7b5b9a1822650bd45aaeb4182d94bceba2030f89` read (`action.yml`,
  `scripts/build_docs.sh`, `src/index.js`, `src/deprecation.js`). Its API-docs build:
  1. `index.js` reads `lakefile.toml` and `lake-manifest.json`: outputs `name` (`physicslib4`),
     `docs_facets` (each default target + `:docs`: `Physicslib4:docs`) and the cache path list
     (`docbuild/.lake/build/doc/<Module>` for each manifest package mapped to its module names, a
     known table plus an UpperCamelCase fallback, then `Init Lake Lean Std`, then `doc-data`, the
     `declarations/declaration-data.bmp`, `api-docs.db`, `doc-manifest.json` and doc-gen4's static
     files).
  2. `actions/cache@5a3ec84e…` (v4.2.3), only on `push`, key
     `Docs-${{ hashFiles('lake-manifest.json', 'references.bib') }}`.
  3. `build_docs.sh`: `docbuild/lakefile.toml` (name `docbuild`, `packagesDir = "../.lake/packages"`,
     requires the project from `../` and `leanprover/doc-gen4` at the revision derived from
     `lean-toolchain`: `v4.X.Y[-rcZ]` tag, else `nightly-testing`/`main`); copies `references.bib`
     to `docbuild/docs/` if present; `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update physicslib4`;
     `lake build Physicslib4:docs`; copies `docbuild/.lake/build/doc` to `<homepage>/docs`.
  4. Upload/deploy: `upload-pages-artifact@56afc609…` (v3.0.1), `deploy-pages@d6db9016…` (v4.0.5).
  - The API docs build and deployment run only on `push`, so a `workflow_dispatch` run of the
    current workflow deploys nothing.
- Last successful run (40730350694): docs cache missed, then saved under
  `Docs-19034e0a…` with the path list above (`«docGen4»`, `Checkdecls`, `Leansqlite` predicted by
  the fallback). Reproducing the list in the same order keeps that cache usable.
- Pages is configured with `build_type: workflow`.
- `web/redirects/` has no `docs/` entry, so copying it over the root never touches the API docs.
- Locally `blueprint/web/.cache/` exists (plasTeX image cache); Jekyll dropped dotfiles, and
  `upload-pages-artifact` v4 excludes them too (`--exclude=".[^/]*"`).

## Step 2: the workflow (2026-10-29)

`.github/workflows/blueprint.yml` rewritten. Two jobs.
- `build` (`ubuntu-latest`; the `ubuntu-24.04` pin was for docgen-action's Ruby/Jekyll setup and
  nothing else needs it): free disk space; checkout (pinned to the `v6.1.0` SHA); `lean-action`
  build/lint; the Verso site, tutorial and manual into `web/_out/` (then `rm -rf web/.lake`); the
  pinned blueprint build (texlive container, output left in `blueprint/print/` and
  `blueprint/web/`); swap/overcommit; the API docs in three steps (metadata, cache, build) that
  reproduce docgen-action; "Assemble the site" into `_site/`; a commented-out stage-6 hook
  (`python3 scripts/postprocess_api_docs.py _site/docs`); `upload-pages-artifact` v4.0.0
  (`7b1f4a76…`, excludes dotfiles).
- `deploy` (`needs: build`, `if: github.ref == 'refs/heads/main'`, `environment: github-pages`,
  `pages: write`, `id-token: write`): `deploy-pages` v4.0.5 (`d6db9016…`, the SHA docgen-action
  uses). A manual run on another branch therefore builds and uploads without deploying, and the
  `github-pages` environment's branch rule is never hit from a branch.
- Deviations from docgen-action, stated in the workflow comment: the API docs (and their cache)
  also run on `workflow_dispatch`; the output stays in `docbuild/.lake/build/doc`.
- No Jekyll, Ruby or `home_page/` use left in the workflow.

## Step 3: validation of the workflow (2026-10-29)

- `ruby -ryaml` parses it; every `uses:` is pinned to a 40-hex SHA.
- The metadata step, run locally on `lakefile.toml`/`lake-manifest.json`: `name=physicslib4`,
  `docs_facets=Physicslib4:docs`, and a 47-line cache path list identical, line for line, to the
  one docgen-action logged in run 40730350694 (so the cache it saved under
  `Docs-19034e0a…` can be restored, as long as `lake-manifest.json` is unchanged).
- The docs build step, with the `lake` lines removed, run in `/tmp`: `docbuild/lakefile.toml`
  identical to docgen-action's template, `rev = "v4.35.0"`; a nightly toolchain gives
  `nightly-testing`.
- Assembly: the step's `run` extracted from the YAML and run unchanged in a staging directory
  (symlinks to `web/`, `blueprint/`; an empty `docbuild/.lake/build/doc`), moved to
  `/tmp/assemble/`. Dotfiles removed as upload-pages-artifact does (only `blueprint/.cache/`).
  Served under `/physicslib4/` with the stage-4 server (404.html on misses) and crawled with the
  stage-4 crawler: 407 pages, 27010 internal links, 0 broken (the stage-4 `blueprint.pdf` miss is
  gone), 99 `/docs/` links not checked (API docs not built locally); missing fragments only the
  known 3108 Verso TOC chapter tags and 1 JS-drawn dependency-graph node. All 11 redirects plus
  `site/` and `site` land on their targets; 404 served at three depths with working links.

## Step 4: leftovers and text (2026-10-29)

- `.gitignore`: the `home_page/site/`, `home_page/tutorial/`, `home_page/manual/` entries replaced by
  `/docbuild/` and `/_site/` (what the workflow writes at the repository root).
- `.github/workflows/lean_action_ci.yml`: the comment and the error message of the root-relative
  check say `/physicslib4/` instead of `/physicslib4/site/`; the check and its paths are unchanged.
- `web/README.md`: "Continuous integration" rewritten (the build job's six stages, the commented
  hook, the main-only deploy job); "The web blueprint" names the step "Build the blueprint"; the
  local recipe also copies `blueprint.pdf`.
- `home_page/` untouched (stage 8); `git grep` finds no use of `home_page/` in `.github/`.
- YAML of both workflows parses; all `uses:` in `blueprint.yml` are SHA-pinned (`lean_action_ci.yml`
  keeps `actions/checkout@v6`, outside this stage's scope). `actionlint` is not installed locally.
- `python3 scripts/check_temporal_wording.py`: OK.

## Risks for the first run on `main`

- The docs build itself is unchanged in substance, but runs outside docgen-action for the first
  time; a cache hit on `Docs-19034e0a…` depends on `lake-manifest.json` being unchanged since run
  40730350694.
- `ubuntu-latest` instead of `ubuntu-24.04`: `free-disk-space` v1.3.2 and the texlive container
  are untested on the newer image in this repository (`lean_action_ci.yml` already uses
  `ubuntu-latest` for the Lean and Verso steps).
- Disk: `_site/docs` is a second copy of the API docs, as Jekyll's `_site/` was.
- Not committed (per instructions).
