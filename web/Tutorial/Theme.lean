import VersoManual
import VersoWeb.Theme.Static
import Site.Theme

/-!
# Tutorial theme

The tutorial is a manual-genre book, whose page template is fixed by Verso: a header with the book
title, a table of contents on the left, and the text. It takes the website's look from the website's
own theme code (`Site.Theme`):

* the design tokens `Site.colorTheme` (teal accent, light and dark values) and the stylesheet
  `Site.siteCss`;
* the `verso-web-components` header styles (`navbar.css`), its
  hover highlight for the navigation (`navbar.js`) and its theme switch script (`dark.js`), which stores the choice of light or dark mode in the browser,
  so the website and the tutorial share it;
* the header `Site.headerWith`, with the plain "physicslib4" wordmark and the same navigation as the
  website. `replaceHeader` puts it in place of the manual genre's header once the HTML is written.
  The book has no footer: the manual genre's previous and next links close each page.

`tutorialCss` maps the manual genre's own style variables to the design tokens, so that the table of
contents, the text and the code follow the accent colour and dark mode, and styles the tutorial's
directives (`Tutorial.Meta`).
-/

open Verso.Genre.Manual
open Verso.Output Html
open Verso.Web.Theme

namespace Tutorial

/-- Styles specific to the tutorial: the manual genre restyled with the website's design tokens. -/
def tutorialCss : String := "
:root {
  --verso-header-height: 4.5rem;
  --verso-structure-font-family: var(--font-primary);
  --verso-text-font-family: var(--font-primary);
  --verso-code-font-family: 'Fira Code', monospace;
  --verso-text-color: var(--color-text);
  --verso-structure-color: var(--color-text);
  --verso-selected-color: var(--color-hover);
  --verso-toc-background-color: var(--color-bg);
  --verso-toc-text-color: var(--color-text);
  --verso-toc-border-color: var(--color-border);
  --verso-burger-toc-hidden-color: var(--color-text);
  --verso-burger-toc-hidden-shadow-color: transparent;
  --verso-burger-toc-visible-shadow-color: transparent;
}
.dark-theme {
  --verso-tooltip-color: var(--color-text);
  --verso-tooltip-bg-color: #262626;
  --verso-tooltip-border-color: #555;
  --verso-tooltip-separator-color: #444;
  --verso-tactic-state-color: var(--color-text);
  --verso-tactic-state-bg-color: var(--card-bg);
  --verso-tactic-state-border-color: var(--color-border-light);
}
html { color-scheme: light; }
html.dark-theme { color-scheme: dark; }
body { background-color: var(--color-surface); color: var(--color-text); font-family: var(--font-primary); }

/* The website header in place of the manual header */
header.site-header { position: fixed; top: 0; left: 0; right: 0; z-index: 99; display: flex; align-items: center;
  height: var(--verso-header-height); box-shadow: none; background-color: var(--color-bg-translucent);
  border-bottom: 1px solid var(--color-border-nav); }
header.site-header .navbar { flex: 1; min-width: 0; height: 100%; padding-top: 0; padding-bottom: 0; border-bottom: 0; }
/* The manual genre's search box, which its script appends to the header */
:root { --search-bar-width: 14rem; --verso-background-color: var(--color-surface); }
header.site-header #search-wrapper { position: static; padding: 0 var(--space-8) 0 0; background: transparent; }
header.site-header #search-wrapper .combobox .cb_edit { border: 1px solid var(--color-border-light); border-radius: var(--radius-md);
  font-family: var(--font-primary); padding: 0.4rem 0.75rem; }
header.site-header #search-wrapper .combobox .group.focus .cb_edit,
header.site-header #search-wrapper .combobox .group .cb_edit:hover { outline: none; border-color: var(--color-primary); background-color: var(--color-surface); }
@media (max-width: 1024px) { header.site-header #search-wrapper { display: none; } }
.site-header .container { max-width: none; padding: 0 var(--space-4); margin: 0 auto; width: 100%; box-sizing: border-box; }
.site-header ul, .site-header menu, .site-header li { margin: 0; padding: 0; list-style: none; }
.site-header button { background: none; border: 0; font: inherit; color: inherit; cursor: pointer; }
.site-header a { text-decoration: none; }
.site-header .nav-link { font-family: var(--font-primary); font-size: var(--fs-base); }
@media screen and (max-width: 700px) {
  .site-header .nav-logo { margin-left: calc(var(--verso-burger-width) + 1.5rem); }
}

/* Table of contents */
#toc { border-right: 1px solid var(--color-border); }
#toc a { color: var(--color-text); }
#toc a:hover { color: var(--color-primary); }
#toc .split-toc label.toggle-split-toc::before { background-color: currentColor; }
#toc .toc-title { display: block; color: var(--color-text); text-decoration: none; padding: 0 0.5rem; }
#toc .toc-title h1 { font-size: var(--fs-lg); font-weight: 600; margin: var(--space-6) 0 var(--space-2); }

/* Text */
main { color: var(--color-text); }
main h1, main h2, main h3, main h4 { color: var(--color-text); font-weight: 600; }
main a { color: var(--color-primary); }
main a:hover { color: var(--color-link-hover); }
.dark-theme main a { color: #5eead4; }
.katex { font-size: 1.1em; }
.prev-next-buttons a { color: var(--color-text); }
.prev-next-buttons a:hover { color: var(--color-primary); }

/* Exercises and solutions */
.exercise { margin: var(--space-6) 0; padding: var(--space-4) var(--space-6); border-left: 4px solid var(--color-primary);
  background: var(--color-hover); border-radius: 0 var(--radius-md) var(--radius-md) 0; }
.exercise > :last-child { margin-bottom: 0; }
.exercise-label { margin: 0 0 var(--space-2); font-weight: 700; color: var(--color-primary); letter-spacing: 0.02em; }
.dark-theme .exercise-label { color: #5eead4; }
details.solution { margin-top: var(--space-3); }
details.solution > summary { cursor: pointer; font-weight: 600; color: var(--color-primary); }
.dark-theme details.solution > summary { color: #5eead4; }
.solution-body { padding-top: var(--space-2); }

/* Figures */
figure.tutorial-figure { margin: var(--space-8) auto; max-width: 420px; }
figure.tutorial-figure figcaption { font-size: var(--fs-sm); color: var(--color-text-light); text-align: center; margin-top: var(--space-2); }
figure.tutorial-figure figcaption p { margin: 0; }
"

/-- The header of every tutorial page: the website header, with "Tutorial" active. -/
def tutorialHeader : Html :=
  Site.headerWith Site.siteFromTutorial Site.tutorialNavLinks (· == "Tutorial")

/--
The tutorial's stylesheet, written to `-verso-data/physicslib4.css`: the website's design tokens,
the `verso-web-components` header styles, the website's stylesheet and `tutorialCss`, in
that order (later rules override earlier ones of equal specificity).
-/
def themeCss : CssFile where
  filename := "physicslib4.css"
  contents := "\n".intercalate [
    Site.colorTheme.toCSS, Static.navbar.css, Site.siteCss, tutorialCss]

/--
The HTML configuration of the tutorial: one HTML page per chapter (`htmlDepth := 1`), and the
shared stylesheets, scripts and icons.
-/
def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1
  logoLink := some "./"
  sourceLink := some Site.githubUrl
  extraCssFiles := ({} : Std.HashSet CssFile).insert themeCss
  extraJsFiles := ({} : Std.HashSet JsFile)
    |>.insert { filename := "dark.js", contents := Static.dark.js, sourceMap? := none }
    |>.insert { filename := "navbar.js", contents := Static.navbar.js, defer := true, sourceMap? := none }
  extraJs := ({} : Std.HashSet JS)
    |>.insert "// dark.js points the favicon at /static/favicon-*.ico, which the tutorial does not have; keep favicon.png.
function updateFaviconForSystemTheme(theme) {}"
  extraHead := #[
    {{ <link rel="preconnect" href="https://fonts.googleapis.com" /> }},
    {{ <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin="anonymous" /> }},
    {{ <link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Fira+Code:wght@300..700&family=Open+Sans:ital,wght@0,300..800;1,300..800&display=swap" /> }},
    {{ <link rel="icon" href="favicon.png" /> }},
    {{ <link rel="apple-touch-icon" href="apple-touch-icon.png" /> }},
    {{ <meta name="theme-color" content={{ Site.accent }} /> }},
    {{ <meta name="description" content="A tutorial on algebraic quantum field theory and its formalisation in Lean 4 in physicslib4." /> }}
  ]
  extraFilesHtml := [
    ("static_files/favicon.png", "favicon.png"),
    ("static_files/apple-touch-icon.png", "apple-touch-icon.png")
  ]

/--
Replaces the first `<header>…</header>` of `page` (the manual genre's header, which holds only the
book title) with `header`.
-/
def replaceHeaderIn (header page : String) : Option String :=
  match page.splitOn "<header>" with
  | before :: rest@(_ :: _) =>
    match ("<header>".intercalate rest).splitOn "</header>" with
    | _ :: after@(_ :: _) => some (before ++ header ++ "</header>".intercalate after)
    | _ => none
  | _ => none

/-- An extra build step: puts `tutorialHeader` in place of the manual header on every HTML page. -/
def replaceHeader : ExtraStep := fun mode cfg _ _ => do
  let dir := cfg.destination / (match mode with | .single => "html-single" | .multi => "html-multi")
  let header := tutorialHeader.asString
  for file in ← (dir.walkDir : IO _) do
    if file.extension == some "html" then
      let page ← (IO.FS.readFile file : IO _)
      match replaceHeaderIn header page with
      | some page' => (IO.FS.writeFile file page' : IO _)
      | none => throw <| IO.userError s!"No <header> element in {file}"

end Tutorial
