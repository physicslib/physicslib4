import VersoManual
import VersoWeb.Theme.Static
import Site.Theme

/-!
# The theme of the books

The tutorial and the reference manual are manual-genre books, whose page template is fixed by
Verso: a header with the book title, a table of contents on the left, and the text. Both take the
website's look from the website's own theme code (`Site.Theme`), through this module:

* the design tokens `Site.colorTheme` (teal accent, light and dark values) and the stylesheet
  `Site.siteCss`;
* the `verso-web-components` header styles (`navbar.css`), its hover highlight for the navigation
  (`navbar.js`) and its theme switch script (`dark.js`), which stores the choice of light or dark
  mode in the browser, so the website and the books share it;
* the header `Site.headerWith`, with the plain "physicslib4" wordmark and the same navigation as the
  website, laid out by the website's `Site.headerCss`, so that it has the same size and position on
  every page. `replaceHeader` puts it in place of the manual genre's header once the HTML is
  written. The manual genre's search box sits at the top of the table of contents (`searchToToc`),
  and on a phone the table-of-contents button sits in the header, left of the navigation button.
  The books have no footer: the manual genre's previous and next links close each page.

`bookCss` maps the manual genre's own style variables to the design tokens, so that the table of
contents, the text and the code follow the accent colour and dark mode, wraps long Lean messages and
long field types in `{docstring}` boxes, and styles the directives of `Tutorial.Meta`. Each book's `config` is `Book.config` with its own description.
-/

open Verso.Genre.Manual
open Verso.Output Html
open Verso.Web.Theme

namespace Book

/-- Styles shared by the books: the manual genre restyled with the website's design tokens. -/
def bookCss : String := "
:root {
  --verso-header-height: var(--site-header-height);
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

/* The website header in place of the manual header: its layout is `Site.headerCss`; here it is
   only fixed to the top of the page, as the manual genre's layout requires */
header.site-header { position: fixed; top: 0; left: 0; right: 0; z-index: 99; }
/* On a phone the table-of-contents button sits in the header, left of the navigation button,
   so that the wordmark keeps its place. Its lines have unequal lengths, like a list of contents,
   to tell it apart from the navigation button */
@media screen and (max-width: 700px) {
  body { --verso-mobile-burger-width: 1.25rem; --verso-mobile-burger-height: 1.1rem; --verso-mobile-burger-line-width: 2px;
    --verso-mobile-burger-line-radius: 1px; }
  #toggle-toc-click { right: calc(var(--space-2) + var(--space-4) + 3.5rem); left: auto; align-items: flex-start; }
  #toggle-toc-click .line2 { width: 70%; }
  #toggle-toc-click .line3 { width: 85%; }
  body:has(#toggle-toc:checked) #toggle-toc-click .line { width: 100%; }
}
/* The manual genre's search box, which its script appends to the header; `searchToToc` moves it
   to the top of the table of contents */
:root { --verso-background-color: var(--color-surface); }
#toc #search-wrapper { position: relative; display: block; box-sizing: border-box; width: 100%; padding: var(--space-4) 0.5rem 0;
  background: transparent; --search-bar-width: 100%; }
#toc #search-wrapper .combobox, #toc #search-wrapper .combobox .group { width: 100%; }
#toc #search-wrapper .combobox .cb_edit { border: 1px solid var(--color-border-light); border-radius: var(--radius-md);
  font-family: var(--font-primary); font-size: var(--fs-sm); padding: 0.4rem 0.75rem; }
#toc #search-wrapper .combobox .group.focus .cb_edit,
#toc #search-wrapper .combobox .group .cb_edit:hover { outline: none; border-color: var(--color-primary); background-color: var(--color-surface); }
#toc #search-wrapper ul[role=\"listbox\"] { border: 1px solid var(--color-border-light); border-radius: var(--radius-md); }

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

/* Long Lean messages (`#check` and `leanOutput` blocks) wrap instead of overflowing, as on the website */
pre.hl.lean.lean-output { white-space: pre-wrap; overflow-wrap: anywhere; }

/* Exercises and solutions (`Tutorial.Meta`) */
.exercise { margin: var(--space-6) 0; padding: var(--space-4) var(--space-6); border-left: 4px solid var(--color-primary);
  background: var(--color-hover); border-radius: 0 var(--radius-md) var(--radius-md) 0; }
.exercise > :last-child { margin-bottom: 0; }
.exercise-label { margin: 0 0 var(--space-2); font-weight: 700; color: var(--color-primary); letter-spacing: 0.02em; }
.dark-theme .exercise-label { color: #5eead4; }
details.solution { margin-top: var(--space-3); }
details.solution > summary { cursor: pointer; font-weight: 600; color: var(--color-primary); }
.dark-theme details.solution > summary { color: #5eead4; }
.solution-body { padding-top: var(--space-2); }

/* Figures (`Tutorial.Meta`) */
figure.tutorial-figure { margin: var(--space-8) auto; max-width: 420px; }
figure.tutorial-figure figcaption { font-size: var(--fs-sm); color: var(--color-text-light); text-align: center; margin-top: var(--space-2); }
figure.tutorial-figure figcaption p { margin: 0; }

/* Declaration boxes (`{docstring}`): a field whose type does not fit wraps, with a hanging indent,
   instead of being cut off at the right edge of the box */
.namedocs .subdocs pre.name-and-type { white-space: pre-wrap; overflow-wrap: anywhere; padding-left: 2em; text-indent: -2em; }
"

/--
The books' stylesheet, written to `-verso-data/physicslib4.css`: the website's design tokens,
the `verso-web-components` header styles, the website's stylesheet and `bookCss`, in
that order (later rules override earlier ones of equal specificity).
-/
def themeCss : CssFile where
  filename := "physicslib4.css"
  contents := "\n".intercalate [
    Site.colorTheme.toCSS, Static.navbar.css, Site.siteCss, Site.headerCss, bookCss]

/--
A script that moves the manual genre's search box, which its search script appends to the
`<header>` on page load, to the top of the table of contents, below the book title, so that the
header row is the same as the website's. The search box keeps its event handlers when moved.
-/
def searchToToc : String := "
document.addEventListener('DOMContentLoaded', () => {
  const header = document.querySelector('header');
  const toc = document.getElementById('toc');
  if (!header || !toc) return;
  const move = () => {
    const search = header.querySelector('#search-wrapper');
    if (!search) return false;
    const title = toc.querySelector('.toc-title');
    if (title) title.after(search); else toc.prepend(search);
    return true;
  };
  if (move()) return;
  const observer = new MutationObserver(() => { if (move()) observer.disconnect(); });
  observer.observe(header, { childList: true });
});"

/--
The HTML configuration of a book with the meta description `description`: one HTML page per
chapter (`htmlDepth := 1`), and the shared stylesheets, scripts and icons.
-/
def config (description : String) : RenderConfig where
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
    |>.insert "// dark.js points the favicon at /static/favicon-*.ico, which the books do not have; keep favicon.png.
function updateFaviconForSystemTheme(theme) {}"
    |>.insert searchToToc
  extraHead := #[
    {{ <link rel="preconnect" href="https://fonts.googleapis.com" /> }},
    {{ <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin="anonymous" /> }},
    {{ <link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Fira+Code:wght@300..700&family=Open+Sans:ital,wght@0,300..800;1,300..800&display=swap" /> }},
    {{ <link rel="icon" href="favicon.png" /> }},
    {{ <link rel="apple-touch-icon" href="apple-touch-icon.png" /> }},
    {{ <meta name="theme-color" content={{ Site.accent }} /> }},
    {{ <meta name="description" content={{ description }} /> }}
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

/-- An extra build step: puts `header` in place of the manual header on every HTML page. -/
def replaceHeader (header : Html) : ExtraStep := fun mode cfg _ _ => do
  let dir := cfg.destination / (match mode with | .single => "html-single" | .multi => "html-multi")
  let header := header.asString
  for file in ← (dir.walkDir : IO _) do
    if file.extension == some "html" then
      let page ← (IO.FS.readFile file : IO _)
      match replaceHeaderIn header page with
      | some page' => (IO.FS.writeFile file page' : IO _)
      | none => throw <| IO.userError s!"No <header> element in {file}"

end Book
