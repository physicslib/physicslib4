import VersoBlog
import VersoWeb.Theme
import VersoWeb.Components.Icon
import Site.Links

/-!
# Site theme

The physicslib4 site uses the Lean FRO look from `verso-web-components`: its stylesheets, scripts,
`<head>` builder, page templates and design tokens. Three things differ from lean-lang.org.

* The header and footer carry a plain "physicslib4" wordmark. The stock `NavBar` and `Footer`
  components of `verso-web-components` draw the Lean logo, so this module writes its own header and
  footer markup with the same CSS classes.
* The accent colour (`--color-primary` and its derived shades) is a deep teal, `#0f766e`.
* Highlighted Lean code is coloured (keywords, constants, bound variables); see `siteCss`.

The tutorial and the reference manual, manual-genre books, reuse `colorTheme`, `siteCss`,
`headerCss` and `headerWith` (`Book.Theme`).
-/

open Verso Genre Blog Output Html Template Multi
open Verso.Web Components Theme

namespace Site

/-- The accent colour of the site. -/
def accent : String := "#0f766e"

/--
Design tokens. These are the lean-lang.org values (from `leanprover/reference-manual`,
`Tutorial/Meta/Theme.lean`), except that the primary colour family is deep teal.
-/
def colorTheme : ThemeConfig := {
  variables := [
    -- Typography
    { name := "font-primary", value := "'Open Sans', Arial, sans-serif" },
    { name := "font-secondary", value := "'Oranienbaum', serif" },
    { name := "fs-xs", value := "0.75rem" },
    { name := "fs-sm", value := "0.875rem" },
    { name := "fs-base", value := "1rem" },
    { name := "fs-md", value := "17px" },
    { name := "fs-lg", value := "1.25rem" },
    { name := "fs-xl", value := "2rem" },
    { name := "fs-2xl", value := "3.3rem" },
    -- Spacing
    { name := "space-1", value := "0.25rem" },
    { name := "space-2", value := "0.5rem" },
    { name := "space-3", value := "0.75rem" },
    { name := "space-4", value := "1rem" },
    { name := "space-5", value := "1.25rem" },
    { name := "space-6", value := "1.5rem" },
    { name := "space-8", value := "2rem" },
    { name := "space-10", value := "2.5rem" },
    { name := "space-12", value := "3rem" },
    { name := "space-13", value := "3.5rem" },
    { name := "space-14", value := "4rem" },
    { name := "space-16", value := "5rem" },
    { name := "gap-sm", value := "var(--space-2)" },
    { name := "gap-md", value := "10px" },
    { name := "gap-lg", value := "30px" },
    { name := "gap-xl", value := "100px" },
    { name := "section-padding", value := "var(--space-10)" },
    { name := "section-padding-top", value := "var(--space-16)" },
    -- Border radius
    { name := "radius-sm", value := "0.25rem" },
    { name := "radius-md", value := "0.5rem" },
    { name := "radius-lg", value := "1rem" },
    { name := "radius-pill", value := "9999px" },
    -- Sizes
    { name := "container-width", value := "1240px" },
    { name := "logo-size", value := "1.25rem" },
    { name := "logo-footer-size", value := "60px" },
    { name := "icon-size", value := "64px" },
    -- Layout
    { name := "nav-padding-y", value := "var(--space-6)" },
    { name := "nav-padding-x", value := "10vw" },
    { name := "nav-height", value := "calc(var(--nav-padding-y) * 2 + 2em)" },
    -- Transitions
    { name := "transition-fast", value := "0.2s" },
    { name := "transition-base", value := "0.3s" },
    { name := "transition-slow", value := "0.6s" },
    { name := "transition-delay-none", value := "0s" },
    { name := "transition-delay-small", value := "0.05s" },
    { name := "transition-delay-medium", value := "0.1s" },
    { name := "transition-delay-large", value := "0.15s" },
    { name := "animation-delay", value := "10000ms" },
    -- Z-index
    { name := "z-below", value := "-1" },
    { name := "z-normal", value := "0" },
    { name := "z-above", value := "1" },
    { name := "z-header", value := "1000" },
    -- Colours: the primary family is the teal accent; the rest is lean-lang.org
    { name := "color-surface", value := "#fff" },
    { name := "color-primary", value := accent },
    { name := "color-primary-focus", value := "#115e59" },
    { name := "color-primary-light", value := "#14b8a6" },
    { name := "color-secondary", value := "#607D8B" },
    { name := "color-text", value := "#333" },
    { name := "color-text-contrast", value := "white" },
    { name := "color-text-light", value := "#64748b" },
    { name := "color-muted", value := "#607D8B" },
    { name := "color-bg", value := "#F9FBFD" },
    { name := "color-bg-translucent", value := "rgba(249, 251, 253, 0.81)" },
    { name := "color-white", value := "#fff" },
    { name := "color-border", value := "#E4EBF3" },
    { name := "color-border-nav", value := "#E4EBF3" },
    { name := "color-border-light", value := "#D1D9E2" },
    { name := "color-hover", value := "rgba(15, 118, 110, 0.08)" },
    { name := "color-link-hover", value := "#0d9488" },
    { name := "color-shadow", value := "rgba(35, 55, 139, 0.1)" },
    -- Components
    { name := "btn-bg", value := "var(--color-primary)" },
    { name := "btn-text", value := "var(--color-white)" },
    { name := "btn-font", value := "var(--font-primary)" },
    { name := "btn-radius", value := "var(--radius-md)" },
    { name := "card-bg", value := "var(--color-white)" },
    { name := "card-border", value := "var(--color-border-light)" },
    { name := "testimonial-bg", value := "var(--color-primary)" },
    { name := "testimonial-text", value := "var(--color-white)" }
  ],
  darkVariables := [
    { name := "color-surface", value := "#121212" },
    { name := "color-primary", value := "#0d9488" },
    { name := "color-primary-focus", value := "#5eead4" },
    { name := "color-primary-light", value := "#5eead4" },
    { name := "color-secondary", value := "#aabfc9" },
    { name := "color-text", value := "#eee" },
    { name := "color-text-light", value := "#bbb" },
    { name := "color-text-contrast", value := "white" },
    { name := "color-muted", value := "#90a4ae" },
    { name := "color-bg", value := "#181818" },
    { name := "color-bg-translucent", value := "rgba(24, 24, 24, 0.85)" },
    { name := "color-white", value := "#1e1e1e" },
    { name := "color-border", value := "#333" },
    { name := "color-border-nav", value := "#333" },
    { name := "color-border-light", value := "#444" },
    { name := "color-hover", value := "rgba(45, 212, 191, 0.14)" },
    { name := "color-link-hover", value := "#5eead4" },
    { name := "color-shadow", value := "rgba(0, 0, 0, 0.5)" },
    { name := "btn-bg", value := "var(--color-primary)" },
    { name := "btn-text", value := "var(--color-white)" },
    { name := "card-bg", value := "#1f1f1f" },
    { name := "card-border", value := "#2a2a2a" },
    { name := "testimonial-bg", value := "#134e4a" },
    { name := "testimonial-text", value := "#fff" }
  ]
}


/--
Additions to the `verso-web-components` stylesheets: the text wordmark, the landing-page layout, the
spacetime diagram, and colours for highlighted Lean code. Colours come from the design tokens above.

Verso marks up Lean code with `.keyword`, `.const` and `.var` token classes, but its defaults (and
lean-lang.org) render all of them in the text colour, distinguished only by weight and slant. This
site gives them colours through Verso's `--verso-code-*-color` variables; inside the `codeGallery`
box, whose stylesheet forces the text colour on every token, the same colours are reapplied.
-/
def siteCss : String := "
:root {
  --verso-code-color: var(--color-text);
  --verso-code-keyword-color: #0f766e;
  --verso-code-const-color: #9a3412;
  --verso-code-var-color: #1e40af;
  --verso-output-info-color: var(--color-primary);
  --verso-info-indicator-color: var(--color-primary);
}
.dark-theme {
  --verso-code-keyword-color: #5eead4;
  --verso-code-const-color: #fdba74;
  --verso-code-var-color: #93c5fd;
  --verso-code-hover-bg-color: rgba(255, 255, 255, 0.1);
}
.code-gallery-box .hl.lean span.keyword { color: var(--verso-code-keyword-color) !important; }
.code-gallery-box .hl.lean span.const { color: var(--verso-code-const-color) !important; }
.code-gallery-box .hl.lean span.var { color: var(--verso-code-var-color) !important; }
.code-gallery-box .hl.lean span.doc-comment, .code-gallery-box .hl.lean span.comment { color: var(--color-text-light) !important; }

.nav-logo.wordmark { font-weight: 600; font-size: 1.4rem; letter-spacing: 0.01em; color: var(--color-text); text-decoration: none; }
.nav-logo.wordmark:hover { color: var(--color-primary); }
.footer-wordmark { font-weight: 600; font-size: 1.25rem; color: var(--color-text-contrast); text-decoration: none; }
.post-content a { color: var(--color-primary); }
.post-content pre.lean-output { white-space: pre-wrap; overflow-wrap: anywhere; }

main.landing { padding-bottom: var(--space-16); }
.landing-hero { display: grid; grid-template-columns: 1.15fr 1fr; gap: var(--space-12); align-items: center; padding-top: var(--space-16); }
.landing-wordmark { font-size: var(--fs-2xl); font-weight: 600; line-height: 1.1; color: var(--color-text); margin: 0; }
.landing-tagline { font-size: var(--fs-lg); color: var(--color-primary); margin: var(--space-3) 0 0; }
.landing-lede p { font-size: var(--fs-md); color: var(--color-text-light); margin: var(--space-6) 0 0; line-height: 1.6; }
.landing-buttons { display: flex; flex-wrap: wrap; gap: var(--space-3); margin-top: var(--space-8); }
.landing-buttons .button { padding: var(--space-3) var(--space-6); text-decoration: none; }
.landing-hero-figure { margin: 0; justify-self: center; width: 100%; max-width: 420px; }
.landing-hero-figure figcaption { font-size: var(--fs-sm); color: var(--color-text-light); text-align: center; margin-top: var(--space-2); }

.st-diagram { width: 100%; height: auto; display: block; }
.st-big { fill: var(--color-primary); fill-opacity: 0.07; stroke: var(--color-primary); stroke-width: 2; }
.st-small { fill: var(--color-primary); fill-opacity: 0.3; stroke: var(--color-primary); stroke-width: 2; }
.st-cone { stroke: var(--color-text-light); stroke-width: 1.5; stroke-dasharray: 5 5; }
.st-axis { stroke: var(--color-text-light); stroke-width: 1.5; }
.st-arrowhead { fill: var(--color-text-light); }
.st-label { fill: var(--color-text); font-family: var(--font-primary); font-size: 20px; font-weight: 600; }
.st-label-small { font-size: 16px; }
.st-axis-label { fill: var(--color-text-light); font-family: serif; font-style: italic; font-size: 16px; }

.landing-section { padding-top: var(--space-16); }
.landing-section-title { font-size: var(--fs-xl); font-weight: 600; color: var(--color-text); margin: 0 0 var(--space-6); }
.landing-section > p { max-width: 46rem; line-height: 1.7; color: var(--color-text); }
.landing-section a { color: var(--color-primary); }
.landing-section .code-gallery-box { height: auto; }
.landing-section .code-gallery-content { min-height: 0; font-size: 1rem; }
.landing-section .code-gallery-snippet.visible-code { padding: var(--space-6) var(--space-8); }
.code-gallery-run svg { fill: var(--color-primary); }
.landing-section .code-gallery-box { margin-top: var(--space-6); }
.landing-section.centered .landing-section-title { text-align: center; }
.landing-section.centered > p { text-align: center; margin-left: auto; margin-right: auto; max-width: 42rem; }

.feature-grid { display: grid; grid-template-columns: repeat(3, 1fr); gap: var(--space-4); }
a.feature-card { display: flex; flex-direction: column; justify-content: space-between; gap: var(--space-6);
  padding: var(--space-8); background: var(--card-bg); border: 1px solid var(--color-border); border-radius: var(--radius-md);
  color: var(--color-text); text-decoration: none; transition: border-color var(--transition-base), box-shadow var(--transition-base); }
a.feature-card:hover { border-color: var(--color-primary); box-shadow: 0 6px 18px var(--color-shadow); }
.feature-card-text { margin: 0; line-height: 1.55; color: var(--color-text); }
.feature-card-text strong { font-weight: 700; }
.feature-card-footer { display: flex; align-items: center; justify-content: space-between; gap: var(--space-3); flex-wrap: wrap; }
.feature-card-tags { display: flex; gap: var(--space-2); flex-wrap: wrap; }
.feature-card-tag { background: var(--color-hover); color: var(--color-primary); padding: 2px 10px; border-radius: var(--radius-pill); font-size: var(--fs-xs); font-weight: 600; }
.feature-card-more { color: var(--color-primary); font-size: var(--fs-sm); font-weight: 600; white-space: nowrap; transition: transform var(--transition-base); }
a.feature-card:hover .feature-card-more { transform: translateX(3px); }

.post-content:has(.page-toc) { position: relative; }
.post-content h2[id] { scroll-margin-top: calc(var(--site-header-height) + var(--space-4)); }
.page-toc { position: absolute; left: calc(100% + var(--space-8)); top: 6rem; width: 12rem; }
@media (max-width: 1279px) { .page-toc { display: none; } }
.page-toc ul { list-style: none; margin: 0; padding: 0; }
.page-toc li { margin: 0 0 var(--space-4); }
.post-content .page-toc a { color: var(--color-text) !important; background: none !important; text-decoration: none; font-size: var(--fs-sm); }
.post-content .page-toc a:hover { color: var(--color-primary) !important; }

.side-figure { display: grid; grid-template-columns: 1.5fr 1fr; gap: var(--space-8); align-items: center; }
.side-figure-image { margin: 0; }
.side-figure-image figcaption { font-size: var(--fs-sm); line-height: 1.45; color: var(--color-text-light); text-align: center; margin-top: var(--space-2); }

.post-content ol.steps { list-style: none; margin: var(--space-6) 0 0; padding: 0; display: grid; grid-template-columns: repeat(4, 1fr); gap: var(--space-5); position: relative; }
.steps::before { content: ''; position: absolute; top: 1.2rem; left: 1.2rem; right: 25%; border-top: 2px solid var(--color-border-light); }
.post-content .steps li.step { display: flex; flex-direction: column; gap: var(--space-2); margin: 0; padding: 0; position: relative; }
.step-number { display: flex; align-items: center; justify-content: center; width: 2.4rem; height: 2.4rem; border-radius: 50%;
  background: var(--testimonial-bg); color: var(--testimonial-text); font-weight: 700; }
.step-title { line-height: 1.3; margin-top: var(--space-2); }
.step-text { font-size: var(--fs-sm); line-height: 1.5; color: var(--color-text-light); }

.contribute-grid { margin-top: var(--space-6); }
.post-content a.contribute-card { padding: var(--space-6); color: var(--color-text) !important; background: var(--card-bg) !important; }
.contribute-card .feature-card-text { margin: 0 0 var(--space-2); font-size: var(--fs-sm); }
.contribute-card .feature-card-text strong { font-size: var(--fs-base); }
.card-icon { display: block; width: 2rem; height: 2rem; margin-bottom: var(--space-3); fill: none; stroke: var(--color-primary); stroke-width: 1.6; stroke-linecap: round; stroke-linejoin: round; }
.dark-theme .card-icon { stroke: #5eead4; }

.callout { display: flex; align-items: center; justify-content: space-between; gap: var(--space-6); margin-top: var(--space-12);
  padding: var(--space-8); border-radius: var(--radius-lg); background: var(--testimonial-bg); color: var(--testimonial-text); }
.post-content .callout h3.callout-heading { margin: 0 0 var(--space-2); font-size: var(--fs-lg); color: inherit; }
.post-content .callout p { margin: 0; color: inherit; }
.post-content .callout-text a { color: inherit !important; text-decoration: underline; background: none !important; }
.post-content a.callout-button { flex: none; padding: var(--space-3) var(--space-6); border-radius: var(--radius-md); background: #fff !important; color: #0f766e !important; font-weight: 600; text-decoration: none; }
.post-content a.callout-button:hover { background: #ccfbf1 !important; }

.nav-item.active .nav-link { background-color: rgba(15, 118, 110, 0.12); color: var(--color-primary); }
.dark-theme .nav-item.active .nav-link { background-color: rgba(45, 212, 191, 0.16); color: #5eead4; }
.dark-theme .nav-link:hover { color: #5eead4; }
.dark-theme .feature-card-tag, .dark-theme .feature-card-more { color: #5eead4; }

@media (max-width: 900px) {
  .landing-hero { grid-template-columns: 1fr; padding-top: var(--space-10); }
  .feature-grid { grid-template-columns: 1fr; }
  .side-figure { grid-template-columns: 1fr; }
  .side-figure-image { max-width: 280px; justify-self: center; }
  .post-content ol.steps { grid-template-columns: 1fr; }
  .steps::before { display: none; }
  .callout { flex-direction: column; align-items: flex-start; }
}
"

/--
The header's geometry and typography, shared by the website and the books (`Book.Theme`), so that
the wordmark, the navigation and the icons have the same size and position on every page. The
manual genre's stylesheet (`book.css`) styles `header`, links, lists and buttons differently from
`verso-web-components`, so every property that affects the header's layout is set here, on
selectors that outrank both: the height (`--site-header-height`, also the books' header height),
the padding and maximum width of the row, the font family, size, weight and line height of the
wordmark and the navigation links, and the list and button resets.
-/
def headerCss : String := "
:root { --site-header-height: 4.5rem; }
header.site-header { display: flex; align-items: center; box-sizing: border-box; height: var(--site-header-height);
  margin: 0; padding: 0; box-shadow: none; background-color: var(--color-bg-translucent);
  border-bottom: 1px solid var(--color-border-nav); font-family: var(--font-primary); font-size: 1rem; line-height: 1.2; }
header.site-header .navbar { flex: 1; min-width: 0; height: 100%; box-sizing: border-box;
  padding: 0 var(--space-8); border-bottom: 0; }
header.site-header .navbar-container.container { max-width: min(var(--container-width), 100vw); padding: 0 var(--space-4);
  margin: 0 auto; width: 100%; box-sizing: border-box; }
header.site-header ul, header.site-header menu, header.site-header li { margin: 0; padding: 0; list-style: none; }
header.site-header button { background: none; border: 0; margin: 0; font: inherit; color: inherit; cursor: pointer; }
header.site-header a { text-decoration: none; }
header.site-header .nav-logo.wordmark { font-family: var(--font-primary); font-size: 1.4rem; font-weight: 600; line-height: 1.2;
  letter-spacing: 0.01em; margin: 0 var(--space-6) 0 0; padding: 0; }
header.site-header .nav-link { font-family: var(--font-primary); font-size: 0.9rem; font-weight: 500; line-height: 1.2;
  padding: var(--space-3) var(--space-4); margin: 0; }
header.site-header .nav-link svg { width: 20px; height: 20px; }
header.site-header .nav-toggle-label { font-size: var(--fs-xl); line-height: 1.2; padding: var(--space-3); }
header.site-header .desktop-menu .nav-link { padding-left: var(--space-2); padding-right: var(--space-2); }
@media (max-width: 1150px) { header.site-header .navbar { padding: 0 var(--space-2); } }
@media (max-width: 1024px) { header.site-header { background-color: var(--color-bg); } }
@media (max-width: 768px) { header.site-header .navbar { padding: 0 var(--space-2); } }
"

/-- One navigation entry, marked active when `active` holds. -/
def navItem (active : Bool) (title url : String) : Html :=
  {{ <li class=s!"nav-item{if active then " active" else ""}"><a class="nav-link" href={{url}}>{{title}}</a></li> }}

/--
The header shared by the website and the books: the wordmark (linking to `home`) on the left;
the navigation `links`, GitHub and the theme switch on the right. `isActive` picks the navigation
entry of the current page by its title.
-/
def headerWith (home : String) (links : Array (String × String)) (isActive : String → Bool) : Html := {{
  <header class="site-header">
    <nav class="navbar" role="navigation" aria-label="Primary navigation">
      <div class="navbar-container container">
        <a class="nav-logo wordmark" href={{ home }}>"physicslib4"</a>
        <div class="nav-toggle">
          <input type="checkbox" id="nav-toggle" class="nav-toggle-checkbox" />
          <label for="nav-toggle" class="nav-toggle-label" aria-label="Toggle navigation menu">"☰"</label>
        </div>
        <menu class="desktop-menu">
          <ul class="desktop-menu-part"></ul>
          <ul class="desktop-menu-part">
            {{ links.map fun (t, u) => navItem (isActive t) t u }}
            <li class="nav-item">
              <a class="nav-link" href={{ githubUrl }} aria-label="GitHub">{{ (Icon.github : Html) }}</a>
            </li>
            <li class="nav-item">
              <button class="nav-link change-theme" aria-label="Change theme">{{ (Icon.moon : Html) }}</button>
            </li>
          </ul>
        </menu>
      </div>
      <menu class="mobile-nav">
        <ul class="nav-list">
          {{ links.map fun (t, u) => navItem (isActive t) t u }}
          {{ navItem false "GitHub" githubUrl }}
        </ul>
      </menu>
    </nav>
  </header>
}}

/--
The website header on the page at `path`. The entry of the current page is active; the entries of
the books, the blueprint and the API docs lead out of the website.
-/
def header (path : Array String) : Html :=
  let current := path[0]?.map (· ++ "/")
  headerWith "./" navLinks fun title =>
    navLinks.any fun (t, u) => t == title && some u == current

/--
The footer of the website, using the `verso-web-components` footer classes. `home` is as in
`headerWith`; `links` are the documentation links.
-/
def footerWith (home : String) (links : Array (String × String)) : Html :=
  let link (title url : String) : Html :=
    {{ <li><a class="footer-text" href={{url}}>{{title}}</a></li> }}
  {{
    <footer role="contentinfo" aria-label="Site footer">
      <div class="footer-grid container">
        <nav class="footer-column" aria-label="physicslib4">
          <a class="footer-wordmark" href={{ home }}>"physicslib4"</a>
        </nav>
        <nav class="footer-column" aria-label="Documentation">
          <h3 class="footer-heading">"Documentation"</h3>
          <ul class="footer-links">
            {{ links.map fun (t, u) => link t u }}
          </ul>
        </nav>
        <nav class="footer-column" aria-label="Project">
          <h3 class="footer-heading">"Project"</h3>
          <ul class="footer-links">
            {{ link "About" aboutPath }}
            {{ link "Roadmap" roadmapPath }}
            {{ link "Get involved" getInvolvedPath }}
            {{ link "GitHub" githubUrl }}
            {{ link "Blueprint (PDF)" (publishedRoot ++ "blueprint.pdf") }}
          </ul>
        </nav>
      </div>
      <div class="footer-divider container" role="separator"></div>
      <div class="footer-bottom container">
        <div class="footer-copy">"physicslib4 is released under the Apache 2.0 licence."</div>
        <div class="footer-socials">
          <label class="theme-switch">
            <input type="checkbox" class="change-theme" />
            <div class="switch-container"><span class="slider"></span></div>
          </label>
        </div>
      </div>
    </footer>
  }}

/-- The website footer. -/
def footer : Html := footerWith "./" (docLinksFrom tutorialPath manualPath)

/--
Page metadata for the `<head>`. The icons are a plain "p4" wordmark tile in the accent colour
(`static_files/apple-touch-icon.png`, `static_files/favicon.png`), copied to the site root.
-/
def headConfig : HeadConfig := {
  description := tagline
  faviconWhite := "favicon.png"
  faviconDark := "favicon.png"
  appleTouchIcon := "apple-touch-icon.png"
  color := accent
}

/-- The outer HTML template, modelled on `Verso.Web.Theme.primaryTemplate`. -/
def primaryTemplate : TemplateM Html := do
  let headHtml ← Verso.Web.Theme.head "physicslib4" s!"physicslib4: {tagline}" headConfig colorTheme
    (extraHead := {{ <style>{{ .text false (siteCss ++ headerCss) }}</style> }})
  return {{
    <html lang="en">
      {{ headHtml }}
      <body>
        {{ header (← currentPath) }}
        {{ ← param "content" }}
        {{ footer }}
        <script>
          "// dark.js points the favicon at /static/favicon-*.ico, which this site does not have; keep favicon.png.
          function updateFaviconForSystemTheme(theme) {}"
        </script>
        <script id="MathJax-script" src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
      </body>
    </html>
  }}

/--
The page template. The landing page is a sequence of full-width sections built by the components in
`Site.Components`; every other page uses the centred article layout of `verso-web-components`.
-/
def pageTemplate : TemplateM Html := do
  let path ← currentPath
  let content ← param "content"
  if path.isEmpty then
    return {{ <main class="landing">{{ content }}</main> }}
  else
    return {{
      <main class="container">
        <div class="post-center post-page">
          <article class="post-container">
            <div class="post-content">
              <h1 class="page-title">{{ ← param (α := String) "title" }}</h1>
              {{ content }}
            </div>
          </article>
        </div>
      </main>
    }}

/-- The site theme. -/
def theme : Theme := {
  primaryTemplate := primaryTemplate
  pageTemplate := pageTemplate
  postTemplate := Verso.Web.Theme.postTemplate {}
  archiveEntryTemplate := Verso.Web.Theme.archiveEntry
  categoryTemplate := Verso.Web.Theme.categoryTemplate
  cssFiles := Verso.Web.Theme.Static.allCSS
  jsFiles := Verso.Web.Theme.Static.allJS.map (fun x => (x.1, x.2, false))
}

end Site
