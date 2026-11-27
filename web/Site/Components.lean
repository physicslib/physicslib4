import VersoBlog
import VersoWeb.Components.Button
import VersoWeb.Components.CodeGallery
import Site.CardArt
import Site.Diagram
import Site.Links

/-!
# Landing-page components

Block components for the landing page. They are thin wrappers around `verso-web-components`
(`button`, `codeGallery`), so that the page itself is written in Verso markup
as a sequence of directives.
-/

open Lean Elab
open Verso Doc Elab ArgParse Output Html
open Verso.Genre Blog Template
open Verso.Web Components

namespace Site

/-- The list of a page's sections, beside the text; the contents of the directive are a list of links. -/
block_component +directive pageToc where
  toHtml _ _ _ goB contents := do
    return {{ <nav class="page-toc" aria-label="On this page">{{ ← contents.mapM goB }}</nav> }}

/--
A section heading with a fixed anchor, the target of a `pageToc` link. The directive has no contents;
the text of the section follows it.
-/
block_component +directive anchoredHeading (anchor : String) (heading : String) where
  toHtml _ _ _ _ _ := do
    return {{ <h2 id={{ anchor }}>{{ heading }}</h2> }}

/-- Text beside the causal-diamond diagram; the argument is the diagram's caption. -/
block_component +directive sideFigure (caption : String) where
  toHtml _ _ _ goB contents := do
    return {{
      <div class="side-figure">
        <div class="side-figure-text">{{ ← contents.mapM goB }}</div>
        <figure class="side-figure-image">
          {{ diamondDiagram }}
          <figcaption>{{ caption }}</figcaption>
        </figure>
      </div>
    }}

/-- The steps of a contribution, as a numbered row. -/
def contributeStepList : Array (String × String) := #[
  ("Set up Lean", "Install Lean, clone the repository and build the library."),
  ("Write it in the blueprint", "State the result and its informal proof, with its dependencies."),
  ("Prove it in Lean", "Add the declaration to the library and link it to its blueprint entry."),
  ("Open a pull request", "It is merged once it passes all status checks, has no conflicts with main, and is approved by a reviewer.")
]

/-- The row of numbered contribution steps. -/
block_component +directive contributeSteps where
  toHtml _ _ _ _ _ := do
    let items : Array Html := contributeStepList.mapIdx fun i (title, desc) => {{
      <li class="step">
        <span class="step-number" aria-hidden="true">{{ toString (i + 1) }}</span>
        <strong class="step-title">{{ title }}</strong>
        <span class="step-text">{{ desc }}</span>
      </li>
    }}
    return {{ <ol class="steps">{{ items }}</ol> }}

/-- A line icon of the Get Involved cards, from its SVG path data. -/
def cardIcon (path : String) : Html := {{
  <svg class="card-icon" viewBox="0 0 24 24" aria-hidden="true" xmlns="http://www.w3.org/2000/svg">
    <path d={{ path }} />
  </svg>
}}

/-- The cards of the Get Involved page: icon path, title, description, link text and link. -/
def contributeCardList : Array (String × String × String × String × String) := #[
  ("M4 5a2 2 0 0 1 2-2h14v16H6a2 2 0 0 0-2 2zM4 21a2 2 0 0 1 2-2h14v2",
    "Learn the library", "The tutorial introduces AQFT and Lean, with worked examples and exercises.",
    "Read the tutorial", tutorialPath),
  ("M6 2h9l5 5v15H6zM15 2v5h5M9 12h8M9 16h8",
    "See what is stated", "The blueprint gives every definition and theorem in mathematical prose, linked to its Lean.",
    "Open the blueprint", blueprintUrl),
  ("M8 6a3 3 0 1 1-3-3 3 3 0 0 1 3 3zM8 18a3 3 0 1 1-3-3 3 3 0 0 1 3 3zM22 18a3 3 0 1 1-3-3 3 3 0 0 1 3 3zM5 9v6M19 15V9a3 3 0 0 0-3-3h-4",
    "Contribute on GitHub", "The source of the library, the blueprint and this website, developed in public.",
    "Go to the repository", githubUrl)
]

/-- The grid of cards of the Get Involved page, in the style of the landing page's feature cards. -/
block_component +directive contributeCards where
  toHtml _ _ _ _ _ := do
    let cards : Array Html := contributeCardList.map fun (icon, title, desc, label, url) => {{
      <a class="feature-card contribute-card" href={{ url }}>
        <div>
          {{ cardIcon icon }}
          <p class="feature-card-text"><strong>{{ title }}</strong></p>
          <p class="feature-card-text">{{ desc }}</p>
        </div>
        <div class="feature-card-footer"><span class="feature-card-more">{{ label }}" →"</span></div>
      </a>
    }}
    return {{ <div class="feature-grid contribute-grid">{{ cards }}</div> }}

/-- A coloured band with a heading, the contents of the directive and a button. -/
block_component +directive callout (heading : String) (label : String) (url : String) where
  toHtml _ _ _ goB contents := do
    return {{
      <aside class="callout">
        <div class="callout-text">
          <h3 class="callout-heading">{{ heading }}</h3>
          {{ ← contents.mapM goB }}
        </div>
        <a class="callout-button" href={{ url }}>{{ label }}</a>
      </aside>
    }}

/--
The hero: wordmark, tagline, the contents of the directive (one sentence), the three call-to-action
buttons, and the causal-diamond diagram.
-/
block_component +directive hero where
  toHtml _ _ _ goB contents := do
    let tutorial ← button .primary tutorialPath {{ "Read the tutorial" }}
    let blueprint ← button .secondary blueprintUrl {{ "Blueprint" }}
    let docs ← button .secondary docsUrl {{ "API docs" }}
    return {{
      <section class="landing-hero container">
        <div class="landing-hero-text">
          <h1 class="landing-wordmark">"hilbert"<span class="wordmark-six">"6"</span></h1>
          <p class="landing-tagline">{{ tagline }}</p>
          <div class="landing-lede">{{ ← contents.mapM goB }}</div>
          <div class="landing-buttons">{{ tutorial }}{{ blueprint }}{{ docs }}</div>
        </div>
        <figure class="landing-hero-figure">
          {{ diamondDiagram }}
          <figcaption>
            "Algebraic quantum field theory's axiom 3 in one picture: the diamonds B₁ and B₂ are spacelike separated inside B, so their observables commute."
          </figcaption>
        </figure>
      </section>
    }}

/-- The markup of a landing-page section; `extraClass` is appended to its classes. -/
def sectionHtml (anchor heading extraClass : String) (body : Html) : Html := {{
  <section class=s!"landing-section container{extraClass}" id={{ anchor }}>
    <h2 class="landing-section-title">{{ heading }}</h2>
    {{ body }}
  </section>
}}

/-- A landing-page section with an anchor and a heading. -/
block_component +directive landingSection (anchor : String) (heading : String) where
  toHtml _ _ _ goB contents := do
    return sectionHtml anchor heading "" (← contents.mapM goB)

/-- A landing-page section whose heading and paragraphs are centred (other blocks keep full width). -/
block_component +directive centeredSection (anchor : String) (heading : String) where
  toHtml _ _ _ goB contents := do
    return sectionHtml anchor heading " centered" (← contents.mapM goB)

/--
`codeGallery` from `verso-web-components` (the tabbed code box of lean-lang.org) as a directive. Its
contents come in groups of four blocks per tab: the tab title, the code, the caption and the caption's
link.
-/
@[directive]
def gallery : DirectiveExpanderOf Unit
  | (), stxs => do
    let contents ← stxs.mapM elabBlock
    ``(Verso.Web.Components.codeGallery #[ $contents,* ])

/-- The groups of feature cards, in the order of the rails on the landing page. -/
inductive FeatureGroup where
  | operators
  | spacetime
  | modular
  | structural
  deriving BEq

/-- The heading of a rail of feature cards. -/
def FeatureGroup.heading : FeatureGroup → String
  | .operators => "Operator algebra and spectral theory"
  | .spacetime => "Spacetime and axioms"
  | .modular => "Modular theory"
  | .structural => "Structural theorems"

/-- The anchor of a rail of feature cards. -/
def FeatureGroup.anchor : FeatureGroup → String
  | .operators => "rail-operators"
  | .spacetime => "rail-spacetime"
  | .modular => "rail-modular"
  | .structural => "rail-structural"

/-- The groups of feature cards, in order. -/
def featureGroups : Array FeatureGroup := #[.operators, .spacetime, .modular, .structural]

/--
One feature card: its group, title, description (at most two lines on the card), blueprint
sections, link, and illustration, the name of a drawing in `Site.cardArt` (written by
`scripts/gen_hero_background.py`).
-/
structure FeatureCard where
  group : FeatureGroup
  title : String
  desc : String
  sections : Array String
  url : String
  image : String

/-- The feature cards, one per area of the formalisation, linking to the matching
reference-manual chapter or section. A card is a single link, so its section tags are not links. -/
def featureCards : Array FeatureCard := #[
  { group := .operators
    title := "The GNS construction"
    desc := "From a state on a C*-algebra to a cyclic representation, unique up to unitary equivalence."
    sections := #["§10.1"]
    url := manualChapterUrl "The-GNS-construction"
    image := "gns" },
  { group := .operators
    title := "The bounded spectral theorem"
    desc := "Projection-valued measures and the functional calculus of bounded normal operators."
    sections := #["§10.2"]
    url := manualChapterUrl "Bounded-spectral-theory"
    image := "spectral-bounded" },
  { group := .operators
    title := "The unbounded spectral theorem"
    desc := "Closed and self-adjoint operators, their spectral measures and functional calculus."
    sections := #["§10.3"]
    url := manualChapterUrl "Unbounded-operators-and-their-spectral-theorem"
    image := "spectral-unbounded" },
  { group := .operators
    title := "Stone's theorem"
    desc := "Every strongly continuous unitary group is U(t) = exp(itA) for a unique self-adjoint A."
    sections := #["§10.4"]
    url := manualChapterUrl "Stones-theorem"
    image := "stone" },
  { group := .spacetime
    title := "Spacetime geometry"
    desc := "Causal structure, the Levi-Civita connection and geodesics on Lorentzian manifolds."
    sections := #["§10.5"]
    url := manualChapterUrl "Spacetime-and-geometry"
    image := "spacetime" },
  { group := .spacetime
    title := "Haag–Kastler axioms in Minkowski spacetime"
    desc := "Local C*-algebras on causal diamonds: isotony, local commutativity, Lorentz covariance."
    sections := #["§10.6"]
    url := manualChapterUrl "Haag-Kastler-axioms-in-Minkowski-spacetime"
    image := "haag-kastler" },
  { group := .spacetime
    title := "The axioms in curved spacetime"
    desc := "The same axioms on a Lorentzian spacetime, with isometric and general covariance."
    sections := #["§10.7", "§10.8"]
    url := manualChapterUrl "The-axioms-in-curved-spacetime-and-general-covariance"
    image := "curved" },
  { group := .modular
    title := "Tomita–Takesaki theory"
    desc := "The modular operator and conjugation, Tomita's theorem and Takesaki's KMS theorem."
    sections := #["§10.10"]
    url := manualChapterUrl "Tomita-Takesaki-theory"
    image := "tomita-takesaki" },
  { group := .modular
    title := "Borchers' theorem and the wedge modular group"
    desc := "The modular group dilates half-sided translations; for a wedge it acts on them as boosts."
    sections := #["§10.11"]
    url := manualChapterUrl "Borchers-theorem-and-the-wedge-modular-group"
    image := "borchers" },
  { group := .structural
    title := "The Reeh–Schlieder theorem"
    desc := "The vacuum is cyclic for every nonempty diamond, and separating where there is spacelike room."
    sections := #["§10.9"]
    url := manualChapterUrl "The-Reeh-Schlieder-theorem"
    image := "reeh-schlieder" },
  { group := .structural
    title := "Bisognano–Wichmann up to an internal symmetry"
    desc := "Under modular covariance, the wedge modular group is the boost group up to an internal symmetry."
    sections := #["§10.11"]
    url := manualChapterUrl "Borchers-theorem-and-the-wedge-modular-group" ++
      "#borchers-wedges-bw-internal"
    image := "bisognano-wichmann" }
]

/--
The script of the rails, run once the page is loaded (Verso puts the scripts of components in the
`<head>`): it shows each rail's previous and next buttons (hidden without
JavaScript, when the rail is a plain scrollable row), scrolls the rail by one card per click, and
disables a button at the matching end of the rail. Rails whose cards all fit hide their buttons.
-/
def railScript : String := "
document.addEventListener('DOMContentLoaded', function () {
document.querySelectorAll('.feature-rail').forEach(function (rail) {
  var track = rail.querySelector('.feature-rail-track');
  var controls = rail.querySelector('.feature-rail-controls');
  var prev = rail.querySelector('.feature-rail-prev');
  var next = rail.querySelector('.feature-rail-next');
  if (!track || !controls) return;
  function step() {
    var card = track.querySelector('.feature-card');
    var gap = parseFloat(getComputedStyle(track).columnGap) || 0;
    return card ? card.getBoundingClientRect().width + gap : track.clientWidth;
  }
  function update() {
    var max = track.scrollWidth - track.clientWidth;
    controls.hidden = max <= 1;
    prev.disabled = track.scrollLeft <= 1;
    next.disabled = track.scrollLeft >= max - 1;
  }
  prev.addEventListener('click', function () { track.scrollBy({ left: -step(), behavior: 'smooth' }); });
  next.addEventListener('click', function () { track.scrollBy({ left: step(), behavior: 'smooth' }); });
  track.addEventListener('scroll', update, { passive: true });
  window.addEventListener('resize', update);
  update();
});
});
"

/--
One feature card, a single link. Its illustration is the inline SVG of `Site.cardArt`, drawn in
`currentColor` with accent groups, so its colours follow the theme (`Site.siteCss`).
-/
def featureCardHtml (c : FeatureCard) : Html :=
  let art := ((cardArt.lookup c.image).getD "")
  {{
    <a class="feature-card rail-card" href={{ c.url }}>
      <span class="feature-card-art" aria-hidden="true">{{ Html.raw art }}</span>
      <span class="feature-card-title">{{ c.title }}</span>
      <span class="feature-card-desc">{{ c.desc }}</span>
      <span class="feature-card-footer">
        <span class="feature-card-tags">
          {{ c.sections.map fun (t : String) => ({{ <span class="feature-card-tag">{{ t }}</span> }} : Html) }}
        </span>
        <span class="feature-card-more">"Read more →"</span>
      </span>
    </a>
  }}

/--
The feature cards in four rails, one per `FeatureGroup`, each with a heading and a horizontally
scrolling, scroll-snapping row of cards. The markup is this site's own (`verso-web-components`'
`learnCard` has a fixed "OPEN" label); the styles are in `Site.Theme.siteCss`. Without JavaScript a
rail is a scrollable row; with it, `railScript` adds previous and next buttons.
-/
block_component +directive features where
  toHtml _ _ _ _ _ := do
    saveJs railScript
    let rail (g : FeatureGroup) : Html := {{
      <section class="feature-rail" aria-labelledby={{ g.anchor }}>
        <div class="feature-rail-head">
          <h3 class="feature-rail-heading" id={{ g.anchor }}>{{ g.heading }}</h3>
          <div class="feature-rail-controls" hidden="">
            <button type="button" class="feature-rail-button feature-rail-prev" aria-label=s!"Previous cards: {g.heading}">"←"</button>
            <button type="button" class="feature-rail-button feature-rail-next" aria-label=s!"Next cards: {g.heading}">"→"</button>
          </div>
        </div>
        <div class="feature-rail-track" role="list" tabindex="0" aria-label={{ g.heading }}>
          {{ (featureCards.filter (·.group == g)).map fun c =>
              ({{ <div class="feature-rail-item" role="listitem">{{ featureCardHtml c }}</div> }} : Html) }}
        </div>
      </section>
    }}
    return {{ <div class="feature-rails">{{ featureGroups.map rail }}</div> }}

end Site
