import VersoBlog
import VersoWeb.Components.Button
import VersoWeb.Components.CodeGallery
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
          <h1 class="landing-wordmark">"physicslib4"</h1>
          <p class="landing-tagline">{{ tagline }}</p>
          <div class="landing-lede">{{ ← contents.mapM goB }}</div>
          <div class="landing-buttons">{{ tutorial }}{{ blueprint }}{{ docs }}</div>
        </div>
        <figure class="landing-hero-figure">
          {{ diamondDiagram }}
          <figcaption>
            "Axiom 3 in one picture: the diamonds B₁ and B₂ are spacelike separated inside B, so their observables commute."
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

/-- One feature card: title, description, blueprint sections and link. -/
structure FeatureCard where
  title : String
  desc : String
  sections : Array String
  url : String

/-- The feature cards, one per area of the formalisation, linking to the top of the matching
reference-manual chapter. The spectral card covers two chapters and links to the first, "Bounded
spectral theory"; a card is a single link, so its section tags are not links. -/
def featureCards : Array FeatureCard := #[
  { title := "Haag–Kastler axioms in Minkowski spacetime."
    desc := "Local C*-algebras on causal diamonds, isotony, local commutativity, Lorentz covariance, and the quasilocal algebra."
    sections := #["§10.6"]
    url := manualChapterUrl "Haag-Kastler-axioms-in-Minkowski-spacetime" },
  { title := "The axioms in curved spacetime."
    desc := "The same axioms on a Lorentzian spacetime, with isometric covariance and general covariance across backgrounds."
    sections := #["§10.7", "§10.8"]
    url := manualChapterUrl "The-axioms-in-curved-spacetime-and-general-covariance" },
  { title := "The GNS construction."
    desc := "From a state on a C*-algebra to a cyclic Hilbert-space representation, unique up to unitary equivalence."
    sections := #["§10.1"]
    url := manualChapterUrl "The-GNS-construction" },
  { title := "Spectral theorems."
    desc := "Projection-valued measures for bounded and for unbounded self-adjoint operators, with their functional calculi."
    sections := #["§10.2", "§10.3"]
    url := manualChapterUrl "Bounded-spectral-theory" },
  { title := "Stone's theorem."
    desc := "Every strongly continuous one-parameter unitary group has the form U(t) = exp(itA) for a unique self-adjoint generator A."
    sections := #["§10.4"]
    url := manualChapterUrl "Stones-theorem" },
  { title := "Spacetime geometry."
    desc := "Causal structure, the Levi-Civita connection and geodesics on Lorentzian manifolds."
    sections := #["§10.5"]
    url := manualChapterUrl "Spacetime-and-geometry" }
]

/--
The grid of feature cards. The markup is this site's own (`verso-web-components`' `learnCard` has a fixed
"OPEN" label); the styles are in `Site.Theme.siteCss`. Each card is a single link.
-/
block_component +directive features where
  toHtml _ _ _ _ _ := do
    return {{
      <div class="feature-grid">
        {{ featureCards.map fun c => {{
          <a class="feature-card" href={{ c.url }}>
            <p class="feature-card-text"><strong>{{ c.title }}</strong>" "{{ c.desc }}</p>
            <div class="feature-card-footer">
              <div class="feature-card-tags">
                {{ c.sections.map fun (t : String) => ({{ <span class="feature-card-tag">{{ t }}</span> }} : Html) }}
              </div>
              <span class="feature-card-more">"Read more →"</span>
            </div>
          </a>
        }} }}
      </div>
    }}

end Site
