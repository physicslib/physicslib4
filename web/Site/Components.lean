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

/-- The feature cards, one per area of the formalisation, linking to the blueprint guide pages. -/
def featureCards : Array FeatureCard := #[
  { title := "Haag–Kastler axioms in Minkowski spacetime."
    desc := "Local C*-algebras on causal diamonds, isotony, local commutativity, Lorentz covariance, and the quasilocal algebra."
    sections := #["§10.6"]
    url := sectionUrl "sec10-6-haag-kastler" },
  { title := "The axioms in curved spacetime."
    desc := "The same axioms on a Lorentzian spacetime, with isometric covariance and general covariance across backgrounds."
    sections := #["§10.7", "§10.8"]
    url := sectionUrl "sec10-7-curved" },
  { title := "The GNS construction."
    desc := "From a state on a C*-algebra to a cyclic Hilbert-space representation, unique up to unitary equivalence."
    sections := #["§10.1"]
    url := sectionUrl "sec10-1-gns" },
  { title := "Spectral theorems."
    desc := "Projection-valued measures for bounded and for unbounded self-adjoint operators, with their functional calculi."
    sections := #["§10.2", "§10.3"]
    url := sectionUrl "sec10-2-spectral" },
  { title := "Stone's theorem."
    desc := "Every strongly continuous one-parameter unitary group has the form U(t) = exp(itA) for a unique self-adjoint generator A."
    sections := #["§10.4"]
    url := sectionUrl "sec10-4-stone" },
  { title := "Spacetime geometry."
    desc := "Causal structure, the Levi-Civita connection and geodesics on Lorentzian manifolds."
    sections := #["§10.5"]
    url := sectionUrl "sec10-5-spacetime" }
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
