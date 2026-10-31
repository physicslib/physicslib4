import Verso.Output.Html

/-!
# Spacetime diagrams

`diamondDiagram` is the diagram on the landing page, also used in the tutorial; `conesDiagram` is
used in the tutorial only. Both are 1+1-dimensional (time up, space to the right, light rays at 45°).

The landing-page diagram shows the setting of Axiom 3, local commutativity: a causal diamond `B`
containing two smaller, spacelike-separated diamonds `B₁` and `B₂`. The dashed lines are the light
cones of `B₁`: its causal future and past, which `B₂` avoids. Colours come from CSS classes in
`Site.Theme.siteCss`, so the diagrams follow light and dark mode. The repository's `README.md` cannot use
inline SVG or these classes, so it shows standalone copies of `diamondDiagram`,
`static_files/axiom3-diagram-light.svg` and `static_files/axiom3-diagram-dark.svg`; a change to the
diagram is made in those files too.
-/

open Verso Output Html

namespace Site

/-- The causal-diamond diagram, as inline SVG. -/
def diamondDiagram : Html := {{
  <svg class="st-diagram" viewBox="0 0 400 420" role="img"
      aria-labelledby="st-diagram-title st-diagram-desc" xmlns="http://www.w3.org/2000/svg">
    <title id="st-diagram-title">"Two spacelike-separated diamonds inside a causal diamond"</title>
    <desc id="st-diagram-desc">"A large causal diamond B contains two smaller diamonds B1 and B2 side by side. Dashed light-cone lines at 45 degrees from B1 bound its causal future and past; B2 lies outside them, so B1 and B2 are spacelike separated."</desc>
    <defs>
      <marker id="st-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7"
          orient="auto-start-reverse">
        <path class="st-arrowhead" d="M 0 0 L 10 5 L 0 10 z" />
      </marker>
    </defs>
    <polygon class="st-big" points="200,30 370,200 200,370 30,200" />
    <line class="st-cone" x1="130" y1="245" x2="272.5" y2="102.5" />
    <line class="st-cone" x1="130" y1="245" x2="57.5" y2="172.5" />
    <line class="st-cone" x1="130" y1="155" x2="272.5" y2="297.5" />
    <line class="st-cone" x1="130" y1="155" x2="57.5" y2="227.5" />
    <polygon class="st-small" points="130,155 175,200 130,245 85,200" />
    <polygon class="st-small" points="270,155 315,200 270,245 225,200" />
    <text class="st-label" x="200" y="70" text-anchor="middle">"B"</text>
    <text class="st-label st-label-small" x="130" y="207" text-anchor="middle">"B₁"</text>
    <text class="st-label st-label-small" x="270" y="207" text-anchor="middle">"B₂"</text>
    <line class="st-axis" x1="20" y1="405" x2="20" y2="345" marker-end="url(#st-arrow)" />
    <line class="st-axis" x1="20" y1="405" x2="80" y2="405" marker-end="url(#st-arrow)" />
    <text class="st-axis-label" x="28" y="352">"t"</text>
    <text class="st-axis-label" x="76" y="398">"x"</text>
  </svg>
}}

/--
The causal diamond `I⁺(p) ∩ I⁻(q)`, as inline SVG: the dashed lines bound the chronological future of
`p` and the chronological past of `q`, and the shaded region is their intersection. Used in the
tutorial.
-/
def conesDiagram : Html := {{
  <svg class="st-diagram" viewBox="0 0 400 420" role="img"
      aria-labelledby="st-cones-title st-cones-desc" xmlns="http://www.w3.org/2000/svg">
    <title id="st-cones-title">"A causal diamond as the intersection of two light cones"</title>
    <desc id="st-cones-desc">"A point p near the bottom and a point q near the top. Dashed lines at 45 degrees bound the chronological future of p, opening upwards, and the chronological past of q, opening downwards. Their intersection, shaded, is the diamond B."</desc>
    <defs>
      <marker id="st-cones-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7"
          orient="auto-start-reverse">
        <path class="st-arrowhead" d="M 0 0 L 10 5 L 0 10 z" />
      </marker>
    </defs>
    <line class="st-cone" x1="200" y1="340" x2="20" y2="160" />
    <line class="st-cone" x1="200" y1="340" x2="380" y2="160" />
    <line class="st-cone" x1="200" y1="80" x2="20" y2="260" />
    <line class="st-cone" x1="200" y1="80" x2="380" y2="260" />
    <polygon class="st-small" points="200,340 330,210 200,80 70,210" />
    <circle class="st-arrowhead" cx="200" cy="340" r="4" />
    <circle class="st-arrowhead" cx="200" cy="80" r="4" />
    <text class="st-label st-label-small" x="200" y="366" text-anchor="middle">"p"</text>
    <text class="st-label st-label-small" x="200" y="66" text-anchor="middle">"q"</text>
    <text class="st-label" x="200" y="217" text-anchor="middle">"B"</text>
    <text class="st-label st-label-small" x="335" y="135" text-anchor="middle">"I⁺(p)"</text>
    <text class="st-label st-label-small" x="335" y="300" text-anchor="middle">"I⁻(q)"</text>
    <line class="st-axis" x1="20" y1="405" x2="20" y2="345" marker-end="url(#st-cones-arrow)" />
    <line class="st-axis" x1="20" y1="405" x2="80" y2="405" marker-end="url(#st-cones-arrow)" />
    <text class="st-axis-label" x="28" y="352">"t"</text>
    <text class="st-axis-label" x="76" y="398">"x"</text>
  </svg>
}}

end Site
