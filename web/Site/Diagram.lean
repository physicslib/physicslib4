import Verso.Output.Html

/-!
# The spacetime diagram on the landing page

A 1+1-dimensional spacetime diagram (time up, space to the right, light rays at 45°) of the setting of
Axiom 3, local commutativity: a causal diamond `B` containing two smaller, spacelike-separated diamonds
`B₁` and `B₂`. The dashed lines are the light cones of `B₁`: its causal future and past, which `B₂`
avoids. Colours come from CSS classes in `Site.Theme.siteCss`, so the diagram follows light and dark
mode.
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

end Site
