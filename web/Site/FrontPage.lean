import VersoBlog
import Site.Components
import Physicslib4.Spacetime.LorentzCausality
import Physicslib4.AQFT.HaagKastler.Net

open Verso Genre Blog
open Site

#doc (Page) "physicslib4" =>

%%%
showInNav := false
htmlId := some "frontpage"
%%%

:::hero
A Lean 4 formalisation of axiomatic physical theories.
:::

```leanInit physicslib4
```

```lean physicslib4 -show
open Physicslib4 Spacetime AQFT.HaagKastler

/-- Minkowski space. -/
local notation "𝕄" => StandardMinkowskiSpacetime.Carrier

/-- Causal precedence in Minkowski space, for the standard time orientation. -/
local notation:50 p:51 " ≺ " q:51 =>
  CausallyPrecedes StandardMinkowskiSpacetime standardMinkowskiTimeOrientation p q
```

::::::centeredSection "example" "Checked by Lean"

A Poincaré transformation maps causal curves to causal curves, so it cannot change which events can
influence which. In the library this is a theorem, proved in the first tab. The second tab proves
that a Haag–Kastler net exists, so the axioms are consistent. (Hover over a name to see its
type.)

:::::gallery

Lorentz invariance

```lean physicslib4
/-- Causal precedence is invariant under
the Poincaré group. -/
example (g : InhomogeneousLorentzGroup) (p q : 𝕄) :
    g • p ≺ g • q ↔ p ≺ q :=
  causallyPrecedes_smul_iff g p q
```

With 𝕄 for Minkowski space and ≺ for causal precedence: the statement of `causallyPrecedes_smul_iff`.

manual/Spacetime-and-geometry/

Consistent axioms

```lean physicslib4
/-- The axioms have a model: the net that
assigns the trivial algebra to every region. -/
example : Nonempty HaagKastlerNet.{0} :=
  ⟨trivialHaagKastlerNet⟩
```

A Haag–Kastler net exists, so the axioms are consistent.

manual/Haag-Kastler-axioms-in-Minkowski-spacetime/

:::::

::::::

::::::centeredSection "contents" "What is currently formalised"

:::features
:::

::::::
