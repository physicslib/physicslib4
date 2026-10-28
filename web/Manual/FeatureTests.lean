import VersoManual
import Book.Meta
import Physicslib4.AQFT.HaagKastler.Net
import Physicslib4.AQFT.HaagKastler.EinsteinCausality
import Physicslib4.GNS.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

#doc (Manual) "Feature tests" =>

%%%
tag := "feature-tests"
draft := true
%%%

A draft-only chapter, built with `generate-manual --draft`. It shows the two ways the manual displays
a declaration, and links to the API docs, as an example of the markup.

# Structures: `{docstring}`

A structure with its docstring, constructor and fields:

{docstring Physicslib4.AQFT.HaagKastler.LocalNet}

A structure whose fields have longer types:

{docstring Physicslib4.AQFT.HaagKastler.HaagKastlerNet}

A structure that extends another. The fields inherited from the parent (here those of a
continuous linear map) are hidden until the reader ticks the parent under "Extends":

{docstring Physicslib4.GNS.State}

Without the constructor and the fields:

{docstring Physicslib4.GNS.State +hideFields +hideStructureConstructor}

# Theorems: `#check`

`#check` of a theorem shows its signature. Verso prints Lean messages 120 columns wide whatever
`format.width` says; the stylesheet wraps the longer lines at the width of the text column.

```lean (name := checkEinstein)
open Physicslib4 AQFT HaagKastler in
#check HaagKastlerNet.einstein_causality
```

```leanOutput checkEinstein
Physicslib4.AQFT.HaagKastler.HaagKastlerNet.einstein_causality.{u, u_1} (N : HaagKastlerNet) {H : Type u_1}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : N.quasilocal.carrier →⋆ₐ[ℂ] H →L[ℂ] H)
  ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄ (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
  (hs : StandardMinkowskiSpacetime.IsCompletelySpacelike standardMinkowskiTimeOrientation B₁ B₂) (a : N.U.algebra B₁)
  (b : N.U.algebra B₂) : Commute (π ((N.quasilocal.ι hB₁) a)) (π ((N.quasilocal.ι hB₂) b))
```

# Links to the API docs

{apiDocs Physicslib4.AQFT.HaagKastler.LocalNet}[], or with text:
{apiDocs Physicslib4.AQFT.HaagKastler.HaagKastlerNet.einstein_causality}[Einstein causality],
and a Mathlib declaration: {apiDocs CStarAlgebra}[].
