/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalAlgebras
import Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra
import Physicslib4.Spacetime.Causality

/-!
# Axiom 3: Local Commutativity

This file formalises the blueprint declaration
`def:local-commutativity` (Axiom 3 of the "sharpened" Haag-Kastler
axioms, section 10.3 of the AQFT-in-Lean blueprint):

> If two Alexandrov-basis sets `𝐁₁`, `𝐁₂` are *completely spacelike*
> with respect to each other, then the local algebras `𝔘(𝐁₁)` and
> `𝔘(𝐁₂)` commute *inside the quasilocal algebra* `𝔘`.

## Main definitions

* `Physicslib4.AQFT.HaagKastler.LocalCommutativity`: a `Prop`-valued
  predicate on a `LocalNet` asserting Axiom 3.

## Modelling notes

* "Commuting in the quasilocal algebra" requires an ambient
  C*-algebra `𝔘` containing every `𝔘(B)` as a subalgebra. Rather
  than inlining that data, we quantify existentially over a
  `QuasilocalAlgebra U` — the bundled structure that packages an
  ambient C*-algebra together with the family of faithful unital
  `*`-monomorphisms `ιB : 𝔘(B) →⋆ₐ[ℂ] 𝔘`. Axiom 3 then asserts
  that, for *some* such ambient algebra, the images of any two
  completely-spacelike local algebras commute pointwise.

* The quasilocal algebra itself — including its density / completion
  property — is the subject of Axiom 4 (`QuasilocalCompleteness`);
  here we only *use* the structure to phrase commutativity. The two
  axioms can in principle share the same witness.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4

/--
**Axiom 3 (Local Commutativity).** A local net `U` satisfies *local
commutativity* if there exists a `QuasilocalAlgebra U` — i.e. an
ambient unital C*-algebra `Q.carrier` equipped with faithful unital
`*`-monomorphisms `Q.ι B : U.algebra B →⋆ₐ[ℂ] Q.carrier` for every
Alexandrov-basis set `B` — such that whenever two basis sets
`B₁`, `B₂` are completely spacelike with respect to each other,
the images `Q.ι B₁ (U.algebra B₁)` and `Q.ι B₂ (U.algebra B₂)`
commute pointwise inside `Q.carrier`.

Blueprint reference: `def:local-commutativity`.
-/
def LocalCommutativity (U : LocalNet) (i : Isotony U) : Prop :=
  ∃ Q : QuasilocalAlgebra U i,
    ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
      (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂),
      Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation B₁ B₂ →
      ∀ (a : U.algebra B₁) (b : U.algebra B₂),
        Commute (Q.ι hB₁ a) (Q.ι hB₂ b)

end HaagKastler
end AQFT
end Physicslib4
