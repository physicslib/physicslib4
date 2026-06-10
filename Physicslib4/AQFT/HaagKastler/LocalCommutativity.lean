/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalAlgebras
import Physicslib4.Spacetime.Causality

/-!
# Axiom 3: Local Commutativity

This file formalises the blueprint declaration
`def:local-commutativity` (Axiom 3 of the "sharpened" Haag-Kastler
axioms, section 9.3 of the AQFT-in-Lean blueprint):

> If two Alexandrov-basis sets `𝐁₁`, `𝐁₂` are *completely spacelike*
> with respect to each other, then the local algebras `𝔘(𝐁₁)` and
> `𝔘(𝐁₂)` commute *inside the quasilocal algebra* `𝔘`.

## Main definitions

* `Physicslib4.AQFT.HaagKastler.LocalCommutativity`: a `Prop`-valued
  predicate on a `LocalNet` asserting Axiom 3.

## Modelling notes

* "Commuting in the quasilocal algebra" requires an ambient
  C*-algebra `𝔘` containing every `𝔘(B)` as a subalgebra. We
  package this as: the *existence* of a unital C*-algebra `Q`
  together with unital `*`-monomorphisms
  `ιB : 𝔘(B) →⋆ₐ[ℂ] Q`, valid for every Alexandrov-basis `B`, such
  that whenever `B₁` and `B₂` are completely spacelike, the images
  `ιB₁(𝔘(B₁))` and `ιB₂(𝔘(B₂))` commute pointwise in `Q`.

* The quasilocal algebra and its embeddings are fully constructed
  in Axiom 4 (`QuasilocalCompleteness`); here we only *assert* that
  the local-commutativity property holds for *some* such ambient
  data, which is the weakest mathematically faithful form of
  Axiom 3 that is statable in isolation.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4

/--
**Axiom 3 (Local Commutativity).** A local net `U` satisfies *local
commutativity* if there exists a unital ambient C*-algebra `Q`
(playing the role of the quasilocal algebra) together with unital
`*`-monomorphisms `ιB : U.algebra B →⋆ₐ[ℂ] Q` for every
Alexandrov-basis set `B`, such that whenever two basis sets
`B₁`, `B₂` are completely spacelike with respect to each other,
the images `ιB₁(U.algebra B₁)` and `ιB₂(U.algebra B₂)` commute
pointwise inside `Q`.

Blueprint reference: `def:local-commutativity`.
-/
def LocalCommutativity (U : LocalNet) : Prop :=
  ∃ (Q : Type) (_ : CStarAlgebra Q)
    (ι : ∀ B : Set StandardMinkowskiSpacetime.Carrier, StarAlgHom ℂ (U.algebra B) Q),
      (∀ B, IsAlexandrovBasisSet B → Function.Injective (ι B)) ∧
      ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄,
        IsAlexandrovBasisSet B₁ → IsAlexandrovBasisSet B₂ →
        Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
          standardMinkowskiTimeOrientation B₁ B₂ →
        ∀ (a : U.algebra B₁) (b : U.algebra B₂),
          Commute (ι B₁ a) (ι B₂ b)

end HaagKastler
end AQFT
end Physicslib4
