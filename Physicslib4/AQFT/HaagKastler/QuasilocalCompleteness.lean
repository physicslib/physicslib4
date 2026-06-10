/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalAlgebras

/-!
# Axiom 4: Quasilocal Completeness

This file formalises the blueprint declaration
`def:quasilocal-completeness` (Axiom 4 of the "sharpened"
Haag-Kastler axioms, section 9.3 of the AQFT-in-Lean blueprint):

> All "observables" are *quasilocal observables*: the union of the
> images of all local algebras `𝔘(𝐁)` is dense in (and thus
> completes to) the *quasilocal algebra* `𝔘`, which is the
> C*-algebra that "contains all observables of interest".

## Main definitions

* `Physicslib4.AQFT.HaagKastler.QuasilocalCompleteness`: a
  `Prop`-valued predicate on a `LocalNet` asserting Axiom 4.

## Modelling notes

* Following the blueprint, the quasilocal algebra `𝔘` is the
  C*-algebraic *completion* of the set-theoretic union of all
  `𝔘(B)`. We encode this by requiring the existence of a unital
  C*-algebra `Q`, together with unital `*`-monomorphisms
  `ιB : 𝔘(B) →⋆ₐ[ℂ] Q` for every Alexandrov-basis set `B`, such
  that the union of their images is *dense* in `Q`.

* The density condition captures "all observables are quasilocal":
  every element of `Q` is the norm-limit of a sequence (or net) of
  elements of `⋃_B ιB(𝔘(B))`.

* This is closely related to (and refines) the existence statement
  used in `LocalCommutativity`; the two predicates can in principle
  be witnessed by the *same* ambient algebra `Q`, but we keep them
  separate so each axiom can be stated and tested in isolation.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4

/--
**Axiom 4 (Quasilocal Completeness).** A local net `U` satisfies
*quasilocal completeness* if there exists a unital ambient
C*-algebra `Q` — the *quasilocal algebra* — together with unital
`*`-monomorphisms `ιB : U.algebra B →⋆ₐ[ℂ] Q` for every
Alexandrov-basis set `B`, such that the union
`⋃ B, Set.range (ιB)` is *dense* in `Q`.

This expresses the blueprint's "all observables are quasilocal
observables": every element of `Q` is the norm-limit of a sequence
of elements of `⋃_B 𝔘(B)`.

Blueprint reference: `def:quasilocal-completeness`.
-/
def QuasilocalCompleteness (U : LocalNet) : Prop :=
  ∃ (Q : Type) (_ : CStarAlgebra Q)
    (ι : ∀ B : Set StandardMinkowskiSpacetime.Carrier,
           StarAlgHom ℂ (U.algebra B) Q),
      (∀ B, IsAlexandrovBasisSet B → Function.Injective (ι B)) ∧
      Dense (⋃ (B : Set StandardMinkowskiSpacetime.Carrier)
                (_ : IsAlexandrovBasisSet B),
                Set.range (ι B))

end HaagKastler
end AQFT
end Physicslib4
