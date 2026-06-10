/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalAlgebras

/-!
# Axiom 2: Isotony

This file formalises the blueprint declaration `def:isotony`
(Axiom 2 of the "sharpened" Haag-Kastler axioms, section 9.3 of the
AQFT-in-Lean blueprint):

> If `𝐁₁ ⊆ 𝐁₂` (basis sets of the Alexandrov topology) then the
> inclusion induces a *unital `*`-monomorphism*
> `𝔘(𝐁₁) ↪ 𝔘(𝐁₂)` between the corresponding local algebras.

## Main definitions

* `Physicslib4.AQFT.HaagKastler.Isotony`: a `Prop`-valued predicate
  on a `LocalNet` asserting Axiom 2.

## Modelling notes

* The blueprint statement is the existence of an *injective unital
  `*`-homomorphism* for every inclusion of basis sets. Mathlib's
  `StarAlgHom ℂ A B` is unital by virtue of preserving the `Algebra
  ℂ`-structure (and in particular `1`), so requiring a
  `StarAlgHom` together with `Function.Injective` captures the
  blueprint's "unital `*`-monomorphism".

* We keep the basis-set restriction explicit: Axiom 2 only mentions
  *basis sets* of the Alexandrov topology, so the quantifier ranges
  over `B₁`, `B₂` satisfying `IsAlexandrovBasisSet`.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

/--
**Axiom 2 (Isotony).** A local net `U` satisfies *isotony* if every
inclusion `B₁ ⊆ B₂` between Alexandrov-basis sets of Minkowski
spacetime is implemented by a *unital `*`-monomorphism*
`𝔘(B₁) ↪ 𝔘(B₂)`.

Blueprint reference: `def:isotony`.
-/
def Isotony (U : LocalNet) : Prop :=
  ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄,
    IsAlexandrovBasisSet B₁ → IsAlexandrovBasisSet B₂ → B₁ ⊆ B₂ →
      ∃ φ : StarAlgHom ℂ (U.algebra B₁) (U.algebra B₂),
        Function.Injective φ

end HaagKastler
end AQFT
end Physicslib4
