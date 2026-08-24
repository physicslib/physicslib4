/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalAlgebras

/-!
# Axiom 2: Isotony

This file formalises the blueprint declaration `def:isotony`
(Axiom 2 of the "sharpened" Haag-Kastler axioms, section 10.3 of the
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

The family is *chosen data*, not an existence statement: the identity and
composition laws below are equations between the maps themselves, so there is
nothing to state unless the maps are fixed. An axiom of the form "for each
inclusion there exists some monomorphism" cannot express functoriality at all.

`map_self` and `map_comp` say exactly that `B ↦ 𝔘(B)` is a functor on the
inclusion order of basis sets. They are *required* rather than derived because
they constrain the net's chosen embeddings, not the spacetime. Their payoff is
that the local algebras form a genuine directed system, which is what gives the
quasilocal algebra (`def:quasilocal-algebra`) its algebra structure.
-/
structure Isotony (U : LocalNet) where
  /-- The chosen unital `*`-monomorphism implementing each inclusion of basis
  sets. This is data, which is what makes the two laws below statable. -/
  map : ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄,
    IsAlexandrovBasisSet B₁ → IsAlexandrovBasisSet B₂ → B₁ ⊆ B₂ →
      StarAlgHom ℂ (U.algebra B₁) (U.algebra B₂)
  /-- Each chosen embedding is injective, i.e. a monomorphism. -/
  injective : ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (h₁ : IsAlexandrovBasisSet B₁) (h₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂),
    Function.Injective (map h₁ h₂ h)
  /-- **Identity law.** The embedding along `B ⊆ B` is the identity. -/
  map_self : ∀ ⦃B : Set StandardMinkowskiSpacetime.Carrier⦄
    (h : IsAlexandrovBasisSet B),
    map h h (subset_refl B) = StarAlgHom.id ℂ (U.algebra B)
  /-- **Composition law.** The embedding along `B₁ ⊆ B₃` factors through any
  intermediate `B₂`. -/
  map_comp : ∀ ⦃B₁ B₂ B₃ : Set StandardMinkowskiSpacetime.Carrier⦄
    (h₁ : IsAlexandrovBasisSet B₁) (h₂ : IsAlexandrovBasisSet B₂)
    (h₃ : IsAlexandrovBasisSet B₃) (h₁₂ : B₁ ⊆ B₂) (h₂₃ : B₂ ⊆ B₃),
    (map h₂ h₃ h₂₃).comp (map h₁ h₂ h₁₂) = map h₁ h₃ (h₁₂.trans h₂₃)

/-- **Isotony is reflexive.** Every Alexandrov-basis set embeds into
itself via the identity unital `*`-monomorphism, independently of any
isotony hypothesis. -/
theorem exists_injective_self (U : LocalNet)
    {B : Set StandardMinkowskiSpacetime.Carrier} :
    ∃ φ : StarAlgHom ℂ (U.algebra B) (U.algebra B), Function.Injective φ :=
  ⟨StarAlgHom.id ℂ (U.algebra B), fun _ _ h => h⟩

/-- **Isotony is transitive.** Given inclusions `B₁ ⊆ B₂ ⊆ B₃` of
Alexandrov-basis sets, the isotony embeddings compose to a unital
`*`-monomorphism `𝔘(B₁) ↪ 𝔘(B₃)`. -/
theorem Isotony.trans {U : LocalNet} (h : Isotony U)
    ⦃B₁ B₂ B₃ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
    (hB₃ : IsAlexandrovBasisSet B₃) (h₁₂ : B₁ ⊆ B₂) (h₂₃ : B₂ ⊆ B₃) :
    ∃ φ : StarAlgHom ℂ (U.algebra B₁) (U.algebra B₃), Function.Injective φ := by
  refine ⟨(h.map hB₂ hB₃ h₂₃).comp (h.map hB₁ hB₂ h₁₂), ?_⟩
  simpa using (h.injective hB₂ hB₃ h₂₃).comp (h.injective hB₁ hB₂ h₁₂)

end HaagKastler
end AQFT
end Physicslib4
