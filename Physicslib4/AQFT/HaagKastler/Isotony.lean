/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalAlgebras

/-!
# Axiom 2: Isotony

This file formalises the blueprint declaration `def:isotony`
(Axiom 2 of the "sharpened" Haag-Kastler axioms, section 10.6 of the
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
Axiom 2 (isotony): a chosen unital *-monomorphism 𝔘(B₁) → 𝔘(B₂) for each inclusion of diamonds.

An observable measurable in a diamond B₁ is also measurable in any larger diamond B₂ ⊇ B₁. Since
the local algebras are abstract, this is expressed by a map i(B₁, B₂) : 𝔘(B₁) → 𝔘(B₂), which is a
unital *-homomorphism and injective. The maps are coherent: i(B, B) is the identity, and
i(B₂, B₃) ∘ i(B₁, B₂) = i(B₁, B₃) for B₁ ⊆ B₂ ⊆ B₃. In other words B ↦ 𝔘(B) is a functor on the
diamonds ordered by inclusion.

The family is data, not an existence statement. The identity and composition laws are equations
between the maps themselves, so they can only be stated once the maps are fixed. They are required
rather than derived, since nothing about the spacetime constrains which monomorphism a net chooses.
They make the local algebras a directed system, which is what makes their directed colimit, and so
the quasilocal algebra (`exists_quasilocalAlgebra`), an algebra.

Implementation note: a unital *-homomorphism is Mathlib's `StarAlgHom`, which preserves the unit
because it is an algebra homomorphism.

Blueprint: def:isotony
-/
structure Isotony (U : LocalNet) where
  /-- The embedding i(B₁, B₂) : 𝔘(B₁) → 𝔘(B₂) of a diamond B₁ into a diamond B₂ ⊇ B₁. -/
  map : ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄,
    IsAlexandrovBasisSet B₁ → IsAlexandrovBasisSet B₂ → B₁ ⊆ B₂ →
      StarAlgHom ℂ (U.algebra B₁) (U.algebra B₂)
  /-- Each embedding is injective. -/
  injective : ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (h₁ : IsAlexandrovBasisSet B₁) (h₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂),
    Function.Injective (map h₁ h₂ h)
  /-- The identity law: the embedding of a diamond in itself is the identity. -/
  map_self : ∀ ⦃B : Set StandardMinkowskiSpacetime.Carrier⦄
    (h : IsAlexandrovBasisSet B),
    map h h (subset_refl B) = StarAlgHom.id ℂ (U.algebra B)
  /-- The composition law: for B₁ ⊆ B₂ ⊆ B₃, the embedding of B₁ in B₃ is the composite of the
  embeddings of B₁ in B₂ and of B₂ in B₃. -/
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
