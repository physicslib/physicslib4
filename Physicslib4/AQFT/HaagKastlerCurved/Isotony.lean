/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.LocalAlgebras

/-!
# Axiom 2 (Isotony), curved spacetime

This file formalises the blueprint declaration
`def:isotony-in-curved-spacetime` (Axiom 2 of the Haag-Kastler
axioms on a Lorentzian spacetime, Chapter 10
(`sections/sec10/haag-kastler-axioms-in-curved-spacetime`) of the AQFT-in-Lean
blueprint):

> If `𝐁₁ ⊆ 𝐁₂` (Alexandrov-basis sets) then the inclusion induces a
> *unital `*`-monomorphism* `i : 𝔘(𝐁₁) ↪ 𝔘(𝐁₂)`.

## Main definitions

* `Physicslib4.AQFT.HaagKastlerCurved.Isotony`: a `Prop`-valued
  predicate on a `LocalNet M` asserting Axiom 2.

This is the verbatim curved analogue of the Minkowski `Isotony`
(`def:isotony`); only the carrier and basis predicate change to the
abstract interface `M`.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastlerCurved

variable {M : LorentzianSpacetime}

/--
Axiom 2 in curved spacetime (isotony): a chosen unital *-monomorphism 𝔘(B₁) → 𝔘(B₂) for each
inclusion of basis sets.

An observable measurable in a basis set B₁ is also measurable in any larger basis set B₂ ⊇ B₁.
Since the local algebras are abstract, this is expressed by a map i(B₁, B₂) : 𝔘(B₁) → 𝔘(B₂), which
is a unital *-homomorphism and injective. The maps are coherent: i(B, B) is the identity, and
i(B₂, B₃) ∘ i(B₁, B₂) = i(B₁, B₃) for B₁ ⊆ B₂ ⊆ B₃. In other words B ↦ 𝔘(B) is a functor on the
basis sets ordered by inclusion. The hypothesis is the non-strict inclusion B₁ ⊆ B₂; the case
B₁ = B₂ is what makes the identity law expressible.

The family is data, not an existence statement, exactly as in Minkowski spacetime: the identity
and composition laws are equations between the maps themselves, so they can only be stated once
the maps are fixed. They are required rather than derived, since nothing about the spacetime
constrains which monomorphism a net chooses. Curved spacetime has no quasilocal algebra, so
statements about nested regions B₁ ⊆ B₂ ⊆ B are made inside a common containing algebra 𝔘(B); the
composition law makes the embedding of 𝔘(B₁) in 𝔘(B) factor through 𝔘(B₂) for every net. Axiom 3
uses this same family.

Implementation note: a unital *-homomorphism is Mathlib's `StarAlgHom`, which preserves the unit
because it is an algebra homomorphism.

Blueprint: def:isotony-in-curved-spacetime
-/
structure Isotony (U : LocalNet M) where
  /-- The embedding i(B₁, B₂) : 𝔘(B₁) → 𝔘(B₂) of a basis set B₁ into a basis set B₂ ⊇ B₁. -/
  map : ∀ ⦃B₁ B₂ : Set M.Carrier⦄,
    M.IsBasisSet B₁ → M.IsBasisSet B₂ → B₁ ⊆ B₂ →
      StarAlgHom ℂ (U.algebra B₁) (U.algebra B₂)
  /-- Each embedding is injective. -/
  injective : ∀ ⦃B₁ B₂ : Set M.Carrier⦄
    (h₁ : M.IsBasisSet B₁) (h₂ : M.IsBasisSet B₂) (h : B₁ ⊆ B₂),
    Function.Injective (map h₁ h₂ h)
  /-- The identity law: the embedding of a basis set in itself is the identity. -/
  map_self : ∀ ⦃B : Set M.Carrier⦄ (h : M.IsBasisSet B),
    map h h (subset_refl B) = StarAlgHom.id ℂ (U.algebra B)
  /-- The composition law: for B₁ ⊆ B₂ ⊆ B₃, the embedding of B₁ in B₃ is the composite of the
  embeddings of B₁ in B₂ and of B₂ in B₃. -/
  map_comp : ∀ ⦃B₁ B₂ B₃ : Set M.Carrier⦄
    (h₁ : M.IsBasisSet B₁) (h₂ : M.IsBasisSet B₂) (h₃ : M.IsBasisSet B₃)
    (h₁₂ : B₁ ⊆ B₂) (h₂₃ : B₂ ⊆ B₃),
    (map h₂ h₃ h₂₃).comp (map h₁ h₂ h₁₂) = map h₁ h₃ (h₁₂.trans h₂₃)

/-- **Isotony is reflexive.** Every Alexandrov-basis set embeds into
itself via the identity unital `*`-monomorphism, independently of any
isotony hypothesis. -/
theorem exists_injective_self (U : LocalNet M) {B : Set M.Carrier} :
    ∃ φ : StarAlgHom ℂ (U.algebra B) (U.algebra B), Function.Injective φ :=
  ⟨StarAlgHom.id ℂ (U.algebra B), fun _ _ h => h⟩

/-- **Isotony is transitive.** Given inclusions `B₁ ⊆ B₂ ⊆ B₃` of
Alexandrov-basis sets, the isotony embeddings compose to a unital
`*`-monomorphism `𝔘(B₁) ↪ 𝔘(B₃)`. -/
theorem Isotony.trans {U : LocalNet M} (h : Isotony U)
    ⦃B₁ B₂ B₃ : Set M.Carrier⦄
    (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂) (hB₃ : M.IsBasisSet B₃)
    (h₁₂ : B₁ ⊆ B₂) (h₂₃ : B₂ ⊆ B₃) :
    ∃ φ : StarAlgHom ℂ (U.algebra B₁) (U.algebra B₃), Function.Injective φ := by
  refine ⟨(h.map hB₂ hB₃ h₂₃).comp (h.map hB₁ hB₂ h₁₂), ?_⟩
  simpa using (h.injective hB₂ hB₃ h₂₃).comp (h.injective hB₁ hB₂ h₁₂)

end HaagKastlerCurved
end AQFT
end Physicslib4
