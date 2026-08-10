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
**Axiom 2 (Isotony), curved spacetime.** A local net `U` on a
Lorentzian spacetime `M` satisfies *isotony* if every inclusion
`B₁ ⊆ B₂` between Alexandrov-basis sets is implemented by a unital
`*`-monomorphism `𝔘(B₁) ↪ 𝔘(B₂)`.

Blueprint reference: `def:isotony-in-curved-spacetime`.

The family is *chosen data*, not an existence statement: the identity and
composition laws below are equations between the maps themselves, so there is
nothing to state unless the maps are fixed. An axiom of the form "for each
inclusion there exists some monomorphism" cannot express functoriality at all.

Conditions `map_self` and `map_comp` say exactly that `B ↦ 𝔘(B)` is a functor on
the inclusion order of basis sets. They are *required* rather than derived
because they constrain the net's chosen embeddings, not the spacetime: no
geometric fact about Alexandrov diamonds determines which monomorphism a net
picks for a given inclusion.
-/
structure Isotony (U : LocalNet M) where
  /-- The chosen unital `*`-monomorphism implementing each inclusion of basis
  sets. This is data, which is what makes the two laws below statable. -/
  map : ∀ ⦃B₁ B₂ : Set M.Carrier⦄,
    M.IsBasisSet B₁ → M.IsBasisSet B₂ → B₁ ⊆ B₂ →
      StarAlgHom ℂ (U.algebra B₁) (U.algebra B₂)
  /-- Each chosen embedding is injective, i.e. a monomorphism. -/
  injective : ∀ ⦃B₁ B₂ : Set M.Carrier⦄
    (h₁ : M.IsBasisSet B₁) (h₂ : M.IsBasisSet B₂) (h : B₁ ⊆ B₂),
    Function.Injective (map h₁ h₂ h)
  /-- **Identity law.** The embedding along `B ⊆ B` is the identity. -/
  map_self : ∀ ⦃B : Set M.Carrier⦄ (h : M.IsBasisSet B),
    map h h (subset_refl B) = StarAlgHom.id ℂ (U.algebra B)
  /-- **Composition law.** The embedding along `B₁ ⊆ B₃` factors through any
  intermediate `B₂`. This is what lets a three-fold inclusion be factored
  without carrying coherence as a separate hypothesis at each use site. -/
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
