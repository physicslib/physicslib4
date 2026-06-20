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
(`sections/sec10/10-4_haag-kastler-axioms-in-curved-spacetime`) of the AQFT-in-Lean
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
-/
def Isotony (U : LocalNet M) : Prop :=
  ∀ ⦃B₁ B₂ : Set M.Carrier⦄,
    M.IsBasisSet B₁ → M.IsBasisSet B₂ → B₁ ⊆ B₂ →
      ∃ φ : StarAlgHom ℂ (U.algebra B₁) (U.algebra B₂),
        Function.Injective φ

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
  obtain ⟨φ, hφ⟩ := h hB₁ hB₂ h₁₂
  obtain ⟨ψ, hψ⟩ := h hB₂ hB₃ h₂₃
  exact ⟨ψ.comp φ, fun a b hab => hφ (hψ (by simpa using hab))⟩

end HaagKastlerCurved
end AQFT
end Physicslib4
