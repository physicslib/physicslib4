/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.Net
import Physicslib4.GNS.Construction

/-!
# Einstein causality in curved spacetime

This is the curved-spacetime counterpart of Minkowski Einstein causality. There is
no quasilocal algebra in curved spacetime, so local commutativity is phrased
inside a common containing basis algebra `𝔘(B)`: if `B₁, B₂` are completely
spacelike and both contained in `B`, then the images of `𝔘(B₁)` and `𝔘(B₂)` in
`𝔘(B)` commute. This file pushes that into Hilbert space: under any
`*`-representation `π` of the containing algebra `𝔘(B)` - in particular the GNS
representation of any state on `𝔘(B)` - the spacelike-separated local observables
commute as bounded operators.

## Main results

* `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.einstein_causality`: causality
  in any representation of the containing algebra.
* `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_einstein_causality`:
  the GNS specialization.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastlerCurved
namespace HaagKastlerNet

open Physicslib4.GNS
open scoped InnerProductSpace

variable {M : LorentzianSpacetime} (N : HaagKastlerNet M)

/-- **Einstein causality in a representation (curved spacetime).** For any
`*`-representation `π` of a containing basis algebra `𝔘(B)`, the images of the
local observables of two completely spacelike-separated subregions `B₁, B₂ ⊆ B`
commute as bounded operators. This is `Commute.map` applied to the curved local
commutativity `commute_of_spacelike`. -/
theorem einstein_causality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {B : Set M.Carrier} (hB : M.IsBasisSet B)
    (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (hs : M.IsCompletelySpacelike B₁ B₂) (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B)
    (a : N.algebra B₁) (b : N.algebra B₂) :
    Commute (π (N.commIsotony hB₁ hB h₁ a)) (π (N.commIsotony hB₂ hB h₂ b)) :=
  (N.commute_of_spacelike hB₁ hB₂ hB hs h₁ h₂ a b).map π

/-- **Einstein causality on a GNS Hilbert space (curved spacetime).** For any
state `ω` on a containing basis algebra `𝔘(B)` there is a GNS triple `(H, π, Ω)`
reproducing `ω` in which the local observables of completely spacelike-separated
subregions commute as operators on `H`. -/
theorem exists_gns_einstein_causality {B : Set M.Carrier} (hB : M.IsBasisSet B)
    (ω : State (N.algebra B)) :
    ∃ (H : Type)
      (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        IsCyclicVector π Ω ∧
        (∀ a : N.algebra B, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        ∀ ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂),
          M.IsCompletelySpacelike B₁ B₂ → ∀ (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B)
            (a : N.algebra B₁) (b : N.algebra B₂),
            Commute (π (N.commIsotony hB₁ hB h₁ a)) (π (N.commIsotony hB₂ hB h₂ b)) := by
  obtain ⟨H, i1, i2, i3, π, Ω, hcyc, hrep, _⟩ := gns_construction ω
  exact ⟨H, i1, i2, i3, π, Ω, hcyc, hrep,
    fun B₁ B₂ hB₁ hB₂ hs h₁ h₂ a b => N.einstein_causality hB π hB₁ hB₂ hs h₁ h₂ a b⟩

end HaagKastlerNet
end HaagKastlerCurved
end AQFT
end Physicslib4
