/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.Net
import Physicslib4.GNS.Construction

/-!
# Einstein causality (microcausality) in a representation

Axiom 3 (local commutativity) asserts that the local algebras of two completely
spacelike-separated regions commute inside the quasilocal algebra. This file
pushes that algebraic statement into Hilbert space: under *any* `*`-representation
`π` of the quasilocal algebra - in particular the GNS representation of any state -
the local observables of spacelike-separated regions commute as bounded operators.

This is the operator form of Einstein causality: spacelike-separated measurements
do not interfere.

## Main results

* `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.einstein_causality`: in any
  `*`-representation `π`, `π(ι_{B₁} a)` and `π(ι_{B₂} b)` commute when `B₁, B₂`
  are completely spacelike.
* `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.exists_gns_einstein_causality`: the
  GNS specialization - for any state there is a GNS triple in which spacelike
  local observables commute.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler
namespace HaagKastlerNet

open Physicslib4.GNS
open scoped InnerProductSpace

variable (N : HaagKastlerNet)

/-- **Einstein causality in a representation.** For any `*`-representation `π` of
the quasilocal algebra witnessing local commutativity, the images of the local
observables of two completely spacelike-separated basis regions commute as
bounded operators. This is `Commute.map` applied to Axiom 3
(`commute_ι_of_spacelike`). -/
theorem einstein_causality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
    (hs : Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂)
    (a : N.U.algebra B₁) (b : N.U.algebra B₂) :
    Commute (π (N.commAlgebra.ι B₁ a)) (π (N.commAlgebra.ι B₂ b)) :=
  (N.commute_ι_of_spacelike hB₁ hB₂ hs a b).map π

/-- **Einstein causality on a GNS Hilbert space.** For any state `ω` on the
quasilocal algebra there is a GNS triple `(H, π, Ω)` reproducing `ω` in which the
local observables of completely spacelike-separated regions commute as operators
on `H`. -/
theorem exists_gns_einstein_causality (ω : State N.commAlgebra.carrier) :
    ∃ (H : Type)
      (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        IsCyclicVector π Ω ∧
        (∀ a : N.commAlgebra.carrier, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄,
          IsAlexandrovBasisSet B₁ → IsAlexandrovBasisSet B₂ →
          Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
            standardMinkowskiTimeOrientation B₁ B₂ →
          ∀ (a : N.U.algebra B₁) (b : N.U.algebra B₂),
            Commute (π (N.commAlgebra.ι B₁ a)) (π (N.commAlgebra.ι B₂ b)) := by
  obtain ⟨H, i1, i2, i3, π, Ω, hcyc, hrep, _⟩ := gns_construction ω
  exact ⟨H, i1, i2, i3, π, Ω, hcyc, hrep,
    fun B₁ B₂ hB₁ hB₂ hs a b => N.einstein_causality π hB₁ hB₂ hs a b⟩

end HaagKastlerNet
end HaagKastler
end AQFT
end Physicslib4
