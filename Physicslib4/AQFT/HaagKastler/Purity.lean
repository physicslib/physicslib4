/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.Net
import Physicslib4.GNS.RadonNikodym
import Physicslib4.GNS.ExtremeState

/-!
# Purity of states on the quasilocal algebra

The canonical quasilocal algebra `𝔘` of a Minkowski Haag-Kastler net is a unital
C*-algebra, so the abstract characterizations of purity apply to it. This file
registers them for `𝔘`:

* a state on `𝔘` is pure iff it is an extreme point of the state space;
* a state on `𝔘` is pure iff its GNS representation is irreducible.

Unlike the curved setting, Minkowski spacetime has a single global quasilocal
algebra `𝔘`, so these are statements about its global state space - the natural
home for the vacuum and other distinguished states.

## Main results

* `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.pure_iff_extreme`
* `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.exists_gns_pure_iff_irreducible`
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler
namespace HaagKastlerNet

open Physicslib4.GNS
open scoped InnerProductSpace

variable (N : HaagKastlerNet)

/-- **Pure ⟺ extreme point for the quasilocal algebra.** A state `ω` on the
canonical quasilocal algebra `𝔘` of a Minkowski Haag-Kastler net is pure if and
only if it is an extreme point of the state space of `𝔘`. This is the abstract
equivalence `isPure_iff_isExtremePoint` applied to the C*-algebra `𝔘`. -/
theorem pure_iff_extreme (ω : State N.quasilocal.carrier) :
    IsPure ω ↔ ω.IsExtremePoint :=
  isPure_iff_isExtremePoint ω

/-- **Pure ⟺ irreducible GNS representation for the quasilocal algebra.** For a
state `ω` on the quasilocal algebra `𝔘`, there is a GNS triple `(H, π, Ω)`
reproducing `ω` in which `ω` is pure if and only if the representation `π` is
irreducible (its commutant is trivial). This combines the GNS construction with
the abstract `isPure_iff_isIrreducible`. -/
theorem exists_gns_pure_iff_irreducible (ω : State N.quasilocal.carrier) :
    ∃ (H : Type)
      (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        IsCyclicVector π Ω ∧
        (∀ a : N.quasilocal.carrier, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (IsPure ω ↔ IsIrreducible π) := by
  obtain ⟨H, i1, i2, i3, π, Ω, hcyc, hrep, _⟩ := gns_construction ω
  exact ⟨H, i1, i2, i3, π, Ω, hcyc, hrep, isPure_iff_isIrreducible hcyc hrep⟩

end HaagKastlerNet
end HaagKastler
end AQFT
end Physicslib4
