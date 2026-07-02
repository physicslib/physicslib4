/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.Net
import Physicslib4.GNS.RadonNikodym
import Physicslib4.GNS.ExtremeState

/-!
# Purity of states on curved local algebras

The local algebra `𝔘(B)` of a Haag-Kastler net in curved spacetime is a unital
C*-algebra, so the abstract characterizations of purity of a state apply to it
verbatim. This file registers them for `𝔘(B)`:

* a state on `𝔘(B)` is pure iff it is an extreme point of the state space;
* a state on `𝔘(B)` is pure iff its GNS representation is irreducible.

There is no quasilocal algebra in curved spacetime, so these statements are
phrased per region, on each local algebra `𝔘(B)` separately - which is exactly
the right generality, since each `𝔘(B)` is itself a C*-algebra with its own state
space and GNS representations.

## Main results

* `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.pure_iff_extreme`
* `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.exists_gns_pure_iff_irreducible`
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastlerCurved
namespace HaagKastlerNet

open Physicslib4.GNS
open scoped InnerProductSpace

variable {M : LorentzianSpacetime} (N : HaagKastlerNet M)

/-- **Pure ⟺ extreme point for a curved local algebra.** A state `ω` on the local
algebra `𝔘(B)` of a curved Haag-Kastler net is pure if and only if it is an
extreme point of the state space of `𝔘(B)`. This is the abstract equivalence
`isPure_iff_isExtremePoint` applied to the C*-algebra `𝔘(B)`. -/
theorem pure_iff_extreme {B : Set M.Carrier} (ω : State (N.algebra B)) :
    IsPure ω ↔ ω.IsExtremePoint :=
  isPure_iff_isExtremePoint ω

/-- **Pure ⟺ irreducible GNS representation for a curved local algebra.** For a
state `ω` on the local algebra `𝔘(B)`, there is a GNS triple `(H, π, Ω)`
reproducing `ω` in which `ω` is pure if and only if the representation `π` is
irreducible (its commutant is trivial). This combines the GNS construction with
the abstract `isPure_iff_isIrreducible`. -/
theorem exists_gns_pure_iff_irreducible {B : Set M.Carrier} (ω : State (N.algebra B)) :
    ∃ (H : Type)
      (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        IsCyclicVector π Ω ∧
        (∀ a : N.algebra B, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (IsPure ω ↔ IsIrreducible π) := by
  obtain ⟨H, i1, i2, i3, π, Ω, hcyc, hrep, _⟩ := gns_construction ω
  exact ⟨H, i1, i2, i3, π, Ω, hcyc, hrep, isPure_iff_isIrreducible hcyc hrep⟩

/-- **The GNS representation of a pure state on a curved local algebra is a factor.**
For a pure state `ω` on `𝔘(B)` there is a cyclic GNS triple reproducing `ω` whose
generated von Neumann algebra `π(𝔘(B))''` has trivial center (its center equals the
scalars). The abstract `GNS.exists_gns_factor_of_isPure` at the C*-algebra `𝔘(B)`. -/
theorem exists_gns_factor_of_isPure {B : Set M.Carrier} {ω : State (N.algebra B)}
    (hpure : IsPure ω) :
    ∃ (H : Type)
      (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        IsCyclicVector π Ω ∧
        (∀ a : N.algebra B, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        gnsVonNeumann π ∩ Set.centralizer (gnsVonNeumann π)
          = {T : H →L[ℂ] H | ∃ c : ℂ, T = c • 1} :=
  GNS.exists_gns_factor_of_isPure hpure

/-- **The GNS representation of a pure state on a curved local algebra generates `𝓑(H)`.**
For a pure state `ω` on `𝔘(B)` there is a cyclic GNS triple reproducing `ω` whose generated
von Neumann algebra is all of `𝓑(H)`: `π(𝔘(B))'' = 𝓑(H)`. The abstract
`GNS.exists_gns_generates_all_of_isPure` at the C*-algebra `𝔘(B)`. -/
theorem exists_gns_generates_all_of_isPure {B : Set M.Carrier} {ω : State (N.algebra B)}
    (hpure : IsPure ω) :
    ∃ (H : Type)
      (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        IsCyclicVector π Ω ∧
        (∀ a : N.algebra B, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        gnsVonNeumann π = Set.univ :=
  GNS.exists_gns_generates_all_of_isPure hpure

end HaagKastlerNet
end HaagKastlerCurved
end AQFT
end Physicslib4
