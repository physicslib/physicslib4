/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.Net
import Physicslib4.GNS.Basic

/-!
# Covariant families of local states, curved spacetime

This file mirrors `Physicslib4.AQFT.HaagKastler.CovariantState` for a
Haag-Kastler net over an abstract Lorentzian spacetime `M`. The
identity-component isometry action on the net is implemented fiberwise by
the covariance equivalences `α_φ : 𝔘(B) ≃⋆ₐ[ℂ] 𝔘(φ·B)`
(`HaagKastlerNet.covEquiv`, from Axiom 5). A *covariant family of local
states* is a choice of state `ω B` on each local algebra `𝔘(B)` that is
intertwined by these equivalences.

## Main definitions

* `Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet.IsCovariantFamily`: a
  family `ω : ∀ B, State 𝔘(B)` is covariant if `ω B a = ω (φ·B) (α_φ a)`
  for every isometry `φ`, region `B`, and `a ∈ 𝔘(B)`.

## Main results

* `IsCovariantFamily.one`: at the identity, covariance reduces to the
  canonical identification `𝔘(B) = 𝔘(1·B)` (via `covEquiv_one`).
* `IsCovariantFamily.comp`: covariance composes - chaining through `φ`
  then `φ'` expresses `ω B` via the state on `φ'·(φ·B)`.

## Notes

As in the Minkowski case, this is the local, fiberwise form of covariance; a
genuine isometry-invariant *vacuum state* additionally requires lifting the
fiberwise action to an automorphism group, which is not yet available.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastlerCurved

open Physicslib4 Physicslib4.GNS
open scoped Pointwise

namespace HaagKastlerNet

variable {M : LorentzianSpacetime} (N : HaagKastlerNet M)

/--
A *covariant family of local states* assigns to every region `B` a state
`ω B` on the local algebra `𝔘(B)` such that the state on `B` is the
pullback of the state on the isometric image `φ·B` along the covariance
equivalence: `ω B a = ω (φ·B) (α_φ a)` for all `φ`, `B`, and `a ∈ 𝔘(B)`.
-/
def IsCovariantFamily (ω : ∀ B : Set M.Carrier, State (N.algebra B)) : Prop :=
  ∀ (φ : M.Isom) (B : Set M.Carrier) (a : N.algebra B),
    ω B a = ω (φ • B) (N.covEquiv φ B a)

/-- **Covariance at the identity.** For a covariant family, the state on `B`
agrees with the state on `1·B` transported along the canonical identification
`𝔘(B) = 𝔘(1·B)` (from `one_smul`). -/
theorem IsCovariantFamily.one
    {ω : ∀ B : Set M.Carrier, State (N.algebra B)}
    (hω : N.IsCovariantFamily ω) (B : Set M.Carrier) (a : N.algebra B) :
    ω B a
      = ω ((1 : M.Isom) • B)
          ((congrArg N.U.algebra (one_smul M.Isom B).symm).mp a) := by
  rw [hω 1 B a, N.covEquiv_one B a]

/-- **Covariance composes.** Chaining covariance through `φ` and then `φ'`
expresses the state on `B` via the state on `φ'·(φ·B)` and the composed
equivalences. -/
theorem IsCovariantFamily.comp
    {ω : ∀ B : Set M.Carrier, State (N.algebra B)}
    (hω : N.IsCovariantFamily ω) (φ φ' : M.Isom)
    (B : Set M.Carrier) (a : N.algebra B) :
    ω B a
      = ω (φ' • (φ • B)) (N.covEquiv φ' (φ • B) (N.covEquiv φ B a)) := by
  rw [hω φ B a, hω φ' (φ • B) (N.covEquiv φ B a)]

/--
**Fiberwise weak continuity of the covariance action (state-relative),
curved spacetime.** Mirror of
`Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsWeaklyContinuousAction`.

Continuity is measured relative to a state `ω` on the algebra of a
*containing* region `B`. A fixed observable `a ∈ 𝔘(B)` is compared against
the isometry-transported observable `α_φ b` of a `b ∈ 𝔘(O)` from a
sub-region `O`. Since `α_φ b` lives in the *different* algebra `𝔘(φ·O)`,
it is embedded back into `𝔘(B)` along a supplied isotony inclusion `incl`
(explicit data, not the existential isotony witness). The family is
*weakly continuous* if for all `a`, `b` the matrix coefficient
`φ ↦ ω(a⋆ · ι_{φ·O ⊆ B}(α_φ b))`
is continuous on the subspace of isometries keeping `φ·O` a basis set
inside `B`.

Because the abstract `LorentzianSpacetime` interface equips `M.Isom` with
only a group and an action - no topology - the topology required to state
continuity enters as an explicit `[TopologicalSpace M.Isom]` instance
argument rather than as a field on the interface. The definition is
otherwise identical to the Minkowski one and uses no quasilocal algebra,
confirming that the fiberwise form ports cleanly to curved spacetime. -/
def IsWeaklyContinuousAction [TopologicalSpace M.Isom]
    (O B : Set M.Carrier)
    (ω : State (N.algebra B))
    (incl : ∀ φ : M.Isom,
        M.IsBasisSet (φ • O) → φ • O ⊆ B →
          N.algebra (φ • O) →⋆ₐ[ℂ] N.algebra B) :
    Prop :=
  ∀ (a : N.algebra B) (b : N.algebra O),
    Continuous fun φ : {φ : M.Isom //
        M.IsBasisSet (φ • O) ∧ φ • O ⊆ B} =>
      ω (star a * incl φ.1 φ.2.1 φ.2.2 (N.covEquiv φ.1 O b))

end HaagKastlerNet

end HaagKastlerCurved
end AQFT
end Physicslib4
