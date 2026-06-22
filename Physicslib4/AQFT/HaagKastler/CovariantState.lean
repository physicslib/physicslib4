/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.Net
import Physicslib4.GNS.Basic

/-!
# Covariant families of local states

This file begins the scaffolding for *covariant states* on a Haag-Kastler
net over Minkowski spacetime. The Lorentz action on the net is implemented
fiberwise by the covariance equivalences `α_L : 𝔘(B) ≃⋆ₐ[ℂ] 𝔘(L·B)`
(`HaagKastlerNet.covEquiv`, from Axiom 5). A *covariant family of local
states* is a choice of state `ω B` on each local algebra `𝔘(B)` that is
intertwined by these equivalences.

## Main definitions

* `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.IsCovariantFamily`: a
  family `ω : ∀ B, State 𝔘(B)` is covariant if `ω B a = ω (L·B) (α_L a)`
  for every Lorentz transformation `L`, region `B`, and `a ∈ 𝔘(B)`.

## Main results

* `IsCovariantFamily.one`: at the identity, covariance reduces to the
  canonical identification `𝔘(B) = 𝔘(1·B)` (via `covEquiv_one`).
* `IsCovariantFamily.comp`: covariance composes - chaining through `L`
  then `L'` expresses `ω B` via the state on `L'·(L·B)`.

## Notes

This is the local, fiberwise form of covariance. A genuine *vacuum state*
- a single Lorentz-invariant state on the quasilocal algebra `𝔘` - additionally
requires lifting the fiberwise action to an automorphism group of the quasilocal
algebra, which is not yet available; that is the natural next layer.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4 Physicslib4.GNS
open scoped Pointwise

namespace HaagKastlerNet

variable (N : HaagKastlerNet)

/--
A *covariant family of local states* assigns to every region `B` a state
`ω B` on the local algebra `𝔘(B)` such that the state on `B` is the
pullback of the state on the Lorentz translate `L·B` along the covariance
equivalence: `ω B a = ω (L·B) (α_L a)` for all `L`, `B`, and `a ∈ 𝔘(B)`.
-/
def IsCovariantFamily
    (ω : ∀ B : Set StandardMinkowskiSpacetime.Carrier, State (N.algebra B)) :
    Prop :=
  ∀ (L : InhomogeneousLorentzGroup)
    (B : Set StandardMinkowskiSpacetime.Carrier) (a : N.algebra B),
    ω B a = ω (L • B) (N.covEquiv L B a)

/-- **Covariance at the identity.** For a covariant family, the state on `B`
agrees with the state on `1·B` transported along the canonical identification
`𝔘(B) = 𝔘(1·B)` (from `one_smul`). -/
theorem IsCovariantFamily.one
    {ω : ∀ B : Set StandardMinkowskiSpacetime.Carrier, State (N.algebra B)}
    (hω : N.IsCovariantFamily ω)
    (B : Set StandardMinkowskiSpacetime.Carrier) (a : N.algebra B) :
    ω B a
      = ω ((1 : InhomogeneousLorentzGroup) • B)
          ((congrArg N.U.algebra
            (one_smul InhomogeneousLorentzGroup B).symm).mp a) := by
  rw [hω 1 B a, N.covEquiv_one B a]

/-- **Covariance composes.** Chaining covariance through `L` and then `L'`
expresses the state on `B` via the state on `L'·(L·B)` and the composed
equivalences. -/
theorem IsCovariantFamily.comp
    {ω : ∀ B : Set StandardMinkowskiSpacetime.Carrier, State (N.algebra B)}
    (hω : N.IsCovariantFamily ω) (L L' : InhomogeneousLorentzGroup)
    (B : Set StandardMinkowskiSpacetime.Carrier) (a : N.algebra B) :
    ω B a
      = ω (L' • (L • B)) (N.covEquiv L' (L • B) (N.covEquiv L B a)) := by
  rw [hω L B a, hω L' (L • B) (N.covEquiv L B a)]

/--
**Fiberwise weak continuity of the covariance action (state-relative).**

This is the fiberwise, state-relative continuity hypothesis for the Lorentz
action. It does *not* strengthen Axiom 5 and uses no quasilocal algebra, so
the notion ports verbatim to curved spacetime (where there is no ambient
quasilocal algebra).

Continuity is measured relative to a state `ω` on the algebra of a
*containing* region `B`. A fixed observable `a ∈ 𝔘(B)` is compared against
the Lorentz-transported observable `α_L b` of a `b ∈ 𝔘(O)` from a
sub-region `O`. The transported observable `α_L b` lives in the *different*
algebra `𝔘(L·O)`, so it is embedded back into `𝔘(B)` along a supplied
isotony inclusion `incl` (the fiberwise isotony datum). The inclusion is
explicit data rather than the existential isotony witness, because an
uncontrolled per-`L` choice would make "continuous in `L`" ill-defined.

The family is *weakly continuous* if for all `a ∈ 𝔘(B)`, `b ∈ 𝔘(O)` the
GNS matrix coefficient
`L ↦ ω(a⋆ · ι_{L·O ⊆ B}(α_L b))`
is continuous on the subspace of transformations `L` keeping `L·O` an
Alexandrov-basis set inside `B`.

The *diagonal* coefficient `ω(α_L(a⋆ b))` collapses to `ω(a⋆ b)` by
covariance (constant); this off-diagonal form is the genuine continuity
content, and is the standard input - together with uniform boundedness
`‖U(L)‖ = 1` - from which strong continuity of the GNS unitary
representation follows.
-/
def IsWeaklyContinuousAction
    (O B : Set StandardMinkowskiSpacetime.Carrier)
    (ω : State (N.algebra B))
    (incl : ∀ L : InhomogeneousLorentzGroup,
        IsAlexandrovBasisSet (L • O) → L • O ⊆ B →
          N.algebra (L • O) →⋆ₐ[ℂ] N.algebra B) :
    Prop :=
  ∀ (a : N.algebra B) (b : N.algebra O),
    Continuous fun L : {L : InhomogeneousLorentzGroup //
        IsAlexandrovBasisSet (L • O) ∧ L • O ⊆ B} =>
      ω (star a * incl L.1 L.2.1 L.2.2 (N.covEquiv L.1 O b))

end HaagKastlerNet

end HaagKastler
end AQFT
end Physicslib4
