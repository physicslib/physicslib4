/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.Concrete
import Physicslib4.AQFT.HaagKastlerCurved.Net
import Physicslib4.Spacetime.IsometryTopology
import Physicslib4.Spacetime.IsometryCausality

/-!
# Bridging via the identity-component isometry group

This file provides the variant of the concrete-to-abstract bridge
(`Physicslib4.Spacetime.LorentzianSpacetime.toAbstract`) that instantiates
the abstract interface's isometry group `Isom` with the **identity
component** of the isometry group, matching the blueprint's "isometries
connected to the identity" in Axiom 5
(`def:isometric-covariance-in-curved-spacetime`).

## Main definitions

* `Physicslib4.Spacetime.LorentzianSpacetime.toAbstractIdentityComponent`.

## Modelling notes

The isometry group is a topological group under the `(map, inverse)`-induced
topology (see `Physicslib4/Spacetime/IsometryTopology.lean`), so the
identity-component subgroup is unconditional and this bridge yields the
abstract interface with `Isom` the genuine identity-component subgroup
(isometries connected to the identity).
-/

namespace Physicslib4

namespace Spacetime

namespace LorentzianSpacetime

/--
The abstract Haag-Kastler interface induced by a concrete Lorentzian
spacetime, with the isometry group taken to be the **oriented identity
component** (identity-component isometries that also preserve the future
orientation), as in Axiom 5. Using the oriented component makes basis-set
preservation `φ(𝐁)` a theorem (`toAbstractIdentityComponent_isBasisSet_smul`)
rather than an unprovable consequence of the bare (C⁰) group topology.
-/
noncomputable def toAbstractIdentityComponent (L : LorentzianSpacetime) :
    AQFT.HaagKastlerCurved.LorentzianSpacetime where
  Carrier := L.Carrier
  IsBasisSet := L.IsBasisSet
  IsCompletelySpacelike := L.IsCompletelySpacelike
  Isom := ↥(Spacetime.Isometry.orientedIdentityComponent L.toSpacetime
    L.timeOrientation)
  instGroup := inferInstance
  instAction := inferInstance

@[simp] theorem toAbstractIdentityComponent_Carrier (L : LorentzianSpacetime) :
    (L.toAbstractIdentityComponent).Carrier = L.Carrier := rfl

@[simp] theorem toAbstractIdentityComponent_IsBasisSet (L : LorentzianSpacetime) :
    (L.toAbstractIdentityComponent).IsBasisSet = L.IsBasisSet := rfl

open scoped Pointwise in
/-- **Axiom 5 basis-set preservation, wired into the abstract bridge.** Every
isometry `φ` of the abstract spacetime carries Alexandrov-basis sets to basis
sets: `φ(𝐁)` is again a basis set. The isometry group `(L.toAbstractIdentity
Component).Isom` is, by definition, the oriented identity component
`↥(orientedIdentityComponent ..)`, so this statement applies to bridge
isometries verbatim; it is what makes the Axiom 5 action `𝔘(𝐁) → 𝔘(φ(𝐁))`
well-defined. -/
theorem toAbstractIdentityComponent_isBasisSet_smul (L : LorentzianSpacetime)
    (φ : ↥(Spacetime.Isometry.orientedIdentityComponent L.toSpacetime
      L.timeOrientation)) {B : Set L.Carrier} (hB : L.IsBasisSet B) :
    L.IsBasisSet ((φ : Spacetime.Isometry L.toSpacetime) • B) :=
  L.isBasisSet_smul (↑φ) φ.2 hB

/-- The identity-component isometry group acts **faithfully** on the
spacetime: an identity-component isometry is determined by its action on
points. (Inherited from the faithful action of the full isometry group.) -/
theorem identityComponent_faithfulSMul (L : LorentzianSpacetime) :
    FaithfulSMul (↥(Spacetime.Isometry.identityComponent L.toSpacetime))
      L.toSpacetime.Carrier :=
  inferInstance

/-- **Relating back to Axiom 5 over the concrete spacetime.** The trivial net
over the concrete Lorentzian spacetime — with `Isom` the genuine
identity-component isometry group — satisfies *isometric covariance*
(`def:isometric-covariance-in-curved-spacetime`). -/
theorem isometricCovariance_trivial_identityComponent (L : LorentzianSpacetime) :
    Physicslib4.AQFT.HaagKastlerCurved.IsometricCovariance
      (Physicslib4.AQFT.HaagKastlerCurved.trivialLocalNet
        L.toAbstractIdentityComponent) :=
  Physicslib4.AQFT.HaagKastlerCurved.trivialLocalNet_isometricCovariance _

/-- Over the concrete spacetime (with the identity-component isometry group),
the full set of curved-spacetime Haag-Kastler axioms is jointly satisfiable. -/
theorem nonempty_haagKastlerNet_identityComponent (L : LorentzianSpacetime) :
    Nonempty (Physicslib4.AQFT.HaagKastlerCurved.HaagKastlerNet
      L.toAbstractIdentityComponent) :=
  Physicslib4.AQFT.HaagKastlerCurved.nonempty_haagKastlerNet _

end LorentzianSpacetime

end Spacetime

end Physicslib4
