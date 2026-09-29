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
# The identity-component bridge: faithfulness and satisfiability

The concrete-to-abstract bridge
`Physicslib4.Spacetime.LorentzianSpacetime.toAbstractIdentityComponent`
(`Physicslib4/AQFT/HaagKastlerCurved/Concrete.lean`) instantiates the abstract
interface's isometry group `Isom` with the oriented identity component of the
isometry group, matching the blueprint's "isometries connected to the identity" in
Axiom 5 (`def:isometric-covariance-in-curved-spacetime`). This file records that the
identity component acts faithfully and that the curved Haag-Kastler axioms are jointly
satisfiable over the bridge.
-/

namespace Physicslib4

namespace Spacetime

namespace LorentzianSpacetime

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
        L.toAbstractIdentityComponent)
      (Physicslib4.AQFT.HaagKastlerCurved.trivialLocalNetIsotony
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
