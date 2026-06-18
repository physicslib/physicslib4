/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.Spacetime
import Physicslib4.Spacetime.LorentzianSpacetime
import Physicslib4.Spacetime.Isometry

/-!
# Bridging a concrete spacetime to the abstract Haag-Kastler interface

This file connects the concrete blueprint object
`Physicslib4.Spacetime.LorentzianSpacetime` (`def:lorentzian-spacetime`)
to the abstract interface
`Physicslib4.AQFT.HaagKastlerCurved.LorentzianSpacetime` over which
Axioms 1-5 are stated.

## Main definitions

* `Physicslib4.Spacetime.LorentzianSpacetime.toAbstract`: the abstract
  interface induced by a concrete Lorentzian spacetime.

## Modelling notes

The four pieces of the abstract interface are read off the concrete
spacetime:

* `Carrier` is the manifold's point set;
* `IsBasisSet` is membership in the Alexandrov basis of diamonds
  `I⁺(p) ∩ I⁻(q)`;
* `IsCompletelySpacelike` is the spacelike-separation relation of the
  underlying spacetime, with respect to its chosen time orientation;
* `Isom` is `Physicslib4.Spacetime.Isometry` of the underlying
  spacetime, with its `Group` and `MulAction` instances.

The same deferred refinements noted on `Spacetime.Isometry` apply here:
the isometry group is the full metric-preserving group (its
identity-component restriction is not yet captured) and its bundled
differential is not yet tied to the manifold derivative.
-/

namespace Physicslib4

namespace Spacetime

namespace LorentzianSpacetime

/--
The abstract Haag-Kastler interface
(`AQFT.HaagKastlerCurved.LorentzianSpacetime`) induced by a concrete
Lorentzian spacetime: carrier, Alexandrov-basis predicate,
complete-spacelike relation, and the isometry group with its action.
-/
noncomputable def toAbstract (L : LorentzianSpacetime) :
    AQFT.HaagKastlerCurved.LorentzianSpacetime where
  Carrier := L.Carrier
  IsBasisSet := L.IsBasisSet
  IsCompletelySpacelike := L.IsCompletelySpacelike
  Isom := Isometry L.toSpacetime
  instGroup := inferInstance
  instAction := inferInstance

@[simp] theorem toAbstract_Carrier (L : LorentzianSpacetime) :
    L.toAbstract.Carrier = L.Carrier := rfl

@[simp] theorem toAbstract_IsBasisSet (L : LorentzianSpacetime) :
    L.toAbstract.IsBasisSet = L.IsBasisSet := rfl

@[simp] theorem toAbstract_IsCompletelySpacelike (L : LorentzianSpacetime) :
    L.toAbstract.IsCompletelySpacelike = L.IsCompletelySpacelike := rfl

end LorentzianSpacetime

end Spacetime

end Physicslib4
