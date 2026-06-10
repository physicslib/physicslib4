/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalAlgebras
import Physicslib4.AQFT.HaagKastler.Isotony
import Physicslib4.AQFT.HaagKastler.LocalCommutativity
import Physicslib4.AQFT.HaagKastler.QuasilocalCompleteness
import Physicslib4.AQFT.HaagKastler.LorentzCovariance

/-!
# Haag-Kastler nets

This file bundles the data of Axiom 1 (`def:local-algebras`)
together with the propositional content of Axioms 2-5 into a single
`structure HaagKastlerNet`, formalising the blueprint declaration
`def:haag-kastler-net` (section 9.3 of the AQFT-in-Lean blueprint).

## Main definitions

* `Physicslib4.AQFT.HaagKastler.HaagKastlerNet`: a structure
  consisting of a `LocalNet` (the Axiom 1 data) plus proofs of
  `Isotony`, `LocalCommutativity`, `QuasilocalCompleteness`, and
  `LorentzCovariance`.

## Notes

* The structure intentionally does not bundle Axiom 6 (Primitivity)
  or further axioms; those will be added as separate structure
  fields in subsequent files when they are formalised.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

/--
A *Haag-Kastler net* on (the Alexandrov-basis sets of) Minkowski
spacetime: the data of Axiom 1 (`def:local-algebras`) together with
proofs of Axioms 2-5 (`def:isotony`,
`def:local-commutativity`, `def:quasilocal-completeness`,
`def:lorentz-covariance`).

Blueprint reference: `def:haag-kastler-net`.
-/
structure HaagKastlerNet where
  /-- The underlying assignment `B ↦ 𝔘(B)` (Axiom 1). -/
  U : LocalNet
  /-- *Isotony*: inclusions of Alexandrov-basis sets induce unital
  `*`-monomorphisms of the corresponding local algebras
  (Axiom 2). -/
  isotony : Isotony U
  /-- *Local commutativity*: local algebras of completely-spacelike
  basis sets commute inside the quasilocal algebra (Axiom 3). -/
  localCommutativity : LocalCommutativity U
  /-- *Quasilocal completeness*: the local algebras' images are
  dense in the quasilocal algebra; i.e. all observables are
  quasilocal observables (Axiom 4). -/
  quasilocalCompleteness : QuasilocalCompleteness U
  /-- *Lorentz covariance*: the inhomogeneous Lorentz group acts on
  the net and the action commutes with isotony (Axiom 5). -/
  lorentzCovariance : LorentzCovariance U

end HaagKastler
end AQFT
end Physicslib4
