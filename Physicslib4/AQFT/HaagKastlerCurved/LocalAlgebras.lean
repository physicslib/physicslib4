/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Dimension.Finrank
import Physicslib4.AQFT.HaagKastlerCurved.Spacetime

/-!
# Axiom 1 (Local Algebras), curved spacetime

This file formalises the blueprint declaration
`def:local-algebras-in-curved-spacetime` (Axiom 1 of the
Haag-Kastler axioms on a Lorentzian spacetime, Chapter 10
(`sections/sec10/10-4_haag-kastler-axioms-in-curved-spacetime`) of the
AQFT-in-Lean blueprint):

> For any basis element `𝐁` of the Alexandrov topology on a
> Lorentzian spacetime `M`, i.e. any set of the form
> `I⁺(p) ∩ I⁻(q)`, there is a corresponding abstract C*-algebra
> `𝔘(𝐁)`, and when `𝐁` is the empty set, `𝔘(∅) = ℂ · 1`.

## Main definitions

* `Physicslib4.AQFT.HaagKastlerCurved.LocalNet`: a `structure`
  bundling the data of Axiom 1 over an abstract `LorentzianSpacetime`
  `M`.

## Modelling notes

The shape is identical to the Minkowski `LocalNet`
(`def:local-algebras`), but with the fixed Minkowski carrier and
Alexandrov-basis predicate replaced by the abstract interface
`M : LorentzianSpacetime`. The empty-region normalisation
`𝔘(∅) = ℂ · 1` is encoded by a `StarAlgEquiv` between the fiber over
`∅` and `ℂ`.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastlerCurved

variable (M : LorentzianSpacetime)

/--
**Axiom 1 (Local Algebras), curved spacetime.** The *data* of a
Haag-Kastler local net on a Lorentzian spacetime `M`: an assignment,
for every subset `B` of `M` (thought of as an Alexandrov-basis set,
with the empty set covering the normalisation `𝔘(∅) = ℂ · 1`), of a
unital C*-algebra `algebra B`.

The `𝔘(∅) = ℂ` normalisation is captured by the field
`emptyEquivComplex` exhibiting a `StarAlgEquiv` between `algebra ∅`
and `ℂ`.

Blueprint reference: `def:local-algebras-in-curved-spacetime`.
-/
structure LocalNet where
  /-- The C*-algebra `𝔘(B)` assigned to a (would-be Alexandrov-basis)
  region `B`. -/
  algebra : Set M.Carrier → Type
  /-- The `CStarAlgebra` instance on each fiber `𝔘(B)`. -/
  instCStarAlgebra : ∀ B, CStarAlgebra (algebra B)
  /-- Normalisation: `𝔘(∅) = ℂ · 1`, encoded as a `*`-algebra
  isomorphism `algebra ∅ ≃⋆ₐ[ℂ] ℂ`. -/
  emptyEquivComplex : StarAlgEquiv ℂ (algebra ∅) ℂ

attribute [instance] LocalNet.instCStarAlgebra

variable {M}

/-- The empty-region algebra `𝔘(∅)` is *commutative*: it is
`*`-isomorphic to `ℂ` via `emptyEquivComplex`, so its multiplication
inherits commutativity from `ℂ`. -/
theorem LocalNet.mul_comm_algebra_empty (U : LocalNet M) (a b : U.algebra ∅) :
    a * b = b * a :=
  U.emptyEquivComplex.injective <| by
    rw [map_mul, map_mul]; exact mul_comm _ _

/-- The empty-region algebra `𝔘(∅)` is *one-dimensional* over `ℂ`. -/
theorem LocalNet.finrank_algebra_empty (U : LocalNet M) :
    Module.finrank ℂ (U.algebra ∅) = 1 := by
  rw [U.emptyEquivComplex.toAlgEquiv.toLinearEquiv.finrank_eq]
  exact CommSemiring.finrank_self ℂ

end HaagKastlerCurved
end AQFT
end Physicslib4
