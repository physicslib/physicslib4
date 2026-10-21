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
(`sections/sec10/haag-kastler-axioms-in-curved-spacetime`) of the
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

As in the Minkowski `LocalNet`, the local algebras are universe
polymorphic: `LocalNet.{u, v} M` assigns algebras in `Type v` over a
spacetime `M : LorentzianSpacetime.{u}`, with `v` independent of the
carrier's universe `u`.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastlerCurved

universe u v

variable (M : LorentzianSpacetime.{u})

/--
Axiom 1 in curved spacetime (local algebras): a unital C*-algebra 𝔘(B) for each region B of M.

The algebra 𝔘(B) is the abstract algebra of the observables that can be measured in the region B
of the spacetime M. The regions that matter are the causal diamonds, the basis sets
`M.IsBasisSet` of the Alexandrov topology, and the axioms that follow quantify over those only.
The empty region is assigned the one-dimensional algebra ℂ·1 of multiples of the unit. The shape
is that of the Minkowski net, with Minkowski space replaced by the abstract spacetime M.

Implementation note: `algebra` is defined on every subset of M, so that it is a plain function; its
values on sets that are not basis sets are never used. The normalisation 𝔘(∅) = ℂ·1 is a
*-isomorphism `emptyEquivComplex` onto ℂ. The algebras live in a universe v that is independent
of the universe u of the points: `LocalNet.{u, v} M` has algebras in `Type v`.

Blueprint: def:local-algebras-in-curved-spacetime
-/
structure LocalNet where
  /-- The local algebra 𝔘(B) of a region B, in `Type v`. Only its values on basis sets are
  constrained by the axioms. -/
  algebra : Set M.Carrier → Type v
  /-- Each local algebra 𝔘(B) is a unital C*-algebra. -/
  instCStarAlgebra : ∀ B, CStarAlgebra (algebra B)
  /-- The normalisation 𝔘(∅) = ℂ·1: a *-isomorphism from the algebra of the empty region onto ℂ. -/
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
