/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Physicslib4.Spacetime.Minkowski

/-!
# Axiom 1: Local Algebras

This file formalises the blueprint declaration `def:local-algebras`
(Axiom 1 of the "sharpened" Haag-Kastler axioms, section 9.3 of the
AQFT-in-Lean blueprint):

> An assignment from the Alexandrov-basis sets `𝐁` of Minkowski
> spacetime to (abstract, unital) C*-algebras `𝔘(𝐁)`, with
> `𝔘(∅) = ℂ · 1`.

## Main definitions

* `Physicslib4.AQFT.HaagKastler.LocalNet`: a `structure` bundling
  the *data* of Axiom 1: for every Alexandrov-basis set `𝐁` of
  Minkowski spacetime (together with the empty set), a carrier type
  `algebra B` and a `CStarAlgebra` instance on it, plus the
  normalisation condition that the algebra assigned to `∅` is
  (isomorphic to) `ℂ`.

## Modelling notes

* The blueprint regions `𝐁` are *non-empty* Alexandrov-basis sets,
  plus the convention `𝔘(∅) = ℂ · 1` for normalisation. We package
  this by indexing the net over arbitrary subsets `B : Set
  MinkowskiSpacetime.Carrier`, with the data only "meaningful" for
  `B ∈ Spacetime.alexandrovBasis _ _` or `B = ∅`. The Lean shape
  thus stores the assignment as a function `Set ... → Type*`
  carrying a `CStarAlgebra` instance.

* The Alexandrov-basis condition is left as a separate predicate
  `IsAlexandrovBasisSet`; downstream axioms (Isotony, Local
  Commutativity, ...) quantify only over basis sets.

* The "𝔘(∅) = ℂ" condition is encoded by a distinguished
  `StarAlgEquiv` between the fiber over `∅` and `ℂ`. We use
  `sorry`-placeholders where the unification of the `CStarAlgebra`
  instance is non-trivial; the *statement* is faithful.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4

/-- An *Alexandrov-basis set* of Minkowski spacetime: a subset of
`StandardMinkowskiSpacetime.Carrier` of the form `I⁺(p) ∩ I⁻(q)`
for some points `p, q`. We index over the underlying carrier of
`StandardMinkowskiSpacetime` (which is defeq to
`MinkowskiSpacetime.Carrier`) so that the Alexandrov-basis predicate
and the completely-spacelike predicate (used in Axiom 3) talk about
the same `Set`. -/
def IsAlexandrovBasisSet (B : Set StandardMinkowskiSpacetime.Carrier) : Prop :=
  B ∈ Spacetime.alexandrovBasis StandardMinkowskiSpacetime
    standardMinkowskiTimeOrientation

/--
**Axiom 1 (Local Algebras).** The *data* of a Haag-Kastler local
net: an assignment, for every subset `B` of Minkowski spacetime
(thought of as an Alexandrov-basis set, with the empty set covering
the normalisation `𝔘(∅) = ℂ · 1`), of a unital C*-algebra `algebra
B`.

The "𝔘(∅) = ℂ" normalisation is captured by the field
`emptyEquivComplex` exhibiting a `StarAlgEquiv` between
`algebra ∅` and `ℂ`.

Blueprint reference: `def:local-algebras`.
-/
structure LocalNet where
  /-- The C*-algebra `𝔘(B)` assigned to a (would-be Alexandrov-basis)
  region `B`. -/
  algebra : Set StandardMinkowskiSpacetime.Carrier → Type*
  /-- The `CStarAlgebra` instance on each fiber `𝔘(B)`. -/
  instCStarAlgebra : ∀ B, CStarAlgebra (algebra B)
  /-- Normalisation: `𝔘(∅) = ℂ · 1`, encoded as a `*`-algebra
  isomorphism `algebra ∅ ≃⋆ₐ[ℂ] ℂ`. -/
  emptyEquivComplex : StarAlgEquiv ℂ (algebra ∅) ℂ

attribute [instance] LocalNet.instCStarAlgebra

/-!
**Unitality.** In `Mathlib v4.31.0-rc1`, `CStarAlgebra` is *defined* as
the class of *unital* (complex) C\*-algebras: it extends `NormedRing`
(which extends `Ring`, so we get `(1 : algebra B)` for free) plus
`StarRing`, `CStarRing`, `NormedAlgebra ℂ _`, etc. The non-unital
version is the separately-named `NonUnitalCStarAlgebra` class.
Consequently `(1 : U.algebra B)` is available for every `B`, and
every `StarAlgHom ℂ (U.algebra B₁) (U.algebra B₂)` automatically
preserves `1` (via its `AlgHom` parent). The blueprint's "unital
\*-monomorphism" language in downstream axioms (Isotony, Lorentz
Covariance, ...) is therefore honoured by the present `LocalNet`
structure without an extra `One`/`NormedAlgebra` bundle. -/

-- Compile-time witnesses for the docstring above. These also serve as
-- a regression check should the underlying Mathlib `CStarAlgebra`
-- class drift back to a non-unital baseline.

example (U : LocalNet) (B : Set StandardMinkowskiSpacetime.Carrier) :
    U.algebra B :=
  (1 : U.algebra B)

example (U : LocalNet) (B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier)
    (φ : StarAlgHom ℂ (U.algebra B₁) (U.algebra B₂)) :
    φ (1 : U.algebra B₁) = (1 : U.algebra B₂) :=
  map_one φ

/-- The empty-region algebra `𝔘(∅)` is *commutative*: it is `*`-isomorphic to
`ℂ` via the normalisation `emptyEquivComplex`, so its multiplication inherits
commutativity from `ℂ`. -/
theorem LocalNet.mul_comm_algebra_empty (U : LocalNet) (a b : U.algebra ∅) :
    a * b = b * a :=
  U.emptyEquivComplex.injective <| by
    rw [map_mul, map_mul]; exact mul_comm _ _

/-- The empty-region algebra `𝔘(∅)` is *one-dimensional* over `ℂ`: the
normalisation `emptyEquivComplex : 𝔘(∅) ≃⋆ₐ[ℂ] ℂ` is in particular a
`ℂ`-linear equivalence, so `𝔘(∅)` has the same `ℂ`-dimension as `ℂ`. -/
theorem LocalNet.finrank_algebra_empty (U : LocalNet) :
    Module.finrank ℂ (U.algebra ∅) = 1 := by
  rw [U.emptyEquivComplex.toAlgEquiv.toLinearEquiv.finrank_eq]
  exact CommSemiring.finrank_self ℂ

end HaagKastler
end AQFT
end Physicslib4
