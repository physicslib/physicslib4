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
(Axiom 1 of the "sharpened" Haag-Kastler axioms, section 10.6 of the
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
  `StarAlgEquiv` field `emptyEquivComplex` between the fiber over `∅`
  and `ℂ`, supplied by each concrete net (e.g. `StarAlgEquiv.refl`
  for the trivial net).
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4

/-- A set of Minkowski spacetime is an *Alexandrov-basis set* if it is a causal diamond.

A causal diamond is a set I⁺(p) ∩ I⁻(q), the chronological future of a point p intersected with
the chronological past of a point q. These sets form a basis of the Alexandrov topology, and they
are the regions to which the Haag–Kastler axioms attach local algebras. The diamond is empty unless
p chronologically precedes q, and the empty set is a basis set too.

Implementation note: the predicate is stated on subsets of `StandardMinkowskiSpacetime.Carrier`,
which is definitionally `MinkowskiSpacetime.Carrier`, so that it and the completely-spacelike
predicate of Axiom 3 are about the same sets. -/
def IsAlexandrovBasisSet (B : Set StandardMinkowskiSpacetime.Carrier) : Prop :=
  B ∈ Spacetime.alexandrovBasis StandardMinkowskiSpacetime
    standardMinkowskiTimeOrientation

/--
Axiom 1 (local algebras): a unital C*-algebra 𝔘(B) for each region B of Minkowski spacetime.

The algebra 𝔘(B) is the abstract algebra of the observables that can be measured in B. The
regions that matter are the causal diamonds (`IsAlexandrovBasisSet`), and the axioms that follow
quantify over those only. The empty region is assigned the one-dimensional algebra ℂ·1 of
multiples of the unit. The algebras are unital because Mathlib's `CStarAlgebra` is the class of
unital C*-algebras.

Implementation note: `algebra` is defined on every subset of spacetime, so that it is a plain
function; its values on sets that are not diamonds are never used. The normalisation 𝔘(∅) = ℂ·1
is a *-isomorphism `emptyEquivComplex` onto ℂ.

Blueprint: def:local-algebras
-/
structure LocalNet where
  /-- The local algebra 𝔘(B) of a region B. Only its values on causal diamonds are constrained by
  the axioms. -/
  algebra : Set StandardMinkowskiSpacetime.Carrier → Type*
  /-- Each local algebra 𝔘(B) is a unital C*-algebra. -/
  instCStarAlgebra : ∀ B, CStarAlgebra (algebra B)
  /-- The normalisation 𝔘(∅) = ℂ·1: a *-isomorphism from the algebra of the empty region onto ℂ. -/
  emptyEquivComplex : StarAlgEquiv ℂ (algebra ∅) ℂ

attribute [instance] LocalNet.instCStarAlgebra

/-!
**Unitality.** Mathlib's `CStarAlgebra` is the class of *unital* (complex)
C\*-algebras: it extends `NormedRing`
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
