/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Physicslib4.AQFT.HaagKastlerCurved.Isotony

/-!
# Axiom 5 (Isometric Covariance), curved spacetime

This file formalises the blueprint declaration
`def:isometric-covariance-in-curved-spacetime` (Axiom 5 of the
Haag-Kastler axioms on a Lorentzian spacetime, Chapter 10
(`sections/sec10/haag-kastler-axioms-in-curved-spacetime`) of the
AQFT-in-Lean blueprint):

> A member `φ` of the group of isometries of `M` connected to the
> identity acts on `𝔘(𝐁)` via a unital `*`-isomorphism
> `α_φ : 𝔘(𝐁) → 𝔘(φ(𝐁))`, where `φ(𝐁)` is the image of the basis
> set. The action satisfies (1) `α_𝟙 = id`, (2)
> `α_{φ'·φ} = α_{φ'} ∘ α_φ`, and (3) it commutes with the isotony
> monomorphism `i` (Axiom 2).

## Main definitions

* `Physicslib4.AQFT.HaagKastlerCurved.IsometricCovariance`: a
  `Prop`-valued predicate on a `LocalNet M` and its Axiom 2 isotony family
  asserting Axiom 5.

## Modelling notes

* The Minkowski analogue (`LorentzCovariance`) uses the identity
  component of the inhomogeneous Lorentz group. Here the analogous
  role is played by the abstract group `M.Isom` of isometries
  connected to the identity, acting on `M.Carrier`; the induced
  pointwise action on `Set M.Carrier` (`φ • B = φ(B)`) supplies the
  blueprint's `φ(𝐁)`.

* Conditions (1) and (2) carry cross-fiber identifications
  `U.algebra (1 • B) = U.algebra B` and
  `U.algebra ((φ'·φ) • B) = U.algebra (φ' • (φ • B))` coming from
  `one_smul`/`mul_smul`, implemented as `Eq.mpr`/`congrArg`. This
  matches the Minkowski `LorentzCovariance` encoding verbatim.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastlerCurved

open scoped Pointwise

variable {M : LorentzianSpacetime}

/--
**Axiom 5 (Isometric Covariance), curved spacetime.** A local net
`U` on a Lorentzian spacetime `M` is *isometrically covariant* if the
group `M.Isom` of identity-component isometries acts on the
assignment `B ↦ U.algebra B` and the action

(1) sends the identity isometry to the identity automorphism,
(2) is multiplicative in the group element,
    `α (φ' · φ) = α φ' ∘ α φ`, and
(3) *commutes with isotony*.

Concretely, there exists, for every isometry `φ : M.Isom` and every
Alexandrov-basis set `B`, a `*`-algebra equivalence
`α φ B : U.algebra B ≃⋆ₐ[ℂ] U.algebra (φ • B)` such that (1) `α 1 B a = a`,
(2) `α (φ' * φ) B a = α φ' (φ • B) (α φ B a)`, and (3) for every `φ` and
inclusion `B₁ ⊆ B₂`, `α φ B₂ ∘ i.map = i.map ∘ α φ B₁`.

Condition (3) is stated for the isotony family `i` of Axiom 2, which this
predicate takes as a parameter, not for a separately chosen family: the
blueprint's Axiom 5 commutes with "the unital `*`-monomorphism `i` of Axiom 2".

Blueprint reference: `def:isometric-covariance-in-curved-spacetime`.
-/
def IsometricCovariance (U : LocalNet M) (i : Isotony U) : Prop :=
  ∃ α : ∀ (φ : M.Isom) (B : Set M.Carrier),
        StarAlgEquiv ℂ (U.algebra B) (U.algebra ((φ • B : Set M.Carrier))),
      -- (1) Identity: α 1 B a = a, modulo `one_smul : (1 : M.Isom) • B = B`.
      (∀ (B : Set M.Carrier) (a : U.algebra B),
          (α (1 : M.Isom) B :
              U.algebra B → U.algebra ((1 : M.Isom) • B)) a
            = (congrArg U.algebra (one_smul M.Isom B).symm).mp a) ∧
      -- (2) Composition: α (φ' * φ) B a = α φ' (φ • B) (α φ B a), modulo
      -- `mul_smul : (φ' * φ) • B = φ' • (φ • B)`.
      (∀ (φ φ' : M.Isom) (B : Set M.Carrier) (a : U.algebra B),
          (α (φ' * φ) B : U.algebra B → U.algebra ((φ' * φ) • B)) a
            = (congrArg U.algebra (mul_smul φ' φ B).symm).mp
                ((α φ' (φ • B) : U.algebra (φ • B) → U.algebra (φ' • (φ • B)))
                  ((α φ B : U.algebra B → U.algebra (φ • B)) a))) ∧
      -- (3) The action commutes with the Axiom 2 isotony family `i`.
      ∀ (φ : M.Isom) ⦃B₁ B₂ : Set M.Carrier⦄
        (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
        (h : B₁ ⊆ B₂)
        (hφB₁ : M.IsBasisSet (φ • B₁))
        (hφB₂ : M.IsBasisSet (φ • B₂))
        (hφ : (φ • B₁ : Set _) ⊆ φ • B₂)
        (a : U.algebra B₁),
          (α φ B₂ : U.algebra B₂ → U.algebra (φ • B₂)) (i.map hB₁ hB₂ h a)
            = i.map hφB₁ hφB₂ hφ ((α φ B₁ : U.algebra B₁ → U.algebra (φ • B₁)) a)

end HaagKastlerCurved
end AQFT
end Physicslib4
