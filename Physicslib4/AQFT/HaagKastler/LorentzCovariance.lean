/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Physicslib4.AQFT.HaagKastler.LocalAlgebras

/-!
# Axiom 5: Lorentz Covariance

This file formalises the blueprint declaration
`def:lorentz-covariance` (Axiom 5 of the "sharpened" Haag-Kastler
axioms, section 9.3 of the AQFT-in-Lean blueprint):

> The inhomogeneous Lorentz group `𝓛` (more precisely, its identity
> component; see section 7.1 of the blueprint) acts on the
> assignment `B ↦ 𝔘(B)`. For every `L ∈ 𝓛`, there is a
> `*`-isomorphism `αL B : 𝔘(B) ≃⋆ₐ[ℂ] 𝔘(L·B)` such that the action
> commutes with isotony, in the sense that for every inclusion
> `B₁ ⊆ B₂` of basis sets the obvious diagram of inclusion arrows
> and `αL`-arrows commutes.

## Main definitions

* `Physicslib4.AQFT.HaagKastler.InhomogeneousLorentzGroup`: an
  opaque placeholder for the identity component of the
  inhomogeneous Lorentz group acting on Minkowski spacetime.
  Mathlib (at `v4.31.0-rc1`) does not provide a packaged
  `LorentzGroup` type (the `PhysLean` library does, but is not a
  dependency of this project), so we leave both the group and its
  action on `StandardMinkowskiSpacetime.Carrier` as `sorry`-bearing
  declarations.

* `Physicslib4.AQFT.HaagKastler.LorentzCovariance`: a `Prop`-valued
  predicate on a `LocalNet` asserting Axiom 5.

## Modelling notes

* The Lorentz-action data is given as: a group `InhomogeneousLorentzGroup`,
  a `MulAction` of that group on `StandardMinkowskiSpacetime.Carrier`,
  and, for each pair `(L, B)`, a `*`-algebra equivalence
  `αL B : U.algebra B ≃⋆ₐ[ℂ] U.algebra (L • B)`.

* "Commutes with isotony" is encoded by the commutativity of, for
  every `B₁ ⊆ B₂` (basis sets) and every `L`, the square formed by
  the isotony arrow `𝔘(B₁) ↪ 𝔘(B₂)` and the action arrows
  `𝔘(B₁) ≃ 𝔘(L·B₁)` and `𝔘(B₂) ≃ 𝔘(L·B₂)`. Because the isotony
  arrows are existentially quantified (see `Isotony`), we quantify
  over them: the predicate asks that *some* choice of isotony
  arrows makes the action equivariant.

* The Lorentz group itself is left as an opaque `Type` with a
  `Group` instance produced by `sorry`, to be replaced by the
  genuine identity component of the inhomogeneous Lorentz group
  once Mathlib (or a future blueprint section) provides one.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4
open scoped Pointwise

/-- A placeholder for the identity component of the inhomogeneous
Lorentz group, acting on Minkowski spacetime.

Mathlib v4.31.0-rc1 does not provide a `LorentzGroup` type. The
genuine construction lives in `PhysLean`, which is not a dependency
of this project. Downstream work should replace this opaque type by
the genuine identity component (see section 7.1 of the
blueprint). -/
opaque InhomogeneousLorentzGroup : Type

/-- A `Group` instance on the placeholder `InhomogeneousLorentzGroup`. -/
noncomputable instance : Group InhomogeneousLorentzGroup := sorry

/-- A placeholder `MulAction` of the inhomogeneous Lorentz group on
the carrier of standard Minkowski spacetime. -/
noncomputable instance :
    MulAction InhomogeneousLorentzGroup StandardMinkowskiSpacetime.Carrier :=
  sorry

/--
**Axiom 5 (Lorentz Covariance).** A local net `U` is *Lorentz
covariant* if the inhomogeneous Lorentz group acts on the assignment
`B ↦ U.algebra B` and the action

(1) sends the identity element of the Lorentz group to the identity
    automorphism,
(2) is multiplicative in the group element, i.e.
    `α (L' · L) = α L' ∘ α L`, and
(3) *commutes with isotony*.

Concretely, there exist:

* for every group element `L : InhomogeneousLorentzGroup` and every
  Alexandrov-basis set `B`, a `*`-algebra equivalence
  `α L B : U.algebra B ≃⋆ₐ[ℂ] U.algebra (L • B)`;
* for every inclusion `B₁ ⊆ B₂` of basis sets, a choice of
  isotony-witness unital `*`-monomorphism
  `ι B₁ B₂ : U.algebra B₁ →⋆ₐ[ℂ] U.algebra B₂`;

such that

(1) [identity] for every basis set `B` and every `a : U.algebra B`,
    `α 1 B a = a` (modulo the canonical identification
    `U.algebra (1 • B) = U.algebra B` coming from `one_smul`);

(2) [composition] for every pair `L, L' : InhomogeneousLorentzGroup`,
    every basis set `B` and every `a : U.algebra B`,
    `α (L' * L) B a = α L' (L • B) (α L B a)` (modulo the canonical
    identification `U.algebra ((L' * L) • B) = U.algebra (L' • (L • B))`
    coming from `mul_smul`); and

(3) [isotony] for every `L`, every inclusion `B₁ ⊆ B₂`, and every
    element `a : U.algebra B₁`, the action of `L` commutes with the
    isotony inclusion:
    `α L B₂ (ι B₁ B₂ a) = ι' (L • B₁) (L • B₂) (α L B₁ a)`,
    where `ι'` is the isotony-witness arrow for `L • B₁ ⊆ L • B₂`
    (which holds because `L • _` preserves set inclusions).

The cross-fiber identifications in conditions (1) and (2) are
implemented as `Eq.mpr` of the obvious congruence
`U.algebra _ = U.algebra _` produced from `one_smul`/`mul_smul`.

Blueprint reference: `def:lorentz-covariance`.
-/
def LorentzCovariance (U : LocalNet) : Prop :=
  ∃ (α : ∀ (L : InhomogeneousLorentzGroup)
          (B : Set StandardMinkowskiSpacetime.Carrier),
        StarAlgEquiv ℂ (U.algebra B)
          (U.algebra ((L • B : Set StandardMinkowskiSpacetime.Carrier))))
    (ι : ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄,
          IsAlexandrovBasisSet B₁ → IsAlexandrovBasisSet B₂ →
          B₁ ⊆ B₂ → StarAlgHom ℂ (U.algebra B₁) (U.algebra B₂)),
      (∀ ⦃B₁ B₂⦄ (hB₁ : IsAlexandrovBasisSet B₁)
         (hB₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂),
          Function.Injective (ι hB₁ hB₂ h)) ∧
      -- (1) Identity: α 1 B a = a, modulo `one_smul : (1 : G) • B = B`.
      (∀ (B : Set StandardMinkowskiSpacetime.Carrier) (a : U.algebra B),
          (α (1 : InhomogeneousLorentzGroup) B :
              U.algebra B → U.algebra ((1 : InhomogeneousLorentzGroup) • B)) a
            = (congrArg U.algebra
                (one_smul InhomogeneousLorentzGroup B).symm).mp a) ∧
      -- (2) Composition: α (L' * L) B a = α L' (L • B) (α L B a), modulo
      -- `mul_smul : (L' * L) • B = L' • (L • B)`.
      (∀ (L L' : InhomogeneousLorentzGroup)
         (B : Set StandardMinkowskiSpacetime.Carrier) (a : U.algebra B),
          (α (L' * L) B : U.algebra B → U.algebra ((L' * L) • B)) a
            = (congrArg U.algebra (mul_smul L' L B).symm).mp
                ((α L' (L • B) : U.algebra (L • B) → U.algebra (L' • (L • B)))
                  ((α L B : U.algebra B → U.algebra (L • B)) a))) ∧
      -- (3) The action commutes with isotony (already in the original predicate).
      ∀ (L : InhomogeneousLorentzGroup)
        ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
        (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
        (h : B₁ ⊆ B₂)
        (hLB₁ : IsAlexandrovBasisSet (L • B₁))
        (hLB₂ : IsAlexandrovBasisSet (L • B₂))
        (hL : (L • B₁ : Set _) ⊆ L • B₂)
        (a : U.algebra B₁),
          (α L B₂ : U.algebra B₂ → U.algebra (L • B₂)) (ι hB₁ hB₂ h a)
            = ι hLB₁ hLB₂ hL ((α L B₁ : U.algebra B₁ → U.algebra (L • B₁)) a)

end HaagKastler
end AQFT
end Physicslib4
