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

* `Physicslib4.AQFT.HaagKastler.InhomogeneousLorentzGroup`: a
  concrete realisation of the inhomogeneous Lorentz group acting on
  Minkowski spacetime, modelled as the set of pairs
  `(L, t)` where `L : V ≃ₗ[ℝ] V` is a linear automorphism of the
  spacetime carrier `V` and `t : V` is a translation. The group
  operation is composition of the affine maps `x ↦ L x + t`. This
  is the "first-pass" Poincaré group: the genuine identity
  component of the orthochronous Lorentz group lives inside it as
  a subgroup whose `L` lies in `SO(1,3)↑`, and a future refinement
  can restrict to that subgroup.

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

* The "linear" component is taken as the full group of `ℝ`-linear
  automorphisms of `StandardMinkowskiSpacetime.Carrier`. The
  genuine identity component of the orthochronous Lorentz group is
  the subgroup whose linear part preserves the Minkowski metric
  and has positive time orientation; this is the natural next
  refinement.
-/

namespace Physicslib4

/-- Additive-group structure on the Minkowski spacetime carrier,
inherited from `SpacetimeModel = EuclideanSpace ℝ (Fin 4)`. -/
noncomputable instance instAddCommGroupCarrier :
    AddCommGroup StandardMinkowskiSpacetime.Carrier := by
  change AddCommGroup SpacetimeModel
  infer_instance

/-- `ℝ`-module structure on the Minkowski spacetime carrier,
inherited from `SpacetimeModel = EuclideanSpace ℝ (Fin 4)`. -/
noncomputable instance instModuleCarrier :
    Module ℝ StandardMinkowskiSpacetime.Carrier := by
  change Module ℝ SpacetimeModel
  infer_instance

namespace AQFT
namespace HaagKastler

open Physicslib4
open scoped Pointwise

/-- A concrete first-pass realisation of the inhomogeneous Lorentz
group acting on Minkowski spacetime, as the set of pairs `(L, t)`
where `L` is an `ℝ`-linear automorphism of the spacetime carrier
and `t` is a translation vector. The group law is composition of
the affine maps `x ↦ L x + t`.

The genuine identity component of the orthochronous Lorentz group
(restricting `L` to `SO(1,3)↑`) is a subgroup of this type; a
future refinement can substitute the subgroup. -/
structure InhomogeneousLorentzGroup where
  /-- The "Lorentz part": an `ℝ`-linear automorphism of the
  Minkowski spacetime carrier. -/
  linear : StandardMinkowskiSpacetime.Carrier ≃ₗ[ℝ]
              StandardMinkowskiSpacetime.Carrier
  /-- The translation part: a vector in the spacetime carrier. -/
  translation : StandardMinkowskiSpacetime.Carrier

namespace InhomogeneousLorentzGroup

@[ext]
theorem ext {a b : InhomogeneousLorentzGroup}
    (hL : a.linear = b.linear) (ht : a.translation = b.translation) :
    a = b := by
  cases a; cases b; simp_all

/-- Group structure on the inhomogeneous Lorentz group: the product
`(L₁, t₁) * (L₂, t₂) = (L₁ ∘ L₂, t₁ + L₁ t₂)` is the composition
of the affine maps `x ↦ Lᵢ x + tᵢ`. -/
noncomputable instance : Group InhomogeneousLorentzGroup where
  mul a b :=
    { linear := b.linear.trans a.linear
      translation := a.translation + a.linear b.translation }
  one :=
    { linear := LinearEquiv.refl ℝ _
      translation := 0 }
  inv a :=
    { linear := a.linear.symm
      translation := -a.linear.symm a.translation }
  mul_assoc a b c := by
    refine ext ?_ ?_
    · ext x; rfl
    · change (a.translation + a.linear b.translation)
            + (b.linear.trans a.linear) c.translation
          = a.translation
            + a.linear (b.translation + b.linear c.translation)
      rw [LinearEquiv.trans_apply, map_add, add_assoc]
  one_mul a := by
    refine ext ?_ ?_
    · ext x; rfl
    · change (0 : StandardMinkowskiSpacetime.Carrier)
            + (LinearEquiv.refl ℝ _) a.translation
          = a.translation
      simp
  mul_one a := by
    refine ext ?_ ?_
    · ext x; rfl
    · change a.translation + a.linear 0 = a.translation
      simp
  inv_mul_cancel a := by
    refine ext ?_ ?_
    · ext x
      change a.linear.symm (a.linear x) = x
      simp
    · change -a.linear.symm a.translation + a.linear.symm a.translation = 0
      simp

/-- The `MulAction` of the inhomogeneous Lorentz group on the
Minkowski spacetime carrier: `(L, t) • x = L x + t`. -/
noncomputable instance :
    MulAction InhomogeneousLorentzGroup StandardMinkowskiSpacetime.Carrier where
  smul g x := g.linear x + g.translation
  one_smul x := by
    change (LinearEquiv.refl ℝ _) x + (0 : StandardMinkowskiSpacetime.Carrier) = x
    simp
  mul_smul g h x := by
    change (h.linear.trans g.linear) x
          + (g.translation + g.linear h.translation)
        = g.linear (h.linear x + h.translation) + g.translation
    rw [LinearEquiv.trans_apply, map_add]
    abel

end InhomogeneousLorentzGroup

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
