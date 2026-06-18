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
axioms, section 10.3 of the AQFT-in-Lean blueprint):

> The inhomogeneous Lorentz group `𝓛` (more precisely, its identity
> component; see section 7.1 of the blueprint) acts on the
> assignment `B ↦ 𝔘(B)`. For every `L ∈ 𝓛`, there is a
> `*`-isomorphism `αL B : 𝔘(B) ≃⋆ₐ[ℂ] 𝔘(L·B)` such that the action
> commutes with isotony, in the sense that for every inclusion
> `B₁ ⊆ B₂` of basis sets the obvious diagram of inclusion arrows
> and `αL`-arrows commutes.

## Main definitions

* `Physicslib4.AQFT.HaagKastler.InhomogeneousLorentzGroup`: the
  identity component of the inhomogeneous Lorentz group acting on
  Minkowski spacetime, modelled as the set of pairs `(L, t)` where
  `L : V ≃ₗ[ℝ] V` is a linear automorphism of the spacetime
  carrier `V` lying in `SO(1,3)↑` (preserves the Minkowski form,
  has determinant `1`, and preserves the future time direction)
  and `t : V` is a translation. The group operation is composition
  of the affine maps `x ↦ L x + t`.

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

* The "linear" component is restricted to the orthochronous proper
  Lorentz subgroup `SO(1,3)↑` of `ℝ`-linear automorphisms of
  `StandardMinkowskiSpacetime.Carrier`: those preserving the
  Minkowski form, with determinant `+1`, and preserving the future
  time direction. Closure of the orthochronous condition under
  composition and inversion is provided by
  `Physicslib4.isOrthochronous_trans` and
  `Physicslib4.isOrthochronous_symm` in `Spacetime/Minkowski.lean`,
  proved via the reverse Cauchy-Schwarz inequality on the Minkowski
  form.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4
open scoped Pointwise

/-- The identity component of the inhomogeneous Lorentz group
acting on Minkowski spacetime, as the set of pairs `(L, t)` where
`L` is an `ℝ`-linear automorphism of the spacetime carrier lying
in `SO(1,3)↑` (Lorentz, proper, orthochronous) and `t` is a
translation vector. The group law is composition of the affine
maps `x ↦ L x + t`. -/
structure InhomogeneousLorentzGroup where
  /-- The "Lorentz part": an `ℝ`-linear automorphism of the
  Minkowski spacetime carrier. -/
  linear : StandardMinkowskiSpacetime.Carrier ≃ₗ[ℝ]
              StandardMinkowskiSpacetime.Carrier
  /-- The translation part: a vector in the spacetime carrier. -/
  translation : StandardMinkowskiSpacetime.Carrier
  /-- The linear part preserves the Minkowski form. -/
  isLorentz : IsLorentz linear
  /-- The linear part is proper (determinant `1`). -/
  isProper : IsProper linear
  /-- The linear part is orthochronous (preserves the direction of time). -/
  isOrthochronous : IsOrthochronous linear

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
      translation := a.translation + a.linear b.translation
      isLorentz := isLorentz_trans b.isLorentz a.isLorentz
      isProper := isProper_trans b.isProper a.isProper
      isOrthochronous :=
        isOrthochronous_trans b.isLorentz b.isOrthochronous
          a.isLorentz a.isOrthochronous }
  one :=
    { linear := LinearEquiv.refl ℝ _
      translation := 0
      isLorentz := isLorentz_refl
      isProper := isProper_refl
      isOrthochronous := isOrthochronous_refl }
  inv a :=
    { linear := a.linear.symm
      translation := -a.linear.symm a.translation
      isLorentz := isLorentz_symm a.isLorentz
      isProper := isProper_symm a.isProper
      isOrthochronous := isOrthochronous_symm a.isLorentz a.isOrthochronous }
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

/-- The translation part of the action cancels on differences: the displacement
between two points is transformed by the *linear* part alone. -/
theorem smul_sub_smul (g : InhomogeneousLorentzGroup)
    (x y : StandardMinkowskiSpacetime.Carrier) :
    g • x - g • y = g.linear (x - y) := by
  change (g.linear x + g.translation) - (g.linear y + g.translation)
      = g.linear (x - y)
  rw [map_sub]
  abel

/-- **The inhomogeneous Lorentz group acts by isometries of the Minkowski
form.** Since the translation part cancels on differences and the linear part
is Lorentz, the Minkowski inner product of displacements is preserved. -/
theorem minkowskiForm_smul_sub_smul (g : InhomogeneousLorentzGroup)
    (x y z w : StandardMinkowskiSpacetime.Carrier) :
    minkowskiForm (g • x - g • y) (g • z - g • w)
      = minkowskiForm (x - y) (z - w) := by
  rw [smul_sub_smul, smul_sub_smul]
  exact g.isLorentz (x - y) (z - w)

/-- The *Minkowski interval* between two events is invariant under the
inhomogeneous Lorentz group: `‖g • x - g • y‖²_M = ‖x - y‖²_M`. This is the
diagonal case of `minkowskiForm_smul_sub_smul`. -/
theorem minkowskiForm_smul_sub_self (g : InhomogeneousLorentzGroup)
    (x y : StandardMinkowskiSpacetime.Carrier) :
    minkowskiForm (g • x - g • y) (g • x - g • y)
      = minkowskiForm (x - y) (x - y) :=
  minkowskiForm_smul_sub_smul g x y x y

/-- The action preserves *timelike separation*: `g • x` and `g • y` are
timelike-separated (negative Minkowski interval) iff `x` and `y` are. -/
theorem timelike_separated_smul_iff (g : InhomogeneousLorentzGroup)
    (x y : StandardMinkowskiSpacetime.Carrier) :
    minkowskiForm (g • x - g • y) (g • x - g • y) < 0
      ↔ minkowskiForm (x - y) (x - y) < 0 := by
  rw [minkowskiForm_smul_sub_self]

/-- The action preserves *spacelike separation*: `g • x` and `g • y` are
spacelike-separated (positive Minkowski interval) iff `x` and `y` are. -/
theorem spacelike_separated_smul_iff (g : InhomogeneousLorentzGroup)
    (x y : StandardMinkowskiSpacetime.Carrier) :
    0 < minkowskiForm (g • x - g • y) (g • x - g • y)
      ↔ 0 < minkowskiForm (x - y) (x - y) := by
  rw [minkowskiForm_smul_sub_self]

/-- The action preserves *null separation*: `g • x` and `g • y` are
null-separated (zero Minkowski interval) iff `x` and `y` are. -/
theorem null_separated_smul_iff (g : InhomogeneousLorentzGroup)
    (x y : StandardMinkowskiSpacetime.Carrier) :
    minkowskiForm (g • x - g • y) (g • x - g • y) = 0
      ↔ minkowskiForm (x - y) (x - y) = 0 := by
  rw [minkowskiForm_smul_sub_self]

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
