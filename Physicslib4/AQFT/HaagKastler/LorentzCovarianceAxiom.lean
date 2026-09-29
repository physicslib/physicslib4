/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.Isotony
import Physicslib4.AQFT.HaagKastler.LorentzCovariance
import Physicslib4.Spacetime.LorentzCausality

/-!
# Axiom 5: Lorentz Covariance, the predicate

This file states Axiom 5 (`def:lorentz-covariance`) for a local net and its Axiom 2
isotony family. The inhomogeneous Lorentz group and its action are in
`Physicslib4/AQFT/HaagKastler/LorentzCovariance.lean`. The predicate sits after
`Physicslib4/Spacetime/LorentzCausality.lean` so that condition (3) can use
`isAlexandrovBasisSet_smul`: Lorentz transformations carry Alexandrov basis sets to basis
sets, so the isotony embedding between the images needs no extra hypothesis.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4
open scoped Pointwise

/--
**Axiom 5 (Lorentz Covariance).** A local net `U` is *Lorentz
covariant* if the inhomogeneous Lorentz group acts on the assignment
`B ↦ U.algebra B` and the action

(1) sends the identity element of the Lorentz group to the identity
    automorphism,
(2) is multiplicative in the group element, i.e.
    `α (L' · L) = α L' ∘ α L`, and
(3) *commutes with isotony*.

Concretely, there exists, for every group element
`L : InhomogeneousLorentzGroup` and every Alexandrov-basis set `B`, a
`*`-algebra equivalence `α L B : U.algebra B ≃⋆ₐ[ℂ] U.algebra (L • B)`,
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
    `α L B₂ (i.map a) = i.map (α L B₁ a)`, where the right-hand `i.map`
    is the Axiom 2 embedding for `L • B₁ ⊆ L • B₂`. Neither that inclusion nor
    the fact that `L • B₁` and `L • B₂` are basis sets is a hypothesis: they are
    `Set.smul_set_mono h` and `isAlexandrovBasisSet_smul`. The isotony family `i` is the one of
    Axiom 2, taken as a parameter, not a separately chosen family.

The cross-fiber identifications in conditions (1) and (2) are
implemented as `Eq.mpr` of the obvious congruence
`U.algebra _ = U.algebra _` produced from `one_smul`/`mul_smul`.

Blueprint reference: `def:lorentz-covariance`.
-/
def LorentzCovariance (U : LocalNet) (i : Isotony U) : Prop :=
  ∃ α : ∀ (L : InhomogeneousLorentzGroup)
          (B : Set StandardMinkowskiSpacetime.Carrier),
        StarAlgEquiv ℂ (U.algebra B)
          (U.algebra ((L • B : Set StandardMinkowskiSpacetime.Carrier))),
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
      -- (3) The action commutes with the Axiom 2 isotony family `i`.
      ∀ (L : InhomogeneousLorentzGroup)
        ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
        (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
        (h : B₁ ⊆ B₂) (a : U.algebra B₁),
          (α L B₂ : U.algebra B₂ → U.algebra (L • B₂)) (i.map hB₁ hB₂ h a)
            = i.map (isAlexandrovBasisSet_smul L hB₁) (isAlexandrovBasisSet_smul L hB₂)
                (Set.smul_set_mono h)
                ((α L B₁ : U.algebra B₁ → U.algebra (L • B₁)) a)

end HaagKastler
end AQFT
end Physicslib4
