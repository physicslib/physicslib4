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
Axiom 5 (Lorentz covariance): the Poincaré group acts on the net, compatibly with isotony.

The axiom asks for a unital *-isomorphism α_L : 𝔘(B) → 𝔘(LB) for every element L of the identity
component of the Poincaré group (`InhomogeneousLorentzGroup`) and every region B, where LB is the
image of B under L, such that

1. α_1 is the identity;
2. α_(L'L) = α_L' ∘ α_L; and
3. α_L commutes with isotony: α_L ∘ i(B₁, B₂) = i(LB₁, LB₂) ∘ α_L for diamonds B₁ ⊆ B₂, where i
   is the isotony family of Axiom 2.

In condition 3, LB₁ and LB₂ are diamonds with LB₁ ⊆ LB₂ because L preserves chronological
precedence (`isAlexandrovBasisSet_smul`, `Set.smul_set_mono`), so no further hypothesis is
needed. The predicate takes the isotony family as a parameter, so the action respects the net's own
embeddings.
`HaagKastlerNet.covEquiv` chooses the maps α_L, and `HaagKastlerNet.action` extends them to
automorphisms of the quasilocal algebra.

Implementation note: 𝔘(1B) and 𝔘(B), and 𝔘((L'L)B) and 𝔘(L'(LB)), are different types that are
equal only propositionally, so conditions 1 and 2 transport along those equalities (`one_smul`,
`mul_smul`) with `Eq.mp`.

Blueprint: def:lorentz-covariance
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
