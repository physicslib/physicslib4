/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.Net

/-!
# Lifting the covariance action to the quasilocal algebra

The Lorentz action on a Haag-Kastler net is given *fiberwise* by the
covariance equivalences `α_L : 𝔘(B) ≃⋆ₐ[ℂ] 𝔘(L·B)`
(`HaagKastlerNet.covEquiv`). To obtain a single dynamical system one wants
to *lift* this fiberwise action to a `*`-automorphism `β_L` of the quasilocal
algebra `𝔘` (the ambient C*-algebra of a `QuasilocalAlgebra`), intertwining
the local embeddings: `β_L (ι_B a) = ι_{L·B} (α_L a)`.

This file isolates the *specification* of such a lift and proves it is
**unique**. The local embeddings `ι_B` have dense union in `𝔘`, and a
`*`-automorphism of a C*-algebra is continuous; hence a lift is determined by
its action on the generators, so at most one lift exists for each `L`.

## Main definitions

* `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.QuasilocalLift`: a `*`-automorphism
  of the quasilocal algebra intertwining the fiberwise action of `L`.

## Main results

* `QuasilocalLift.unique`: any two lifts of the same `L` have equal underlying
  automorphism.
* `instSubsingletonQuasilocalLift`: consequently the type of lifts is a
  subsingleton.

## Notes

This is the *uniqueness* half of the lifting problem. **Existence** - actually
constructing `β_L` by extending the densely-defined intertwiner to the
completion - requires the union of local images to form a `*`-subalgebra and a
uniformly-continuous-extension argument, and is deferred.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4
open scoped Pointwise

namespace HaagKastlerNet

variable (N : HaagKastlerNet)

/--
A *lift* of the fiberwise covariance action of `L` to a quasilocal algebra
`Q`: a `*`-automorphism `β` of the ambient algebra `Q.carrier` that
intertwines the covariance equivalence `α_L` with the local embeddings, i.e.
`β (ι_B a) = ι_{L·B} (α_L a)` for every Alexandrov-basis set `B`.
-/
structure QuasilocalLift (Q : QuasilocalAlgebra N.U)
    (L : InhomogeneousLorentzGroup) where
  /-- The `*`-automorphism of the quasilocal algebra implementing `L`. -/
  β : Q.carrier ≃⋆ₐ[ℂ] Q.carrier
  /-- `β` intertwines the fiberwise action `α_L` with the local embeddings. -/
  intertwines : ∀ ⦃B : Set StandardMinkowskiSpacetime.Carrier⦄,
    IsAlexandrovBasisSet B → ∀ a : N.algebra B,
      β (Q.ι B a) = Q.ι (L • B) (N.covEquiv L B a)

variable {N}

/-- **Uniqueness of the lift.** Two lifts of the same Lorentz transformation
have the same underlying automorphism: they agree on the dense union of the
local images, and `*`-automorphisms of a C*-algebra are continuous. -/
theorem QuasilocalLift.unique {Q : QuasilocalAlgebra N.U}
    {L : InhomogeneousLorentzGroup} (l₁ l₂ : N.QuasilocalLift Q L) :
    l₁.β = l₂.β := by
  apply DFunLike.coe_injective
  refine Continuous.ext_on Q.dense_range
    (NonUnitalStarAlgHom.isometry l₁.β l₁.β.injective).continuous
    (NonUnitalStarAlgHom.isometry l₂.β l₂.β.injective).continuous ?_
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_range] at hx
  obtain ⟨B, hB, a, rfl⟩ := hx
  change l₁.β (Q.ι B a) = l₂.β (Q.ι B a)
  rw [l₁.intertwines hB a, l₂.intertwines hB a]

/-- The type of lifts of a fixed `L` is a subsingleton: a lift is determined by
its underlying automorphism (`QuasilocalLift.unique`), and the intertwining
field is a proposition. -/
instance instSubsingletonQuasilocalLift {Q : QuasilocalAlgebra N.U}
    {L : InhomogeneousLorentzGroup} : Subsingleton (N.QuasilocalLift Q L) where
  allEq l₁ l₂ := by
    have h := QuasilocalLift.unique l₁ l₂
    cases l₁; cases l₂
    simp only [QuasilocalLift.mk.injEq]
    exact h

end HaagKastlerNet

end HaagKastler
end AQFT
end Physicslib4
