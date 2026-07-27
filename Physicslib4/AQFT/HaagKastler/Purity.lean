/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.Net
import Physicslib4.GNS.RadonNikodym
import Physicslib4.GNS.ExtremeState
import Physicslib4.GNS.Covariance

/-!
# Purity of states on the quasilocal algebra

The canonical quasilocal algebra `𝔘` of a Minkowski Haag-Kastler net is a unital
C*-algebra, so the abstract characterizations of purity apply to it. This file
registers them for `𝔘`:

* a state on `𝔘` is pure iff it is an extreme point of the state space;
* a state on `𝔘` is pure iff its GNS representation is irreducible.

Unlike the curved setting, Minkowski spacetime has a single global quasilocal
algebra `𝔘`, so these are statements about its global state space - the natural
home for the vacuum and other distinguished states.

## Main results

* `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.pure_iff_extreme`
* `Physicslib4.AQFT.HaagKastler.HaagKastlerNet.exists_gns_pure_iff_irreducible`
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler
namespace HaagKastlerNet

open Physicslib4.GNS
open scoped InnerProductSpace Pointwise

variable (N : HaagKastlerNet)

/-- **Pure ⟺ extreme point for the quasilocal algebra.** A state `ω` on the
canonical quasilocal algebra `𝔘` of a Minkowski Haag-Kastler net is pure if and
only if it is an extreme point of the state space of `𝔘`. This is the abstract
equivalence `isPure_iff_isExtremePoint` applied to the C*-algebra `𝔘`. -/
theorem pure_iff_extreme (ω : State N.quasilocal.carrier) :
    IsPure ω ↔ ω.IsExtremePoint :=
  isPure_iff_isExtremePoint ω

/-- **Pure ⟺ irreducible GNS representation for the quasilocal algebra.** For a
state `ω` on the quasilocal algebra `𝔘`, there is a GNS triple `(H, π, Ω)`
reproducing `ω` in which `ω` is pure if and only if the representation `π` is
irreducible (its commutant is trivial). This combines the GNS construction with
the abstract `isPure_iff_isIrreducible`. -/
theorem exists_gns_pure_iff_irreducible (ω : State N.quasilocal.carrier) :
    ∃ (H : Type)
      (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        IsCyclicVector π Ω ∧
        (∀ a : N.quasilocal.carrier, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (IsPure ω ↔ IsIrreducible π) := by
  obtain ⟨H, i1, i2, i3, π, Ω, hcyc, hrep, _⟩ := gns_construction ω
  exact ⟨H, i1, i2, i3, π, Ω, hcyc, hrep, isPure_iff_isIrreducible hcyc hrep⟩

/-! ### GNS covariance for the local algebras -/

section Covariance

variable (L : InhomogeneousLorentzGroup) (B : Set StandardMinkowskiSpacetime.Carrier)
  (ω : State (N.algebra (L • B)))
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  (π₁ : N.algebra B →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (Ω₁ : H₁)
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  (π₂ : N.algebra (L • B) →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)) (Ω₂ : H₂)

/-- **GNS covariance for local algebras.** The Axiom 5 covariance equivalence
`α_L : 𝔘(B) ≃⋆ₐ[ℂ] 𝔘(L·B)` is a `*`-isomorphism of local algebras, so a cyclic
representation of `𝔘(B)` reproducing the pullback state `ω ∘ α_L` is unitarily
equivalent to `π_ω ∘ α_L`. -/
theorem unitaryEquiv_gns_covEquiv
    (hcyc₁ : IsCyclicVector π₁ Ω₁)
    (hrep₁ : ∀ a : N.algebra B,
      ((ω.comp (N.covEquiv L B).toStarAlgHom) a : ℂ) = ⟪Ω₁, π₁ a Ω₁⟫_ℂ)
    (hcyc₂ : IsCyclicVector π₂ Ω₂)
    (hrep₂ : ∀ b : N.algebra (L • B), (ω b : ℂ) = ⟪Ω₂, π₂ b Ω₂⟫_ℂ) :
    UnitaryEquiv π₁ (π₂.comp (N.covEquiv L B).toStarAlgHom) :=
  unitaryEquiv_comp_of_gns (N.covEquiv L B) ω π₁ Ω₁ hcyc₁ hrep₁ π₂ Ω₂ hcyc₂ hrep₂

/-- **Irreducibility is constant along the Lorentz orbit of a region.** With the GNS
data above, `π₁` is irreducible exactly when `π₂` is. -/
theorem isIrreducible_iff_gns_covEquiv
    (hcyc₁ : IsCyclicVector π₁ Ω₁)
    (hrep₁ : ∀ a : N.algebra B,
      ((ω.comp (N.covEquiv L B).toStarAlgHom) a : ℂ) = ⟪Ω₁, π₁ a Ω₁⟫_ℂ)
    (hcyc₂ : IsCyclicVector π₂ Ω₂)
    (hrep₂ : ∀ b : N.algebra (L • B), (ω b : ℂ) = ⟪Ω₂, π₂ b Ω₂⟫_ℂ) :
    IsIrreducible π₁ ↔ IsIrreducible π₂ :=
  isIrreducible_iff_of_gns_comp (N.covEquiv L B) ω π₁ Ω₁ hcyc₁ hrep₁ π₂ Ω₂ hcyc₂ hrep₂

/-- **Factoriality is constant along the Lorentz orbit of a region.** With the GNS data
above, `π₁(𝔘(B))''` is a factor exactly when `π₂(𝔘(L·B))''` is. So the superselection
type of a local state is a Lorentz-orbit invariant. -/
theorem isFactor_iff_gns_covEquiv
    (hcyc₁ : IsCyclicVector π₁ Ω₁)
    (hrep₁ : ∀ a : N.algebra B,
      ((ω.comp (N.covEquiv L B).toStarAlgHom) a : ℂ) = ⟪Ω₁, π₁ a Ω₁⟫_ℂ)
    (hcyc₂ : IsCyclicVector π₂ Ω₂)
    (hrep₂ : ∀ b : N.algebra (L • B), (ω b : ℂ) = ⟪Ω₂, π₂ b Ω₂⟫_ℂ) :
    IsFactor (gnsVonNeumann π₁) ↔ IsFactor (gnsVonNeumann π₂) :=
  isFactor_iff_of_gns_comp (N.covEquiv L B) ω π₁ Ω₁ hcyc₁ hrep₁ π₂ Ω₂ hcyc₂ hrep₂

end Covariance

end HaagKastlerNet
end HaagKastler
end AQFT
end Physicslib4
