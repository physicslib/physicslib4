/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.Basic

/-!
# The GNS Construction Theorem

This file states the GNS Construction Theorem from the AQFT-in-Lean blueprint
(section 9.1, label `thrm:gns-construction-theorem`).

Given a state `ω` over a unital C*-algebra `A`, the theorem asserts the
existence of a complex Hilbert space `H_ω`, a *-representation
`π_ω : A →⋆ₐ[ℂ] (H_ω →L[ℂ] H_ω)`, and a cyclic vector `Ω ∈ H_ω` for `π_ω`
such that
* `ω a = ⟪Ω, π_ω a Ω⟫` for every `a : A`, and
* if `ω` is faithful, then `π_ω` is injective.

The triple is also unique up to unitary equivalence, which we state as a
separate theorem `gns_unique` because expressing the uniqueness clause as a
conjunct inside the existence statement above is awkward (the two Hilbert
spaces being compared live in different types).

## Main statements

* `Physicslib4.GNS.gns_construction`: existence of the GNS triple `(H, π, Ω)`,
  with the cyclicity, reproducing-formula, and faithfulness clauses bundled
  inside a single existential.
* `Physicslib4.GNS.gns_unique`: uniqueness of the GNS triple up to a unitary
  equivalence intertwining the representations and sending the cyclic vector
  to the cyclic vector.

## Notes

The Hilbert space `H` is existentially quantified in `Type` (rather than
`Type*`) to avoid the usual universe-polymorphism issues that arise when
existentially quantifying over a type variable. In practice the GNS Hilbert
space is constructed as a completion of a quotient of `A`, so this is not
a real restriction provided one is willing to work universe-polymorphically
in `A`'s universe; the precise universe placement is left to the eventual
proof.
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder
open scoped InnerProductSpace

/--
**GNS Construction Theorem** (blueprint label `thrm:gns-construction-theorem`).

Let `ω` be a state over a unital C*-algebra `A`. Then there exist a complex
Hilbert space `H`, a *-representation `π : A →⋆ₐ[ℂ] (H →L[ℂ] H)`, and a
cyclic vector `Ω : H` for `π`, such that the reproducing formula
`ω a = ⟪Ω, π a Ω⟫_ℂ` holds for every `a : A`. Moreover, if `ω` is faithful
then `π` is injective.

Uniqueness up to unitary equivalence is stated separately as `gns_unique`.
-/
theorem gns_construction {A : Type*} [CStarAlgebra A] (ω : State A) :
    ∃ (H : Type)
      (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        IsCyclicVector π Ω ∧
        (∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        (ω.IsFaithful → Function.Injective π) := by
  sorry

/--
**Uniqueness of the GNS triple, up to unitary equivalence**
(blueprint label `thrm:gns-construction-theorem`, uniqueness clause).

Suppose two GNS-type triples `(H₁, π₁, Ω₁)` and `(H₂, π₂, Ω₂)` are both
associated to the same state `ω` on the unital C*-algebra `A`, in the sense
that each is a cyclic *-representation reproducing `ω` via its inner
product. Then there exists a unitary (linear isometric) equivalence
`U : H₁ ≃ₗᵢ[ℂ] H₂` intertwining the representations
(`U (π₁ a x) = π₂ a (U x)` for all `a` and `x`) and sending `Ω₁` to `Ω₂`.
-/
theorem gns_unique {A : Type*} [CStarAlgebra A] (ω : State A)
    {H₁ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    (π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (Ω₁ : H₁)
    (hcyc₁ : IsCyclicVector π₁ Ω₁)
    (hrep₁ : ∀ a : A, (ω a : ℂ) = ⟪Ω₁, π₁ a Ω₁⟫_ℂ)
    {H₂ : Type*}
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)) (Ω₂ : H₂)
    (hcyc₂ : IsCyclicVector π₂ Ω₂)
    (hrep₂ : ∀ a : A, (ω a : ℂ) = ⟪Ω₂, π₂ a Ω₂⟫_ℂ) :
    ∃ U : H₁ ≃ₗᵢ[ℂ] H₂,
      U Ω₁ = Ω₂ ∧ ∀ (a : A) (x : H₁), U (π₁ a x) = π₂ a (U x) := by
  sorry

end GNS
end Physicslib4
