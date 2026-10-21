/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.IdentityComponent
import Physicslib4.Spacetime.CrossMetricIsometry

/-!
# General covariance: nets on pullback-related metrics

This file formalises Section 10.8 of the AQFT-in-Lean blueprint
(`sections/sec10/general-covariance-in-curved-spacetime`): the notion of an
*equivalence of Haag-Kastler nets* along a basis-set-preserving bijection of
carriers, and the postulate of *general covariance* for a net theory.

## Main definitions

* `Physicslib4.AQFT.HaagKastlerCurved.NetEquivalence`
  (`def:net-equivalence-in-curved-spacetime`): a chosen family of unital
  `*`-isomorphisms `Θ_B : 𝔘₁(B) ≃⋆ₐ[ℂ] 𝔘₂(e(B))`, natural with respect to the
  Axiom 2 isotony embeddings of the two nets.
* `Physicslib4.AQFT.HaagKastlerCurved.NetTheory`
  (`def:general-covariance-in-curved-spacetime`, first half): a section of the
  family of Haag-Kastler nets over geometric Lorentzian spacetimes.
* `Physicslib4.AQFT.HaagKastlerCurved.IsGenerallyCovariant`
  (`def:general-covariance-in-curved-spacetime`): the postulate that a net
  theory assigns equivalent nets to diffeomorphism-related backgrounds.

## Modelling notes

* **The carriers are related by data, not by an equality.** An abstract
  `LorentzianSpacetime` carries its point set as a field, so "two spacetimes on
  a common carrier" would be an assertion of *type* equality. `NetEquivalence`
  therefore takes a bijection `e : M₁.Carrier ≃ M₂.Carrier` as data; the
  geometric case supplies the relabelling diffeomorphism, which is a bijection
  of the carrier with itself.
* **Only the basis-set condition on `e` is needed.** `NetEquivalence` mentions
  neither metrics nor isometries: all that is required of `e` is the hypothesis
  `he`, that it carries basis sets to basis sets. The geometric input is
  supplied at the point of use by
  `Spacetime.LorentzianSpacetime.toAbstractIdentityComponent_pullback_isBasisSet`, which is
  `Spacetime.pullback_alexandrovBasis_image`
  (`lmm:cross-metric-isometry-preserves-basis-sets` applied to `ψ` read as a
  cross-metric isometry `ψ^*(M,g) → (M,g)`).
* **`Θ` is data and the vertical arrows come for free.** The naturality square
  refers to chosen maps on all four sides, so `Θ` is a structure field rather
  than an existence statement; the vertical arrows are the Axiom 2 family
  `HaagKastlerNet.commIsotony` of the two nets, which is already chosen data.
* **General covariance is a property of the section, not a sixth axiom.**
  Axioms 1-5 constrain a single net over a fixed spacetime, whereas general
  covariance relates two nets over two spacetimes. Unlike Axiom 5, no
  restriction to diffeomorphisms connected to the identity is imposed: the
  equivalence compares two nets rather than making a group act on one.
-/

namespace Physicslib4

namespace Spacetime

namespace LorentzianSpacetime

/--
The relabelling bijection of general covariance: a diffeomorphism ψ of M, read as a map from the
points of ψ*L to the points of L.

The pullback ψ*L has the same manifold as L, with the pulled-back metric ψ*g and time orientation
ψ*t. As a map from ψ*L to L, the diffeomorphism ψ is an isometry, and it carries the causal
diamonds of ψ*L to those of L (`toAbstractIdentityComponent_pullback_isBasisSet`). It is ψ, not
its inverse, that does this. General covariance compares the nets over ψ*L and over L along this
bijection.

Implementation note: the two carriers are definitionally equal (`pullback` changes only the
metric and the time orientation), but the blueprint relates the two spacetimes by data rather
than by a type equality, and this is that datum. The type is stated with `.Carrier` rather than
`.toAbstractIdentityComponent.Carrier`: the two are definitionally equal, but
`toAbstractIdentityComponent_Carrier` is a `simp` lemma, so only the former leaves
`pullbackCarrierEquiv_apply` in simp-normal form.

Blueprint: def:general-covariance-in-curved-spacetime
-/
noncomputable def pullbackCarrierEquiv (L : LorentzianSpacetime)
    (ψ : Diffeo L.toSpacetime L.toSpacetime) :
    (L.pullback ψ).Carrier ≃ L.Carrier :=
  (L.toSpacetime.pullbackDiffeo ψ).toEquiv

/-- The relabelling bijection of `pullbackCarrierEquiv` is `ψ` itself. -/
@[simp] theorem pullbackCarrierEquiv_apply (L : LorentzianSpacetime)
    (ψ : Diffeo L.toSpacetime L.toSpacetime) :
    ⇑(L.pullbackCarrierEquiv ψ) = ψ := rfl

/--
**The relabelling bijection carries basis sets to basis sets.**

The basis-set hypothesis that `NetEquivalence` requires of `e`, discharged in
the geometric situation of `def:general-covariance-in-curved-spacetime`: an
Alexandrov diamond of `ψ^*L` is carried by `ψ` to an Alexandrov diamond of `L`.

This is `Spacetime.pullback_alexandrovBasis_image`
(`lmm:cross-metric-isometry-preserves-basis-sets` applied to `ψ` viewed as a
cross-metric isometry from `ψ^*(M,g)` to `(M,g)`, whose two-sided orientation
hypothesis is `lmm:pullback-preserves-future-orientation`), read through the
bridge `toAbstractIdentityComponent`.
-/
theorem toAbstractIdentityComponent_pullback_isBasisSet (L : LorentzianSpacetime)
    (ψ : Diffeo L.toSpacetime L.toSpacetime) :
    ∀ ⦃B : Set (L.pullback ψ).toAbstractIdentityComponent.Carrier⦄,
      (L.pullback ψ).toAbstractIdentityComponent.IsBasisSet B →
        L.toAbstractIdentityComponent.IsBasisSet (⇑(L.pullbackCarrierEquiv ψ) '' B) := by
  intro B hB
  exact Spacetime.pullback_alexandrovBasis_image L.toSpacetime ψ L.timeOrientation hB

end LorentzianSpacetime

end Spacetime

namespace AQFT

namespace HaagKastlerCurved

/--
An equivalence of two Haag–Kastler nets along a bijection e of their spacetimes: *-isomorphisms
Θ_B : 𝔘₁(B) → 𝔘₂(e(B)) compatible with isotony.

Let M₁ and M₂ be spacetimes, e a bijection from the points of M₁ to those of M₂ that maps basis
sets to basis sets (hypothesis `he`), and N₁, N₂ Haag–Kastler nets over M₁ and M₂. An equivalence
of N₁ and N₂ along e chooses, for each basis set B of M₁, a unital *-isomorphism

Θ_B : 𝔘₁(B) → 𝔘₂(e(B)),

which makes sense because e(B) is a basis set of M₂. The isomorphisms must be compatible with the
isotony embeddings i₁ and i₂ of the two nets (`HaagKastlerNet.commIsotony`): whenever B₁ ⊆ B₂ are
basis sets of M₁,

Θ_(B₂) ∘ i₁(B₁, B₂) = i₂(e(B₁), e(B₂)) ∘ Θ_(B₁).

The two nets then describe the same physics, with the region B of M₁ corresponding to the region
e(B) of M₂.

The family Θ is data, not an existence statement, since the square refers to the chosen maps. The
definition mentions no metric and no isometry: all it asks of e is that it carry basis sets to
basis sets. The square is attached to a single inclusion, so no coherence hypothesis is needed;
Axiom 2 carries the identity and composition laws of the embeddings in any case.

Implementation note: the spacetimes are related by the bijection e rather than by an equality of
their carriers, which would be an equality of types and could not be transported along.

Blueprint: def:net-equivalence-in-curved-spacetime
-/
structure NetEquivalence {M₁ M₂ : LorentzianSpacetime}
    (e : M₁.Carrier ≃ M₂.Carrier)
    (he : ∀ ⦃B : Set M₁.Carrier⦄, M₁.IsBasisSet B → M₂.IsBasisSet (⇑e '' B))
    (N₁ : HaagKastlerNet M₁) (N₂ : HaagKastlerNet M₂) where
  /-- The unital *-isomorphism Θ_B : 𝔘₁(B) → 𝔘₂(e(B)), for each basis set B of M₁. -/
  theta : ∀ ⦃B : Set M₁.Carrier⦄, M₁.IsBasisSet B →
    StarAlgEquiv ℂ (N₁.algebra B) (N₂.algebra (⇑e '' B))
  /-- Naturality: with i₁ and i₂ the isotony embeddings of the two nets, every inclusion
  B₁ ⊆ B₂ of basis sets of M₁ gives Θ_(B₂) ∘ i₁(B₁, B₂) = i₂(e(B₁), e(B₂)) ∘ Θ_(B₁). -/
  naturality : ∀ ⦃B₁ B₂ : Set M₁.Carrier⦄ (h₁ : M₁.IsBasisSet B₁)
      (h₂ : M₁.IsBasisSet B₂) (h : B₁ ⊆ B₂) (a : N₁.algebra B₁),
    theta h₂ (N₁.commIsotony h₁ h₂ h a)
      = N₂.commIsotony (he h₁) (he h₂) (Set.image_mono h) (theta h₁ a)

/--
A net theory: a choice of Haag–Kastler net 𝔘_L over every geometric Lorentzian spacetime L.

A quantum field theory in curved spacetime is not one net but a rule assigning a net to each
background. Here the rule is a function L ↦ 𝔘_L from geometric Lorentzian spacetimes to nets over
the abstract interfaces they induce (`toAbstractIdentityComponent`). Quantifying over all
Lorentzian spacetimes, rather than over the metrics on one fixed manifold, is what makes general
covariance (`IsGenerallyCovariant`) a statement about the theory: the pullback of any L is again a
Lorentzian spacetime, so both nets that general covariance compares are values of the same
function.

Implementation note: the spacetimes have their points in `Type`, and the nets of a net theory
share one universe for their local algebras, the universe parameter of `NetTheory`.

Blueprint: def:general-covariance-in-curved-spacetime
-/
abbrev NetTheory :=
  ∀ L : Spacetime.LorentzianSpacetime, HaagKastlerNet L.toAbstractIdentityComponent

/--
General covariance: a net theory assigns equivalent nets to diffeomorphism-related backgrounds.

The gauge group of general relativity is the diffeomorphism group of M, acting on all fields,
the metric included. For a Lorentzian spacetime L with manifold M, metric g and time orientation
t, and a smooth diffeomorphism ψ of M, the pullback ψ*L, with metric ψ*g and time orientation ψ*t,
differs from L only by a relabelling of the points. A net theory 𝔘 is generally covariant when
the nets 𝔘_(ψ*L) and 𝔘_L are equivalent (`NetEquivalence`) for every such L and ψ, along ψ read as
a bijection from the points of ψ*L to those of L (`pullbackCarrierEquiv`). That ψ carries the
diamonds of ψ*L to those of L is `toAbstractIdentityComponent_pullback_isBasisSet`.

This is a postulate, not a consequence of Axioms 1 to 5, which each constrain a single net over a
single spacetime. It encodes Leibniz equivalence, the resolution of the hole argument: the choice
of representative within a diffeomorphism class is gauge and can have no observable consequences.
It is a property of the theory L ↦ 𝔘_L, not an extra field of `HaagKastlerNet`, and it says
nothing about backgrounds that are not related by a diffeomorphism. Unlike Axiom 5, it is not
restricted to diffeomorphisms connected to the identity, since it compares two nets rather than
making a group act on one.

Blueprint: def:general-covariance-in-curved-spacetime
-/
def IsGenerallyCovariant (𝔘 : NetTheory) : Prop :=
  ∀ (L : Spacetime.LorentzianSpacetime)
    (ψ : Spacetime.Diffeo L.toSpacetime L.toSpacetime),
    Nonempty (NetEquivalence (L.pullbackCarrierEquiv ψ)
      (L.toAbstractIdentityComponent_pullback_isBasisSet ψ) (𝔘 (L.pullback ψ)) (𝔘 L))

end HaagKastlerCurved

end AQFT

end Physicslib4
