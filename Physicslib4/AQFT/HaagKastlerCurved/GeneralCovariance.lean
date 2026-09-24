/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.Concrete
import Physicslib4.Spacetime.CrossMetricIsometry

/-!
# General covariance: nets on pullback-related metrics

This file formalises Section 10.7 of the AQFT-in-Lean blueprint
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
  `Spacetime.LorentzianSpacetime.toAbstract_pullback_isBasisSet`, which is
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
The relabelling bijection of carriers underlying general covariance: the
diffeomorphism `ψ`, read as a bijection from the carrier of the pullback
Lorentzian spacetime `ψ^*L` to the carrier of `L`.

The two carriers are definitionally equal (`pullback` changes only the metric
and the time orientation), but the blueprint insists that the two spacetimes be
related by *data* rather than by a type equality; this is that datum.

Stated with `.Carrier` rather than `.toAbstract.Carrier`: the two are
definitionally equal, but `toAbstract_Carrier` is a `simp` lemma, so only the
former leaves `pullbackCarrierEquiv_apply` in simp-normal form.
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
bridge `toAbstract`.
-/
theorem toAbstract_pullback_isBasisSet (L : LorentzianSpacetime)
    (ψ : Diffeo L.toSpacetime L.toSpacetime) :
    ∀ ⦃B : Set (L.pullback ψ).toAbstract.Carrier⦄,
      (L.pullback ψ).toAbstract.IsBasisSet B →
        L.toAbstract.IsBasisSet (⇑(L.pullbackCarrierEquiv ψ) '' B) := by
  intro B hB
  exact Spacetime.pullback_alexandrovBasis_image L.toSpacetime ψ L.timeOrientation hB

end LorentzianSpacetime

end Spacetime

namespace AQFT

namespace HaagKastlerCurved

/--
**Equivalence of Haag-Kastler nets** (`def:net-equivalence-in-curved-spacetime`).

Let `M₁`, `M₂` be abstract Lorentzian spacetimes, let `e` be a bijection of
their carriers which maps basis sets to basis sets (hypothesis `he`), and let
`N₁`, `N₂` be Haag-Kastler nets over `M₁` and `M₂`. An *equivalence of nets
along `e`* is a chosen family of unital `*`-isomorphisms

`Θ_B : 𝔘₁(B) ≃⋆ₐ[ℂ] 𝔘₂(e(B))`,

one for each basis set `B` of `M₁` — well typed precisely because of `he` — such
that for every inclusion `B₁ ⊆ B₂` of basis sets of `M₁` the square formed with
the Axiom 2 isotony embeddings `HaagKastlerNet.commIsotony` of the two nets
commutes.

Naturality needs no separate coherence hypothesis: the square is attached to a
single inclusion and never composes two embeddings, and in any case Axiom 2
carries the identity and composition laws itself.

Blueprint reference: `def:net-equivalence-in-curved-spacetime`.
-/
structure NetEquivalence {M₁ M₂ : LorentzianSpacetime}
    (e : M₁.Carrier ≃ M₂.Carrier)
    (he : ∀ ⦃B : Set M₁.Carrier⦄, M₁.IsBasisSet B → M₂.IsBasisSet (⇑e '' B))
    (N₁ : HaagKastlerNet M₁) (N₂ : HaagKastlerNet M₂) where
  /-- The chosen unital `*`-isomorphism `Θ_B : 𝔘₁(B) ≃⋆ₐ[ℂ] 𝔘₂(e(B))`, one for
  each basis set `B` of `M₁`. -/
  theta : ∀ ⦃B : Set M₁.Carrier⦄, M₁.IsBasisSet B →
    StarAlgEquiv ℂ (N₁.algebra B) (N₂.algebra (⇑e '' B))
  /-- **Naturality.** For basis sets `B₁ ⊆ B₂` of `M₁`, the square formed by
  `Θ_{B₁}`, `Θ_{B₂}` and the two nets' isotony embeddings commutes. -/
  naturality : ∀ ⦃B₁ B₂ : Set M₁.Carrier⦄ (h₁ : M₁.IsBasisSet B₁)
      (h₂ : M₁.IsBasisSet B₂) (h : B₁ ⊆ B₂) (a : N₁.algebra B₁),
    theta h₂ (N₁.commIsotony h₁ h₂ h a)
      = N₂.commIsotony (he h₁) (he h₂) (Set.image_mono h) (theta h₁ a)

/--
**A net theory** (`def:general-covariance-in-curved-spacetime`, first half): a
section of the family of Haag-Kastler nets over geometric Lorentzian
spacetimes, assigning to every `L` a net `𝔘_L` over the abstract spacetime
interface `L.toAbstract` it induces.

Quantifying over *all* Lorentzian spacetimes, rather than over the metrics on
one fixed carrier, is what makes general covariance a statement about the
theory: the pullback of any `L` is again an object of the same family, so both
sides of the equivalence are always in scope.
-/
abbrev NetTheory :=
  ∀ L : Spacetime.LorentzianSpacetime, HaagKastlerNet L.toAbstract

/--
**General covariance** (`def:general-covariance-in-curved-spacetime`).

A net theory `𝔘` is *generally covariant* when, for every geometric Lorentzian
spacetime `L` with underlying spacetime `(M, g, t)` and every `C^∞`
diffeomorphism `ψ` of `M`, the nets `𝔘_{ψ^*L}` and `𝔘_L` are equivalent in the
sense of `NetEquivalence` along the relabelling bijection `e := ψ` of the common
carrier.

This is a *postulate*, encoding Leibniz equivalence: the choice of
representative within a diffeomorphism class is gauge and can have no
observable consequences. It is a property of the section `L ↦ 𝔘_L`, not an
extra field of `HaagKastlerNet`, and it says nothing about backgrounds that are
not diffeomorphism-related.

Blueprint reference: `def:general-covariance-in-curved-spacetime`.
-/
def IsGenerallyCovariant (𝔘 : NetTheory) : Prop :=
  ∀ (L : Spacetime.LorentzianSpacetime)
    (ψ : Spacetime.Diffeo L.toSpacetime L.toSpacetime),
    Nonempty (NetEquivalence (L.pullbackCarrierEquiv ψ)
      (L.toAbstract_pullback_isBasisSet ψ) (𝔘 (L.pullback ψ)) (𝔘 L))

end HaagKastlerCurved

end AQFT

end Physicslib4
