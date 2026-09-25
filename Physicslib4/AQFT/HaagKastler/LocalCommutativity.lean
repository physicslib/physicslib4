/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalAlgebras
import Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra
import Physicslib4.Spacetime.Causality
import Physicslib4.Spacetime.MinkowskiDirected

/-!
# Axiom 3: Local Commutativity

This file formalises the blueprint declaration
`def:local-commutativity` (Axiom 3 of the "sharpened" Haag-Kastler
axioms, section 10.5 of the AQFT-in-Lean blueprint):

> If two Alexandrov-basis sets `𝐁₁`, `𝐁₂` are *completely spacelike*
> with respect to each other, then the local algebras `𝔘(𝐁₁)` and
> `𝔘(𝐁₂)` commute *inside the quasilocal algebra* `𝔘`.

## Main definitions

* `Physicslib4.AQFT.HaagKastler.LocalCommutativity`: a `Prop`-valued
  predicate on a `LocalNet` asserting Axiom 3.

## Main results

* `Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra.commute_ι_iff_commute_map`:
  commutation of two local images in a quasilocal algebra is equivalent to
  commutation of their isotony images in a common local algebra `𝔘(B)`.
* `Physicslib4.AQFT.HaagKastler.LocalCommutativity.commute_ι`
  (`lmm:local-commutativity-any-quasilocal`): Axiom 3 holds in *every*
  quasilocal algebra of the net, in particular in the canonical one.

## Modelling notes

* "Commuting in the quasilocal algebra" requires an ambient
  C*-algebra `𝔘` containing every `𝔘(B)` as a subalgebra. Rather
  than inlining that data, we quantify existentially over a
  `QuasilocalAlgebra U` — the bundled structure that packages an
  ambient C*-algebra together with the family of faithful unital
  `*`-monomorphisms `ιB : 𝔘(B) →⋆ₐ[ℂ] 𝔘`. Axiom 3 then asserts
  that, for *some* such ambient algebra, the images of any two
  completely-spacelike local algebras commute pointwise. The choice of
  ambient algebra does not matter: `LocalCommutativity.commute_ι`
  shows the commutation then holds in *every* `QuasilocalAlgebra U i`.

* The quasilocal algebra itself — including its density / completion
  property — is *constructed* from the net by
  `exists_quasilocalAlgebra` (`thrm:quasilocal-algebra-exists`); here
  we only *use* the structure to phrase commutativity, and by
  `LocalCommutativity.commute_ι` Axiom 3 holds in that canonical algebra.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4

/--
**Axiom 3 (Local Commutativity).** A local net `U` satisfies *local
commutativity* if there exists a `QuasilocalAlgebra U` — i.e. an
ambient unital C*-algebra `Q.carrier` equipped with faithful unital
`*`-monomorphisms `Q.ι B : U.algebra B →⋆ₐ[ℂ] Q.carrier` for every
Alexandrov-basis set `B` — such that whenever two basis sets
`B₁`, `B₂` are completely spacelike with respect to each other,
the images `Q.ι B₁ (U.algebra B₁)` and `Q.ι B₂ (U.algebra B₂)`
commute pointwise inside `Q.carrier`.

Blueprint reference: `def:local-commutativity`.
-/
def LocalCommutativity (U : LocalNet) (i : Isotony U) : Prop :=
  ∃ Q : QuasilocalAlgebra U i,
    ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
      (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂),
      Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation B₁ B₂ →
      ∀ (a : U.algebra B₁) (b : U.algebra B₂),
        Commute (Q.ι hB₁ a) (Q.ι hB₂ b)

/-- **Commutation in a quasilocal algebra is decided locally.** For basis sets
`B₁, B₂ ⊆ B`, the images `Q.ι hB₁ a` and `Q.ι hB₂ b` commute in `Q.carrier` iff
the isotony images of `a` and `b` commute in the local algebra `𝔘(B)`. The
condition on the right does not mention `Q`. -/
theorem QuasilocalAlgebra.commute_ι_iff_commute_map {U : LocalNet} {i : Isotony U}
    (Q : QuasilocalAlgebra U i) {B₁ B₂ B : Set StandardMinkowskiSpacetime.Carrier}
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
    (hB : IsAlexandrovBasisSet B) (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B)
    (a : U.algebra B₁) (b : U.algebra B₂) :
    Commute (Q.ι hB₁ a) (Q.ι hB₂ b) ↔
      Commute (i.map hB₁ hB h₁ a) (i.map hB₂ hB h₂ b) := by
  rw [← Q.ι_inclusion hB₁ hB h₁ a, ← Q.ι_inclusion hB₂ hB h₂ b]
  refine ⟨fun h => Q.ι_injective hB ?_, fun h => h.map (Q.ι hB)⟩
  simpa only [map_mul] using h.eq

/-- **Axiom 3 holds in every quasilocal algebra.** `LocalCommutativity` asserts
commutation of completely-spacelike local algebras in *some* quasilocal algebra;
since commutation is decided inside a common local algebra `𝔘(B)`
(`QuasilocalAlgebra.commute_ι_iff_commute_map`), it then holds in *every*
`QuasilocalAlgebra U i`, in particular in the canonical one built by
`exists_quasilocalAlgebra`.

Blueprint reference: `lmm:local-commutativity-any-quasilocal`. -/
theorem LocalCommutativity.commute_ι {U : LocalNet} {i : Isotony U}
    (h : LocalCommutativity U i) (Q : QuasilocalAlgebra U i)
    ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
    (hs : Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂)
    (a : U.algebra B₁) (b : U.algebra B₂) :
    Commute (Q.ι hB₁ a) (Q.ι hB₂ b) := by
  obtain ⟨Q₀, hQ₀⟩ := h
  obtain ⟨B, hB, h₁, h₂⟩ := Spacetime.alexandrovBasis_directed hB₁ hB₂
  exact (Q.commute_ι_iff_commute_map hB₁ hB₂ hB h₁ h₂ a b).2
    ((Q₀.commute_ι_iff_commute_map hB₁ hB₂ hB h₁ h₂ a b).1 (hQ₀ hB₁ hB₂ hs a b))

end HaagKastler
end AQFT
end Physicslib4
