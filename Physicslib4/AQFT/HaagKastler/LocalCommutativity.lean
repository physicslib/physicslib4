/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalAlgebras
import Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra
import Physicslib4.AQFT.HaagKastler.QuasilocalExistence
import Physicslib4.Spacetime.Causality
import Physicslib4.Spacetime.MinkowskiDirected

/-!
# Axiom 3: Local Commutativity

This file formalises the blueprint declaration
`def:local-commutativity` (Axiom 3 of the "sharpened" Haag-Kastler
axioms, section 10.6 of the AQFT-in-Lean blueprint):

> If two Alexandrov-basis sets `𝐁₁`, `𝐁₂` are *completely spacelike*
> with respect to each other, then for every Alexandrov-basis set `𝐁`
> containing both, the isotony images of `𝔘(𝐁₁)` and `𝔘(𝐁₂)` commute in
> the local algebra `𝔘(𝐁)`.

This is the curved-spacetime Axiom 3 (`HaagKastlerCurved.LocalCommutativity`)
with the Minkowski basis sets; the only difference is that in Minkowski
spacetime a containing basis set always exists (`alexandrovBasis_directed`).

## Main definitions

* `Physicslib4.AQFT.HaagKastler.LocalCommutativity`: a `Prop`-valued
  predicate on a `LocalNet` asserting Axiom 3.

## Main results

* `Physicslib4.AQFT.HaagKastler.QuasilocalAlgebra.commute_ι_iff_commute_map`:
  commutation of two local images in a quasilocal algebra is equivalent to
  commutation of their isotony images in a common local algebra `𝔘(B)`.
* `Physicslib4.AQFT.HaagKastler.LocalCommutativity.commute_ι`
  (`lmm:local-commutativity-any-quasilocal`): Axiom 3 implies commutation in
  every quasilocal algebra of the net, in particular in the canonical one.
* `Physicslib4.AQFT.HaagKastler.localCommutativity_iff_exists_commute_ι`
  (`lmm:local-commutativity-iff-quasilocal`): Axiom 3 is equivalent to
  commutation in some quasilocal algebra, the form used by earlier versions.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open Physicslib4

/--
**Axiom 3 (Local Commutativity).** A local net `U`, with Axiom 2 isotony family `i`,
satisfies *local commutativity* if whenever two Alexandrov-basis sets `B₁`, `B₂` are
completely spacelike and both contained in an Alexandrov-basis set `B`, their images in
`𝔘(B)` under the isotony embeddings `i.map` commute pointwise.

In Minkowski spacetime a containing basis set always exists
(`Spacetime.alexandrovBasis_directed`), so the condition is never vacuous. The
equivalent form in a quasilocal algebra is `localCommutativity_iff_exists_commute_ι`.

Blueprint reference: `def:local-commutativity`.
-/
def LocalCommutativity (U : LocalNet) (i : Isotony U) : Prop :=
  ∀ ⦃B₁ B₂ B : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
    (hB : IsAlexandrovBasisSet B),
    Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂ →
    (h₁ : B₁ ⊆ B) → (h₂ : B₂ ⊆ B) →
    ∀ (a : U.algebra B₁) (b : U.algebra B₂),
      Commute (i.map hB₁ hB h₁ a) (i.map hB₂ hB h₂ b)

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

/-- **Axiom 3 holds in every quasilocal algebra.** Commutation of completely-spacelike
local algebras in a common containing `𝔘(B)` transfers, through the cocone condition and
`QuasilocalAlgebra.commute_ι_iff_commute_map`, to commutation of their images in *every*
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
  obtain ⟨B, hB, h₁, h₂⟩ := Spacetime.alexandrovBasis_directed hB₁ hB₂
  exact (Q.commute_ι_iff_commute_map hB₁ hB₂ hB h₁ h₂ a b).2 (h hB₁ hB₂ hB hs h₁ h₂ a b)

/-- **Axiom 3 in the quasilocal algebra.** A net satisfies Axiom 3 if and only if there is a
quasilocal algebra in which the images of any two completely-spacelike local algebras commute.
This was the form of Axiom 3 in earlier versions of the blueprint; by
`LocalCommutativity.commute_ι` the commutation then holds in every quasilocal algebra.

Blueprint reference: `lmm:local-commutativity-iff-quasilocal`. -/
theorem localCommutativity_iff_exists_commute_ι (U : LocalNet) (i : Isotony U) :
    LocalCommutativity U i ↔
      ∃ Q : QuasilocalAlgebra U i,
        ∀ ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
          (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂),
          Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
            standardMinkowskiTimeOrientation B₁ B₂ →
          ∀ (a : U.algebra B₁) (b : U.algebra B₂),
            Commute (Q.ι hB₁ a) (Q.ι hB₂ b) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨Q⟩ := exists_quasilocalAlgebra U i
    exact ⟨Q, fun B₁ B₂ hB₁ hB₂ hs a b => h.commute_ι Q hB₁ hB₂ hs a b⟩
  · rintro ⟨Q, hQ⟩ B₁ B₂ B hB₁ hB₂ hB hs h₁ h₂ a b
    exact (Q.commute_ι_iff_commute_map hB₁ hB₂ hB h₁ h₂ a b).1 (hQ hB₁ hB₂ hs a b)

end HaagKastler
end AQFT
end Physicslib4
