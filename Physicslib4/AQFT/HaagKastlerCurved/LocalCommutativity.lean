/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.LocalAlgebras

/-!
# Axiom 3 (Local Commutativity), curved spacetime

This file formalises the blueprint declaration
`def:local-commutativity-in-curved-spacetime` (Axiom 3 of the
Haag-Kastler axioms on a Lorentzian spacetime, Chapter 10
(`sections/sec10/10-4_haag-kastler-axioms-in-curved-spacetime`) of the
AQFT-in-Lean blueprint):

> Let `𝐁₁`, `𝐁₂` be Alexandrov-basis sets. If `𝐁₁` and `𝐁₂` are
> completely spacelike, then for *any* basis element `𝐁` with
> `𝐁₁, 𝐁₂ ⊆ 𝐁` the algebras `𝔘(𝐁₁)` and `𝔘(𝐁₂)` commute inside
> `𝔘(𝐁)`, i.e. `i(a₁) i(a₂) - i(a₂) i(a₁) = 0`, where `i` is the
> isotony `*`-monomorphism (Axiom 2). If no such `𝐁` exists, no
> condition is imposed.

## Main definitions

* `Physicslib4.AQFT.HaagKastlerCurved.LocalCommutativity`: a
  `Prop`-valued predicate on a `LocalNet M` asserting Axiom 3.

## Modelling notes

* This is the point where the curved axioms genuinely *diverge* from
  the Minkowski ones: there is no global quasilocal algebra on a
  generic Lorentzian spacetime, so commutativity cannot be phrased
  inside one ambient C*-algebra. Instead we quantify over a common
  *containing basis set* `B` (when one exists) and assert
  commutativity inside the local algebra `𝔘(B)`, transported there
  by the isotony embeddings `i : 𝔘(Bᵢ) ↪ 𝔘(B)`.

* The isotony embeddings used are exactly those of Axiom 2; we
  existentially bind a coherent family `ι` of injective unital
  `*`-monomorphisms (one per basis-set inclusion) and require their
  images to commute. When no common containing basis set `B` exists,
  the universally quantified condition is vacuously satisfied,
  matching the blueprint's "if no such `𝐁` exists, it doesn't make
  sense to ask whether they commute".
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastlerCurved

variable {M : LorentzianSpacetime}

/--
**Axiom 3 (Local Commutativity), curved spacetime.** A local net `U`
on a Lorentzian spacetime `M` satisfies *local commutativity* if
there is a coherent family of isotony `*`-monomorphisms
`ι : 𝔘(B₁) ↪ 𝔘(B₂)` (for inclusions `B₁ ⊆ B₂` of basis sets) such
that whenever two basis sets `B₁`, `B₂` are completely spacelike and
both contained in a common basis set `B`, their images in `𝔘(B)`
under the isotony embeddings commute pointwise.

If no common containing basis set exists, no constraint is imposed,
reflecting that there is then no algebra in which to compare them.

Blueprint reference: `def:local-commutativity-in-curved-spacetime`.
-/
def LocalCommutativity (U : LocalNet M) : Prop :=
  ∃ ι : ∀ ⦃B₁ B₂ : Set M.Carrier⦄,
          M.IsBasisSet B₁ → M.IsBasisSet B₂ → B₁ ⊆ B₂ →
            StarAlgHom ℂ (U.algebra B₁) (U.algebra B₂),
    (∀ ⦃B₁ B₂ : Set M.Carrier⦄ (h₁ : M.IsBasisSet B₁) (h₂ : M.IsBasisSet B₂)
        (h : B₁ ⊆ B₂), Function.Injective (ι h₁ h₂ h)) ∧
    ∀ ⦃B₁ B₂ B : Set M.Carrier⦄
      (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂) (hB : M.IsBasisSet B),
      M.IsCompletelySpacelike B₁ B₂ →
      (h₁ : B₁ ⊆ B) → (h₂ : B₂ ⊆ B) →
      ∀ (a : U.algebra B₁) (b : U.algebra B₂),
        Commute (ι hB₁ hB h₁ a) (ι hB₂ hB h₂ b)

end HaagKastlerCurved
end AQFT
end Physicslib4
