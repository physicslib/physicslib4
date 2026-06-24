/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.EinsteinCausality

/-!
# Local von Neumann algebras and spacelike commutation (curved spacetime)

This is the curved-spacetime counterpart of the Minkowski local von Neumann
algebra construction. There is no quasilocal algebra in curved spacetime, so the
relevant representations are of a containing basis algebra `𝔘(B)`. Given such a
representation `π`, the *local von Neumann algebra* of a subregion `B' ⊆ B` is the
bicommutant `R(B') = π(𝔘(B'))''` of the local observable operators (the embedding
`𝔘(B') → 𝔘(B)` being the isotony witness `commIsotony`). Mathlib models the
commutant by `Set.centralizer`, so `R(B')` is the double centralizer.

The headline result is **microcausality at the von Neumann level**: for completely
spacelike-separated subregions `B₁, B₂ ⊆ B`, the local algebras commute,
`R(B₁) ⊆ R(B₂)'`. It is the von Neumann form of curved Einstein causality
(`einstein_causality`): elementwise commutation of the local operators, pushed
through the centralizer.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastlerCurved
namespace HaagKastlerNet

open Physicslib4.GNS

variable {M : LorentzianSpacetime} (N : HaagKastlerNet M)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The local observable operators of a subregion `B' ⊆ B` in a representation `π`
of the containing algebra `𝔘(B)`: the image `π(𝔘(B'))` of the local algebra under
the isotony embedding. -/
def localOperators {B : Set M.Carrier} (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B' : Set M.Carrier⦄ (hB' : M.IsBasisSet B') (hB : M.IsBasisSet B)
    (h : B' ⊆ B) : Set (H →L[ℂ] H) :=
  Set.range fun a : N.algebra B' => π (N.commIsotony hB' hB h a)

/-- The **local von Neumann algebra** `R(B') = π(𝔘(B'))''`, the bicommutant of the
local observable operators (the commutant being `Set.centralizer`). -/
def localVonNeumann {B : Set M.Carrier} (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B' : Set M.Carrier⦄ (hB' : M.IsBasisSet B') (hB : M.IsBasisSet B)
    (h : B' ⊆ B) : Set (H →L[ℂ] H) :=
  Set.centralizer (Set.centralizer (N.localOperators π hB' hB h))

/-- **Microcausality at the von Neumann level (curved spacetime).** For completely
spacelike-separated basis subregions `B₁, B₂ ⊆ B`, the local von Neumann algebras
commute: `R(B₁) ⊆ R(B₂)'`. This is the von Neumann form of curved Einstein
causality. -/
theorem localVonNeumann_subset_centralizer
    {B : Set M.Carrier} (hB : M.IsBasisSet B)
    (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (hs : M.IsCompletelySpacelike B₁ B₂) (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B) :
    N.localVonNeumann π hB₁ hB h₁ ⊆ Set.centralizer (N.localVonNeumann π hB₂ hB h₂) := by
  have hcomm :
      N.localOperators π hB₂ hB h₂ ⊆ Set.centralizer (N.localOperators π hB₁ hB h₁) := by
    rintro y ⟨b, rfl⟩
    rw [Set.mem_centralizer_iff]
    rintro x ⟨a, rfl⟩
    exact N.einstein_causality hB π hB₁ hB₂ hs h₁ h₂ a b
  have h1 : N.localVonNeumann π hB₁ hB h₁ ⊆ Set.centralizer (N.localOperators π hB₂ hB h₂) :=
    Set.centralizer_subset hcomm
  change N.localVonNeumann π hB₁ hB h₁
    ⊆ Set.centralizer (Set.centralizer (Set.centralizer (N.localOperators π hB₂ hB h₂)))
  rwa [Set.centralizer_centralizer_centralizer]

/-- **Isotony of the net of von Neumann algebras (curved spacetime).** For nested
basis subregions `B₁ ⊆ B₂ ⊆ B`, the local von Neumann algebras are nested:
`R(B₁) ⊆ R(B₂)`. Unlike Minkowski, the curved Axiom 3 isotony embeddings
(`commIsotony`) are chosen witnesses with no built-in composition law, so the
coherence `commIsotony (B₁ ⊆ B) = commIsotony (B₂ ⊆ B) ∘ commIsotony (B₁ ⊆ B₂)`
is taken as an explicit hypothesis `hcoh` (it is automatic whenever the embeddings
are coherent, e.g. for a net whose Axiom 3 witnesses come from a genuine inclusion
family). Given it, the local observables of `B₁` embed into those of `B₂` and the
double commutant is monotone. -/
theorem localVonNeumann_mono
    {B : Set M.Carrier} (hB : M.IsBasisSet B)
    (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set M.Carrier⦄
    (hB₁ : M.IsBasisSet B₁) (hB₂ : M.IsBasisSet B₂)
    (h₁₂ : B₁ ⊆ B₂) (h₂ : B₂ ⊆ B)
    (hcoh : ∀ a : N.algebra B₁,
        N.commIsotony hB₁ hB (h₁₂.trans h₂) a
          = N.commIsotony hB₂ hB h₂ (N.commIsotony hB₁ hB₂ h₁₂ a)) :
    N.localVonNeumann π hB₁ hB (h₁₂.trans h₂) ⊆ N.localVonNeumann π hB₂ hB h₂ := by
  have hsub : N.localOperators π hB₁ hB (h₁₂.trans h₂)
      ⊆ N.localOperators π hB₂ hB h₂ := by
    rintro x ⟨a, rfl⟩
    exact ⟨N.commIsotony hB₁ hB₂ h₁₂ a, congrArg π (hcoh a).symm⟩
  exact Set.centralizer_subset (Set.centralizer_subset hsub)

end HaagKastlerNet
end HaagKastlerCurved
end AQFT
end Physicslib4
