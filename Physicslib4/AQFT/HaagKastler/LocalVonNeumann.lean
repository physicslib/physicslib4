/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.EinsteinCausality

/-!
# Local von Neumann algebras and spacelike commutation

In a representation `π` of the quasilocal algebra, the *local von Neumann algebra*
of a region `B` is the bicommutant `R(B) = π(𝔘(B))''` of the local observable
operators. Mathlib models the commutant by `Set.centralizer`, so `R(B)` is the
double centralizer.

The headline result is **microcausality at the von Neumann level**: for completely
spacelike-separated regions `B₁, B₂`, the local algebras commute,
`R(B₁) ⊆ R(B₂)'`. It is the von Neumann form of Einstein causality
(`einstein_causality`): elementwise commutation of the local operators, pushed
through the centralizer.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler
namespace HaagKastlerNet

open Physicslib4.GNS

variable (N : HaagKastlerNet)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The local observable operators of a region `B` in a representation `π`: the
image `π(𝔘(B))` of the local algebra. -/
def localOperators (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B : Set StandardMinkowskiSpacetime.Carrier) : Set (H →L[ℂ] H) :=
  Set.range fun a : N.U.algebra B => π (N.commAlgebra.ι B a)

/-- The **local von Neumann algebra** `R(B) = π(𝔘(B))''`, the bicommutant of the
local observable operators (the commutant being `Set.centralizer`). -/
def localVonNeumann (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B : Set StandardMinkowskiSpacetime.Carrier) : Set (H →L[ℂ] H) :=
  Set.centralizer (Set.centralizer (N.localOperators π B))

/-- **Microcausality at the von Neumann level.** For completely spacelike-separated
basis regions `B₁, B₂`, the local von Neumann algebras commute:
`R(B₁) ⊆ R(B₂)'`. This is the von Neumann form of Einstein causality. -/
theorem localVonNeumann_subset_centralizer
    (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂)
    (hs : Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation B₁ B₂) :
    N.localVonNeumann π B₁ ⊆ Set.centralizer (N.localVonNeumann π B₂) := by
  have hcomm : N.localOperators π B₂ ⊆ Set.centralizer (N.localOperators π B₁) := by
    rintro y ⟨b, rfl⟩
    rw [Set.mem_centralizer_iff]
    rintro x ⟨a, rfl⟩
    exact N.einstein_causality π hB₁ hB₂ hs a b
  have h1 : N.localVonNeumann π B₁ ⊆ Set.centralizer (N.localOperators π B₂) :=
    Set.centralizer_subset hcomm
  change N.localVonNeumann π B₁
    ⊆ Set.centralizer (Set.centralizer (Set.centralizer (N.localOperators π B₂)))
  rwa [Set.centralizer_centralizer_centralizer]

/-- **Isotony of the net of von Neumann algebras.** For basis regions `B₁ ⊆ B₂`,
the local von Neumann algebras are nested: `R(B₁) ⊆ R(B₂)`. The local observables
of `B₁` embed into those of `B₂` via the quasilocal isotony coherence
(`ι_inclusion`), and the double commutant is monotone. -/
theorem localVonNeumann_mono
    (π : N.commAlgebra.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier⦄
    (hB₁ : IsAlexandrovBasisSet B₁) (hB₂ : IsAlexandrovBasisSet B₂) (h : B₁ ⊆ B₂) :
    N.localVonNeumann π B₁ ⊆ N.localVonNeumann π B₂ := by
  have hsub : N.localOperators π B₁ ⊆ N.localOperators π B₂ := by
    rintro x ⟨a, rfl⟩
    exact ⟨N.commAlgebra.inclusion hB₁ hB₂ h a,
      congrArg π (N.commAlgebra.ι_inclusion hB₁ hB₂ h a)⟩
  exact Set.centralizer_subset (Set.centralizer_subset hsub)

end HaagKastlerNet
end HaagKastler
end AQFT
end Physicslib4
