/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.LocalVonNeumann
import Physicslib4.AQFT.HaagKastler.Wedges
import Physicslib4.Operators.Modular.Tomita

/-!
# The von Neumann algebra of a region

In a `*`-representation `π` of the quasilocal algebra, the von Neumann algebra of an arbitrary set
`O` of spacetime points is `R(O) = S(O)''`, where `S(O)` is the union of the local von Neumann
algebras `R(B)` of the diamonds `B ⊆ O`. It is a derived object, not part of the net axioms, and
exists only in a representation. It agrees with `localVonNeumann` on diamonds, is monotone in `O`,
and satisfies locality for regions whose diamonds are completely spacelike. The wedge algebras are
the `R(W)` with `IsWedge W`.

Commutants are `Set.centralizer` in the bounded operators on `H`.
-/

namespace Physicslib4
namespace AQFT
namespace HaagKastler

open scoped Pointwise
open Physicslib4.Modular

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace HaagKastlerNet

variable (N : HaagKastlerNet)

/-- The generating set `S(O) = ⋃ {R(B) | B a diamond, B ⊆ O}` of the algebra of a region `O`, the
union of the local von Neumann algebras of the diamonds contained in `O`.

Blueprint: def:region-algebra -/
def regionGeneratingSet (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (O : Set StandardMinkowskiSpacetime.Carrier) : Set (H →L[ℂ] H) :=
  ⋃ (B : Set StandardMinkowskiSpacetime.Carrier) (hB : IsAlexandrovBasisSet B) (_ : B ⊆ O),
    N.localVonNeumann π hB

/-- The von Neumann algebra `R(O) = S(O)''` of an arbitrary region `O` in the representation `π`.

It is a derived object, not part of the net axioms. The inclusion `B ⊆ O` of diamonds is plain
inclusion, so `R(B)` agrees with `localVonNeumann` on every diamond
(`regionVonNeumann_of_isAlexandrovBasisSet`); a region containing no nonempty diamond has
`R(O) = ℂ1`. The wedge algebras are the `R(W)` with `IsWedge W`.

Blueprint: def:region-algebra -/
def regionVonNeumann (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (O : Set StandardMinkowskiSpacetime.Carrier) : Set (H →L[ℂ] H) :=
  Set.centralizer (Set.centralizer (N.regionGeneratingSet π O))

/-- The generating set `S(O)` is self-adjoint and `R(O)` is a von Neumann algebra.

Blueprint: lmm:region-algebra-von-neumann -/
theorem regionVonNeumann_isVonNeumannSet (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (O : Set StandardMinkowskiSpacetime.Carrier) :
    (∀ a ∈ N.regionGeneratingSet π O, star a ∈ N.regionGeneratingSet π O) ∧
      IsVonNeumannSet (N.regionVonNeumann π O) := by
  have hcent : ∀ {S : Set (H →L[ℂ] H)}, (∀ a ∈ S, star a ∈ S) →
      (∀ a ∈ Set.centralizer S, star a ∈ Set.centralizer S) := fun {S} hS a ha => by
    have hA : (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H)) = Set.centralizer S := by
      rw [StarSubalgebra.coe_centralizer,
        Set.union_eq_left.mpr fun b hb => by simpa using hS _ hb]
    rw [← hA] at ha ⊢
    exact star_mem ha
  have hS : ∀ a ∈ N.regionGeneratingSet π O, star a ∈ N.regionGeneratingSet π O := by
    simp only [regionGeneratingSet, Set.mem_iUnion]
    rintro a ⟨B, hB, hBO, ha⟩
    exact ⟨B, hB, hBO, hcent (hcent (N.localOperators_selfAdjoint π hB)) a ha⟩
  exact ⟨hS, hcent (hcent hS), Set.centralizer_centralizer_centralizer _⟩

/-- Monotonicity: if `O₁ ⊆ O₂`, then `S(O₁) ⊆ S(O₂)` and `R(O₁) ⊆ R(O₂)`.

Blueprint: lmm:region-algebra-mono -/
theorem regionVonNeumann_mono (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    {O₁ O₂ : Set StandardMinkowskiSpacetime.Carrier} (h : O₁ ⊆ O₂) :
    N.regionGeneratingSet π O₁ ⊆ N.regionGeneratingSet π O₂ ∧
      N.regionVonNeumann π O₁ ⊆ N.regionVonNeumann π O₂ := by
  have hS : N.regionGeneratingSet π O₁ ⊆ N.regionGeneratingSet π O₂ := fun x hx => by
    simp only [regionGeneratingSet, Set.mem_iUnion] at hx ⊢
    obtain ⟨B, hB, hBO, hx⟩ := hx
    exact ⟨B, hB, hBO.trans h, hx⟩
  exact ⟨hS, Set.centralizer_subset (Set.centralizer_subset hS)⟩

/-- Local operators lie in the region algebra: if `B ⊆ O` is a diamond, then
`π(𝔘(B)) ⊆ R(B) ⊆ R(O)`.

Blueprint: lmm:region-algebra-contains-local -/
theorem localVonNeumann_subset_regionVonNeumann (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    {B O : Set StandardMinkowskiSpacetime.Carrier} (hB : IsAlexandrovBasisSet B) (hBO : B ⊆ O) :
    N.localOperators π hB ⊆ N.localVonNeumann π hB ∧
      N.localVonNeumann π hB ⊆ N.regionVonNeumann π O := by
  sorry

/-- On a diamond `B`, the algebra of the region `B` is the local von Neumann algebra `R(B)`.

Blueprint: lmm:region-algebra-diamond -/
theorem regionVonNeumann_of_isAlexandrovBasisSet (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    {B : Set StandardMinkowskiSpacetime.Carrier} (hB : IsAlexandrovBasisSet B) :
    N.regionVonNeumann π B = N.localVonNeumann π hB := by
  sorry

end HaagKastlerNet

/-- The bicommutant of a commuting set: if every `s ∈ S` commutes with every `t ∈ T`, then
`S'' ⊆ T'`; moreover `T' = (T'')'`.

Blueprint: lmm:bicommutant-subset-commutant -/
theorem centralizer_centralizer_subset_centralizer_of_commute {S T : Set (H →L[ℂ] H)}
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    Set.centralizer (Set.centralizer S) ⊆ Set.centralizer T ∧
      Set.centralizer T = Set.centralizer (Set.centralizer (Set.centralizer T)) := by
  sorry

namespace HaagKastlerNet

variable (N : HaagKastlerNet)

/-- Locality of region algebras: if every diamond `B₁ ⊆ O₁` and every diamond `B₂ ⊆ O₂` are
completely spacelike, then `R(O₁) ⊆ R(O₂)'`. This holds in particular when `O₁` and `O₂` are
completely spacelike.

Blueprint: thrm:region-algebra-locality -/
theorem regionVonNeumann_subset_centralizer (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (∀ O₁ O₂ : Set StandardMinkowskiSpacetime.Carrier,
      (∀ B₁ B₂ : Set StandardMinkowskiSpacetime.Carrier, IsAlexandrovBasisSet B₁ →
        IsAlexandrovBasisSet B₂ → B₁ ⊆ O₁ → B₂ ⊆ O₂ →
          Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
            standardMinkowskiTimeOrientation B₁ B₂) →
        N.regionVonNeumann π O₁ ⊆ Set.centralizer (N.regionVonNeumann π O₂)) ∧
      ∀ O₁ O₂ : Set StandardMinkowskiSpacetime.Carrier,
        Spacetime.IsCompletelySpacelike StandardMinkowskiSpacetime
            standardMinkowskiTimeOrientation O₁ O₂ →
          N.regionVonNeumann π O₁ ⊆ Set.centralizer (N.regionVonNeumann π O₂) := by
  sorry

/-- Locality of opposite wedge algebras: for every `g`, `R(g W_R) ⊆ R(g W_L)'` and
`R(g W_L) ⊆ R(g W_R)'`. In particular `R(W_R) ⊆ R(W_L)'`.

Blueprint: crllr:opposite-wedge-locality -/
theorem regionVonNeumann_oppositeWedge_subset_centralizer
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (∀ g : InhomogeneousLorentzGroup,
      N.regionVonNeumann π (g • rightWedge) ⊆
          Set.centralizer (N.regionVonNeumann π (g • leftWedge)) ∧
        N.regionVonNeumann π (g • leftWedge) ⊆
          Set.centralizer (N.regionVonNeumann π (g • rightWedge))) ∧
      N.regionVonNeumann π rightWedge ⊆ Set.centralizer (N.regionVonNeumann π leftWedge) := by
  sorry

/-- Reindexing the generating set of a transformed region: for every `g` and every `O`,
`⋃ {R(g B) | B a diamond, B ⊆ O} = S(g O)`.

Blueprint: lmm:region-generating-set-reindex -/
theorem regionGeneratingSet_smul (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (g : InhomogeneousLorentzGroup) (O : Set StandardMinkowskiSpacetime.Carrier) :
    ⋃ (B : Set StandardMinkowskiSpacetime.Carrier) (hB : IsAlexandrovBasisSet B) (_ : B ⊆ O),
        N.localVonNeumann π (isAlexandrovBasisSet_smul g hB) =
      N.regionGeneratingSet π (g • O) := by
  sorry

end HaagKastlerNet

end HaagKastler
end AQFT
end Physicslib4
