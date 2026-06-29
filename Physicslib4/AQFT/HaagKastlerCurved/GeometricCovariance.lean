/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.LocalVonNeumann
import Physicslib4.AQFT.HaagKastlerCurved.StabilizerAction
import Physicslib4.AQFT.HaagKastler.GeometricCovariance

/-!
# Geometric covariance of the local von Neumann net (curved spacetime)

This is the curved-spacetime, stabilizer-subgroup analogue of the Minkowski
geometric covariance result. There is no quasilocal algebra in curved spacetime,
so the representation `π` is of a containing basis algebra `𝔘(B)`, and the only
genuine symmetries acting on `𝔘(B)` are the elements of the stabilizer
`Stab(B) = {g : g · B = B}` (via `stabAut`). For `g ∈ Stab(B)`, the implementing
unitary `U(g)` of the stabilizer GNS representation conjugates the local von
Neumann algebra of a subregion `B₁ ⊆ B` onto that of `g · B₁`:
`U(g) · R(B₁) · U(g)⁻¹ = R(g · B₁)`.

Compared with Minkowski, the abstract `LorentzianSpacetime` interface provides
neither basis-set preservation (`M.IsBasisSet (g · B₁)`) nor the
covariance-versus-isotony coherence relating the stabilizer action `stabAut g` to
the chosen isotony embeddings `commIsotony`. Both therefore enter as explicit
hypotheses (`hgB₁`, `h₁'`, `hcompat`), exactly as elsewhere in the curved
development (e.g. `localVonNeumann_mono`). For a net arising from a concrete
geometric spacetime they are discharged by `isBasisSet_smul` and the genuine
covariance of the action.

The reusable conjugation machinery (`lieConj`, `MulEquiv.image_centralizer`) is
shared with the Minkowski development.
-/

open scoped Pointwise

namespace Physicslib4
namespace AQFT
namespace HaagKastlerCurved
namespace HaagKastlerNet

open Physicslib4.GNS

variable {M : LorentzianSpacetime} (N : HaagKastlerNet M)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Conjugation carries the local operators of `B₁` onto those of `g · B₁`.**
Given operator covariance `U π(a) U⁻¹ = π(stabAut g · a)` for `g ∈ Stab(B)` and the
covariance-isotony coherence `hcompat`, conjugation `lieConj U` maps the local
observable operators of a subregion `B₁ ⊆ B` onto those of `g · B₁`. -/
theorem lieConj_image_localOperators
    {B : Set M.Carrier} (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Uop : H ≃ₗᵢ[ℂ] H) (g : ↥(MulAction.stabilizer M.Isom B))
    ⦃B₁ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (h₁ : B₁ ⊆ B)
    (hgB₁ : M.IsBasisSet ((g : M.Isom) • B₁)) (h₁' : (g : M.Isom) • B₁ ⊆ B)
    (hcov : ∀ (a : N.algebra B) (x : H),
      Uop (π a (Uop.symm x)) = π (N.stabAutHom B g a) x)
    (hcompat : ∀ a : N.algebra B₁,
      N.stabAutHom B g (N.commIsotony hB₁ hB h₁ a)
        = N.commIsotony hgB₁ hB h₁' (N.covEquiv (g : M.Isom) B₁ a)) :
    Physicslib4.lieConj Uop '' N.localOperators π hB₁ hB h₁
      = N.localOperators π hgB₁ hB h₁' := by
  have hconj : ∀ a : N.algebra B,
      Physicslib4.lieConj Uop (π a) = π (N.stabAutHom B g a) := by
    intro a
    ext x
    rw [Physicslib4.lieConj_apply]
    exact hcov a x
  ext y
  simp only [localOperators, Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨N.covEquiv (g : M.Isom) B₁ a,
      by rw [hconj (N.commIsotony hB₁ hB h₁ a), hcompat a]⟩
  · rintro ⟨a', rfl⟩
    refine ⟨π (N.commIsotony hB₁ hB h₁ ((N.covEquiv (g : M.Isom) B₁).symm a')),
      ⟨(N.covEquiv (g : M.Isom) B₁).symm a', rfl⟩, ?_⟩
    rw [hconj (N.commIsotony hB₁ hB h₁ ((N.covEquiv (g : M.Isom) B₁).symm a')),
      hcompat ((N.covEquiv (g : M.Isom) B₁).symm a'), StarAlgEquiv.apply_symm_apply]

/-- **Geometric covariance of the local von Neumann net (curved spacetime).** For
`g ∈ Stab(B)`, conjugation by the implementing unitary `U(g)` of the stabilizer
GNS representation carries the local von Neumann algebra of a subregion `B₁ ⊆ B`
onto that of `g · B₁`:
`U(g) · R(B₁) · U(g)⁻¹ = R(g · B₁)`.

The operator-covariance hypothesis `hcov` is the last clause supplied by
`exists_gns_unitary_stabilizer`; the coherence `hcompat` and the geometric data
`hgB₁`, `h₁'` are the curved-spacetime side conditions discussed in the module
docstring. In particular `R(B₁)` and `R(g · B₁)` are unitarily equivalent. -/
theorem lieConj_image_localVonNeumann
    {B : Set M.Carrier} (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Uop : H ≃ₗᵢ[ℂ] H) (g : ↥(MulAction.stabilizer M.Isom B))
    ⦃B₁ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (h₁ : B₁ ⊆ B)
    (hgB₁ : M.IsBasisSet ((g : M.Isom) • B₁)) (h₁' : (g : M.Isom) • B₁ ⊆ B)
    (hcov : ∀ (a : N.algebra B) (x : H),
      Uop (π a (Uop.symm x)) = π (N.stabAutHom B g a) x)
    (hcompat : ∀ a : N.algebra B₁,
      N.stabAutHom B g (N.commIsotony hB₁ hB h₁ a)
        = N.commIsotony hgB₁ hB h₁' (N.covEquiv (g : M.Isom) B₁ a)) :
    Physicslib4.lieConj Uop '' N.localVonNeumann π hB₁ hB h₁
      = N.localVonNeumann π hgB₁ hB h₁' := by
  unfold localVonNeumann
  rw [(Physicslib4.lieConj Uop).image_centralizer_centralizer (N.localOperators π hB₁ hB h₁),
    N.lieConj_image_localOperators hB π Uop g hB₁ h₁ hgB₁ h₁' hcov hcompat]

/-- **Geometric covariance, bundled (curved spacetime).** The set image of the
bundled local `VonNeumannAlgebra` `R(B₁)` under conjugation by `U(g)` is the
bundled `R(g · B₁)`. -/
theorem lieConj_image_localVonNeumannAlgebra
    {B : Set M.Carrier} (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Uop : H ≃ₗᵢ[ℂ] H) (g : ↥(MulAction.stabilizer M.Isom B))
    ⦃B₁ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (h₁ : B₁ ⊆ B)
    (hgB₁ : M.IsBasisSet ((g : M.Isom) • B₁)) (h₁' : (g : M.Isom) • B₁ ⊆ B)
    (hcov : ∀ (a : N.algebra B) (x : H),
      Uop (π a (Uop.symm x)) = π (N.stabAutHom B g a) x)
    (hcompat : ∀ a : N.algebra B₁,
      N.stabAutHom B g (N.commIsotony hB₁ hB h₁ a)
        = N.commIsotony hgB₁ hB h₁' (N.covEquiv (g : M.Isom) B₁ a)) :
    Physicslib4.lieConj Uop '' (N.localVonNeumannAlgebra π hB₁ hB h₁ : Set (H →L[ℂ] H))
      = (N.localVonNeumannAlgebra π hgB₁ hB h₁' : Set (H →L[ℂ] H)) := by
  simp only [coe_localVonNeumannAlgebra]
  exact N.lieConj_image_localVonNeumann hB π Uop g hB₁ h₁ hgB₁ h₁' hcov hcompat

end HaagKastlerNet
end HaagKastlerCurved
end AQFT
end Physicslib4
