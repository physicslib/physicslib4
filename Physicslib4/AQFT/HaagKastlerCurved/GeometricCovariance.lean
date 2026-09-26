/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastlerCurved.LocalVonNeumann
import Physicslib4.AQFT.HaagKastlerCurved.StabilizerAction
import Physicslib4.Operators.Conjugation

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

Compared with Minkowski, the abstract `LorentzianSpacetime` interface does not
provide basis-set preservation (`M.IsBasisSet (g · B₁)`), so it enters as the
explicit hypothesis `hgB₁`, exactly as elsewhere in the curved development
(e.g. `localVonNeumann_mono`). The coherence between the stabilizer action and the
isotony embeddings is not a hypothesis: it is `stabAutHom_commIsotony`, derived
from Axiom 5 (3), which is stated for the Axiom 2 isotony family.

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

omit N in
/-- A stabilizer element of `B` maps every subregion of `B` into `B`:
`B₁ ⊆ B` and `g · B = B` give `g · B₁ ⊆ B`. -/
theorem smul_subset_of_mem_stabilizer {B B₁ : Set M.Carrier}
    (g : ↥(MulAction.stabilizer M.Isom B)) (h₁ : B₁ ⊆ B) : (g : M.Isom) • B₁ ⊆ B :=
  (Set.smul_set_mono h₁).trans (MulAction.mem_stabilizer_iff.mp g.2).le

/-- **The stabilizer action commutes with isotony.** For `g ∈ Stab(B)` and a
subregion `B₁ ⊆ B` (so `g · B₁ ⊆ B`, `smul_subset_of_mem_stabilizer`), the
stabilizer automorphism of `𝔘(B)` carries
the image of `𝔘(B₁)` onto that of `𝔘(g · B₁)`, compatibly with the covariance
equivalence. This is Axiom 5 (3) (`covEquiv_commIsotony`) transported along
`g · B = B`. -/
theorem stabAutHom_commIsotony
    {B : Set M.Carrier} (hB : M.IsBasisSet B) (g : ↥(MulAction.stabilizer M.Isom B))
    ⦃B₁ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (h₁ : B₁ ⊆ B)
    (hgB₁ : M.IsBasisSet ((g : M.Isom) • B₁))
    (a : N.algebra B₁) :
    N.stabAutHom B g (N.commIsotony hB₁ hB h₁ a)
      = N.commIsotony hgB₁ hB (smul_subset_of_mem_stabilizer g h₁)
          (N.covEquiv (g : M.Isom) B₁ a) := by
  have e : (g : M.Isom) • B = B := MulAction.mem_stabilizer_iff.mp g.2
  have hgB : M.IsBasisSet ((g : M.Isom) • B) := by rw [e]; exact hB
  rw [stabAutHom, stabAut_apply,
    N.covEquiv_commIsotony (g : M.Isom) hB₁ hB h₁ hgB₁ hgB (Set.smul_set_mono h₁)]
  exact N.cast_commIsotony e _ _ _ _ _ _

/-- **Conjugation carries the local operators of `B₁` onto those of `g · B₁`.**
Given operator covariance `U π(a) U⁻¹ = π(stabAut g · a)` for `g ∈ Stab(B)`,
conjugation `lieConj U` maps the local
observable operators of a subregion `B₁ ⊆ B` onto those of `g · B₁`. -/
theorem lieConj_image_localOperators
    {B : Set M.Carrier} (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Uop : H ≃ₗᵢ[ℂ] H) (g : ↥(MulAction.stabilizer M.Isom B))
    ⦃B₁ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (h₁ : B₁ ⊆ B)
    (hgB₁ : M.IsBasisSet ((g : M.Isom) • B₁))
    (hcov : ∀ (a : N.algebra B) (x : H),
      Uop (π a (Uop.symm x)) = π (N.stabAutHom B g a) x) :
    Physicslib4.lieConj Uop '' N.localOperators π hB₁ hB h₁
      = N.localOperators π hgB₁ hB (smul_subset_of_mem_stabilizer g h₁) := by
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
      by rw [hconj (N.commIsotony hB₁ hB h₁ a), N.stabAutHom_commIsotony hB g hB₁ h₁ hgB₁ a]⟩
  · rintro ⟨a', rfl⟩
    refine ⟨π (N.commIsotony hB₁ hB h₁ ((N.covEquiv (g : M.Isom) B₁).symm a')),
      ⟨(N.covEquiv (g : M.Isom) B₁).symm a', rfl⟩, ?_⟩
    rw [hconj (N.commIsotony hB₁ hB h₁ ((N.covEquiv (g : M.Isom) B₁).symm a')),
      N.stabAutHom_commIsotony hB g hB₁ h₁ hgB₁ ((N.covEquiv (g : M.Isom) B₁).symm a'),
      StarAlgEquiv.apply_symm_apply]

/-- **Geometric covariance of the local von Neumann net (curved spacetime).** For
`g ∈ Stab(B)`, conjugation by the implementing unitary `U(g)` of the stabilizer
GNS representation carries the local von Neumann algebra of a subregion `B₁ ⊆ B`
onto that of `g · B₁`:
`U(g) · R(B₁) · U(g)⁻¹ = R(g · B₁)`.

The operator-covariance hypothesis `hcov` is the last clause supplied by
`exists_gns_unitary_stabilizer`; the geometric datum
`hgB₁` is the curved-spacetime side condition discussed in the module
docstring. In particular `R(B₁)` and `R(g · B₁)` are unitarily equivalent. -/
theorem lieConj_image_localVonNeumann
    {B : Set M.Carrier} (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Uop : H ≃ₗᵢ[ℂ] H) (g : ↥(MulAction.stabilizer M.Isom B))
    ⦃B₁ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (h₁ : B₁ ⊆ B)
    (hgB₁ : M.IsBasisSet ((g : M.Isom) • B₁))
    (hcov : ∀ (a : N.algebra B) (x : H),
      Uop (π a (Uop.symm x)) = π (N.stabAutHom B g a) x) :
    Physicslib4.lieConj Uop '' N.localVonNeumann π hB₁ hB h₁
      = N.localVonNeumann π hgB₁ hB (smul_subset_of_mem_stabilizer g h₁) := by
  unfold localVonNeumann
  rw [(Physicslib4.lieConj Uop).image_centralizer_centralizer (N.localOperators π hB₁ hB h₁),
    N.lieConj_image_localOperators hB π Uop g hB₁ h₁ hgB₁ hcov]

/-- **Geometric covariance, bundled (curved spacetime).** The set image of the
bundled local `VonNeumannAlgebra` `R(B₁)` under conjugation by `U(g)` is the
bundled `R(g · B₁)`. -/
theorem lieConj_image_localVonNeumannAlgebra
    {B : Set M.Carrier} (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Uop : H ≃ₗᵢ[ℂ] H) (g : ↥(MulAction.stabilizer M.Isom B))
    ⦃B₁ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (h₁ : B₁ ⊆ B)
    (hgB₁ : M.IsBasisSet ((g : M.Isom) • B₁))
    (hcov : ∀ (a : N.algebra B) (x : H),
      Uop (π a (Uop.symm x)) = π (N.stabAutHom B g a) x) :
    Physicslib4.lieConj Uop '' (N.localVonNeumannAlgebra π hB₁ hB h₁ : Set (H →L[ℂ] H))
      = (N.localVonNeumannAlgebra π hgB₁ hB (smul_subset_of_mem_stabilizer g h₁) :
          Set (H →L[ℂ] H)) := by
  simp only [coe_localVonNeumannAlgebra]
  exact N.lieConj_image_localVonNeumann hB π Uop g hB₁ h₁ hgB₁ hcov

/-- **Orbit-invariance of factoriality (curved spacetime).** If the local von
Neumann algebra `R(B₁)` of a subregion is a factor, then so is `R(g · B₁)` for
`g ∈ Stab(B)`. Geometric covariance exhibits `R(g · B₁)` as the unitary conjugate
`U(g) R(B₁) U(g)⁻¹`, and conjugation preserves the factor property; so being a
factor is constant along the stabilizer orbit of a subregion. -/
theorem localVonNeumann_isFactor_smul
    {B : Set M.Carrier} (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Uop : H ≃ₗᵢ[ℂ] H) (g : ↥(MulAction.stabilizer M.Isom B))
    ⦃B₁ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (h₁ : B₁ ⊆ B)
    (hgB₁ : M.IsBasisSet ((g : M.Isom) • B₁))
    (hcov : ∀ (a : N.algebra B) (x : H),
      Uop (π a (Uop.symm x)) = π (N.stabAutHom B g a) x)
    (h : Physicslib4.IsFactor (N.localVonNeumann π hB₁ hB h₁)) :
    Physicslib4.IsFactor (N.localVonNeumann π hgB₁ hB (smul_subset_of_mem_stabilizer g h₁)) := by
  rw [← N.lieConj_image_localVonNeumann hB π Uop g hB₁ h₁ hgB₁ hcov]
  exact h.conj Uop

/-- **Geometric covariance as a von Neumann algebra isomorphism (curved spacetime).**
For `g ∈ Stab(B)`, conjugation by the implementing unitary `U(g)` is the
`*`-isomorphism `R(B₁) ≃ R(g · B₁)` of local von Neumann algebras: it restricts the
conjugation `*`-automorphism `T ↦ U(g) T U(g)⁻¹` of `B(H)`, whose image of `R(B₁)`
is exactly `R(g · B₁)` by geometric covariance. -/
noncomputable def localVonNeumannEquiv
    {B : Set M.Carrier} (hB : M.IsBasisSet B) (π : N.algebra B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Uop : H ≃ₗᵢ[ℂ] H) (g : ↥(MulAction.stabilizer M.Isom B))
    ⦃B₁ : Set M.Carrier⦄ (hB₁ : M.IsBasisSet B₁) (h₁ : B₁ ⊆ B)
    (hgB₁ : M.IsBasisSet ((g : M.Isom) • B₁))
    (hcov : ∀ (a : N.algebra B) (x : H),
      Uop (π a (Uop.symm x)) = π (N.stabAutHom B g a) x) :
    (N.localVonNeumannAlgebra π hB₁ hB h₁).toStarSubalgebra ≃⋆ₐ[ℂ]
      (N.localVonNeumannAlgebra π hgB₁ hB
        (smul_subset_of_mem_stabilizer g h₁)).toStarSubalgebra := by
  have hfun : (⇑(LinearIsometryEquiv.conjStarAlgEquiv Uop) : (H →L[ℂ] H) → (H →L[ℂ] H))
      = ⇑(Physicslib4.lieConj Uop) := by
    funext T; exact (Physicslib4.lieConj_apply_eq_conjStarAlgEquiv Uop T).symm
  have himg : ⇑(LinearIsometryEquiv.conjStarAlgEquiv Uop) '' N.localVonNeumann π hB₁ hB h₁
      = N.localVonNeumann π hgB₁ hB (smul_subset_of_mem_stabilizer g h₁) := by
    rw [hfun]; exact N.lieConj_image_localVonNeumann hB π Uop g hB₁ h₁ hgB₁ hcov
  have himg' : ⇑(LinearIsometryEquiv.conjStarAlgEquiv Uop).symm ''
      N.localVonNeumann π hgB₁ hB (smul_subset_of_mem_stabilizer g h₁)
        = N.localVonNeumann π hB₁ hB h₁ := by
    rw [← himg, Set.image_image]
    simp only [StarAlgEquiv.symm_apply_apply, Set.image_id']
  refine Physicslib4.restrictStarAlgEquiv (LinearIsometryEquiv.conjStarAlgEquiv Uop)
    (fun x hx => ?_) (fun y hy => ?_)
  · have hx' : x ∈ N.localVonNeumann π hB₁ hB h₁ := by
      have h1 : x ∈ ((N.localVonNeumannAlgebra π hB₁ hB h₁).toStarSubalgebra : Set (H →L[ℂ] H)) :=
        hx
      rwa [VonNeumannAlgebra.coe_toStarSubalgebra, coe_localVonNeumannAlgebra] at h1
    have hmem : LinearIsometryEquiv.conjStarAlgEquiv Uop x
        ∈ N.localVonNeumann π hgB₁ hB (smul_subset_of_mem_stabilizer g h₁) := by
      rw [← himg]; exact Set.mem_image_of_mem _ hx'
    change LinearIsometryEquiv.conjStarAlgEquiv Uop x
      ∈ (N.localVonNeumannAlgebra π hgB₁ hB (smul_subset_of_mem_stabilizer g h₁)).toStarSubalgebra
    rw [← SetLike.mem_coe, VonNeumannAlgebra.coe_toStarSubalgebra, coe_localVonNeumannAlgebra]
    exact hmem
  · have hy' : y ∈ N.localVonNeumann π hgB₁ hB (smul_subset_of_mem_stabilizer g h₁) := by
      have h1 : y ∈ ((N.localVonNeumannAlgebra π hgB₁ hB
          (smul_subset_of_mem_stabilizer g h₁)).toStarSubalgebra :
          Set (H →L[ℂ] H)) := hy
      rwa [VonNeumannAlgebra.coe_toStarSubalgebra, coe_localVonNeumannAlgebra] at h1
    have hmem : (LinearIsometryEquiv.conjStarAlgEquiv Uop).symm y
        ∈ N.localVonNeumann π hB₁ hB h₁ := by
      rw [← himg']; exact Set.mem_image_of_mem _ hy'
    change (LinearIsometryEquiv.conjStarAlgEquiv Uop).symm y
      ∈ (N.localVonNeumannAlgebra π hB₁ hB h₁).toStarSubalgebra
    rw [← SetLike.mem_coe, VonNeumannAlgebra.coe_toStarSubalgebra, coe_localVonNeumannAlgebra]
    exact hmem

end HaagKastlerNet
end HaagKastlerCurved
end AQFT
end Physicslib4
