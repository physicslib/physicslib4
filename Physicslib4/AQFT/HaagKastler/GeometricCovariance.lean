/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.QuasilocalIntertwiner
import Physicslib4.AQFT.HaagKastler.LocalVonNeumann
import Physicslib4.Operators.Conjugation

/-!
# Geometric covariance of the local von Neumann net

In the covariant representation of a Haag-Kastler net, the implementing unitaries
`U(L)` carry the local von Neumann algebra of a region `B` onto that of the
Lorentz-transformed region `L · B`:
`U(L) · R(B) · U(L)⁻¹ = R(L · B)`.

This is the statement that the symmetry group acts *geometrically* on the net of
von Neumann algebras. It rests on three ingredients, all already available:

* **Operator covariance** `U(L) π(a) U(L)⁻¹ = π(β_L a)` (from the GNS unitary
  construction, `IsInvariantState.exists_gns_unitary`);
* the fact that the covariance automorphism `β_L = N.action L` maps the local
  image `ι_B(𝔘(B))` onto `ι_{L·B}(𝔘(L·B))` (from `action_ι` and surjectivity of
  the covariance equivalence `covEquiv`);
* the algebraic fact that conjugation by a unit is a multiplicative automorphism,
  which therefore commutes with the bicommutant.

The reusable algebraic core is `MulEquiv.image_centralizer`: a multiplicative
automorphism maps the centralizer of a set onto the centralizer of its image,
hence maps bicommutants to bicommutants.
-/

open scoped Pointwise

namespace Physicslib4.GNS

variable {A : Type*} [CStarAlgebra A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The von Neumann algebra of an irreducible representation is a factor.** This
restates `center_gnsVonNeumann_eq_of_isIrreducible` in the factor vocabulary
(`Physicslib4.IsFactor`, the predicate used for orbit-invariance): the center
`π(A)'' ∩ (π(A)'')'` is exactly the scalars. -/
theorem isFactor_gnsVonNeumann_of_isIrreducible {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (hirr : IsIrreducible π) : Physicslib4.IsFactor (gnsVonNeumann π) :=
  center_gnsVonNeumann_eq_of_isIrreducible hirr

end Physicslib4.GNS

namespace Physicslib4
namespace AQFT
namespace HaagKastler
namespace HaagKastlerNet

open Physicslib4.GNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The local observable operators of a region `B` in a representation `π` of the
quasilocal algebra of a covariant net: the image `π(ι_B(𝔘(B)))`. -/
def covLocalOperators (N : HaagKastlerNet)
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B : Set StandardMinkowskiSpacetime.Carrier⦄ (hB : IsAlexandrovBasisSet B) : Set (H →L[ℂ] H) :=
  Set.range fun a : N.U.algebra B => π (N.quasilocal.ι hB a)

/-- The local von Neumann algebra `R(B) = π(ι_B(𝔘(B)))''` in a representation `π`
of the covariant net's quasilocal algebra. -/
def covLocalVonNeumann (N : HaagKastlerNet)
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B : Set StandardMinkowskiSpacetime.Carrier⦄ (hB : IsAlexandrovBasisSet B) : Set (H →L[ℂ] H) :=
  Set.centralizer (Set.centralizer (N.covLocalOperators π hB))

/-- **Conjugation carries the local operators of `B` onto those of `L · B`.**
Given operator covariance `U π(a) U⁻¹ = π(β_L a)`, the conjugation `lieConj U`
maps the local observable operators of `B` onto those of `L · B`. -/
theorem lieConj_image_covLocalOperators (N : HaagKastlerNet)
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Uop : H ≃ₗᵢ[ℂ] H)
    (L : InhomogeneousLorentzGroup) {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B)
    (hcov : ∀ (a : N.quasilocal.carrier) (x : H),
      Uop (π a (Uop.symm x)) = π (N.action L a) x) :
    Physicslib4.lieConj Uop '' N.covLocalOperators π hB
      = N.covLocalOperators π (isAlexandrovBasisSet_smul L hB) := by
  have hconj : ∀ a : N.quasilocal.carrier,
      Physicslib4.lieConj Uop (π a) = π (N.action L a) := by
    intro a
    ext x
    rw [Physicslib4.lieConj_apply]
    exact hcov a x
  ext y
  simp only [covLocalOperators, Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨N.covEquiv L B a, by rw [hconj (N.quasilocal.ι hB a), action_ι N L hB a]⟩
  · rintro ⟨a', rfl⟩
    refine ⟨π (N.quasilocal.ι hB ((N.covEquiv L B).symm a')),
      ⟨(N.covEquiv L B).symm a', rfl⟩, ?_⟩
    rw [hconj (N.quasilocal.ι hB ((N.covEquiv L B).symm a')),
      action_ι N L hB ((N.covEquiv L B).symm a'), StarAlgEquiv.apply_symm_apply]

/-- **Geometric covariance of the local von Neumann net (Minkowski).** In a
covariant representation `π` of the quasilocal algebra with operator covariance
`U(L) π(a) U(L)⁻¹ = π(β_L a)`, conjugation by the implementing unitary `U(L)`
carries the local von Neumann algebra of a region `B` onto that of the
Lorentz-transformed region `L · B`:
`U(L) · R(B) · U(L)⁻¹ = R(L · B)`.

The operator covariance hypothesis is exactly the last clause provided by
`IsInvariantState.exists_gns_unitary`, so this holds in the covariant GNS
representation of any invariant state. -/
theorem lieConj_image_covLocalVonNeumann (N : HaagKastlerNet)
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Uop : H ≃ₗᵢ[ℂ] H)
    (L : InhomogeneousLorentzGroup) {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B)
    (hcov : ∀ (a : N.quasilocal.carrier) (x : H),
      Uop (π a (Uop.symm x)) = π (N.action L a) x) :
    Physicslib4.lieConj Uop '' N.covLocalVonNeumann π hB
      = N.covLocalVonNeumann π (isAlexandrovBasisSet_smul L hB) := by
  unfold covLocalVonNeumann
  rw [(Physicslib4.lieConj Uop).image_centralizer_centralizer (N.covLocalOperators π hB),
    N.lieConj_image_covLocalOperators π Uop L hB hcov]

/-- The local observable operators of a region form a self-adjoint set. -/
theorem covLocalOperators_selfAdjoint (N : HaagKastlerNet)
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B : Set StandardMinkowskiSpacetime.Carrier⦄ (hB : IsAlexandrovBasisSet B) :
    ∀ x ∈ N.covLocalOperators π hB, star x ∈ N.covLocalOperators π hB := by
  rintro x ⟨a, rfl⟩
  exact ⟨star a, by simp only [map_star]⟩

/-- The local von Neumann algebra `R(B)` as a bundled `VonNeumannAlgebra`. -/
noncomputable def covLocalVonNeumannAlgebra (N : HaagKastlerNet)
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B : Set StandardMinkowskiSpacetime.Carrier⦄ (hB : IsAlexandrovBasisSet B) :
    VonNeumannAlgebra H :=
  vonNeumannOfSelfAdjoint (N.covLocalOperators π hB) (N.covLocalOperators_selfAdjoint π hB)

@[simp] theorem coe_covLocalVonNeumannAlgebra (N : HaagKastlerNet)
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    ⦃B : Set StandardMinkowskiSpacetime.Carrier⦄ (hB : IsAlexandrovBasisSet B) :
    (N.covLocalVonNeumannAlgebra π hB : Set (H →L[ℂ] H)) = N.covLocalVonNeumann π hB :=
  coe_vonNeumannOfSelfAdjoint _ _

/-- **Geometric covariance as a von Neumann algebra isomorphism (Minkowski).**
Conjugation by the implementing unitary `U(L)` is the `*`-isomorphism
`R(B) ≃ R(L · B)` of local von Neumann algebras: it restricts the conjugation
`*`-automorphism `T ↦ U(L) T U(L)⁻¹` of `B(H)` (Mathlib's
`LinearIsometryEquiv.conjStarAlgEquiv`), whose image of `R(B)` is exactly
`R(L · B)` by geometric covariance. -/
noncomputable def covLocalVonNeumannEquiv (N : HaagKastlerNet)
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Uop : H ≃ₗᵢ[ℂ] H)
    (L : InhomogeneousLorentzGroup) {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B)
    (hcov : ∀ (a : N.quasilocal.carrier) (x : H),
      Uop (π a (Uop.symm x)) = π (N.action L a) x) :
    (N.covLocalVonNeumannAlgebra π hB).toStarSubalgebra ≃⋆ₐ[ℂ]
      (N.covLocalVonNeumannAlgebra π (isAlexandrovBasisSet_smul L hB)).toStarSubalgebra := by
  let hL : IsAlexandrovBasisSet (L • B) := isAlexandrovBasisSet_smul L hB
  have hfun : (⇑(LinearIsometryEquiv.conjStarAlgEquiv Uop) : (H →L[ℂ] H) → (H →L[ℂ] H))
      = ⇑(Physicslib4.lieConj Uop) := by
    funext T; exact (Physicslib4.lieConj_apply_eq_conjStarAlgEquiv Uop T).symm
  have himg : ⇑(LinearIsometryEquiv.conjStarAlgEquiv Uop) '' N.covLocalVonNeumann π hB
      = N.covLocalVonNeumann π hL := by
    rw [hfun]; exact N.lieConj_image_covLocalVonNeumann π Uop L hB hcov
  have himg' : ⇑(LinearIsometryEquiv.conjStarAlgEquiv Uop).symm ''
      N.covLocalVonNeumann π hL = N.covLocalVonNeumann π hB := by
    rw [← himg, Set.image_image]
    simp only [StarAlgEquiv.symm_apply_apply, Set.image_id']
  refine Physicslib4.restrictStarAlgEquiv (LinearIsometryEquiv.conjStarAlgEquiv Uop)
    (fun x hx => ?_) (fun y hy => ?_)
  · have hx' : x ∈ N.covLocalVonNeumann π hB := by
      have h1 : x ∈ ((N.covLocalVonNeumannAlgebra π hB).toStarSubalgebra : Set (H →L[ℂ] H)) := hx
      rwa [VonNeumannAlgebra.coe_toStarSubalgebra, coe_covLocalVonNeumannAlgebra] at h1
    have hmem : LinearIsometryEquiv.conjStarAlgEquiv Uop x
        ∈ N.covLocalVonNeumann π hL := by
      rw [← himg]; exact Set.mem_image_of_mem _ hx'
    change LinearIsometryEquiv.conjStarAlgEquiv Uop x
      ∈ (N.covLocalVonNeumannAlgebra π hL).toStarSubalgebra
    rw [← SetLike.mem_coe, VonNeumannAlgebra.coe_toStarSubalgebra, coe_covLocalVonNeumannAlgebra]
    exact hmem
  · have hy' : y ∈ N.covLocalVonNeumann π hL := by
      have h1 : y ∈ ((N.covLocalVonNeumannAlgebra π hL).toStarSubalgebra : Set (H →L[ℂ] H)) :=
        hy
      rwa [VonNeumannAlgebra.coe_toStarSubalgebra, coe_covLocalVonNeumannAlgebra] at h1
    have hmem : (LinearIsometryEquiv.conjStarAlgEquiv Uop).symm y
        ∈ N.covLocalVonNeumann π hB := by
      rw [← himg']; exact Set.mem_image_of_mem _ hy'
    change (LinearIsometryEquiv.conjStarAlgEquiv Uop).symm y
      ∈ (N.covLocalVonNeumannAlgebra π hB).toStarSubalgebra
    rw [← SetLike.mem_coe, VonNeumannAlgebra.coe_toStarSubalgebra, coe_covLocalVonNeumannAlgebra]
    exact hmem

/-- **Orbit-invariance of factoriality (Minkowski).** If the local von Neumann
algebra `R(B)` of a region is a factor (trivial center), then so is `R(L · B)`
for every Lorentz transformation `L`. Geometric covariance exhibits `R(L · B)` as
the unitary conjugate `U(L) R(B) U(L)⁻¹`, and conjugation preserves the factor
property. So being a factor is constant along the Lorentz orbit of a region. -/
theorem covLocalVonNeumann_isFactor_smul (N : HaagKastlerNet)
    (π : N.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Uop : H ≃ₗᵢ[ℂ] H)
    (L : InhomogeneousLorentzGroup) {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B)
    (hcov : ∀ (a : N.quasilocal.carrier) (x : H),
      Uop (π a (Uop.symm x)) = π (N.action L a) x)
    (h : Physicslib4.IsFactor (N.covLocalVonNeumann π hB)) :
    Physicslib4.IsFactor (N.covLocalVonNeumann π (isAlexandrovBasisSet_smul L hB)) := by
  rw [← N.lieConj_image_covLocalVonNeumann π Uop L hB hcov]
  exact h.conj Uop

end HaagKastlerNet
end HaagKastler
end AQFT
end Physicslib4
