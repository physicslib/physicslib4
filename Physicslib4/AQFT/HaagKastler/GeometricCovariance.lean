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
* the fact that the covariance automorphism `β_L = C.action L` maps the local
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
namespace CovariantQuasilocalAlgebra

open Physicslib4.GNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The local observable operators of a region `B` in a representation `π` of the
quasilocal algebra of a covariant net: the image `π(ι_B(𝔘(B)))`. -/
def covLocalOperators (C : CovariantQuasilocalAlgebra)
    (π : C.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B : Set StandardMinkowskiSpacetime.Carrier) : Set (H →L[ℂ] H) :=
  Set.range fun a : C.net.U.algebra B => π (C.quasilocal.ι B a)

/-- The local von Neumann algebra `R(B) = π(ι_B(𝔘(B)))''` in a representation `π`
of the covariant net's quasilocal algebra. -/
def covLocalVonNeumann (C : CovariantQuasilocalAlgebra)
    (π : C.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B : Set StandardMinkowskiSpacetime.Carrier) : Set (H →L[ℂ] H) :=
  Set.centralizer (Set.centralizer (C.covLocalOperators π B))

/-- **Conjugation carries the local operators of `B` onto those of `L · B`.**
Given operator covariance `U π(a) U⁻¹ = π(β_L a)`, the conjugation `lieConj U`
maps the local observable operators of `B` onto those of `L · B`. -/
theorem lieConj_image_covLocalOperators (C : CovariantQuasilocalAlgebra)
    (π : C.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Uop : H ≃ₗᵢ[ℂ] H)
    (L : InhomogeneousLorentzGroup) {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B)
    (hcov : ∀ (a : C.quasilocal.carrier) (x : H),
      Uop (π a (Uop.symm x)) = π (C.action L a) x) :
    Physicslib4.lieConj Uop '' C.covLocalOperators π B = C.covLocalOperators π (L • B) := by
  have hconj : ∀ a : C.quasilocal.carrier,
      Physicslib4.lieConj Uop (π a) = π (C.action L a) := by
    intro a
    ext x
    rw [Physicslib4.lieConj_apply]
    exact hcov a x
  ext y
  simp only [covLocalOperators, Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨C.net.covEquiv L B a, by rw [hconj (C.quasilocal.ι B a), action_ι C L hB a]⟩
  · rintro ⟨a', rfl⟩
    refine ⟨π (C.quasilocal.ι B ((C.net.covEquiv L B).symm a')),
      ⟨(C.net.covEquiv L B).symm a', rfl⟩, ?_⟩
    rw [hconj (C.quasilocal.ι B ((C.net.covEquiv L B).symm a')),
      action_ι C L hB ((C.net.covEquiv L B).symm a'), StarAlgEquiv.apply_symm_apply]

/-- **Geometric covariance of the local von Neumann net (Minkowski).** In a
covariant representation `π` of the quasilocal algebra with operator covariance
`U(L) π(a) U(L)⁻¹ = π(β_L a)`, conjugation by the implementing unitary `U(L)`
carries the local von Neumann algebra of a region `B` onto that of the
Lorentz-transformed region `L · B`:
`U(L) · R(B) · U(L)⁻¹ = R(L · B)`.

The operator covariance hypothesis is exactly the last clause provided by
`IsInvariantState.exists_gns_unitary`, so this holds in the covariant GNS
representation of any invariant state. -/
theorem lieConj_image_covLocalVonNeumann (C : CovariantQuasilocalAlgebra)
    (π : C.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Uop : H ≃ₗᵢ[ℂ] H)
    (L : InhomogeneousLorentzGroup) {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B)
    (hcov : ∀ (a : C.quasilocal.carrier) (x : H),
      Uop (π a (Uop.symm x)) = π (C.action L a) x) :
    Physicslib4.lieConj Uop '' C.covLocalVonNeumann π B
      = C.covLocalVonNeumann π (L • B) := by
  unfold covLocalVonNeumann
  rw [(Physicslib4.lieConj Uop).image_centralizer_centralizer (C.covLocalOperators π B),
    C.lieConj_image_covLocalOperators π Uop L hB hcov]

/-- The local observable operators of a region form a self-adjoint set. -/
theorem covLocalOperators_selfAdjoint (C : CovariantQuasilocalAlgebra)
    (π : C.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B : Set StandardMinkowskiSpacetime.Carrier) :
    ∀ x ∈ C.covLocalOperators π B, star x ∈ C.covLocalOperators π B := by
  rintro x ⟨a, rfl⟩
  exact ⟨star a, by simp only [map_star]⟩

/-- The local von Neumann algebra `R(B)` as a bundled `VonNeumannAlgebra`. -/
noncomputable def covLocalVonNeumannAlgebra (C : CovariantQuasilocalAlgebra)
    (π : C.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B : Set StandardMinkowskiSpacetime.Carrier) : VonNeumannAlgebra H :=
  vonNeumannOfSelfAdjoint (C.covLocalOperators π B) (C.covLocalOperators_selfAdjoint π B)

@[simp] theorem coe_covLocalVonNeumannAlgebra (C : CovariantQuasilocalAlgebra)
    (π : C.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B : Set StandardMinkowskiSpacetime.Carrier) :
    (C.covLocalVonNeumannAlgebra π B : Set (H →L[ℂ] H)) = C.covLocalVonNeumann π B :=
  coe_vonNeumannOfSelfAdjoint _ _

/-- **Geometric covariance as a von Neumann algebra isomorphism (Minkowski).**
Conjugation by the implementing unitary `U(L)` is the `*`-isomorphism
`R(B) ≃ R(L · B)` of local von Neumann algebras: it restricts the conjugation
`*`-automorphism `T ↦ U(L) T U(L)⁻¹` of `B(H)` (Mathlib's
`LinearIsometryEquiv.conjStarAlgEquiv`), whose image of `R(B)` is exactly
`R(L · B)` by geometric covariance. -/
noncomputable def covLocalVonNeumannEquiv (C : CovariantQuasilocalAlgebra)
    (π : C.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Uop : H ≃ₗᵢ[ℂ] H)
    (L : InhomogeneousLorentzGroup) {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B)
    (hcov : ∀ (a : C.quasilocal.carrier) (x : H),
      Uop (π a (Uop.symm x)) = π (C.action L a) x) :
    (C.covLocalVonNeumannAlgebra π B).toStarSubalgebra ≃⋆ₐ[ℂ]
      (C.covLocalVonNeumannAlgebra π (L • B)).toStarSubalgebra := by
  have hfun : (⇑(LinearIsometryEquiv.conjStarAlgEquiv Uop) : (H →L[ℂ] H) → (H →L[ℂ] H))
      = ⇑(Physicslib4.lieConj Uop) := by
    funext T; exact (Physicslib4.lieConj_apply_eq_conjStarAlgEquiv Uop T).symm
  have himg : ⇑(LinearIsometryEquiv.conjStarAlgEquiv Uop) '' C.covLocalVonNeumann π B
      = C.covLocalVonNeumann π (L • B) := by
    rw [hfun]; exact C.lieConj_image_covLocalVonNeumann π Uop L hB hcov
  have himg' : ⇑(LinearIsometryEquiv.conjStarAlgEquiv Uop).symm ''
      C.covLocalVonNeumann π (L • B) = C.covLocalVonNeumann π B := by
    rw [← himg, Set.image_image]
    simp only [StarAlgEquiv.symm_apply_apply, Set.image_id']
  refine Physicslib4.restrictStarAlgEquiv (LinearIsometryEquiv.conjStarAlgEquiv Uop)
    (fun x hx => ?_) (fun y hy => ?_)
  · have hx' : x ∈ C.covLocalVonNeumann π B := by
      have h1 : x ∈ ((C.covLocalVonNeumannAlgebra π B).toStarSubalgebra : Set (H →L[ℂ] H)) := hx
      rwa [VonNeumannAlgebra.coe_toStarSubalgebra, coe_covLocalVonNeumannAlgebra] at h1
    have hmem : LinearIsometryEquiv.conjStarAlgEquiv Uop x
        ∈ C.covLocalVonNeumann π (L • B) := by
      rw [← himg]; exact Set.mem_image_of_mem _ hx'
    change LinearIsometryEquiv.conjStarAlgEquiv Uop x
      ∈ (C.covLocalVonNeumannAlgebra π (L • B)).toStarSubalgebra
    rw [← SetLike.mem_coe, VonNeumannAlgebra.coe_toStarSubalgebra, coe_covLocalVonNeumannAlgebra]
    exact hmem
  · have hy' : y ∈ C.covLocalVonNeumann π (L • B) := by
      have h1 : y ∈ ((C.covLocalVonNeumannAlgebra π (L • B)).toStarSubalgebra : Set (H →L[ℂ] H)) :=
        hy
      rwa [VonNeumannAlgebra.coe_toStarSubalgebra, coe_covLocalVonNeumannAlgebra] at h1
    have hmem : (LinearIsometryEquiv.conjStarAlgEquiv Uop).symm y
        ∈ C.covLocalVonNeumann π B := by
      rw [← himg']; exact Set.mem_image_of_mem _ hy'
    change (LinearIsometryEquiv.conjStarAlgEquiv Uop).symm y
      ∈ (C.covLocalVonNeumannAlgebra π B).toStarSubalgebra
    rw [← SetLike.mem_coe, VonNeumannAlgebra.coe_toStarSubalgebra, coe_covLocalVonNeumannAlgebra]
    exact hmem

/-- **Orbit-invariance of factoriality (Minkowski).** If the local von Neumann
algebra `R(B)` of a region is a factor (trivial center), then so is `R(L · B)`
for every Lorentz transformation `L`. Geometric covariance exhibits `R(L · B)` as
the unitary conjugate `U(L) R(B) U(L)⁻¹`, and conjugation preserves the factor
property. So being a factor is constant along the Lorentz orbit of a region. -/
theorem covLocalVonNeumann_isFactor_smul (C : CovariantQuasilocalAlgebra)
    (π : C.quasilocal.carrier →⋆ₐ[ℂ] (H →L[ℂ] H)) (Uop : H ≃ₗᵢ[ℂ] H)
    (L : InhomogeneousLorentzGroup) {B : Set StandardMinkowskiSpacetime.Carrier}
    (hB : IsAlexandrovBasisSet B)
    (hcov : ∀ (a : C.quasilocal.carrier) (x : H),
      Uop (π a (Uop.symm x)) = π (C.action L a) x)
    (h : Physicslib4.IsFactor (C.covLocalVonNeumann π B)) :
    Physicslib4.IsFactor (C.covLocalVonNeumann π (L • B)) := by
  rw [← C.lieConj_image_covLocalVonNeumann π Uop L hB hcov]
  exact h.conj Uop

end CovariantQuasilocalAlgebra
end HaagKastler
end AQFT
end Physicslib4
