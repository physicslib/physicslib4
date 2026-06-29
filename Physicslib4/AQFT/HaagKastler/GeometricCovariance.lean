/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.HaagKastler.QuasilocalIntertwiner
import Physicslib4.AQFT.HaagKastler.LocalVonNeumann

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

namespace Units

variable {M : Type*} [Monoid M]

/-- Conjugation by a unit `u`, as a multiplicative automorphism of the monoid:
`x ↦ u * x * u⁻¹`. -/
def conjMulEquiv (u : Mˣ) : M ≃* M where
  toFun x := ↑u * x * ↑u⁻¹
  invFun x := ↑u⁻¹ * x * ↑u
  left_inv x := by
    calc (↑u⁻¹ : M) * (↑u * x * ↑u⁻¹) * ↑u
        = (↑u⁻¹ * ↑u) * x * (↑u⁻¹ * ↑u) := by noncomm_ring
      _ = x := by rw [u.inv_mul]; noncomm_ring
  right_inv x := by
    calc (↑u : M) * (↑u⁻¹ * x * ↑u) * ↑u⁻¹
        = (↑u * ↑u⁻¹) * x * (↑u * ↑u⁻¹) := by noncomm_ring
      _ = x := by rw [u.mul_inv]; noncomm_ring
  map_mul' x y := by
    calc (↑u : M) * (x * y) * ↑u⁻¹
        = ↑u * x * (↑u⁻¹ * ↑u) * y * ↑u⁻¹ := by rw [u.inv_mul]; noncomm_ring
      _ = (↑u * x * ↑u⁻¹) * (↑u * y * ↑u⁻¹) := by noncomm_ring

@[simp] theorem conjMulEquiv_apply (u : Mˣ) (x : M) :
    conjMulEquiv u x = ↑u * x * ↑u⁻¹ := rfl

end Units

namespace MulEquiv

variable {M : Type*} [Mul M]

/-- A multiplicative automorphism maps the centralizer of a set onto the
centralizer of its image. -/
theorem image_centralizer (φ : M ≃* M) (S : Set M) :
    φ '' Set.centralizer S = Set.centralizer (φ '' S) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [Set.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Set.mem_centralizer_iff.mp hx s hs)
  · intro y hy
    refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
    rw [Set.mem_centralizer_iff]
    intro s hs
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply]
    exact Set.mem_centralizer_iff.mp hy (φ s) ⟨s, hs, rfl⟩

/-- A multiplicative automorphism maps bicommutants to bicommutants. -/
theorem image_centralizer_centralizer (φ : M ≃* M) (S : Set M) :
    φ '' Set.centralizer (Set.centralizer S)
      = Set.centralizer (Set.centralizer (φ '' S)) := by
  rw [φ.image_centralizer, φ.image_centralizer]

end MulEquiv

namespace Physicslib4

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Conjugation by a unitary `U : H ≃ₗᵢ[ℂ] H` as a multiplicative automorphism of
the algebra `H →L[ℂ] H` of bounded operators: `T ↦ U T U⁻¹`. -/
noncomputable def lieConj (Uop : H ≃ₗᵢ[ℂ] H) : (H →L[ℂ] H) ≃* (H →L[ℂ] H) :=
  Units.conjMulEquiv (Uop.toContinuousLinearEquiv.toUnit)

omit [CompleteSpace H] in
@[simp] theorem lieConj_apply (Uop : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) (x : H) :
    lieConj Uop T x = Uop (T (Uop.symm x)) := by
  change ((Uop.toContinuousLinearEquiv : H →L[ℂ] H) * T
        * (Uop.toContinuousLinearEquiv.symm : H →L[ℂ] H)) x = Uop (T (Uop.symm x))
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

/-- The scalar operators `{c · 1 : c ∈ ℂ}` of a Hilbert space, the (would-be)
center of any von Neumann algebra acting irreducibly. -/
def scalarOperators (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Set (H →L[ℂ] H) :=
  {T : H →L[ℂ] H | ∃ c : ℂ, T = c • 1}

/-- A von Neumann algebra (a set of operators) is a *factor* when its center
`R ∩ R'` is exactly the scalars. -/
def IsFactor (R : Set (H →L[ℂ] H)) : Prop :=
  R ∩ Set.centralizer R = scalarOperators H

omit [CompleteSpace H] in
/-- Conjugation by a unitary fixes the scalar operators setwise:
`U (c · 1) U⁻¹ = c · 1`. -/
theorem lieConj_image_scalarOperators (Uop : H ≃ₗᵢ[ℂ] H) :
    lieConj Uop '' scalarOperators H = scalarOperators H := by
  have hfix : ∀ c : ℂ, lieConj Uop (c • (1 : H →L[ℂ] H)) = c • 1 := by
    intro c
    ext x
    rw [lieConj_apply]
    simp
  ext T
  simp only [scalarOperators, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, hfix c⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c • (1 : H →L[ℂ] H), ⟨c, rfl⟩, hfix c⟩

omit [CompleteSpace H] in
/-- **Conjugation preserves factoriality.** If a von Neumann algebra `R` is a
factor, so is its conjugate `U R U⁻¹`. Conjugation is a multiplicative
automorphism, so it carries the center `R ∩ R'` onto the center of `U R U⁻¹` and
fixes the scalars. -/
theorem IsFactor.conj (Uop : H ≃ₗᵢ[ℂ] H) {R : Set (H →L[ℂ] H)} (h : IsFactor R) :
    IsFactor (lieConj Uop '' R) := by
  unfold IsFactor at h ⊢
  rw [← (lieConj Uop).image_centralizer R, ← Set.image_inter (lieConj Uop).injective, h,
    lieConj_image_scalarOperators]

end Physicslib4

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
