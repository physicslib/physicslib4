/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.Irreducibility
import Physicslib4.Operators.Conjugation

/-!
# Unitary equivalence of representations

Two `*`-representations `π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)` and
`π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)` are **unitarily equivalent** when there is a
Hilbert-space isometric isomorphism `U : H₁ ≃ₗᵢ[ℂ] H₂` intertwining them:
`U (π₁ a x) = π₂ a (U x)`. This is the basic equivalence of the representation
theory underlying superselection sectors.

This file defines `UnitaryEquiv`, proves it is an equivalence relation
(reflexive, symmetric, transitive), and shows that the two central
representation-theoretic properties — **irreducibility** and **factoriality**
(trivial center of the generated von Neumann algebra) — are invariants of unitary
equivalence. The transport is packaged through the cross-space conjugation
`conjMulEquiv U : (H₁ →L[ℂ] H₁) ≃* (H₂ →L[ℂ] H₂)`, `T ↦ U T U⁻¹`, which carries
`π₁(A)` onto `π₂(A)`, centralizers onto centralizers, and scalars onto scalars.
-/

namespace Physicslib4
namespace GNS

variable {A : Type*} [CStarAlgebra A]
variable {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
variable {H₃ : Type*} [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃]

/-- Two `*`-representations of `A` are **unitarily equivalent** when an isometric
isomorphism of the underlying Hilbert spaces intertwines them. -/
def UnitaryEquiv (π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)) :
    Prop :=
  ∃ U : H₁ ≃ₗᵢ[ℂ] H₂, ∀ (a : A) (x : H₁), U (π₁ a x) = π₂ a (U x)

/-! ### Equivalence relation -/

/-- Unitary equivalence is reflexive. -/
theorem UnitaryEquiv.refl (π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) : UnitaryEquiv π π :=
  ⟨LinearIsometryEquiv.refl ℂ H₁, fun _ _ => rfl⟩

/-- Unitary equivalence is symmetric. -/
theorem UnitaryEquiv.symm {π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)}
    {π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)} (h : UnitaryEquiv π₁ π₂) : UnitaryEquiv π₂ π₁ := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U.symm, fun a y => U.injective ?_⟩
  rw [LinearIsometryEquiv.apply_symm_apply, hU, LinearIsometryEquiv.apply_symm_apply]

/-- Unitary equivalence is transitive. -/
theorem UnitaryEquiv.trans {π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)}
    {π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)} {π₃ : A →⋆ₐ[ℂ] (H₃ →L[ℂ] H₃)}
    (h₁₂ : UnitaryEquiv π₁ π₂) (h₂₃ : UnitaryEquiv π₂ π₃) : UnitaryEquiv π₁ π₃ := by
  obtain ⟨U, hU⟩ := h₁₂
  obtain ⟨V, hV⟩ := h₂₃
  refine ⟨U.trans V, fun a x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply]
  rw [hU, hV]

/-! ### Cross-space conjugation of operators -/

/-- Conjugation of an operator `T : H₁ →L H₁` by a unitary `U : H₁ ≃ₗᵢ H₂`,
producing `U T U⁻¹ : H₂ →L H₂`. -/
noncomputable def conjCLM (U : H₁ ≃ₗᵢ[ℂ] H₂) (T : H₁ →L[ℂ] H₁) : H₂ →L[ℂ] H₂ :=
  (↑U.toContinuousLinearEquiv : H₁ →L[ℂ] H₂).comp
    (T.comp (↑U.symm.toContinuousLinearEquiv : H₂ →L[ℂ] H₁))

omit [CompleteSpace H₁] [CompleteSpace H₂] in
@[simp] theorem conjCLM_apply (U : H₁ ≃ₗᵢ[ℂ] H₂) (T : H₁ →L[ℂ] H₁) (x : H₂) :
    conjCLM U T x = U (T (U.symm x)) := by
  simp [conjCLM, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]

/-- Conjugation by `U` as a multiplicative isomorphism of operator algebras
`(H₁ →L H₁) ≃* (H₂ →L H₂)`. -/
noncomputable def conjMulEquiv (U : H₁ ≃ₗᵢ[ℂ] H₂) :
    (H₁ →L[ℂ] H₁) ≃* (H₂ →L[ℂ] H₂) where
  toFun := conjCLM U
  invFun := conjCLM U.symm
  left_inv T := by ext x; simp
  right_inv S := by ext x; simp
  map_mul' S T := by
    ext x; simp [ContinuousLinearMap.mul_apply]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
@[simp] theorem conjMulEquiv_apply (U : H₁ ≃ₗᵢ[ℂ] H₂) (T : H₁ →L[ℂ] H₁) :
    conjMulEquiv U T = conjCLM U T := rfl

/-- The general fact that a multiplicative isomorphism carries centralizers to
centralizers. -/
theorem mulEquiv_image_centralizer {M N : Type*} [Monoid M] [Monoid N] (e : M ≃* N)
    (s : Set M) : e '' Set.centralizer s = Set.centralizer (e '' s) := by
  ext y
  simp only [Set.mem_image, Set.mem_centralizer_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩ _ ⟨m, hm, rfl⟩
    rw [← map_mul, ← map_mul, hx m hm]
  · intro hy
    refine ⟨e.symm y, fun m hm => ?_, e.apply_symm_apply y⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy (e m) ⟨m, hm, rfl⟩

/-- Conjugation carries `π₁(a)` to `π₂(a)` when `U` intertwines the two
representations. -/
theorem conjMulEquiv_pi {π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)}
    {π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)} {U : H₁ ≃ₗᵢ[ℂ] H₂}
    (hU : ∀ (a : A) (x : H₁), U (π₁ a x) = π₂ a (U x)) (a : A) :
    conjMulEquiv U (π₁ a) = π₂ a := by
  ext x
  rw [conjMulEquiv_apply, conjCLM_apply, hU, LinearIsometryEquiv.apply_symm_apply]

/-- Conjugation carries the image of `π₁` onto the image of `π₂`. -/
theorem conjMulEquiv_image_range {π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)}
    {π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)} {U : H₁ ≃ₗᵢ[ℂ] H₂}
    (hU : ∀ (a : A) (x : H₁), U (π₁ a x) = π₂ a (U x)) :
    conjMulEquiv U '' Set.range π₁ = Set.range π₂ := by
  ext S
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (conjMulEquiv_pi hU a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨π₁ a, ⟨a, rfl⟩, conjMulEquiv_pi hU a⟩

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- Conjugation fixes the scalar operators setwise. -/
theorem conjMulEquiv_image_scalar (U : H₁ ≃ₗᵢ[ℂ] H₂) :
    conjMulEquiv U '' scalarOperators H₁ = scalarOperators H₂ := by
  have hfix : ∀ c : ℂ, conjMulEquiv U (c • 1) = c • 1 := by
    intro c
    ext x
    rw [conjMulEquiv_apply, conjCLM_apply]
    simp [map_smul]
  ext S
  simp only [scalarOperators, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, hfix c⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c • 1, ⟨c, rfl⟩, hfix c⟩

/-! ### Invariance of irreducibility and factoriality -/

/-- Irreducibility is exactly triviality of the commutant: the commutant of the
image `π(A)` is the scalar operators. -/
theorem isIrreducible_iff_centralizer {π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)} :
    IsIrreducible π ↔ Set.centralizer (Set.range π) = scalarOperators H₁ := by
  constructor
  · intro hirr
    refine Set.Subset.antisymm (fun T hT => hirr T ?_) ?_
    · exact fun a => Set.mem_centralizer_iff.mp hT (π a) ⟨a, rfl⟩
    · rintro _ ⟨c, rfl⟩
      exact Set.mem_centralizer_iff.mpr fun M _ => by
        rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  · intro hcent T hT
    have hmem : T ∈ Set.centralizer (Set.range π) :=
      Set.mem_centralizer_iff.mpr (by rintro _ ⟨a, rfl⟩; exact hT a)
    rw [hcent] at hmem
    exact hmem

/-- **Irreducibility is a unitary invariant.** If `π₁` is unitarily equivalent to
`π₂` and `π₁` is irreducible, then so is `π₂`. -/
theorem UnitaryEquiv.isIrreducible {π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)}
    {π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)} (h : UnitaryEquiv π₁ π₂)
    (hirr : IsIrreducible π₁) : IsIrreducible π₂ := by
  obtain ⟨U, hU⟩ := h
  rw [isIrreducible_iff_centralizer] at hirr ⊢
  rw [← conjMulEquiv_image_range hU, ← mulEquiv_image_centralizer, hirr,
    conjMulEquiv_image_scalar]

/-- **Irreducibility is invariant under unitary equivalence** (iff form). -/
theorem UnitaryEquiv.isIrreducible_iff {π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)}
    {π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)} (h : UnitaryEquiv π₁ π₂) :
    IsIrreducible π₁ ↔ IsIrreducible π₂ :=
  ⟨h.isIrreducible, h.symm.isIrreducible⟩

/-- Conjugation carries the generated von Neumann algebra of `π₁` onto that of
`π₂`. -/
theorem conjMulEquiv_image_gnsVonNeumann {π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)}
    {π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)} {U : H₁ ≃ₗᵢ[ℂ] H₂}
    (hU : ∀ (a : A) (x : H₁), U (π₁ a x) = π₂ a (U x)) :
    gnsVonNeumann π₂ = conjMulEquiv U '' gnsVonNeumann π₁ := by
  unfold gnsVonNeumann
  rw [← conjMulEquiv_image_range hU, ← mulEquiv_image_centralizer,
    ← mulEquiv_image_centralizer]

/-- **Factoriality is a unitary invariant.** If `π₁` is unitarily equivalent to
`π₂` and the von Neumann algebra `π₁(A)''` is a factor, then so is `π₂(A)''`. -/
theorem UnitaryEquiv.isFactor {π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)}
    {π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)} (h : UnitaryEquiv π₁ π₂)
    (hf : IsFactor (gnsVonNeumann π₁)) : IsFactor (gnsVonNeumann π₂) := by
  obtain ⟨U, hU⟩ := h
  rw [conjMulEquiv_image_gnsVonNeumann hU]
  unfold IsFactor at hf ⊢
  rw [← mulEquiv_image_centralizer, ← Set.image_inter (conjMulEquiv U).injective, hf,
    conjMulEquiv_image_scalar]

/-- **Factoriality is invariant under unitary equivalence** (iff form). -/
theorem UnitaryEquiv.isFactor_iff {π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)}
    {π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)} (h : UnitaryEquiv π₁ π₂) :
    IsFactor (gnsVonNeumann π₁) ↔ IsFactor (gnsVonNeumann π₂) :=
  ⟨h.isFactor, h.symm.isFactor⟩

end GNS
end Physicslib4
