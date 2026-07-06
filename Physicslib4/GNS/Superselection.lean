/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.UnitaryEquiv

/-!
# Disjointness and quasi-equivalence of representations

Building on `UnitaryEquiv`, this file introduces the two coarser comparisons of
`*`-representations from superselection theory:

* an **intertwiner** is a bounded operator `T : H₁ →L H₂` with `T π₁(a) = π₂(a) T`;
* two representations are **disjoint** (`AreDisjoint`) when the only intertwiner is
  `0` — equivalently, they share no unitarily equivalent subrepresentation;
* two representations are **quasi-equivalent** (`QuasiEquiv`) when there is a
  `*`-isomorphism of the generated von Neumann algebras `π₁(A)'' ≃⋆ₐ π₂(A)''`
  carrying `π₁(a)` to `π₂(a)`.

We prove the basic algebra of intertwiners, that disjointness is symmetric and
irreflexive (unitarily equivalent representations are never disjoint), that
quasi-equivalence is an equivalence relation, and that unitary equivalence implies
quasi-equivalence.
-/

namespace Physicslib4
namespace GNS

open scoped InnerProductSpace

variable {A : Type*} [CStarAlgebra A]
variable {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
variable {H₃ : Type*} [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃]

/-! ### Intertwiners -/

/-- `T : H₁ →L H₂` **intertwines** `π₁` and `π₂` when `T π₁(a) = π₂(a) T`. -/
def Intertwines (π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂))
    (T : H₁ →L[ℂ] H₂) : Prop :=
  ∀ (a : A) (x : H₁), T (π₁ a x) = π₂ a (T x)

variable {π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)} {π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)}
  {π₃ : A →⋆ₐ[ℂ] (H₃ →L[ℂ] H₃)}

theorem intertwines_zero : Intertwines π₁ π₂ (0 : H₁ →L[ℂ] H₂) := fun a x => by simp

theorem Intertwines.add {S T : H₁ →L[ℂ] H₂} (hS : Intertwines π₁ π₂ S)
    (hT : Intertwines π₁ π₂ T) : Intertwines π₁ π₂ (S + T) := fun a x => by
  simp only [ContinuousLinearMap.add_apply, hS a x, hT a x, map_add]

theorem Intertwines.smul {T : H₁ →L[ℂ] H₂} (c : ℂ) (hT : Intertwines π₁ π₂ T) :
    Intertwines π₁ π₂ (c • T) := fun a x => by
  simp only [ContinuousLinearMap.smul_apply, hT a x, map_smul]

/-- The composition of intertwiners is an intertwiner. -/
theorem Intertwines.comp {S : H₂ →L[ℂ] H₃} {T : H₁ →L[ℂ] H₂}
    (hS : Intertwines π₂ π₃ S) (hT : Intertwines π₁ π₂ T) :
    Intertwines π₁ π₃ (S.comp T) := fun a x => by
  simp only [ContinuousLinearMap.comp_apply]
  rw [hT a x, hS a (T x)]

/-- The adjoint of an intertwiner `π₁ → π₂` is an intertwiner `π₂ → π₁`. -/
theorem Intertwines.adjoint {T : H₁ →L[ℂ] H₂} (hT : Intertwines π₁ π₂ T) :
    Intertwines π₂ π₁ (ContinuousLinearMap.adjoint T) := by
  have hcomp : ∀ a : A, (ContinuousLinearMap.adjoint T).comp (π₂ a)
      = (π₁ a).comp (ContinuousLinearMap.adjoint T) := by
    intro a
    have h1 : T.comp (π₁ (star a)) = (π₂ (star a)).comp T :=
      ContinuousLinearMap.ext (fun x => hT (star a) x)
    have h2 := congrArg ContinuousLinearMap.adjoint h1
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp] at h2
    have hp1 : ContinuousLinearMap.adjoint (π₁ (star a)) = π₁ a := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_star]
    have hp2 : ContinuousLinearMap.adjoint (π₂ (star a)) = π₂ a := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_star]
    rw [hp1, hp2] at h2
    exact h2.symm
  intro a x
  have hx := DFunLike.congr_fun (hcomp a) x
  simpa only [ContinuousLinearMap.comp_apply] using hx

/-! ### Disjointness -/

/-- Two representations are **disjoint** when the only operator intertwining them
is `0`. -/
def AreDisjoint (π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)) :
    Prop :=
  ∀ T : H₁ →L[ℂ] H₂, Intertwines π₁ π₂ T → T = 0

/-- Disjointness is symmetric (take adjoints of intertwiners). -/
theorem AreDisjoint.symm (h : AreDisjoint π₁ π₂) : AreDisjoint π₂ π₁ := by
  intro T hT
  have h0 : ContinuousLinearMap.adjoint T = 0 := h _ hT.adjoint
  rw [← ContinuousLinearMap.adjoint_adjoint T, h0, map_zero]

/-- A representation on a nonzero Hilbert space is never disjoint from itself (the
identity is a nonzero intertwiner). -/
theorem not_areDisjoint_self [Nontrivial H₁] (π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) :
    ¬ AreDisjoint π π := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : H₁)
  have h1 : (1 : H₁ →L[ℂ] H₁) = 0 := h 1 (fun a x => by simp)
  exact hv (by simpa using ContinuousLinearMap.ext_iff.mp h1 v)

/-- **Unitarily equivalent representations are not disjoint** (on nonzero spaces):
the implementing unitary is a nonzero intertwiner. -/
theorem UnitaryEquiv.not_areDisjoint [Nontrivial H₁] (h : UnitaryEquiv π₁ π₂) :
    ¬ AreDisjoint π₁ π₂ := by
  obtain ⟨U, hU⟩ := h
  intro hd
  have hint : Intertwines π₁ π₂ (↑U.toContinuousLinearEquiv : H₁ →L[ℂ] H₂) := by
    intro a x
    simp only [ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    exact hU a x
  have h0 : (↑U.toContinuousLinearEquiv : H₁ →L[ℂ] H₂) = 0 := hd _ hint
  obtain ⟨v, hv⟩ := exists_ne (0 : H₁)
  have hUv : U v = 0 := by
    have := ContinuousLinearMap.ext_iff.mp h0 v
    simpa only [ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearMap.zero_apply] using this
  exact hv (U.injective (hUv.trans (map_zero U).symm))

/-! ### Quasi-equivalence -/

omit [CompleteSpace H₁] [CompleteSpace H₂] in
theorem conjCLM_add (U : H₁ ≃ₗᵢ[ℂ] H₂) (S T : H₁ →L[ℂ] H₁) :
    conjCLM U (S + T) = conjCLM U S + conjCLM U T := by
  ext x; simp [map_add]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
theorem conjCLM_mul (U : H₁ ≃ₗᵢ[ℂ] H₂) (S T : H₁ →L[ℂ] H₁) :
    conjCLM U (S * T) = conjCLM U S * conjCLM U T := by
  ext x
  simp only [conjCLM_apply, ContinuousLinearMap.mul_apply,
    LinearIsometryEquiv.symm_apply_apply]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
theorem conjCLM_smul (U : H₁ ≃ₗᵢ[ℂ] H₂) (c : ℂ) (T : H₁ →L[ℂ] H₁) :
    conjCLM U (c • T) = c • conjCLM U T := by
  ext x; simp [map_smul]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
theorem conjCLM_leftInv (U : H₁ ≃ₗᵢ[ℂ] H₂) (T : H₁ →L[ℂ] H₁) :
    conjCLM U.symm (conjCLM U T) = T := by
  ext x; simp

/-- Conjugation by a unitary preserves the adjoint (star). -/
theorem conjCLM_star (U : H₁ ≃ₗᵢ[ℂ] H₂) (T : H₁ →L[ℂ] H₁) :
    conjCLM U (star T) = star (conjCLM U T) := by
  conv_rhs => rw [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [conjCLM_apply, conjCLM_apply, ContinuousLinearMap.star_eq_adjoint]
  calc ⟪U (ContinuousLinearMap.adjoint T (U.symm x)), y⟫_ℂ
      = ⟪U (ContinuousLinearMap.adjoint T (U.symm x)), U (U.symm y)⟫_ℂ := by
        rw [LinearIsometryEquiv.apply_symm_apply]
    _ = ⟪ContinuousLinearMap.adjoint T (U.symm x), U.symm y⟫_ℂ :=
        LinearIsometryEquiv.inner_map_map U _ _
    _ = ⟪U.symm x, T (U.symm y)⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_left T (U.symm y) (U.symm x)
    _ = ⟪U (U.symm x), U (T (U.symm y))⟫_ℂ :=
        (LinearIsometryEquiv.inner_map_map U _ _).symm
    _ = ⟪x, U (T (U.symm y))⟫_ℂ := by rw [LinearIsometryEquiv.apply_symm_apply]

/-- Conjugation by a unitary as a `*`-algebra isomorphism of the operator
algebras. -/
noncomputable def conjStarAlgEquiv (U : H₁ ≃ₗᵢ[ℂ] H₂) :
    (H₁ →L[ℂ] H₁) ≃⋆ₐ[ℂ] (H₂ →L[ℂ] H₂) where
  toFun := conjCLM U
  invFun := conjCLM U.symm
  left_inv T := by ext x; simp
  right_inv S := by ext x; simp
  map_mul' := conjCLM_mul U
  map_add' := conjCLM_add U
  map_smul' := conjCLM_smul U
  map_star' := conjCLM_star U

@[simp] theorem conjStarAlgEquiv_apply (U : H₁ ≃ₗᵢ[ℂ] H₂) (T : H₁ →L[ℂ] H₁) :
    conjStarAlgEquiv U T = conjCLM U T := rfl

@[simp] theorem conjStarAlgEquiv_symm_apply (U : H₁ ≃ₗᵢ[ℂ] H₂) (S : H₂ →L[ℂ] H₂) :
    (conjStarAlgEquiv U).symm S = conjCLM U.symm S := rfl

/-- A `*`-isomorphism carrying the underlying set of one star-subalgebra onto that
of another restricts to a `*`-isomorphism between them (cross-space form). -/
def restrictStarAlgEquiv' {B C : Type*}
    [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    [Ring C] [StarRing C] [Algebra ℂ C] [StarModule ℂ C]
    (e : B ≃⋆ₐ[ℂ] C) {S : StarSubalgebra ℂ B} {T : StarSubalgebra ℂ C}
    (hfwd : ∀ x ∈ S, e x ∈ T) (hbwd : ∀ y ∈ T, e.symm y ∈ S) : S ≃⋆ₐ[ℂ] T where
  toFun x := ⟨e x, hfwd x x.2⟩
  invFun y := ⟨e.symm y, hbwd y y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)
  map_star' x := Subtype.ext (map_star e _)

theorem coe_gnsVonNeumann_toStarSubalgebra (π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) :
    ((gnsVonNeumannAlgebra π).toStarSubalgebra : Set (H₁ →L[ℂ] H₁)) = gnsVonNeumann π :=
  coe_gnsVonNeumannAlgebra π

/-- The generators `π(a)` lie in the generated von Neumann algebra `π(A)''`. -/
theorem pi_mem_gnsVonNeumann (π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (a : A) :
    π a ∈ (gnsVonNeumannAlgebra π).toStarSubalgebra := by
  rw [← SetLike.mem_coe, coe_gnsVonNeumann_toStarSubalgebra]
  unfold gnsVonNeumann
  exact Set.mem_centralizer_iff.mpr
    (fun M hM => (Set.mem_centralizer_iff.mp hM (π a) ⟨a, rfl⟩).symm)

/-- Two representations are **quasi-equivalent** when there is a `*`-isomorphism of
their generated von Neumann algebras carrying `π₁(a)` to `π₂(a)`. -/
def QuasiEquiv (π₁ : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) (π₂ : A →⋆ₐ[ℂ] (H₂ →L[ℂ] H₂)) :
    Prop :=
  ∃ Φ : (gnsVonNeumannAlgebra π₁).toStarSubalgebra
          ≃⋆ₐ[ℂ] (gnsVonNeumannAlgebra π₂).toStarSubalgebra,
    ∀ a : A, (Φ ⟨π₁ a, pi_mem_gnsVonNeumann π₁ a⟩ : H₂ →L[ℂ] H₂) = π₂ a

/-- Quasi-equivalence is reflexive. -/
theorem QuasiEquiv.refl (π : A →⋆ₐ[ℂ] (H₁ →L[ℂ] H₁)) : QuasiEquiv π π :=
  ⟨StarAlgEquiv.refl, fun _ => rfl⟩

/-- Quasi-equivalence is symmetric. -/
theorem QuasiEquiv.symm (h : QuasiEquiv π₁ π₂) : QuasiEquiv π₂ π₁ := by
  obtain ⟨Φ, hΦ⟩ := h
  refine ⟨Φ.symm, fun a => ?_⟩
  have hstep : Φ ⟨π₁ a, pi_mem_gnsVonNeumann π₁ a⟩
      = ⟨π₂ a, pi_mem_gnsVonNeumann π₂ a⟩ := Subtype.ext (hΦ a)
  rw [← hstep, StarAlgEquiv.symm_apply_apply]

/-- Quasi-equivalence is transitive. -/
theorem QuasiEquiv.trans (h₁₂ : QuasiEquiv π₁ π₂) (h₂₃ : QuasiEquiv π₂ π₃) :
    QuasiEquiv π₁ π₃ := by
  obtain ⟨Φ, hΦ⟩ := h₁₂
  obtain ⟨Ψ, hΨ⟩ := h₂₃
  refine ⟨Φ.trans Ψ, fun a => ?_⟩
  have hstep : Φ ⟨π₁ a, pi_mem_gnsVonNeumann π₁ a⟩
      = ⟨π₂ a, pi_mem_gnsVonNeumann π₂ a⟩ := Subtype.ext (hΦ a)
  rw [StarAlgEquiv.trans_apply, hstep]
  exact hΨ a

/-- **Unitary equivalence implies quasi-equivalence.** The conjugation
`*`-isomorphism restricts to a `*`-isomorphism of the generated von Neumann
algebras carrying `π₁(a)` to `π₂(a)`. -/
theorem UnitaryEquiv.quasiEquiv (h : UnitaryEquiv π₁ π₂) : QuasiEquiv π₁ π₂ := by
  obtain ⟨U, hU⟩ := h
  have hfwd : ∀ x ∈ (gnsVonNeumannAlgebra π₁).toStarSubalgebra,
      conjStarAlgEquiv U x ∈ (gnsVonNeumannAlgebra π₂).toStarSubalgebra := by
    intro T hT
    rw [← SetLike.mem_coe, coe_gnsVonNeumann_toStarSubalgebra] at hT ⊢
    rw [conjStarAlgEquiv_apply, conjMulEquiv_image_gnsVonNeumann hU]
    exact ⟨T, hT, (conjMulEquiv_apply U T)⟩
  have hbwd : ∀ y ∈ (gnsVonNeumannAlgebra π₂).toStarSubalgebra,
      (conjStarAlgEquiv U).symm y ∈ (gnsVonNeumannAlgebra π₁).toStarSubalgebra := by
    intro S hS
    rw [← SetLike.mem_coe, coe_gnsVonNeumann_toStarSubalgebra] at hS ⊢
    rw [conjMulEquiv_image_gnsVonNeumann hU] at hS
    obtain ⟨T, hT, rfl⟩ := hS
    rw [conjStarAlgEquiv_symm_apply, conjMulEquiv_apply, conjCLM_leftInv]
    exact hT
  refine ⟨restrictStarAlgEquiv' (conjStarAlgEquiv U) hfwd hbwd, fun a => ?_⟩
  change conjStarAlgEquiv U (π₁ a) = π₂ a
  rw [conjStarAlgEquiv_apply, ← conjMulEquiv_apply]
  exact conjMulEquiv_pi hU a

end GNS
end Physicslib4
