/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Operators.Modular.VanDaele
import Physicslib4.Spectral.Unbounded.UnitaryConjugation

/-!
# Unitaries intertwining modular objects

Let `(M₁, Ω₁)` and `(M₂, Ω₂)` be von Neumann algebras on `H` with cyclic and separating vectors,
with reference conjugations `C₁`, `C₂` (antiunitary involutions, chosen independently). A unitary
`V` with `V M₁ V⁻¹ = M₂` and `V Ω₁ = Ω₂` carries the Tomita operator, the modular operator, its
square root, the modular unitary group and the modular conjugation of the first pair onto those
of the second. The special case `M₁ = M₂`, `Ω₁ = Ω₂` says that a unitary that preserves `M` and
fixes `Ω` commutes with all of them.

Conventions:
* `V M₁ V⁻¹ = M₂` is `(fun a => V ∘L a ∘L V⁻¹) '' M₁ = M₂`.
* For an unbounded linear operator, "`B = V A V⁻¹`, including domains" is the graph identity
  `B.graph = A.graph.map Φ_V`, with `Φ_V (φ, ψ) = (V φ, V ψ)` written `Φ[V]` (local notation).
* The Tomita operator is a function on a subtype of `H`, so its intertwining is stated pointwise
  together with the domain condition; the bounded objects `Δ^{it}` and `J` are intertwined
  pointwise.
-/

namespace Physicslib4.Modular

open scoped InnerProductSpace
open Physicslib4.Spectral.Unbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The map `Φ_V (φ, ψ) = (V φ, V ψ)` of `H × H` induced by a unitary `V`. -/
local notation "Φ[" V "]" =>
  LinearMap.prodMap (LinearEquiv.toLinearMap (LinearIsometryEquiv.toLinearEquiv V))
    (LinearEquiv.toLinearMap (LinearIsometryEquiv.toLinearEquiv V))

/-- The conjugate `V a V⁻¹` of a bounded operator `a` by a unitary `V`. -/
local notation "conj[" V "] " a =>
  ContinuousLinearMap.comp (LinearIsometry.toContinuousLinearMap
    (LinearIsometryEquiv.toLinearIsometry V))
    (ContinuousLinearMap.comp a (LinearIsometry.toContinuousLinearMap
      (LinearIsometryEquiv.toLinearIsometry (LinearIsometryEquiv.symm V))))

/-- `V` intertwines the Tomita pre-operators: `Γ(S₀,₂) = Φ_V(Γ(S₀,₁))`, that is,
`Dom S₀,₂ = V (Dom S₀,₁)` and `S₀,₂ V ψ = V S₀,₁ ψ` for `ψ ∈ Dom S₀,₁`.

Blueprint: lmm:unitary-intertwines-tomita-pre-operators -/
theorem tomitaPre_graph_unitary_intertwine {M₁ M₂ : Set (H →L[ℂ] H)} {Ω₁ Ω₂ : H}
    (hM₁ : IsVonNeumannSet M₁) (hM₂ : IsVonNeumannSet M₂)
    (hΩ₁ : IsCyclicSeparatingVector M₁ Ω₁) (hΩ₂ : IsCyclicSeparatingVector M₂ Ω₂)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M₁ = M₂) (hVΩ : V Ω₁ = Ω₂) :
    Set.range (fun x : tomitaPreDomain M₂ Ω₂ => ((x : H), tomitaPre M₂ Ω₂ x)) =
      Prod.map V V ''
        Set.range (fun x : tomitaPreDomain M₁ Ω₁ => ((x : H), tomitaPre M₁ Ω₁ x)) := by
  have hG : ∀ (N : Set (H →L[ℂ] H)) (Ω : H), IsVonNeumannSet N → IsCyclicSeparatingVector N Ω →
      Set.range (fun x : tomitaPreDomain N Ω => ((x : H), tomitaPre N Ω x)) =
        (fun a : H →L[ℂ] H => (a Ω, star a Ω)) '' N := by
    intro N Ω hN hΩ
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨a, ha, hx⟩ := Submodule.mem_map.mp x.2
      have ha' : a ∈ N := span_eq_of_isVonNeumannSet hN ▸ ha
      obtain rfl : x = ⟨a Ω, Submodule.mem_map_of_mem (Submodule.subset_span ha')⟩ :=
        Subtype.ext hx.symm
      exact ⟨a, ha', Prod.ext rfl ((tomitaPre_apply hN hΩ).1 a ha').symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a Ω, Submodule.mem_map_of_mem (Submodule.subset_span ha)⟩,
        Prod.ext rfl ((tomitaPre_apply hN hΩ).1 a ha)⟩
  rw [hG M₂ Ω₂ hM₂ hΩ₂, hG M₁ Ω₁ hM₁ hΩ₁, ← hV, Set.image_image, Set.image_image]
  refine Set.image_congr fun a _ => ?_
  subst hVΩ
  have h₁ : ContinuousLinearMap.adjoint V.toLinearIsometry.toContinuousLinearMap =
      V.symm.toLinearIsometry.toContinuousLinearMap := V.adjoint_eq_symm
  have h₂ : ContinuousLinearMap.adjoint V.symm.toLinearIsometry.toContinuousLinearMap =
      V.toLinearIsometry.toContinuousLinearMap := V.symm.adjoint_eq_symm
  simp [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp, h₁, h₂]

/-- `V` intertwines the Tomita operators: `V S₁ V⁻¹ = S₂`, including domains. That is,
`ψ ∈ Dom S₁` if and only if `V ψ ∈ Dom S₂`, and then `S₂ V ψ = V S₁ ψ`.

Blueprint: lmm:unitary-intertwines-tomita-operator -/
theorem tomitaOperator_unitary_intertwine {M₁ M₂ : Set (H →L[ℂ] H)} {Ω₁ Ω₂ : H}
    (hM₁ : IsVonNeumannSet M₁) (hM₂ : IsVonNeumannSet M₂)
    (hΩ₁ : IsCyclicSeparatingVector M₁ Ω₁) (hΩ₂ : IsCyclicSeparatingVector M₂ Ω₂)
    (C₁ C₂ : H ≃ₗᵢ⋆[ℂ] H) (hC₁ : ∀ x, C₁ (C₁ x) = x) (hC₂ : ∀ x, C₂ (C₂ x) = x)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M₁ = M₂) (hVΩ : V Ω₁ = Ω₂) :
    (∀ ψ : H, ψ ∈ (linearizedTomitaPre M₁ Ω₁ C₁).closure.domain ↔
        V ψ ∈ (linearizedTomitaPre M₂ Ω₂ C₂).closure.domain) ∧
      ∀ (ψ : H) (h₁ : ψ ∈ (linearizedTomitaPre M₁ Ω₁ C₁).closure.domain)
        (h₂ : V ψ ∈ (linearizedTomitaPre M₂ Ω₂ C₂).closure.domain),
        tomitaOperator M₂ Ω₂ C₂ ⟨V ψ, h₂⟩ = V (tomitaOperator M₁ Ω₁ C₁ ⟨ψ, h₁⟩) := by
  have key : Set.range (fun x : (linearizedTomitaPre M₂ Ω₂ C₂).closure.domain =>
      ((x : H), tomitaOperator M₂ Ω₂ C₂ x)) = Prod.map V V '' Set.range
        (fun x : (linearizedTomitaPre M₁ Ω₁ C₁).closure.domain =>
          ((x : H), tomitaOperator M₁ Ω₁ C₁ x)) := by
    rw [tomitaOperator_graph_eq_closure hM₂ hΩ₂ C₂ hC₂,
      tomitaOperator_graph_eq_closure hM₁ hΩ₁ C₁ hC₁, (image_closure_prodMap_unitary V).2,
      tomitaPre_graph_unitary_intertwine hM₁ hM₂ hΩ₁ hΩ₂ V hV hVΩ]
  have mem : ∀ (ψ : H) (h₁ : ψ ∈ (linearizedTomitaPre M₁ Ω₁ C₁).closure.domain),
      ∃ x : (linearizedTomitaPre M₂ Ω₂ C₂).closure.domain,
        (x : H) = V ψ ∧ tomitaOperator M₂ Ω₂ C₂ x = V (tomitaOperator M₁ Ω₁ C₁ ⟨ψ, h₁⟩) := by
    intro ψ h₁
    obtain ⟨x, hx⟩ : (V ψ, V (tomitaOperator M₁ Ω₁ C₁ ⟨ψ, h₁⟩)) ∈ Set.range
        (fun x : (linearizedTomitaPre M₂ Ω₂ C₂).closure.domain =>
          ((x : H), tomitaOperator M₂ Ω₂ C₂ x)) := key ▸ ⟨_, ⟨⟨ψ, h₁⟩, rfl⟩, rfl⟩
    exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
  refine ⟨fun ψ => ⟨fun h₁ => ?_, fun h₂ => ?_⟩, fun ψ h₁ h₂ => ?_⟩
  · obtain ⟨x, hx, -⟩ := mem ψ h₁
    exact hx ▸ x.2
  · have h : (V ψ, tomitaOperator M₂ Ω₂ C₂ ⟨V ψ, h₂⟩) ∈ Set.range
        (fun x : (linearizedTomitaPre M₂ Ω₂ C₂).closure.domain =>
          ((x : H), tomitaOperator M₂ Ω₂ C₂ x)) := ⟨⟨V ψ, h₂⟩, rfl⟩
    rw [key] at h
    obtain ⟨-, ⟨x, rfl⟩, hx⟩ := h
    exact V.injective (congrArg Prod.fst hx) ▸ x.2
  · obtain ⟨x, hx, hS⟩ := mem ψ h₁
    obtain rfl : x = ⟨V ψ, h₂⟩ := Subtype.ext hx
    exact hS

/-- `V` intertwines the modular operators: for all `ψ, χ`, `V ψ ∈ Dom Δ₂` with `Δ₂ V ψ = V χ` if
and only if `ψ ∈ Dom Δ₁` with `Δ₁ ψ = χ`. Consequently `V Δ₁ V⁻¹ = Δ₂`, including domains.

Blueprint: lmm:unitary-intertwines-modular-operator -/
theorem modularOperator_unitary_intertwine {M₁ M₂ : Set (H →L[ℂ] H)} {Ω₁ Ω₂ : H}
    (hM₁ : IsVonNeumannSet M₁) (hM₂ : IsVonNeumannSet M₂)
    (hΩ₁ : IsCyclicSeparatingVector M₁ Ω₁) (hΩ₂ : IsCyclicSeparatingVector M₂ Ω₂)
    (C₁ C₂ : H ≃ₗᵢ⋆[ℂ] H) (hC₁ : ∀ x, C₁ (C₁ x) = x) (hC₂ : ∀ x, C₂ (C₂ x) = x)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M₁ = M₂) (hVΩ : V Ω₁ = Ω₂) :
    (∀ ψ χ : H,
      (∃ h : V ψ ∈ (modularOperator M₂ Ω₂ C₂).domain, modularOperator M₂ Ω₂ C₂ ⟨V ψ, h⟩ = V χ) ↔
        ∃ h : ψ ∈ (modularOperator M₁ Ω₁ C₁).domain, modularOperator M₁ Ω₁ C₁ ⟨ψ, h⟩ = χ) ∧
      (modularOperator M₂ Ω₂ C₂).graph = (modularOperator M₁ Ω₁ C₁).graph.map Φ[V] := by
  obtain ⟨hD, hS⟩ := tomitaOperator_unitary_intertwine hM₁ hM₂ hΩ₁ hΩ₂ C₁ C₂ hC₁ hC₂ V hV hVΩ
  have hS' : ∀ φ' : (linearizedTomitaPre M₂ Ω₂ C₂).closure.domain,
      ∃ φ : (linearizedTomitaPre M₁ Ω₁ C₁).closure.domain,
        (φ' : H) = V φ ∧ tomitaOperator M₂ Ω₂ C₂ φ' = V (tomitaOperator M₁ Ω₁ C₁ φ) := by
    rintro ⟨x, hx⟩
    obtain ⟨ψ, rfl⟩ : ∃ ψ, x = V ψ := ⟨V.symm x, by simp⟩
    exact ⟨⟨ψ, (hD ψ).2 hx⟩, rfl, hS _ _ hx⟩
  have hiff : ∀ ψ χ : H,
      (∃ h : V ψ ∈ (modularOperator M₂ Ω₂ C₂).domain, modularOperator M₂ Ω₂ C₂ ⟨V ψ, h⟩ = V χ) ↔
        ∃ h : ψ ∈ (modularOperator M₁ Ω₁ C₁).domain, modularOperator M₁ Ω₁ C₁ ⟨ψ, h⟩ = χ := by
    intro ψ χ
    rw [mem_modularOperator_iff hM₂ hΩ₂ C₂ hC₂, mem_modularOperator_iff hM₁ hΩ₁ C₁ hC₁]
    constructor
    · rintro ⟨h₂, hφ⟩
      have h₁ := (hD ψ).2 h₂
      refine ⟨h₁, fun φ => ?_⟩
      have := hφ ⟨V φ, (hD φ).1 φ.2⟩
      rwa [hS _ φ.2, hS _ h₁, LinearIsometryEquiv.inner_map_map,
        LinearIsometryEquiv.inner_map_map] at this
    · rintro ⟨h₁, hφ⟩
      refine ⟨(hD ψ).1 h₁, fun φ' => ?_⟩
      obtain ⟨φ, hφ'1, hφ'2⟩ := hS' φ'
      rw [hφ'2, hS _ h₁, hφ'1, LinearIsometryEquiv.inner_map_map,
        LinearIsometryEquiv.inner_map_map]
      exact hφ φ
  refine ⟨hiff, ?_⟩
  ext ⟨x, y⟩
  simp only [Submodule.mem_map, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨⟨z, hz⟩, rfl, rfl⟩
    obtain ⟨ψ, rfl⟩ : ∃ ψ, z = V ψ := ⟨V.symm z, by simp⟩
    obtain ⟨χ, hχ⟩ : ∃ χ, modularOperator M₂ Ω₂ C₂ ⟨V ψ, hz⟩ = V χ :=
      ⟨V.symm (modularOperator M₂ Ω₂ C₂ ⟨V ψ, hz⟩), by simp⟩
    obtain ⟨h, hh⟩ := (hiff ψ χ).1 ⟨hz, hχ⟩
    exact ⟨(ψ, χ), ⟨⟨ψ, h⟩, rfl, hh⟩, by simp [hχ]⟩
  · rintro ⟨⟨a, b⟩, ⟨⟨w, hw⟩, hwa, hwb⟩, hab⟩
    simp only at hwa hwb
    subst hwa hwb
    simp only [LinearMap.prodMap_apply, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    obtain ⟨h, hh⟩ := (hiff w _).2 ⟨hw, rfl⟩
    exact ⟨⟨V w, h⟩, rfl, hh⟩

/-- `V` intertwines functions of the modular operators: `V f(Δ₁) V⁻¹ = f(Δ₂)`, including domains,
for every real measurable `f`. In particular `V Δ₁^{1/2} V⁻¹ = Δ₂^{1/2}`, including domains.

Blueprint: lmm:unitary-intertwines-modular-sqrt -/
theorem modularOperator_functionalCalculus_unitary_intertwine
    {M₁ M₂ : Set (H →L[ℂ] H)} {Ω₁ Ω₂ : H}
    (hM₁ : IsVonNeumannSet M₁) (hM₂ : IsVonNeumannSet M₂)
    (hΩ₁ : IsCyclicSeparatingVector M₁ Ω₁) (hΩ₂ : IsCyclicSeparatingVector M₂ Ω₂)
    (C₁ C₂ : H ≃ₗᵢ⋆[ℂ] H) (hC₁ : ∀ x, C₁ (C₁ x) = x) (hC₂ : ∀ x, C₂ (C₂ x) = x)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M₁ = M₂) (hVΩ : V Ω₁ = Ω₂) :
    (∀ f : ℝ → ℝ, Measurable f →
      (functionalCalculus (modularOperator_isSelfAdjoint hM₂ hΩ₂ C₂ hC₂)
          fun x => (f x : ℂ)).graph =
        (functionalCalculus (modularOperator_isSelfAdjoint hM₁ hΩ₁ C₁ hC₁)
          fun x => (f x : ℂ)).graph.map Φ[V]) ∧
      (modularOperatorSqrt hM₂ hΩ₂ C₂ hC₂).graph =
        (modularOperatorSqrt hM₁ hΩ₁ C₁ hC₁).graph.map Φ[V] := by
  have h := (functionalCalculus_unitaryConj V (modularOperator_isSelfAdjoint hM₁ hΩ₁ C₁ hC₁)
    (modularOperator_unitary_intertwine hM₁ hM₂ hΩ₁ hΩ₂ C₁ C₂ hC₁ hC₂ V hV hVΩ).2).2
    (modularOperator_isSelfAdjoint hM₂ hΩ₂ C₂ hC₂)
  exact ⟨h, h Real.sqrt Real.continuous_sqrt.measurable⟩

/-- `V` intertwines the modular unitary groups: `V Δ₁^{it} V⁻¹ = Δ₂^{it}` for every `t ∈ ℝ`.

Blueprint: lmm:unitary-intertwines-modular-unitary-group -/
theorem modularUnitaryGroup_unitary_intertwine {M₁ M₂ : Set (H →L[ℂ] H)} {Ω₁ Ω₂ : H}
    (hM₁ : IsVonNeumannSet M₁) (hM₂ : IsVonNeumannSet M₂)
    (hΩ₁ : IsCyclicSeparatingVector M₁ Ω₁) (hΩ₂ : IsCyclicSeparatingVector M₂ Ω₂)
    (C₁ C₂ : H ≃ₗᵢ⋆[ℂ] H) (hC₁ : ∀ x, C₁ (C₁ x) = x) (hC₂ : ∀ x, C₂ (C₂ x) = x)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M₁ = M₂) (hVΩ : V Ω₁ = Ω₂) :
    ∀ (t : ℝ) (ψ : H), V (modularUnitaryGroup hM₁ hΩ₁ C₁ hC₁ t (V.symm ψ)) =
      modularUnitaryGroup hM₂ hΩ₂ C₂ hC₂ t ψ := by
  intro t ψ
  obtain ⟨hm, hn, hfc₁, -, -⟩ := modularUnitaryGroup_eq_functionalCalculus hM₁ hΩ₁ C₁ hC₁ t
  obtain ⟨-, -, hfc₂, -, -⟩ := modularUnitaryGroup_eq_functionalCalculus hM₂ hΩ₂ C₂ hC₂ t
  have hg := functionalCalculus_unitaryConj_of_bounded V
    (modularOperator_isSelfAdjoint hM₁ hΩ₁ C₁ hC₁) (modularOperator_isSelfAdjoint hM₂ hΩ₂ C₂ hC₂)
    (modularOperator_unitary_intertwine hM₁ hM₂ hΩ₁ hΩ₂ C₁ C₂ hC₁ hC₂ V hV hVΩ).2 hm
    ⟨1, fun x => (hn x).le⟩
  rw [hfc₁, hfc₂] at hg
  have hmem : (V.symm ψ, modularUnitaryGroup hM₁ hΩ₁ C₁ hC₁ t (V.symm ψ)) ∈
      ((modularUnitaryGroup hM₁ hΩ₁ C₁ hC₁ t).toLinearIsometry.toLinearMap.toPMap ⊤).graph :=
    (LinearPMap.mem_graph_iff _).2 ⟨⟨V.symm ψ, Submodule.mem_top⟩, rfl, rfl⟩
  have h2 := Submodule.mem_map_of_mem (f := Φ[V]) hmem
  rw [← hg, LinearPMap.mem_graph_iff] at h2
  obtain ⟨y, hy1, hy2⟩ := h2
  simp only [LinearMap.toPMap_domain, LinearMap.prodMap_apply, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.apply_symm_apply] at hy1 hy2
  rw [← hy2, ← hy1]
  rfl

/-- `V` intertwines the modular conjugations: `V J₁ V⁻¹ φ = J₂ φ` for every `φ ∈ H`.

Blueprint: lmm:unitary-intertwines-modular-conjugation -/
theorem modularConjugation_unitary_intertwine {M₁ M₂ : Set (H →L[ℂ] H)} {Ω₁ Ω₂ : H}
    (hM₁ : IsVonNeumannSet M₁) (hM₂ : IsVonNeumannSet M₂)
    (hΩ₁ : IsCyclicSeparatingVector M₁ Ω₁) (hΩ₂ : IsCyclicSeparatingVector M₂ Ω₂)
    (C₁ C₂ : H ≃ₗᵢ⋆[ℂ] H) (hC₁ : ∀ x, C₁ (C₁ x) = x) (hC₂ : ∀ x, C₂ (C₂ x) = x)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M₁ = M₂) (hVΩ : V Ω₁ = Ω₂) :
    ∀ φ : H, V (modularConjugation hM₁ hΩ₁ C₁ hC₁ (V.symm φ)) =
      modularConjugation hM₂ hΩ₂ C₂ hC₂ φ := by
  sorry

/-- A unitary `V` between standard pairs, `V M₁ V⁻¹ = M₂` and `V Ω₁ = Ω₂`, intertwines the
modular objects, including domains: `V S₁ V⁻¹ = S₂`, `V Δ₁ V⁻¹ = Δ₂`,
`V Δ₁^{1/2} V⁻¹ = Δ₂^{1/2}`, `V Δ₁^{it} V⁻¹ = Δ₂^{it}` for `t ∈ ℝ`, and `V J₁ V⁻¹ = J₂`.

Blueprint: thrm:unitary-intertwines-modular-objects -/
theorem modular_objects_unitary_intertwine {M₁ M₂ : Set (H →L[ℂ] H)} {Ω₁ Ω₂ : H}
    (hM₁ : IsVonNeumannSet M₁) (hM₂ : IsVonNeumannSet M₂)
    (hΩ₁ : IsCyclicSeparatingVector M₁ Ω₁) (hΩ₂ : IsCyclicSeparatingVector M₂ Ω₂)
    (C₁ C₂ : H ≃ₗᵢ⋆[ℂ] H) (hC₁ : ∀ x, C₁ (C₁ x) = x) (hC₂ : ∀ x, C₂ (C₂ x) = x)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M₁ = M₂) (hVΩ : V Ω₁ = Ω₂) :
    ((∀ ψ : H, ψ ∈ (linearizedTomitaPre M₁ Ω₁ C₁).closure.domain ↔
        V ψ ∈ (linearizedTomitaPre M₂ Ω₂ C₂).closure.domain) ∧
      ∀ (ψ : H) (h₁ : ψ ∈ (linearizedTomitaPre M₁ Ω₁ C₁).closure.domain)
        (h₂ : V ψ ∈ (linearizedTomitaPre M₂ Ω₂ C₂).closure.domain),
        tomitaOperator M₂ Ω₂ C₂ ⟨V ψ, h₂⟩ = V (tomitaOperator M₁ Ω₁ C₁ ⟨ψ, h₁⟩)) ∧
    (modularOperator M₂ Ω₂ C₂).graph = (modularOperator M₁ Ω₁ C₁).graph.map Φ[V] ∧
    (modularOperatorSqrt hM₂ hΩ₂ C₂ hC₂).graph =
      (modularOperatorSqrt hM₁ hΩ₁ C₁ hC₁).graph.map Φ[V] ∧
    (∀ (t : ℝ) (ψ : H), V (modularUnitaryGroup hM₁ hΩ₁ C₁ hC₁ t (V.symm ψ)) =
      modularUnitaryGroup hM₂ hΩ₂ C₂ hC₂ t ψ) ∧
    ∀ φ : H, V (modularConjugation hM₁ hΩ₁ C₁ hC₁ (V.symm φ)) =
      modularConjugation hM₂ hΩ₂ C₂ hC₂ φ := by
  sorry

/-- A unitary `V` with `V M V⁻¹ = M` and `V Ω = Ω` commutes with the modular objects of `(M, Ω)`:
it commutes with `Δ` and with `Δ^{1/2}` (`UnitaryCommutes`), `V` maps `Dom S` onto itself
(`V ψ ∈ Dom S ↔ ψ ∈ Dom S`) with `S V ψ = V S ψ`, and `V Δ^{it} = Δ^{it} V` for `t ∈ ℝ` and
`V J = J V`.

Blueprint: crllr:unitary-commutes-modular-objects -/
theorem modular_objects_unitary_commute {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M = M) (hVΩ : V Ω = Ω) :
    UnitaryCommutes V (modularOperator M Ω C) ∧
    UnitaryCommutes V (modularOperatorSqrt hM hΩ C hC) ∧
    ((∀ ψ : H, V ψ ∈ (linearizedTomitaPre M Ω C).closure.domain ↔
        ψ ∈ (linearizedTomitaPre M Ω C).closure.domain) ∧
      ∀ (ψ : H) (h : ψ ∈ (linearizedTomitaPre M Ω C).closure.domain)
        (h' : V ψ ∈ (linearizedTomitaPre M Ω C).closure.domain),
        tomitaOperator M Ω C ⟨V ψ, h'⟩ = V (tomitaOperator M Ω C ⟨ψ, h⟩)) ∧
    (∀ (t : ℝ) (ψ : H), V (modularUnitaryGroup hM hΩ C hC t ψ) =
      modularUnitaryGroup hM hΩ C hC t (V ψ)) ∧
    ∀ ψ : H, V (modularConjugation hM hΩ C hC ψ) = modularConjugation hM hΩ C hC (V ψ) := by
  sorry

end Physicslib4.Modular
