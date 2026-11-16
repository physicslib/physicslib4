/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Operators.Modular.Tomita
import Physicslib4.Spectral.Unbounded.Polar

/-!
# The modular operator and the modular conjugation

For a von Neumann algebra `M` with a cyclic and separating vector `Ω` and a reference
conjugation `C` (an antiunitary involution), let `S′` be the closure of the linearized Tomita
pre-operator and `S = C S′` the Tomita operator. This file defines the modular operator
`Δ = S′† S′`, its square root `Δ^{1/2} = |S′|`, its inverse square root `Δ^{-1/2}`, and the modular
conjugation `J = C V`, where `V` is the unitary of the polar decomposition `S′ = V |S′|`. It
states the properties of `Δ` and `J`, their independence of `C`, the relations `S = J Δ^{1/2}`
and `S⁻¹ = S`, and the identities `J² = 1`, `J Δ^{1/2} J = Δ^{-1/2}` and `J Δ J = Δ⁻¹`.

The Tomita operator `tomitaOperator M Ω C` is antilinear and is a function on the domain of `S′`,
not a `LinearPMap`; statements about it are pointwise.
-/

namespace Physicslib4.Modular

open scoped InnerProductSpace
open Physicslib4.Spectral.Unbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
The hypotheses of the polar decomposition for `S′`: it is closed and densely defined, its kernel
is `{0}` and its range is dense, in the forms used by `Polar.lean`.

Blueprint: def:modular-conjugation
-/
theorem linearizedTomita_closure_polar_hyps {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    HasDenseDomain (linearizedTomitaPre M Ω C).closure ∧
      (linearizedTomitaPre M Ω C).closure.IsClosed ∧
      ker (linearizedTomitaPre M Ω C).closure = ⊥ ∧
      Dense (range (linearizedTomitaPre M Ω C).closure : Set H) := by
  obtain ⟨hcl, hD, hinj, hR⟩ := linearizedTomita_closure_properties hM hΩ C hC
  refine ⟨hD, hcl, (Submodule.eq_bot_iff _).mpr fun x hx => ?_, ?_⟩
  · obtain ⟨h, h0⟩ := mem_ker.mp hx
    have := @hinj ⟨x, h⟩ 0 (by rw [h0, LinearPMap.map_zero])
    exact congrArg Subtype.val this
  · rw [range, LinearMap.coe_range]
    exact hR

/--
The modular operator `Δ = S′† S′` of `(M, Ω)`, where `S′` is the closure of the linearized
Tomita pre-operator. Its square root `s(Δ)` is `modularOperatorSqrt`, which is `|S′|` by
definition of `absoluteValue`.

Blueprint: def:modular-operator
-/
noncomputable def modularOperator (M : Set (H →L[ℂ] H)) (Ω : H) (C : H ≃ₗᵢ⋆[ℂ] H) :
    H →ₗ.[ℂ] H :=
  adjointMulSelf (linearizedTomitaPre M Ω C).closure

/--
The modular operator is self-adjoint, by von Neumann's theorem.

Blueprint: thrm:modular-operator-properties
-/
theorem modularOperator_isSelfAdjoint {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) : IsSelfAdjoint (modularOperator M Ω C) :=
  (isSelfAdjoint_adjointMulSelf (linearizedTomita_closure_polar_hyps hM hΩ C hC).1
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).2.1).1

/--
The square root `Δ^{1/2} = s(Δ) = |S′|` of the modular operator.

Blueprint: def:modular-operator
-/
noncomputable def modularOperatorSqrt {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) : H →ₗ.[ℂ] H :=
  absoluteValue (linearizedTomitaPre M Ω C).closure
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).1
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).2.1

/--
The inverse square root `Δ^{-1/2} = r(Δ)` of the modular operator, with `r(λ) = λ^{-1/2}` for
`λ > 0` and `r(λ) = 0` otherwise (written `(√λ)⁻¹`).

Blueprint: lmm:tomita-inverse-as-product
-/
noncomputable def modularOperatorInvSqrt {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) : H →ₗ.[ℂ] H :=
  functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC)
    fun x => (((Real.sqrt x)⁻¹ : ℝ) : ℂ)

/--
The modular conjugation `J = C V`, where `V` is a unitary of the polar decomposition
`S′ = V |S′| = V Δ^{1/2}` (`polar_decomposition`, chosen classically; it is unique by
`existsUnique_polarIsometry`).

Blueprint: def:modular-conjugation
-/
noncomputable def modularConjugation {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) : H ≃ₗᵢ⋆[ℂ] H :=
  (Classical.choose (polar_decomposition (linearizedTomita_closure_polar_hyps hM hΩ C hC).1
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).2.1
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).2.2.1
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).2.2.2)).trans C

/--
`Δ` is positive, self-adjoint, densely defined and injective; `Dom Δ^{1/2} = Dom S` and
`‖Δ^{1/2} ψ‖ = ‖S ψ‖` for `ψ ∈ Dom S`.

Blueprint: thrm:modular-operator-properties
-/
theorem modularOperator_properties {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    IsPositive (modularOperator M Ω C) ∧ IsSelfAdjoint (modularOperator M Ω C) ∧
      HasDenseDomain (modularOperator M Ω C) ∧ ker (modularOperator M Ω C) = ⊥ ∧
      (modularOperatorSqrt hM hΩ C hC).domain = (linearizedTomitaPre M Ω C).closure.domain ∧
      ∀ (ψ : H) (h₁ : ψ ∈ (modularOperatorSqrt hM hΩ C hC).domain)
        (h₂ : ψ ∈ (linearizedTomitaPre M Ω C).closure.domain),
        ‖modularOperatorSqrt hM hΩ C hC ⟨ψ, h₁⟩‖ = ‖tomitaOperator M Ω C ⟨ψ, h₂⟩‖ := by
  obtain ⟨hD, hcl, hker, -⟩ := linearizedTomita_closure_polar_hyps hM hΩ C hC
  obtain ⟨hsa, hdense, hpos⟩ := isSelfAdjoint_adjointMulSelf hD hcl
  obtain ⟨-, -, hdom, hnorm⟩ := absoluteValue_domain hD hcl
  refine ⟨hpos, hsa, hdense, (Submodule.eq_bot_iff _).mpr fun x hx => ?_, hdom,
    fun ψ h₁ h₂ => (hnorm ψ h₁ h₂).trans (C.norm_map _).symm⟩
  obtain ⟨h, h0⟩ := mem_ker.mp hx
  have h2 := (inner_adjointMulSelf hD ⟨x, h⟩).2
  rw [show adjointMulSelf _ ⟨x, h⟩ = 0 from h0, inner_zero_right] at h2
  have h3 : (linearizedTomitaPre M Ω C).closure ⟨x, pmapMul_domain_le _ _ h⟩ = 0 := by
    have h4 : ((‖(linearizedTomitaPre M Ω C).closure ⟨x, pmapMul_domain_le _ _ h⟩‖ ^ 2 : ℝ) : ℂ)
        = 0 := by push_cast; exact h2.symm
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (Complex.ofReal_eq_zero.mp h4))
  exact (Submodule.mem_bot ℂ).mp (hker ▸ mem_ker.mpr ⟨_, h3⟩)

/--
`ψ ∈ Dom Δ` with `Δ ψ = χ` if and only if `ψ ∈ Dom S` and `⟪S φ, S ψ⟫ = ⟪χ, φ⟫` for every
`φ ∈ Dom S`.

Blueprint: lmm:modular-operator-intrinsic
-/
theorem mem_modularOperator_iff {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (ψ χ : H) :
    (∃ h : ψ ∈ (modularOperator M Ω C).domain, modularOperator M Ω C ⟨ψ, h⟩ = χ) ↔
      ∃ h : ψ ∈ (linearizedTomitaPre M Ω C).closure.domain,
        ∀ φ : (linearizedTomitaPre M Ω C).closure.domain,
          ⟪tomitaOperator M Ω C φ, tomitaOperator M Ω C ⟨ψ, h⟩⟫_ℂ = ⟪χ, (φ : H)⟫_ℂ := by
  obtain ⟨hD, -, -, -⟩ := linearizedTomita_closure_polar_hyps hM hΩ C hC
  unfold modularOperator
  set T := (linearizedTomitaPre M Ω C).closure with hT
  have key : ∀ φ ψ : T.domain, ⟪tomitaOperator M Ω C φ, tomitaOperator M Ω C ψ⟫_ℂ =
      ⟪T ψ, T φ⟫_ℂ := fun φ ψ =>
    (inner_map_map_of_conjLinearIsometry C.toLinearIsometry (T φ) (T ψ)).trans
      (inner_conj_symm _ _)
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨pmapMul_domain_le _ _ h, fun φ => ?_⟩
    have e := (inner_adjointMulSelf hD ⟨ψ, h⟩).1 φ
    rw [key, ← inner_conj_symm, ← e, inner_conj_symm]
  · rintro ⟨h, hH⟩
    have hdom : T ⟨ψ, h⟩ ∈ T.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨χ, fun φ => by rw [← hH φ, key]⟩
    have hm : ψ ∈ (adjointMulSelf T).domain := (mem_domain_pmapMul_iff _ _ _).mpr ⟨h, hdom⟩
    refine ⟨hm, ?_⟩
    exact (pmapMul_apply _ _ ⟨ψ, hm⟩ hdom).trans
      (LinearPMap.adjoint_apply_eq hD _ fun φ => by rw [← hH φ, key])

/--
`J` is antiunitary (by its type) and `S = J Δ^{1/2}`: `Dom S = Dom Δ^{1/2}` and
`S ψ = J (Δ^{1/2} ψ)`.

Blueprint: thrm:modular-conjugation-polar
-/
theorem tomitaOperator_eq_modularConjugation_sqrt {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    (linearizedTomitaPre M Ω C).closure.domain = (modularOperatorSqrt hM hΩ C hC).domain ∧
      ∀ (ψ : H) (h₁ : ψ ∈ (linearizedTomitaPre M Ω C).closure.domain)
        (h₂ : ψ ∈ (modularOperatorSqrt hM hΩ C hC).domain),
        tomitaOperator M Ω C ⟨ψ, h₁⟩ =
          modularConjugation hM hΩ C hC (modularOperatorSqrt hM hΩ C hC ⟨ψ, h₂⟩) := by
  have hs := Classical.choose_spec (polar_decomposition
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).1
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).2.1
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).2.2.1
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).2.2.2)
  refine ⟨hs.1.symm, fun ψ h₁ h₂ => ?_⟩
  simp only [modularConjugation, LinearIsometryEquiv.trans_apply, modularOperatorSqrt,
    tomitaOperator]
  rw [hs.2.1 ψ h₁ h₂]

/--
`J` is the only continuous map `K : H → H` with `K (Δ^{1/2} ψ) = S ψ` for all
`ψ ∈ Dom Δ^{1/2}`.

Blueprint: lmm:modular-conjugation-intrinsic
-/
theorem eq_modularConjugation_of_continuous {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (K : H → H) (hK : Continuous K)
    (hKS : ∀ (ψ : H) (h₁ : ψ ∈ (linearizedTomitaPre M Ω C).closure.domain)
      (h₂ : ψ ∈ (modularOperatorSqrt hM hΩ C hC).domain),
      K (modularOperatorSqrt hM hΩ C hC ⟨ψ, h₂⟩) = tomitaOperator M Ω C ⟨ψ, h₁⟩) :
    ∀ x, K x = modularConjugation hM hΩ C hC x := by
  have hd : DenseRange (modularOperatorSqrt hM hΩ C hC) := by
    have := (absoluteValue_injective_denseRange
      (linearizedTomita_closure_polar_hyps hM hΩ C hC).1
      (linearizedTomita_closure_polar_hyps hM hΩ C hC).2.1
      (linearizedTomita_closure_polar_hyps hM hΩ C hC).2.2.1).2
    rw [range, LinearMap.coe_range] at this
    exact this
  have hdom := (tomitaOperator_eq_modularConjugation_sqrt hM hΩ C hC).1
  refine congrFun (hd.equalizer hK (modularConjugation hM hΩ C hC).continuous (funext ?_))
  rintro ⟨ψ, h₂⟩
  simp only [Function.comp_apply]
  rw [hKS ψ (hdom ▸ h₂) h₂,
    (tomitaOperator_eq_modularConjugation_sqrt hM hΩ C hC).2 ψ (hdom ▸ h₂) h₂]

/--
`Δ`, `Δ^{1/2}` and `J` are the same for every choice of the reference conjugation: for
antiunitary involutions `C₁` and `C₂`, the modular operators and their square roots are equal and
the modular conjugations agree pointwise.

Blueprint: thrm:modular-objects-independent-of-c
-/
theorem modular_objects_independent_of_conjugation {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C₁ C₂ : H ≃ₗᵢ⋆[ℂ] H)
    (hC₁ : ∀ x, C₁ (C₁ x) = x) (hC₂ : ∀ x, C₂ (C₂ x) = x) :
    modularOperator M Ω C₁ = modularOperator M Ω C₂ ∧
      modularOperatorSqrt hM hΩ C₁ hC₁ = modularOperatorSqrt hM hΩ C₂ hC₂ ∧
      ∀ x, modularConjugation hM hΩ C₁ hC₁ x = modularConjugation hM hΩ C₂ hC₂ x := by
  -- `S` does not depend on the reference conjugation.
  have hS : ∀ (C C' : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (hC' : ∀ x, C' (C' x) = x)
      (ψ : H) (h : ψ ∈ (linearizedTomitaPre M Ω C).closure.domain),
      ∃ h' : ψ ∈ (linearizedTomitaPre M Ω C').closure.domain,
        tomitaOperator M Ω C' ⟨ψ, h'⟩ = tomitaOperator M Ω C ⟨ψ, h⟩ := by
    intro C C' hC hC' ψ h
    have hmem : ((ψ : H), tomitaOperator M Ω C ⟨ψ, h⟩) ∈ Set.range
        (fun x : (linearizedTomitaPre M Ω C').closure.domain =>
          ((x : H), tomitaOperator M Ω C' x)) := by
      rw [tomitaOperator_graph_eq_closure hM hΩ C' hC',
        ← tomitaOperator_graph_eq_closure hM hΩ C hC]
      exact ⟨⟨ψ, h⟩, rfl⟩
    obtain ⟨⟨x, hx⟩, e⟩ := hmem
    obtain ⟨rfl, e2⟩ := Prod.ext_iff.mp e
    exact ⟨hx, e2⟩
  -- `Δ` is determined by `S`.
  have hΔ : ∀ (C C' : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) (hC' : ∀ x, C' (C' x) = x)
      (ψ χ : H), (∃ h : ψ ∈ (modularOperator M Ω C).domain, modularOperator M Ω C ⟨ψ, h⟩ = χ) →
        ∃ h : ψ ∈ (modularOperator M Ω C').domain, modularOperator M Ω C' ⟨ψ, h⟩ = χ := by
    intro C C' hC hC' ψ χ hψ
    obtain ⟨h, hφ⟩ := (mem_modularOperator_iff hM hΩ C hC ψ χ).mp hψ
    obtain ⟨h', e'⟩ := hS C C' hC hC' ψ h
    refine (mem_modularOperator_iff hM hΩ C' hC' ψ χ).mpr ⟨h', fun φ => ?_⟩
    obtain ⟨hφ', eφ⟩ := hS C' C hC' hC φ φ.2
    rw [e', ← eφ]
    exact hφ ⟨φ, hφ'⟩
  have hΔeq : modularOperator M Ω C₁ = modularOperator M Ω C₂ := by
    refine LinearPMap.ext_iff.mpr ⟨Submodule.ext fun ψ =>
      ⟨fun h => (hΔ C₁ C₂ hC₁ hC₂ ψ _ ⟨h, rfl⟩).1, fun h => (hΔ C₂ C₁ hC₂ hC₁ ψ _ ⟨h, rfl⟩).1⟩,
      fun ψ h₁ h₂ => ?_⟩
    obtain ⟨_, e⟩ := hΔ C₁ C₂ hC₁ hC₂ ψ _ ⟨h₁, rfl⟩
    exact e.symm
  have hsq : modularOperatorSqrt hM hΩ C₁ hC₁ = modularOperatorSqrt hM hΩ C₂ hC₂ := by
    have key : ∀ (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B), A = B →
        functionalCalculus hA (fun x => ((Real.sqrt x : ℝ) : ℂ)) =
          functionalCalculus hB (fun x => ((Real.sqrt x : ℝ) : ℂ)) := by
      rintro A _ hA hB rfl; rfl
    exact key _ _ _ _ hΔeq
  refine ⟨hΔeq, hsq, fun x => ?_⟩
  obtain ⟨hdom₂, hJ₂⟩ := tomitaOperator_eq_modularConjugation_sqrt hM hΩ C₂ hC₂
  obtain ⟨-, hsqv⟩ := LinearPMap.ext_iff.mp hsq
  refine (eq_modularConjugation_of_continuous hM hΩ C₁ hC₁ (modularConjugation hM hΩ C₂ hC₂)
    (modularConjugation hM hΩ C₂ hC₂).continuous (fun ψ h₁ h₂ => ?_) x).symm
  obtain ⟨h₁', e⟩ := hS C₁ C₂ hC₁ hC₂ ψ h₁
  rw [← e, hJ₂ ψ h₁' (hdom₂ ▸ h₁'), hsqv]

/--
`S` is injective and `S⁻¹ = S`: `Range S = Dom S` and `S (S x) = x` for `x ∈ Dom S`.

Implementation note: `S` is antilinear, so Mathlib's `LinearPMap.inverse` does not apply; the
identity `S⁻¹ = S` is stated through injectivity, the range, and the pointwise involution.

Blueprint: lmm:tomita-inverse-is-self
-/
theorem tomitaOperator_inverse_eq_self {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    Function.Injective (tomitaOperator M Ω C) ∧
      Set.range (tomitaOperator M Ω C) = (linearizedTomitaPre M Ω C).closure.domain ∧
      ∀ x, ∃ h : tomitaOperator M Ω C x ∈ (linearizedTomitaPre M Ω C).closure.domain,
        tomitaOperator M Ω C ⟨_, h⟩ = x := by
  obtain ⟨hinj, hS, -, -⟩ := tomitaOperator_involution hM hΩ C hC
  refine ⟨hinj, Set.ext fun y => ⟨?_, fun hy => ?_⟩, hS⟩
  · rintro ⟨x, rfl⟩
    exact (hS x).1
  · obtain ⟨h, e⟩ := hS ⟨y, hy⟩
    exact ⟨_, e⟩

/--
With `P = J Δ^{-1/2} J⁻¹` (`antiunitaryConj`), `S = J⁻¹ P`: `Dom S = Dom P` and
`S ψ = J⁻¹ (P ψ)`.

Blueprint: lmm:tomita-inverse-as-product
-/
theorem tomitaOperator_eq_symm_conj_invSqrt {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    (linearizedTomitaPre M Ω C).closure.domain =
        (antiunitaryConj (modularConjugation hM hΩ C hC)
          (modularOperatorInvSqrt hM hΩ C hC)).domain ∧
      ∀ (ψ : H) (h₁ : ψ ∈ (linearizedTomitaPre M Ω C).closure.domain)
        (h₂ : ψ ∈ (antiunitaryConj (modularConjugation hM hΩ C hC)
          (modularOperatorInvSqrt hM hΩ C hC)).domain),
        tomitaOperator M Ω C ⟨ψ, h₁⟩ = (modularConjugation hM hΩ C hC).symm
          (antiunitaryConj (modularConjugation hM hΩ C hC)
            (modularOperatorInvSqrt hM hΩ C hC) ⟨ψ, h₂⟩) := by
  obtain ⟨hD, hcl, hker, -⟩ := linearizedTomita_closure_polar_hyps hM hΩ C hC
  obtain ⟨hpos, hsa, -, hkerΔ, -, -⟩ := modularOperator_properties hM hΩ C hC
  obtain ⟨hdomS, hJ⟩ := tomitaOperator_eq_modularConjugation_sqrt hM hΩ C hC
  obtain ⟨-, -, hinvS⟩ := tomitaOperator_inverse_eq_self hM hΩ C hC
  have hinv : modularOperatorInvSqrt hM hΩ C hC = (modularOperatorSqrt hM hΩ C hC).inverse :=
    (inverse_sqrt_functionalCalculus hsa hpos hkerΔ).symm
  have hks := (absoluteValue_injective_denseRange hD hcl hker).1
  have hf : (modularOperatorSqrt hM hΩ C hC).ker = ⊥ :=
    LinearPMap.ker_eq_bot'.mpr fun x hx =>
      Subtype.ext ((Submodule.mem_bot ℂ).mp (hks ▸ mem_ker.mpr ⟨x.2, hx⟩))
  have key : ∀ (ψ : H) (h₁ : ψ ∈ (linearizedTomitaPre M Ω C).closure.domain),
      (modularConjugation hM hΩ C hC).symm ψ = modularOperatorSqrt hM hΩ C hC
        ⟨tomitaOperator M Ω C ⟨ψ, h₁⟩, hdomS ▸ (hinvS ⟨ψ, h₁⟩).1⟩ := by
    intro ψ h₁
    obtain ⟨h, e⟩ := hinvS ⟨ψ, h₁⟩
    rw [hJ _ h (hdomS ▸ h)] at e
    exact (congrArg (modularConjugation hM hΩ C hC).symm e).symm.trans
      (LinearIsometryEquiv.symm_apply_apply _ _)
  rw [hinv]
  refine ⟨Submodule.ext fun ψ => ⟨fun h₁ => ?_, fun h₂ => ?_⟩, fun ψ h₁ h₂ => ?_⟩
  · change (modularConjugation hM hΩ C hC).symm ψ ∈ (modularOperatorSqrt hM hΩ C hC).inverse.domain
    rw [LinearPMap.inverse_domain, key ψ h₁]
    exact LinearMap.mem_range_self _ _
  · have h₂' : (modularConjugation hM hΩ C hC).symm ψ ∈
        (modularOperatorSqrt hM hΩ C hC).inverse.domain := h₂
    rw [LinearPMap.inverse_domain] at h₂'
    obtain ⟨⟨φ, hφ⟩, e⟩ := h₂'
    have hφ' : φ ∈ (linearizedTomitaPre M Ω C).closure.domain := hdomS ▸ hφ
    have : tomitaOperator M Ω C ⟨φ, hφ'⟩ = ψ := by
      rw [hJ φ hφ' hφ]
      exact (congrArg (modularConjugation hM hΩ C hC) e).trans
        (LinearIsometryEquiv.apply_symm_apply _ _)
    exact this ▸ (hinvS ⟨φ, hφ'⟩).1
  · change _ = (modularConjugation hM hΩ C hC).symm ((modularConjugation hM hΩ C hC)
      ((modularOperatorSqrt hM hΩ C hC).inverse ⟨_, h₂⟩))
    rw [LinearIsometryEquiv.symm_apply_apply,
      LinearPMap.inverse_apply_eq hf (key ψ h₁).symm]

/--
With `P = J Δ^{-1/2} J⁻¹`, `P` is positive and self-adjoint, `C J⁻¹` is unitary, and
`S′ = (C J⁻¹) P`.

Blueprint: lmm:tomita-inverse-polar
-/
theorem linearizedTomita_closure_eq_unitary_conj_invSqrt {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    IsPositive (antiunitaryConj (modularConjugation hM hΩ C hC)
        (modularOperatorInvSqrt hM hΩ C hC)) ∧
      IsSelfAdjoint (antiunitaryConj (modularConjugation hM hΩ C hC)
        (modularOperatorInvSqrt hM hΩ C hC)) ∧
      ∃ U : H ≃ₗᵢ[ℂ] H, (∀ x, U x = C ((modularConjugation hM hΩ C hC).symm x)) ∧
        (linearizedTomitaPre M Ω C).closure = U.toLinearEquiv.toLinearMap.compPMap
          (antiunitaryConj (modularConjugation hM hΩ C hC)
            (modularOperatorInvSqrt hM hΩ C hC)) := by
  obtain ⟨hpos, hsa⟩ :=
    inv_sqrt_functionalCalculus_positive (modularOperator_isSelfAdjoint hM hΩ C hC)
  obtain ⟨hdom, hval⟩ := tomitaOperator_eq_symm_conj_invSqrt hM hΩ C hC
  refine ⟨(antiunitaryConj_positive_injective _).1 hpos,
    (spectralMeasure_antiunitaryConj _ hsa).1,
    (modularConjugation hM hΩ C hC).symm.trans C, fun _ => rfl,
    LinearPMap.ext hdom fun x y hxy => ?_⟩
  rw [← hC ((linearizedTomitaPre M Ω C).closure ⟨x, y⟩)]
  exact congrArg C (hval x y hxy)

/--
`J (J φ) = φ` for every `φ`, and `J Δ^{1/2} J = Δ^{-1/2}`. Since `J⁻¹ = J`, the operator
`J Δ^{1/2} J` is the antiunitary conjugate `J Δ^{1/2} J⁻¹` (`antiunitaryConj`).

Blueprint: thrm:modular-conjugation-involution
-/
theorem modularConjugation_involution {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    (∀ φ, modularConjugation hM hΩ C hC (modularConjugation hM hΩ C hC φ) = φ) ∧
      antiunitaryConj (modularConjugation hM hΩ C hC) (modularOperatorSqrt hM hΩ C hC) =
        modularOperatorInvSqrt hM hΩ C hC := by
  set J := modularConjugation hM hΩ C hC
  obtain ⟨hPpos, hPsa, U, hU, hTUP⟩ := linearizedTomita_closure_eq_unitary_conj_invSqrt hM hΩ C hC
  have hyps := linearizedTomita_closure_polar_hyps hM hΩ C hC
  obtain ⟨hPeq, hUP⟩ := polar_decomposition_unique hyps.1 hyps.2.1 U hPsa hPpos hTUP
  have hPeq' : antiunitaryConj J (modularOperatorInvSqrt hM hΩ C hC) =
      modularOperatorSqrt hM hΩ C hC := hPeq
  have hCU : ∀ x, C (U x) = J x :=
    eq_modularConjugation_of_continuous hM hΩ C hC (fun x => C (U x))
      (C.continuous.comp U.continuous) fun ψ h₁ h₂ => by
        simp only [tomitaOperator]
        rw [← hUP ψ h₁ h₂]
        rfl
  have hJs : ∀ x, J.symm x = J x := fun x => by rw [← hCU, hU, hC]
  have hJJ : ∀ φ, J (J φ) = φ := fun φ => by
    conv_lhs => rw [← hJs φ]
    exact J.apply_symm_apply φ
  refine ⟨hJJ, ?_⟩
  rw [← hPeq']
  have hss : ∀ x, J.symm (J.symm x) = x := fun x => by rw [hJs, hJs, hJJ]
  refine LinearPMap.ext ?_ fun x hx hx' => ?_
  · ext x
    change J.symm (J.symm x) ∈ (modularOperatorInvSqrt hM hΩ C hC).domain ↔
      x ∈ (modularOperatorInvSqrt hM hΩ C hC).domain
    rw [hss]
  · change J (J (modularOperatorInvSqrt hM hΩ C hC ⟨J.symm (J.symm x), hx⟩)) = _
    rw [hJJ]
    exact congrArg _ (Subtype.ext (hss x))

/--
`J Δ J = Δ⁻¹`, with `J Δ J = J Δ J⁻¹` (`antiunitaryConj`, as `J⁻¹ = J`) and `Δ⁻¹` Mathlib's
`LinearPMap.inverse`.

Blueprint: crllr:modular-conjugation-inverts
-/
theorem modularConjugation_conj_modularOperator {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    antiunitaryConj (modularConjugation hM hΩ C hC) (modularOperator M Ω C) =
      (modularOperator M Ω C).inverse := by
  have hsa := modularOperator_isSelfAdjoint hM hΩ C hC
  obtain ⟨hpos, -, -, hker, -⟩ := modularOperator_properties hM hΩ C hC
  have key : ∀ (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B), A = B →
      functionalCalculus hA (fun x => ((x ^ 2 : ℝ) : ℂ)) =
        functionalCalculus hB (fun x => (x : ℂ) ^ 2) := by
    rintro A _ hA hB rfl
    simp only [Complex.ofReal_pow]
  obtain ⟨h, hconj⟩ := functionalCalculus_antiunitaryConj (modularConjugation hM hΩ C hC)
    (sqrt_functionalCalculus_positive hsa).2
  have e1 := hconj (fun x => x ^ 2) (measurable_id.pow_const 2)
  rw [key _ _ _ (sqrt_functionalCalculus_positive hsa).2 rfl,
    sq_sqrt_functionalCalculus hsa hpos] at e1
  rw [e1, key _ _ h (inv_sqrt_functionalCalculus_positive hsa).2
    (modularConjugation_involution hM hΩ C hC).2, sq_inv_sqrt_functionalCalculus hsa hpos hker]

end Physicslib4.Modular
