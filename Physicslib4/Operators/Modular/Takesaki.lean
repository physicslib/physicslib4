/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Operators.Modular.Modular
import Physicslib4.Spectral.Unbounded.Spectrum

/-!
# Takesaki's lemma: the commutant extension lemma and the resolvent of `Δ`

For a von Neumann algebra `M` with a cyclic and separating vector `Ω`, this file states the
commutant extension lemma (a vector `ψ` with `‖b' ψ‖ ≤ c ‖b' Ω‖` for all `b' ∈ M'` is `a Ω` for a
unique `a ∈ M` with `‖a‖ ≤ c`) and the resolvent of the modular operator `Δ` off `[0, ∞)`.

For `z ∉ [0, ∞)` the resolvent function is `r_z = 1_{[0, ∞)} · (z - ι)⁻¹`, written inline as
`(Set.Ici 0).indicator fun t => (z - t)⁻¹`, and `d(z)` is the distance from `z` to `[0, ∞)`,
written `Metric.infDist z (ofReal '' Set.Ici 0)`. The bounded operator `r_z(Δ)` is the bounded
integral `(spectralMeasure _).integral r_z`, which is the functional calculus of `r_z` by
`modularResolvent_bounded`.
-/

namespace Physicslib4.Modular

open scoped InnerProductSpace ComplexConjugate
open Physicslib4.Spectral.Unbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
Under the commutant bound `‖b' ψ‖ ≤ c ‖b' Ω‖`, `b' Ω ↦ b' ψ` is a well-defined linear map
`T₀ : M' Ω → H`, unique, with `‖T₀ η‖ ≤ c ‖η‖`.

Implementation note: `M' Ω` is written as the span of `{b' Ω | b' ∈ M'}`, which is that set
since `M'` is a linear subspace.

Blueprint: lmm:commutant-extension-well-defined
-/
theorem commutantExtension_linearMap {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) {ψ : H} {c : ℝ} (hc : 0 ≤ c)
    (hψ : ∀ b ∈ Set.centralizer M, ‖b ψ‖ ≤ c * ‖b Ω‖) :
    (∃! T₀ : Submodule.span ℂ ((fun b => b Ω) '' Set.centralizer M) →ₗ[ℂ] H,
      ∀ (b : H →L[ℂ] H) (hb : b ∈ Set.centralizer M),
        T₀ ⟨b Ω, Submodule.subset_span ⟨b, hb, rfl⟩⟩ = b ψ) ∧
      ∀ T₀ : Submodule.span ℂ ((fun b => b Ω) '' Set.centralizer M) →ₗ[ℂ] H,
        (∀ (b : H →L[ℂ] H) (hb : b ∈ Set.centralizer M),
          T₀ ⟨b Ω, Submodule.subset_span ⟨b, hb, rfl⟩⟩ = b ψ) →
        ∀ η, ‖T₀ η‖ ≤ c * ‖(η : H)‖ := by
  sorry

/--
Under the commutant bound, there is a unique bounded `T` with `T (b' Ω) = b' ψ` for all
`b' ∈ M'`, and `‖T‖ ≤ c`.

Implementation note: extending `T₀` of `commutantExtension_linearMap` is stated as
`T (b' Ω) = b' ψ` for all `b' ∈ M'`.

Blueprint: lmm:commutant-extension-bounded
-/
theorem commutantExtension_bounded {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) {ψ : H} {c : ℝ} (hc : 0 ≤ c)
    (hψ : ∀ b ∈ Set.centralizer M, ‖b ψ‖ ≤ c * ‖b Ω‖) :
    ∃ T : H →L[ℂ] H, (∀ b ∈ Set.centralizer M, T (b Ω) = b ψ) ∧ ‖T‖ ≤ c ∧
      ∀ T' : H →L[ℂ] H, (∀ b ∈ Set.centralizer M, T' (b Ω) = b ψ) → T' = T := by
  sorry

/--
A bounded `T` with `T (b' Ω) = b' ψ` for all `b' ∈ M'` commutes with every `d' ∈ M'`, and so
lies in `M'' = M`.

Implementation note: `T` is the operator of `commutantExtension_bounded`, characterized by its
values on `M' Ω`; the commutant bound is not needed for this step.

Blueprint: lmm:commutant-extension-in-algebra
-/
theorem commutantExtension_mem {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) {ψ : H} (T : H →L[ℂ] H)
    (hT : ∀ b ∈ Set.centralizer M, T (b Ω) = b ψ) :
    (∀ d ∈ Set.centralizer M, T * d = d * T) ∧ T ∈ M := by
  sorry

/--
The commutant extension lemma: if `‖b' ψ‖ ≤ c ‖b' Ω‖` for all `b' ∈ M'`, then `ψ = a Ω` for a
unique `a ∈ M`, and `‖a‖ ≤ c`.

Blueprint: lmm:commutant-extension
-/
theorem commutantExtension {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) {ψ : H} {c : ℝ} (hc : 0 ≤ c)
    (hψ : ∀ b ∈ Set.centralizer M, ‖b ψ‖ ≤ c * ‖b Ω‖) :
    ∃ a ∈ M, a Ω = ψ ∧ ‖a‖ ≤ c ∧ ∀ a' ∈ M, a' Ω = ψ → a' = a := by
  sorry

/--
For `z ∉ [0, ∞)`: `d(z) > 0`, `r_z` is measurable, `|r_z| ≤ 1/d(z)`, `conj r_z = r_{z̄}` and
`(z - λ) r_z(λ) = 1_{[0, ∞)}(λ)`.

Blueprint: lmm:resolvent-function-props
-/
theorem resolventFunction_properties {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) :
    0 < Metric.infDist z (((↑) : ℝ → ℂ) '' Set.Ici 0) ∧
      Measurable ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) ∧
      (∀ t : ℝ, ‖(Set.Ici (0 : ℝ)).indicator (fun t : ℝ => (z - t)⁻¹) t‖ ≤
        1 / Metric.infDist z (((↑) : ℝ → ℂ) '' Set.Ici 0)) ∧
      (∀ t : ℝ, conj ((Set.Ici (0 : ℝ)).indicator (fun t : ℝ => (z - t)⁻¹) t) =
        (Set.Ici (0 : ℝ)).indicator (fun t : ℝ => (conj z - t)⁻¹) t) ∧
      ∀ t : ℝ, (z - t) * (Set.Ici (0 : ℝ)).indicator (fun t : ℝ => (z - t)⁻¹) t =
        (Set.Ici (0 : ℝ)).indicator 1 t := by
  sorry

/--
For `z ∉ [0, ∞)`, `r_z(Δ)` is the bounded operator `∫ r_z dμ^Δ` on all of `H`, with
`‖r_z(Δ)‖ ≤ 1/d(z)` and `r_z(Δ)* = r_{z̄}(Δ)`.

Blueprint: lmm:modular-resolvent-bounded
-/
theorem modularResolvent_bounded {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) :
    functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC)
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) =
      (((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) : H →ₗ[ℂ] H).toPMap ⊤) ∧
    ‖(spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹)‖ ≤
      1 / Metric.infDist z (((↑) : ℝ → ℂ) '' Set.Ici 0) ∧
    ContinuousLinearMap.adjoint
        ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹)) =
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (conj z - t)⁻¹) := by
  sorry

/--
For `z ∈ ℂ`, `W_{z - ι} = Dom Δ` and `(z - ι)(Δ) ψ = z ψ - Δ ψ` for `ψ ∈ Dom Δ`.

Blueprint: lmm:modular-z-minus-fc
-/
theorem modularOperator_functionalCalculus_const_sub {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (z : ℂ) :
    (functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC)
        fun t : ℝ => z - t).domain = (modularOperator M Ω C).domain ∧
      ∀ (ψ : H) (h₁ : ψ ∈ (functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC)
          fun t : ℝ => z - t).domain) (h₂ : ψ ∈ (modularOperator M Ω C).domain),
        functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC) (fun t : ℝ => z - t)
          ⟨ψ, h₁⟩ = z • ψ - modularOperator M Ω C ⟨ψ, h₂⟩ := by
  sorry

/--
`1_{[0, ∞)}(Δ) = 𝟙`.

Blueprint: lmm:modular-indicator-nonneg-one
-/
theorem modularOperator_functionalCalculus_indicator_Ici {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC) ((Set.Ici (0 : ℝ)).indicator 1) =
      (LinearMap.id : H →ₗ[ℂ] H).toPMap ⊤ := by
  sorry

/--
For `z ∉ [0, ∞)` and `ξ ∈ H`, `r_z(Δ) ξ ∈ Dom Δ` and `z r_z(Δ) ξ - Δ r_z(Δ) ξ = ξ`.

Blueprint: lmm:modular-resolvent-right-inverse
-/
theorem modularResolvent_rightInverse {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) (ξ : H) :
    ∃ h : (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) ξ ∈ (modularOperator M Ω C).domain,
      z • (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) ξ -
        modularOperator M Ω C ⟨_, h⟩ = ξ := by
  sorry

/--
For `z ∉ [0, ∞)` and `ψ ∈ Dom Δ`, `r_z(Δ) (z ψ - Δ ψ) = ψ`.

Blueprint: lmm:modular-resolvent-left-inverse
-/
theorem modularResolvent_leftInverse {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0)
    (ψ : (modularOperator M Ω C).domain) :
    (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹)
        (z • (ψ : H) - modularOperator M Ω C ψ) = ψ := by
  sorry

/--
Every `z ∉ [0, ∞)` is in the resolvent set of `Δ`, with `(Δ - z𝟙)⁻¹ = -r_z(Δ)`; so
`(z - Δ)⁻¹ = r_z(Δ)` is bounded, `‖(z - Δ)⁻¹‖ ≤ 1/d(z)` and `((z - Δ)⁻¹)* = (z̄ - Δ)⁻¹`.

Implementation note: `(Δ - z𝟙)⁻¹ = -r_z(Δ)` is stated as: a bounded `B` is the resolvent
(`IsResolvent`) exactly when `B = -r_z(Δ)`.

Blueprint: crllr:modular-resolvent
-/
theorem modularResolvent_isResolvent {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) :
    z ∈ pmapResolventSet (modularOperator M Ω C) ∧
    (∀ B : H →L[ℂ] H, IsResolvent (modularOperator M Ω C) z B ↔
      B = -(spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹)) ∧
    ‖(spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹)‖ ≤
      1 / Metric.infDist z (((↑) : ℝ → ℂ) '' Set.Ici 0) ∧
    ContinuousLinearMap.adjoint
        ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹)) =
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (conj z - t)⁻¹) := by
  sorry

/-! ### Takesaki's lemma

For `z ∉ [0, ∞)` and `a' ∈ M'`, the blueprint fixes `c = ‖a'‖ / √(2(|z| - Re z))`,
`ψ = (z - Δ)⁻¹ a' Ω`, `𝓑_c = {a ∈ M | ‖a‖ ≤ c}`, `𝒦_c = closure (𝓑_c Ω)` and
`G(u, v; a) = Re ⟪u, a' Ω⟫ - Re (z ⟪u, a Ω⟫ - ⟪a* Ω, v⟫)`. These are written inline:
`ψ` is `(spectralMeasure _).integral r_z (a' Ω)`, `𝒦_c` is
`closure ((fun a => a Ω) '' {a ∈ M | ‖a‖ ≤ c})`, and `G` is expanded. Where a statement uses no
property of the value of `c`, `c` is an arbitrary real number.

For `h ∈ M`, `ε > 0` and `s ∈ ℝ`, the shifted power `P_ε^s = f_s(h* h)` with
`f_s(t) = (ε + max t 0)^s` is written `P[h, ε, s]` (local notation for the continuous functional
calculus `cfc`), `u_ε = h P_ε^{-1/2}`, `x_ε = P_ε^{-1/4} h*`, `p_ε = ‖x_ε* Ω‖` and
`q_ε = ‖x_ε Ω‖`.
-/

/-- The shifted power `P_ε^s = f_s(h* h)`, `f_s(t) = (ε + max t 0)^s`, in the continuous
functional calculus. -/
local notation "P[" h ", " ε ", " s "]" =>
  cfc (fun t : ℝ => (ε + max t 0) ^ (s : ℝ)) (star h * h)

/--
For `z ∉ [0, ∞)`, `|z| - Re z > 0` and `|z p - q| ≥ √(2(|z| - Re z) p q)` for real `p, q ≥ 0`.

Blueprint: lmm:takesaki-elementary-inequality
-/
theorem takesaki_elementary_inequality {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) :
    0 < ‖z‖ - z.re ∧ ∀ p q : ℝ, 0 ≤ p → 0 ≤ q →
      Real.sqrt (2 * (‖z‖ - z.re) * p * q) ≤ ‖z * (p : ℂ) - (q : ℂ)‖ := by
  sorry

/--
`𝒦_c = closure {a Ω | a ∈ M, ‖a‖ ≤ c}` is closed and convex, and contains `0` when `c ≥ 0`.

Blueprint: lmm:takesaki-ball-closed-convex
-/
theorem takesakiBall_closure_isClosed_convex {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M)
    (Ω : H) {c : ℝ} (hc : 0 ≤ c) :
    IsClosed (closure ((fun a : H →L[ℂ] H => a Ω) '' {a ∈ M | ‖a‖ ≤ c})) ∧
      Convex ℝ (closure ((fun a : H →L[ℂ] H => a Ω) '' {a ∈ M | ‖a‖ ≤ c})) ∧
      (0 : H) ∈ closure ((fun a : H →L[ℂ] H => a Ω) '' {a ∈ M | ‖a‖ ≤ c}) := by
  sorry

/--
Every `ξ ∈ 𝒦_c` satisfies `‖b' ξ‖ ≤ c ‖b' Ω‖` for all `b' ∈ M'`.

Blueprint: lmm:takesaki-ball-closure-bound
-/
theorem takesakiBall_closure_bound {M : Set (H →L[ℂ] H)} {Ω : H} {c : ℝ} {ξ : H}
    (hξ : ξ ∈ closure ((fun a : H →L[ℂ] H => a Ω) '' {a ∈ M | ‖a‖ ≤ c})) :
    ∀ b ∈ Set.centralizer M, ‖b ξ‖ ≤ c * ‖b Ω‖ := by
  sorry

/--
A point `ξ` outside a nonempty closed convex `K ⊆ H` is strictly separated from `K`:
`Re ⟪φ, k⟫ + γ ≤ Re ⟪φ, ξ⟫` for all `k ∈ K`, for some `φ` and `γ > 0`.

Blueprint: lmm:takesaki-separation
-/
theorem exists_re_inner_add_le_of_not_mem_convex {K : Set H} (hne : K.Nonempty)
    (hcl : IsClosed K) (hconv : Convex ℝ K) {ξ : H} (hξ : ξ ∉ K) :
    ∃ φ : H, ∃ γ > 0, ∀ k ∈ K, (⟪φ, k⟫_ℂ).re + γ ≤ (⟪φ, ξ⟫_ℂ).re := by
  sorry

/--
For `χ = (z̄ - Δ)⁻¹ φ`: `χ ∈ Dom Δ ⊆ Dom S`, `z̄ χ - Δ χ = φ` and `⟪φ, ψ⟫ = ⟪χ, a' Ω⟫`.

Blueprint: lmm:takesaki-transfer-resolvent
-/
theorem takesaki_transfer_resolvent {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) (a' : H →L[ℂ] H)
    (φ χ : H) (hχ : χ = (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
      ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (conj z - t)⁻¹) φ) :
    ∃ h : χ ∈ (modularOperator M Ω C).domain,
      χ ∈ (linearizedTomitaPre M Ω C).closure.domain ∧
      conj z • χ - modularOperator M Ω C ⟨χ, h⟩ = φ ∧
      ⟪φ, (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) (a' Ω)⟫_ℂ = ⟪χ, a' Ω⟫_ℂ := by
  sorry

/--
For `χ = (z̄ - Δ)⁻¹ φ` and `a ∈ M`, `⟪φ, a Ω⟫ = z ⟪χ, a Ω⟫ - ⟪a* Ω, S χ⟫`, and hence
`Re ⟪φ, ψ⟫ - Re ⟪φ, a Ω⟫ = G(χ, S χ; a)`.

Blueprint: lmm:takesaki-transfer
-/
theorem takesaki_transfer {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) (a' : H →L[ℂ] H)
    (φ χ : H) (hχ : χ = (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
      ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (conj z - t)⁻¹) φ) :
    ∃ hS : χ ∈ (linearizedTomitaPre M Ω C).closure.domain, ∀ a ∈ M,
      ⟪φ, a Ω⟫_ℂ = z * ⟪χ, a Ω⟫_ℂ - ⟪star a Ω, tomitaOperator M Ω C ⟨χ, hS⟩⟫_ℂ ∧
      (⟪φ, (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) (a' Ω)⟫_ℂ).re -
          (⟪φ, a Ω⟫_ℂ).re =
        (⟪χ, a' Ω⟫_ℂ).re -
          (z * ⟪χ, a Ω⟫_ℂ - ⟪star a Ω, tomitaOperator M Ω C ⟨χ, hS⟩⟫_ℂ).re := by
  sorry

/--
`M Ω` is a core for `S`: for `χ ∈ Dom S` there are `h_n ∈ M` with `h_n Ω → χ` and
`h_n* Ω → S χ`.

Blueprint: lmm:tomita-core
-/
theorem tomitaOperator_exists_seq_tendsto {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (χ : (linearizedTomitaPre M Ω C).closure.domain) :
    ∃ h : ℕ → H →L[ℂ] H, (∀ n, h n ∈ M) ∧
      Filter.Tendsto (fun n => h n Ω) Filter.atTop (nhds (χ : H)) ∧
      Filter.Tendsto (fun n => star (h n) Ω) Filter.atTop (nhds (tomitaOperator M Ω C χ)) := by
  sorry

/--
`G` is Lipschitz in `(u, v)`, uniformly in `a ∈ 𝓑_c`:
`|G(u, v; a) - G(u₁, v₁; a)| ≤ (‖a' Ω‖ + |z| c ‖Ω‖) ‖u - u₁‖ + c ‖Ω‖ ‖v - v₁‖`.

Blueprint: lmm:takesaki-G-lipschitz
-/
theorem takesakiG_lipschitz {M : Set (H →L[ℂ] H)} {Ω : H} (z : ℂ) (a' : H →L[ℂ] H) {c : ℝ}
    (u v u₁ v₁ : H) {a : H →L[ℂ] H} (ha : a ∈ M) (hac : ‖a‖ ≤ c) :
    |((⟪u, a' Ω⟫_ℂ).re - (z * ⟪u, a Ω⟫_ℂ - ⟪star a Ω, v⟫_ℂ).re) -
        ((⟪u₁, a' Ω⟫_ℂ).re - (z * ⟪u₁, a Ω⟫_ℂ - ⟪star a Ω, v₁⟫_ℂ).re)| ≤
      (‖a' Ω‖ + ‖z‖ * c * ‖Ω‖) * ‖u - u₁‖ + c * ‖Ω‖ * ‖v - v₁‖ := by
  sorry

/--
For `χ ∈ Dom S` and `δ > 0` there is `h ∈ M` with `|G(χ, S χ; a) - G(h Ω, h* Ω; a)| < δ` for
every `a ∈ 𝓑_c`.

Blueprint: lmm:takesaki-uniform-approximation
-/
theorem takesakiG_uniform_approximation {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (z : ℂ) (a' : H →L[ℂ] H) (c : ℝ)
    (χ : (linearizedTomitaPre M Ω C).closure.domain) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h ∈ M, ∀ a ∈ M, ‖a‖ ≤ c →
      |((⟪(χ : H), a' Ω⟫_ℂ).re -
          (z * ⟪(χ : H), a Ω⟫_ℂ - ⟪star a Ω, tomitaOperator M Ω C χ⟫_ℂ).re) -
        ((⟪h Ω, a' Ω⟫_ℂ).re - (z * ⟪h Ω, a Ω⟫_ℂ - ⟪star a Ω, star h Ω⟫_ℂ).re)| < δ := by
  sorry

/--
For self-adjoint `x ∈ M` and `f : ℝ → ℝ`, the continuous functional calculus `f(x)` lies in `M`.

Blueprint: lmm:cfc-mem-von-neumann
-/
theorem cfc_mem_of_isVonNeumannSet {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M)
    {x : H →L[ℂ] H} (hx : x ∈ M) (hsa : IsSelfAdjoint x) (f : ℝ → ℝ) : cfc f x ∈ M := by
  sorry

/--
For `h ∈ M` and `ε > 0`, `P_ε^s ∈ M`. The other conjuncts of the blueprint lemma are
`takesakiShiftedPow_isSelfAdjoint`, `takesakiShiftedPow_mul`, `takesakiShiftedPow_zero`,
`takesakiShiftedPow_commute` and `takesakiShiftedPow_norm_le`.

Blueprint: lmm:takesaki-shifted-powers
-/
theorem takesakiShiftedPow_mem {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M)
    {h : H →L[ℂ] H} (hh : h ∈ M) {ε : ℝ} (hε : 0 < ε) (s : ℝ) : P[h, ε, s] ∈ M := by
  sorry

/--
`P_ε^s` is self-adjoint (a conjunct of `takesakiShiftedPow_mem`).

Blueprint: lmm:takesaki-shifted-powers
-/
theorem takesakiShiftedPow_isSelfAdjoint (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    IsSelfAdjoint (P[h, ε, s]) := by
  sorry

/--
`P_ε^s P_ε^t = P_ε^{s+t}` (a conjunct of `takesakiShiftedPow_mem`).

Blueprint: lmm:takesaki-shifted-powers
-/
theorem takesakiShiftedPow_mul (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) (s t : ℝ) :
    P[h, ε, s] * P[h, ε, t] = P[h, ε, s + t] := by
  sorry

/--
`P_ε^0 = 𝟙` (a conjunct of `takesakiShiftedPow_mem`).

Blueprint: lmm:takesaki-shifted-powers
-/
theorem takesakiShiftedPow_zero (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) :
    P[h, ε, 0] = 1 := by
  sorry

/--
`P_ε^s` commutes with `P = h* h` (a conjunct of `takesakiShiftedPow_mem`).

Blueprint: lmm:takesaki-shifted-powers
-/
theorem takesakiShiftedPow_commute (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    P[h, ε, s] * (star h * h) = (star h * h) * P[h, ε, s] := by
  sorry

/--
`‖P_ε^s‖ ≤ ε^s` for `s ≤ 0` (a conjunct of `takesakiShiftedPow_mem`).

Blueprint: lmm:takesaki-shifted-powers
-/
theorem takesakiShiftedPow_norm_le (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : s ≤ 0) :
    ‖P[h, ε, s]‖ ≤ ε ^ s := by
  sorry

/--
The approximate polar decomposition: `u_ε, x_ε ∈ M`, `x_ε* = h P_ε^{-1/4}`, `h* = P_ε^{1/4} x_ε`,
`h* u_ε = x_ε x_ε*` and `u_ε h* = x_ε* x_ε`.

Blueprint: lmm:takesaki-approximate-polar
-/
theorem takesaki_approximate_polar {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M)
    {h : H →L[ℂ] H} (hh : h ∈ M) {ε : ℝ} (hε : 0 < ε) :
    h * P[h, ε, -(1/2)] ∈ M ∧ P[h, ε, -(1/4)] * star h ∈ M ∧
      star (P[h, ε, -(1/4)] * star h) = h * P[h, ε, -(1/4)] ∧
      star h = P[h, ε, 1/4] * (P[h, ε, -(1/4)] * star h) ∧
      star h * (h * P[h, ε, -(1/2)]) =
        (P[h, ε, -(1/4)] * star h) * star (P[h, ε, -(1/4)] * star h) ∧
      (h * P[h, ε, -(1/2)]) * star h =
        star (P[h, ε, -(1/4)] * star h) * (P[h, ε, -(1/4)] * star h) := by
  sorry

/--
`‖u_ε‖ ≤ 1` and `‖x_ε‖² ≤ ‖h‖`.

Blueprint: lmm:takesaki-approx-polar-norms
-/
theorem takesaki_approx_polar_norms (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) :
    ‖h * P[h, ε, -(1/2)]‖ ≤ 1 ∧ ‖P[h, ε, -(1/4)] * star h‖ ^ 2 ≤ ‖h‖ := by
  sorry

/--
`‖P_ε^{1/4} Ω‖² ≤ p_ε² + √ε ‖Ω‖²`.

Blueprint: lmm:takesaki-shifted-root-bound
-/
theorem takesaki_shifted_root_bound (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) (Ω : H) :
    ‖P[h, ε, 1/4] Ω‖ ^ 2 ≤
      ‖star (P[h, ε, -(1/4)] * star h) Ω‖ ^ 2 + Real.sqrt ε * ‖Ω‖ ^ 2 := by
  sorry

/--
For `a' ∈ M'`, `h ∈ M` and `ε > 0`, `|⟪h Ω, a' Ω⟫| ≤ ‖a'‖ (p_ε + ε^{1/4} ‖Ω‖) q_ε`.

Blueprint: lmm:takesaki-numerator-bound
-/
theorem takesaki_numerator_bound {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M) (Ω : H)
    {a' : H →L[ℂ] H} (ha' : a' ∈ Set.centralizer M) {h : H →L[ℂ] H} (hh : h ∈ M)
    {ε : ℝ} (hε : 0 < ε) :
    ‖⟪h Ω, a' Ω⟫_ℂ‖ ≤ ‖a'‖ * (‖star (P[h, ε, -(1/4)] * star h) Ω‖ + ε ^ (1/4 : ℝ) * ‖Ω‖) *
      ‖(P[h, ε, -(1/4)] * star h) Ω‖ := by
  sorry

/--
For `w ∈ ℂ` and `c ≥ 0` there is `s ∈ ℂ` with `|s| ≤ c` and `Re (s w) = c |w|`.

Blueprint: lmm:complex-rotation-choice
-/
theorem exists_norm_le_re_mul_eq_mul_norm (w : ℂ) {c : ℝ} (hc : 0 ≤ c) :
    ∃ s : ℂ, ‖s‖ ≤ c ∧ (s * w).re = c * ‖w‖ := by
  sorry

/--
For `s ∈ ℂ`, `⟪h Ω, s u_ε Ω⟫ = s p_ε²` and `⟪(s u_ε)* Ω, h* Ω⟫ = s q_ε²`.

Blueprint: lmm:takesaki-test-inner-products
-/
theorem takesaki_test_inner_products (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) (Ω : H) (s : ℂ) :
    ⟪h Ω, (s • (h * P[h, ε, -(1/2)])) Ω⟫_ℂ =
        s * ((‖star (P[h, ε, -(1/4)] * star h) Ω‖ ^ 2 : ℝ) : ℂ) ∧
      ⟪star (s • (h * P[h, ε, -(1/2)])) Ω, star h Ω⟫_ℂ =
        s * ((‖(P[h, ε, -(1/4)] * star h) Ω‖ ^ 2 : ℝ) : ℂ) := by
  sorry

/--
For `h ∈ M` and `ε > 0` there is `a ∈ 𝓑_c` with
`Re (z ⟪h Ω, a Ω⟫ - ⟪a* Ω, h* Ω⟫) ≥ ‖a'‖ p_ε q_ε`.

Blueprint: lmm:takesaki-test-element
-/
theorem takesaki_test_element {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M) (Ω : H)
    {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) (a' : H →L[ℂ] H) {h : H →L[ℂ] H}
    (hh : h ∈ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ M, ‖a‖ ≤ ‖a'‖ / Real.sqrt (2 * (‖z‖ - z.re)) ∧
      ‖a'‖ * ‖star (P[h, ε, -(1/4)] * star h) Ω‖ * ‖(P[h, ε, -(1/4)] * star h) Ω‖ ≤
        (z * ⟪h Ω, a Ω⟫_ℂ - ⟪star a Ω, star h Ω⟫_ℂ).re := by
  sorry

/--
The key estimate: for `h ∈ M` and `δ > 0` there is `a ∈ 𝓑_c` with `G(h Ω, h* Ω; a) ≤ δ`.

Blueprint: lmm:takesaki-key-estimate
-/
theorem takesaki_key_estimate {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M) (Ω : H)
    {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) {a' : H →L[ℂ] H}
    (ha' : a' ∈ Set.centralizer M) {h : H →L[ℂ] H} (hh : h ∈ M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a ∈ M, ‖a‖ ≤ ‖a'‖ / Real.sqrt (2 * (‖z‖ - z.re)) ∧
      (⟪h Ω, a' Ω⟫_ℂ).re - (z * ⟪h Ω, a Ω⟫_ℂ - ⟪star a Ω, star h Ω⟫_ℂ).re ≤ δ := by
  sorry

/--
The resolvent vector `ψ = (z - Δ)⁻¹ a' Ω` lies in `𝒦_c`.

Blueprint: lmm:takesaki-resolvent-in-ball-closure
-/
theorem takesaki_resolvent_mem_ball_closure {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) {a' : H →L[ℂ] H}
    (ha' : a' ∈ Set.centralizer M) :
    (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) (a' Ω) ∈
      closure ((fun a : H →L[ℂ] H => a Ω) ''
        {a ∈ M | ‖a‖ ≤ ‖a'‖ / Real.sqrt (2 * (‖z‖ - z.re))}) := by
  sorry

/--
Takesaki's lemma: for `z ∉ [0, ∞)` and `a' ∈ M'`, `(z - Δ)⁻¹ a' Ω = a Ω` for a unique `a ∈ M`,
and `‖a‖ ≤ ‖a'‖ / √(2(|z| - Re z))`.

Implementation note: uniqueness is among all `ã ∈ M` with `ã Ω = (z - Δ)⁻¹ a' Ω`, as in
`commutantExtension`.

Blueprint: thrm:takesaki-lemma
-/
theorem takesaki_lemma {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) {a' : H →L[ℂ] H}
    (ha' : a' ∈ Set.centralizer M) :
    ∃ a ∈ M, a Ω = (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) (a' Ω) ∧
      ‖a‖ ≤ ‖a'‖ / Real.sqrt (2 * (‖z‖ - z.re)) ∧
      ∀ ã ∈ M, ã Ω = (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) (a' Ω) → ã = a := by
  sorry

end Physicslib4.Modular
