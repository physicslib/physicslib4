/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.Real.Sqrt

/-!
# Weak continuity implies strong continuity for a family of unitaries

This file proves the analytic core needed to upgrade *weak* continuity of an
implementing unitary representation to *strong* continuity. It is the
spacetime-agnostic ingredient behind the strong continuity of the GNS unitary
`U(L)` attached to an invariant state: weak continuity of the matrix
coefficients on the dense cyclic vectors yields strong continuity of `L ↦ U(L)ψ`
for every vector `ψ`.

## Main result

* `Physicslib4.strongContinuous_of_weak`: for a family `U : X → (H ≃ₗᵢ[ℂ] H)` of
  unitaries indexed by a topological space `X`, if the matrix coefficients
  `x ↦ ⟪ξ, U x η⟫` are continuous for `ξ, η` ranging over a dense set `D`, then
  `x ↦ U x ψ` is continuous for every `ψ : H`.

The proof has three steps, each using only Hilbert-space analysis (no Stone
theorem, no unbounded operators):

1. Extend weak continuity to an arbitrary first slot (second slot still in `D`)
   by uniform approximation, using `‖U x η‖ = ‖η‖`.
2. For `η ∈ D`, the polarization identity
   `‖U x η - U x₀ η‖² = 2‖η‖² - 2 Re⟪U x₀ η, U x η⟫` plus step 1 give continuity
   of `x ↦ U x η`.
3. For arbitrary `ψ`, approximate by `η ∈ D`; since each `U x` is an isometry,
   `‖U x ψ - U x η‖ = ‖ψ - η‖` is constant in `x`, so uniform approximation by
   the (continuous) maps `x ↦ U x η` finishes the proof.
-/

namespace Physicslib4

open scoped InnerProductSpace
open Filter Topology

variable {X : Type*} [TopologicalSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Weak continuity implies strong continuity** for a family of unitaries.

If `U : X → (H ≃ₗᵢ[ℂ] H)` has continuous matrix coefficients
`x ↦ ⟪ξ, U x η⟫` for all `ξ, η` in a dense set `D ⊆ H`, then `x ↦ U x ψ` is
continuous for every `ψ : H`. -/
theorem strongContinuous_of_weak
    (U : X → (H ≃ₗᵢ[ℂ] H)) {D : Set H} (hD : Dense D)
    (hweak : ∀ ξ ∈ D, ∀ η ∈ D, Continuous fun x => ⟪ξ, U x η⟫_ℂ) :
    ∀ ψ : H, Continuous fun x => U x ψ := by
  -- Step 1: weak continuity for an arbitrary first slot, second slot in `D`.
  have weakLeft : ∀ (ξ : H) {η : H}, η ∈ D → Continuous fun x => ⟪ξ, U x η⟫_ℂ := by
    intro ξ η hη
    apply continuous_of_uniform_approx_of_continuous
    intro u hu
    obtain ⟨ε, hε, hball⟩ := Metric.mem_uniformity_dist.mp hu
    obtain ⟨ξ', hξ'D, hξ'⟩ :=
      Metric.mem_closure_iff.mp (hD ξ) (ε / (‖η‖ + 1)) (by positivity)
    refine ⟨fun x => ⟪ξ', U x η⟫_ℂ, hweak ξ' hξ'D η hη, fun x => hball ?_⟩
    rw [dist_eq_norm, ← inner_sub_left]
    calc ‖⟪ξ - ξ', U x η⟫_ℂ‖
        ≤ ‖ξ - ξ'‖ * ‖U x η‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
      _ = ‖ξ - ξ'‖ * ‖η‖ := by rw [LinearIsometryEquiv.norm_map]
      _ < ε := by
          have hpos : (0 : ℝ) < ‖η‖ + 1 := by positivity
          have hd : ‖ξ - ξ'‖ < ε / (‖η‖ + 1) := by rw [← dist_eq_norm]; exact hξ'
          have key : ‖ξ - ξ'‖ * (‖η‖ + 1) < ε := (lt_div_iff₀ hpos).mp hd
          have expand : ‖ξ - ξ'‖ * (‖η‖ + 1) = ‖ξ - ξ'‖ * ‖η‖ + ‖ξ - ξ'‖ := by ring
          rw [expand] at key
          linarith [norm_nonneg (ξ - ξ')]
  -- Step 2: continuity of `x ↦ U x η` for `η ∈ D`.
  have hcontD : ∀ η ∈ D, Continuous fun x => U x η := by
    intro η hη
    rw [continuous_iff_continuousAt]
    intro x₀
    have hre : Continuous fun x => RCLike.re (⟪U x₀ η, U x η⟫_ℂ) :=
      RCLike.continuous_re.comp (weakLeft (U x₀ η) hη)
    have hval : RCLike.re (⟪U x₀ η, U x₀ η⟫_ℂ) = ‖η‖ ^ 2 := by
      rw [inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]
    have hlim : Tendsto (fun x => RCLike.re (⟪U x₀ η, U x η⟫_ℂ)) (𝓝 x₀) (𝓝 (‖η‖ ^ 2)) := by
      have h := hre.tendsto x₀
      rwa [hval] at h
    have hg : Tendsto (fun x => 2 * ‖η‖ ^ 2 - 2 * RCLike.re (⟪U x₀ η, U x η⟫_ℂ))
        (𝓝 x₀) (𝓝 0) := by
      have h : Tendsto (fun x => 2 * ‖η‖ ^ 2 - 2 * RCLike.re (⟪U x₀ η, U x η⟫_ℂ))
          (𝓝 x₀) (𝓝 (2 * ‖η‖ ^ 2 - 2 * ‖η‖ ^ 2)) :=
        tendsto_const_nhds.sub (hlim.const_mul 2)
      simpa using h
    have hnormeq : ∀ x, ‖U x η - U x₀ η‖
        = Real.sqrt (2 * ‖η‖ ^ 2 - 2 * RCLike.re (⟪U x₀ η, U x η⟫_ℂ)) := by
      intro x
      rw [← Real.sqrt_sq (norm_nonneg (U x η - U x₀ η)), norm_sub_sq (𝕜 := ℂ)]
      congr 1
      rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, inner_re_symm (𝕜 := ℂ)]
      ring
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hsqrt : Tendsto
        (fun x => Real.sqrt (2 * ‖η‖ ^ 2 - 2 * RCLike.re (⟪U x₀ η, U x η⟫_ℂ)))
        (𝓝 x₀) (𝓝 0) := by
      have h0 := (Real.continuous_sqrt.tendsto 0).comp hg
      rw [Real.sqrt_zero] at h0
      exact h0
    exact hsqrt.congr fun x => (hnormeq x).symm
  -- Step 3: continuity of `x ↦ U x ψ` for arbitrary `ψ`.
  intro ψ
  apply continuous_of_uniform_approx_of_continuous
  intro u hu
  obtain ⟨ε, hε, hball⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨η, hηD, hη⟩ := Metric.mem_closure_iff.mp (hD ψ) ε hε
  refine ⟨fun x => U x η, hcontD η hηD, fun x => hball ?_⟩
  rw [dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
  exact hη

end Physicslib4
