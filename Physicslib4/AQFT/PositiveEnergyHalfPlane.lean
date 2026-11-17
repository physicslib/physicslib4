/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.PositiveEnergy
import Physicslib4.AQFT.KMS

/-!
# The positive-energy group on the upper half-plane

Let `V` be a one-parameter unitary group with positive energy, and `P` its positive self-adjoint
generator, so `V(t) = e^{itP}` (`isPositiveEnergy_iff_exists_exp`, `stone`). With
`ε_w(λ) = 1_{[0,∞)}(λ) e^{iwλ}` and `δ_w(λ) = 1_{[0,∞)}(λ) iλ e^{iwλ}`, the operators
`Ṽ(w) = ε_w(P)`, `Im w ≥ 0`, are contractions extending `V`, holomorphic in the operator norm on
`Im w > 0` with derivative `δ_w(P)`, and strongly continuous on `Im w ≥ 0`. Composed with the
dilation `z ↦ τ e^{2πz}`, which maps the strip `0 ≤ Im z ≤ 1/2` into the closed upper half-plane,
they give the operator factor of the Borchers function.

## Notation

* `ε[w]` and `δ[w]` are the functions `ε_w` and `δ_w`.
* Inside statements about `V` with `hV : IsPositiveEnergy V`: `Psa` is the proof that the
  generator `P = generator V` is self-adjoint (from `stone`), `μP` is its spectral measure, and
  `Ṽ[w]` is the bounded integral `∫ ε_w dμ^P`. These notations refer to the binder `hV` of the
  declaration in which they occur. The integral is `0` when `ε_w` is unbounded, so `Ṽ[w] = 0` for
  `Im w < 0`; every statement concerns `Im w ≥ 0` only.
-/

namespace Physicslib4
namespace AQFT

open scoped InnerProductSpace
open Spectral.Stone

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The function `ε_w(λ) = 1_{[0,∞)}(λ) e^{iwλ}`. -/
local notation "ε[" w "]" =>
  Set.indicator (Set.Ici (0 : ℝ)) fun x : ℝ => Complex.exp (Complex.I * (w : ℂ) * (x : ℂ))

/-- The function `δ_w(λ) = 1_{[0,∞)}(λ) iλ e^{iwλ}`. -/
local notation "δ[" w "]" =>
  Set.indicator (Set.Ici (0 : ℝ))
    fun x : ℝ => Complex.I * (x : ℂ) * Complex.exp (Complex.I * (w : ℂ) * (x : ℂ))

set_option hygiene false in
/-- Self-adjointness of the generator `P` of `V`, for the binder `hV : IsPositiveEnergy V`. -/
local notation "Psa" => (stone hV.isOneParameterUnitaryGroup hV.isStronglyContinuous).fst

set_option hygiene false in
/-- The spectral measure `μ^P` of the generator `P` of `V`, for the binder `hV`. -/
local notation "μP" => Spectral.Unbounded.spectralMeasure
  (stone hV.isOneParameterUnitaryGroup hV.isStronglyContinuous).fst

set_option hygiene false in
/-- The extension `Ṽ(w) = ε_w(P)` of `V` to the upper half-plane, for the binder `hV`. -/
local notation "Ṽ[" w "]" => (Spectral.Unbounded.spectralMeasure
  (stone hV.isOneParameterUnitaryGroup hV.isStronglyContinuous).fst).integral ε[w]

/-- For `a > 0` and `λ ≥ 0`, `λ e^{-aλ} ≤ 1/(ae)` and `λ² e^{-aλ} ≤ 4/(ae)²`.

Blueprint: lmm:poly-exp-decay -/
theorem mul_exp_neg_le {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    x * Real.exp (-(a * x)) ≤ 1 / (a * Real.exp 1) ∧
      x ^ 2 * Real.exp (-(a * x)) ≤ 4 / (a * Real.exp 1) ^ 2 := by
  sorry

/-- `ε_w` and `δ_w` are measurable; `|ε_w| ≤ 1` if `Im w ≥ 0`; and `|δ_w| ≤ 1/(ce)` if
`c = Im w > 0`.

Blueprint: lmm:half-plane-exp-bounds -/
theorem halfPlaneExp_bounds (w : ℂ) :
    Measurable ε[w] ∧ Measurable δ[w] ∧ (0 ≤ w.im → ∀ x : ℝ, ‖ε[w] x‖ ≤ 1) ∧
      (0 < w.im → ∀ x : ℝ, ‖δ[w] x‖ ≤ 1 / (w.im * Real.exp 1)) := by
  sorry

/-- The Taylor estimate: for `c = Im w > 0` and `|h| ≤ c/2`,
`|ε_{w+h}(λ) - ε_w(λ) - h δ_w(λ)| ≤ 16|h|²/(ce)²` for every `λ`.

Blueprint: lmm:half-plane-exp-taylor -/
theorem halfPlaneExp_taylor {w h : ℂ} (hw : 0 < w.im) (hh : ‖h‖ ≤ w.im / 2) (x : ℝ) :
    ‖ε[w + h] x - ε[w] x - h * δ[w] x‖ ≤ 16 / (w.im * Real.exp 1) ^ 2 * ‖h‖ ^ 2 := by
  sorry

/-- For `Im w ≥ 0`, `Ṽ(w) = ε_w(P)` is a bounded operator with `‖Ṽ(w)‖ ≤ 1`, equal to the
bounded integral `∫ ε_w dμ^P`: the functional calculus `ε_w(P)` is defined on all of `H` and
agrees there with the integral. For real `t`, `Ṽ(t) = V(t)`.

Blueprint: lmm:positive-energy-extension-operators -/
theorem positiveEnergyExtension_operators {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsPositiveEnergy V) :
    (∀ w : ℂ, 0 ≤ w.im →
      ‖Ṽ[w]‖ ≤ 1 ∧
        ∀ ψ : H, ∃ h : ψ ∈ (Spectral.Unbounded.functionalCalculus Psa ε[w]).domain,
          Spectral.Unbounded.functionalCalculus Psa ε[w] ⟨ψ, h⟩ = Ṽ[w] ψ) ∧
      ∀ t : ℝ, Ṽ[(t : ℂ)] = (V t).toLinearIsometry.toContinuousLinearMap := by
  sorry

/-- On the open upper half-plane, `w ↦ Ṽ(w)` is complex differentiable in the operator norm,
with derivative `δ_w(P)`.

Blueprint: lmm:positive-energy-extension-holomorphic -/
theorem hasDerivAt_positiveEnergyExtension {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsPositiveEnergy V)
    {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (fun w' : ℂ => Ṽ[w']) ((μP).integral δ[w]) w := by
  sorry

/-- For every `ψ`, `w ↦ Ṽ(w)ψ` is continuous on the closed upper half-plane.

Blueprint: lmm:positive-energy-extension-strongly-continuous -/
theorem continuousOn_positiveEnergyExtension_apply {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : IsPositiveEnergy V) (ψ : H) :
    ContinuousOn (fun w : ℂ => Ṽ[w] ψ) {w : ℂ | 0 ≤ w.im} := by
  sorry

/-- For `τ ≥ 0`, the dilation `z ↦ τ e^{2πz}` maps the strip `0 ≤ Im z ≤ 1/2` into the closed
upper half-plane, and the open strip into the open upper half-plane if `τ > 0`; on the upper
edge, `τ e^{2π(t + i/2)} = -τ e^{2πt}`.

Blueprint: lmm:dilation-strip-half-plane -/
theorem dilation_strip_halfPlane {τ : ℝ} (hτ : 0 ≤ τ) :
    (∀ z ∈ kmsStrip (1 / 2), 0 ≤ ((τ : ℂ) * Complex.exp (2 * Real.pi * z)).im) ∧
      (0 < τ → ∀ z ∈ kmsStripInterior (1 / 2),
        0 < ((τ : ℂ) * Complex.exp (2 * Real.pi * z)).im) ∧
      ∀ t : ℝ, (τ : ℂ) * Complex.exp (2 * Real.pi * ((t : ℂ) + Complex.I / 2)) =
        -((τ * Real.exp (2 * Real.pi * t) : ℝ) : ℂ) := by
  sorry

/-- For `τ ≥ 0`, `z ↦ Ṽ(τ e^{2πz})` is complex differentiable in the operator norm on the open
strip `0 < Im z < 1/2`, and `z ↦ Ṽ(τ e^{2πz})ψ` is continuous on the closed strip for every `ψ`.

Blueprint: lmm:dilated-extension-analytic -/
theorem dilatedPositiveEnergyExtension_analytic {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : IsPositiveEnergy V) {τ : ℝ} (hτ : 0 ≤ τ) :
    (∀ z ∈ kmsStripInterior (1 / 2),
      DifferentiableAt ℂ (fun z' : ℂ => Ṽ[(τ : ℂ) * Complex.exp (2 * Real.pi * z')]) z) ∧
      ∀ ψ : H, ContinuousOn (fun z : ℂ => Ṽ[(τ : ℂ) * Complex.exp (2 * Real.pi * z)] ψ)
        (kmsStrip (1 / 2)) := by
  sorry

end AQFT
end Physicslib4
