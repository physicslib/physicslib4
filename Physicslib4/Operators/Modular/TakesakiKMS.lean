/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Operators.Modular.VanDaele
import Physicslib4.AQFT.KMS
import Physicslib4.GNS.VectorState

/-!
# Takesaki's KMS theorem: the analytic ingredients

For a von Neumann algebra `M` with a cyclic and separating vector `Ω`, this file states the
ingredients of Takesaki's theorem that the vector state of `Ω` is a KMS state at inverse
temperature `1` for the reversed modular flow `t ↦ σ_{-t}`, `σ_t(x) = Δ^{it} x Δ^{-it}`:

* general facts on eigenvectors of a self-adjoint operator and its spectral measure;
* `ΔΩ = Ω`, `Δ^{it}Ω = Ω`, `J Δ^{it} = Δ^{it} J` and `Δ^{1/2} x Ω = J x* Ω` for `x ∈ M`;
* the KMS function `G_{ξ,η}` on the strip `0 ≤ Im z ≤ 1`, its approximants `G^n_{ξ,η}`, and its
  boundary values;
* the modular algebra `modularAlgebra`, a C*-algebra with underlying set `M`, the modular
  automorphisms `modularAutomorphism`, and Takesaki's theorem `isKMSState_modularAutomorphism`.

## Notation

* `K[n]`, `p[z, n]` and `e[t]` are as in `Physicslib4.Operators.Modular.VanDaele`.
* `u[z]` is `u_z(λ) = 1_{(0,1)}(λ) λ^{-iz}` and `v[z]` is `v_z(λ) = 1_{[1,∞)}(λ) λ^{-iz-1}`, with
  the principal power.
* `g[t]` is `g_t(λ) = 1_{(0,1)}(λ) e_{-t}(λ)`.
* The function `s(λ) = √(max(λ, 0))` is written `Real.sqrt`.
* Inside statements about `M`, `Ω`, `C`: `μΔ` is the spectral measure of `Δ`, `Δs` is
  `Δ^{1/2}` (`modularOperatorSqrt`), `U[t]` is `Δ^{it}` as a bounded operator, and
  `G[ξ, η, hξ, hη]`, `Gn[ξ, η, hξ, hη, n]` are the functions `G_{ξ,η}` and `G^n_{ξ,η}` of the
  blueprint, `G_{ξ,η}` extended by `0` off the closed strip `kmsStrip 1`. These notations
  refer to the binders `hM hΩ C hC` of the declaration in which they occur.
-/

namespace Physicslib4.Modular

open scoped InnerProductSpace ComplexConjugate
open Physicslib4.Spectral.Unbounded Physicslib4.Spectral.Stone
open Filter Topology MeasureTheory
open Physicslib4.AQFT (kmsStrip kmsStripInterior)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The interval `K_n = [1/n, n]`. -/
local notation "K[" n "]" => Set.Icc (1 / (n : ℝ)) (n : ℝ)

/-- The function `p_{z,n}(λ) = 1_{K_n}(λ) λ^z`. -/
local notation "p[" z ", " n "]" =>
  Set.indicator (Set.Icc (1 / (n : ℝ)) (n : ℝ)) fun x : ℝ => (x : ℂ) ^ (z : ℂ)

/-- The function `e_t(λ) = e^{it log λ}`. -/
local notation "e[" t "]" => fun x : ℝ => Complex.exp (Complex.I * (t : ℂ) * (Real.log x : ℂ))

/-- The function `u_z(λ) = 1_{(0,1)}(λ) λ^{-iz}`. -/
local notation "u[" z "]" =>
  Set.indicator (Set.Ioo (0 : ℝ) 1) fun x : ℝ => (x : ℂ) ^ (-Complex.I * (z : ℂ))

/-- The function `v_z(λ) = 1_{[1,∞)}(λ) λ^{-iz-1}`. -/
local notation "v[" z "]" =>
  Set.indicator (Set.Ici (1 : ℝ)) fun x : ℝ => (x : ℂ) ^ (-Complex.I * (z : ℂ) - 1)

/-- The function `g_t(λ) = 1_{(0,1)}(λ) e_{-t}(λ)`. -/
local notation "g[" t "]" =>
  Set.indicator (Set.Ioo (0 : ℝ) 1)
    fun x : ℝ => Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (Real.log x : ℂ))

set_option hygiene false in
/-- The spectral measure `μ` of `Δ`, for the binders `hM hΩ C hC` in scope. -/
local notation "μΔ" => spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)

set_option hygiene false in
/-- `Δ^{1/2}`, for the binders `hM hΩ C hC` in scope. -/
local notation "Δs" => modularOperatorSqrt hM hΩ C hC

set_option hygiene false in
/-- `Δ^{it}` as a bounded operator, for the binders `hM hΩ C hC` in scope. -/
local notation "U[" t "]" =>
  (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap

set_option hygiene false in
/-- The KMS function `G_{ξ,η}(z) = ⟪ξ, u_z(Δ)η⟫ + ⟪Δ^{1/2}ξ, v_z(Δ)Δ^{1/2}η⟫` on the closed strip
`0 ≤ Im z ≤ 1`, and `0` off it. -/
local notation "G[" ξ ", " η ", " hξ ", " hη "]" =>
  Set.indicator (kmsStrip 1) fun w : ℂ =>
    ⟪(ξ : H), (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral u[w] η⟫_ℂ +
      ⟪modularOperatorSqrt hM hΩ C hC ⟨ξ, hξ⟩,
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral v[w]
          (modularOperatorSqrt hM hΩ C hC ⟨η, hη⟩)⟫_ℂ

set_option hygiene false in
/-- The approximant
`G^n_{ξ,η}(z) = ⟪1_{(0,1)}(Δ)ξ, p_{-iz,n}(Δ)η⟫ + ⟪1_{[1,∞)}(Δ)Δ^{1/2}ξ, p_{-iz-1,n}(Δ)Δ^{1/2}η⟫`. -/
local notation "Gn[" ξ ", " η ", " hξ ", " hη ", " n "]" =>
  fun w : ℂ =>
    ⟪spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) (Set.Ioo (0 : ℝ) 1) ξ,
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          p[-Complex.I * w, n] η⟫_ℂ +
      ⟪spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) (Set.Ici (1 : ℝ))
          (modularOperatorSqrt hM hΩ C hC ⟨ξ, hξ⟩),
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          p[-Complex.I * w - 1, n] (modularOperatorSqrt hM hΩ C hC ⟨η, hη⟩)⟫_ℂ

/-! ### Eigenvectors of a self-adjoint operator -/

/-- For `ψ ∈ Dom A`, the functions `1`, `λ` and `λ²` are `μ^A_ψ`-integrable, `μ^A_ψ(ℝ) = ‖ψ‖²`,
`⟪ψ, Aψ⟫` is real, `∫ λ dμ^A_ψ = Re ⟪ψ, Aψ⟫` and `∫ λ² dμ^A_ψ = ‖Aψ‖²`.
Blueprint: lmm:spectral-moments -/
theorem spectralMeasure_moments {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {ψ : H}
    (hψ : ψ ∈ A.domain) :
    Integrable (fun _ : ℝ => (1 : ℝ)) ((spectralMeasure hA).assoc ψ) ∧
      Integrable (fun x : ℝ => x) ((spectralMeasure hA).assoc ψ) ∧
      Integrable (fun x : ℝ => x ^ 2) ((spectralMeasure hA).assoc ψ) ∧
      (spectralMeasure hA).assoc ψ Set.univ = ENNReal.ofReal (‖ψ‖ ^ 2) ∧
      (⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ).im = 0 ∧
      ∫ x, x ∂((spectralMeasure hA).assoc ψ) = (⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ).re ∧
      ∫ x, x ^ 2 ∂((spectralMeasure hA).assoc ψ) = ‖A ⟨ψ, hψ⟩‖ ^ 2 := by
  sorry

/-- For `c ∈ ℝ` and `ψ ∈ Dom A`, `λ ↦ (λ - c)²` is `μ^A_ψ`-integrable and
`∫ (λ - c)² dμ^A_ψ = ‖Aψ - cψ‖²`.
Blueprint: lmm:spectral-eigenvector-variance -/
theorem spectralMeasure_variance {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (c : ℝ) {ψ : H}
    (hψ : ψ ∈ A.domain) :
    Integrable (fun x : ℝ => (x - c) ^ 2) ((spectralMeasure hA).assoc ψ) ∧
      ∫ x, (x - c) ^ 2 ∂((spectralMeasure hA).assoc ψ) = ‖A ⟨ψ, hψ⟩ - (c : ℂ) • ψ‖ ^ 2 := by
  sorry

/-- For a projection-valued measure `μ` and measurable `E`, `μ_ψ(E) = ‖μ(E)ψ‖²`; hence
`μ_ψ(E) = 0` gives `μ(E)ψ = 0` and `μ(Eᶜ)ψ = ψ`.
Blueprint: lmm:pvm-null-set-vector -/
theorem projectionValuedMeasure_apply_of_assoc_eq_zero {X : Type*} [MeasurableSpace X]
    (μ : Spectral.ProjectionValuedMeasure X H) (ψ : H) {E : Set X} (hE : MeasurableSet E) :
    μ.assoc ψ E = ENNReal.ofReal (‖μ E ψ‖ ^ 2) ∧
      (μ.assoc ψ E = 0 → μ E ψ = 0 ∧ μ Eᶜ ψ = ψ) := by
  sorry

/-- If `ψ ∈ Dom A` and `Aψ = cψ` with `c ∈ ℝ`, then `μ^A({c})ψ = ψ`.
Blueprint: lmm:spectral-eigenvector-projection -/
theorem spectralMeasure_singleton_apply_of_eigenvector {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {c : ℝ} {ψ : H} (hψ : ψ ∈ A.domain) (hAψ : A ⟨ψ, hψ⟩ = (c : ℂ) • ψ) :
    spectralMeasure hA {c} ψ = ψ := by
  sorry

/-- If `ψ ∈ Dom A`, `Aψ = cψ` with `c ∈ ℝ`, and `f` is bounded and measurable, then
`f(A)ψ = f(c)ψ`, with `f(A)` the bounded integral `∫ f dμ^A` (equal to the functional calculus
by `functionalCalculus_of_bddMeasurable`).
Blueprint: lmm:spectral-eigenvector-bounded-fc -/
theorem spectralMeasure_integral_apply_of_eigenvector {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {c : ℝ} {ψ : H} (hψ : ψ ∈ A.domain) (hAψ : A ⟨ψ, hψ⟩ = (c : ℂ) • ψ) {f : ℝ → ℂ}
    (hf : f ∈ Spectral.BddMeasurable ℝ) :
    (spectralMeasure hA).integral f ψ = f c • ψ := by
  sorry

/-! ### The invariance of `Ω` -/

/-- `Ω ∈ Dom Δ` and `ΔΩ = Ω`.
Blueprint: lmm:modular-operator-fixes-omega -/
theorem modularOperator_apply_self {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    ∃ h : Ω ∈ (modularOperator M Ω C).domain, modularOperator M Ω C ⟨Ω, h⟩ = Ω := by
  sorry

/-- `Δ^{it}Ω = Ω` for every `t ∈ ℝ`.
Blueprint: lmm:modular-unitary-group-fixes-omega -/
theorem modularUnitaryGroup_apply_self {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (t : ℝ) :
    modularUnitaryGroup hM hΩ C hC t Ω = Ω := by
  sorry

/-- `J Δ^{it} ψ = Δ^{it} J ψ` for every `t ∈ ℝ` and `ψ ∈ H`.
Blueprint: lmm:modular-conjugation-commutes-unitary-group -/
theorem modularConjugation_modularUnitaryGroup {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (t : ℝ) (ψ : H) :
    modularConjugation hM hΩ C hC (modularUnitaryGroup hM hΩ C hC t ψ) =
      modularUnitaryGroup hM hΩ C hC t (modularConjugation hM hΩ C hC ψ) := by
  sorry

/-- For `x ∈ M`, `xΩ ∈ Dom Δ^{1/2}` and `Δ^{1/2} xΩ = J x* Ω`.
Blueprint: lmm:modular-sqrt-on-algebra -/
theorem modularOperatorSqrt_apply_of_mem {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {x : H →L[ℂ] H} (hx : x ∈ M) :
    ∃ h : x Ω ∈ (Δs).domain, Δs ⟨x Ω, h⟩ = modularConjugation hM hΩ C hC (star x Ω) := by
  sorry

/-! ### The scalar functions `u_z`, `v_z` and `g_t` -/

/-- `u_z` and `v_z` are measurable, and `|u_z| ≤ 1`, `|v_z| ≤ 1` for `z` in the closed strip
`0 ≤ Im z ≤ 1`.
Blueprint: lmm:takesaki-functions-bounded -/
theorem takesaki_functions_bounded (z : ℂ) :
    Measurable u[z] ∧ Measurable v[z] ∧
      (z ∈ kmsStrip 1 → ∀ x : ℝ, ‖u[z] x‖ ≤ 1 ∧ ‖v[z] x‖ ≤ 1) := by
  refine ⟨(Complex.measurable_ofReal.pow_const _).indicator measurableSet_Ioo,
    (Complex.measurable_ofReal.pow_const _).indicator measurableSet_Ici, fun hz x => ?_⟩
  obtain ⟨h0, h1⟩ : 0 ≤ z.im ∧ z.im ≤ 1 := by simpa [kmsStrip] using hz
  constructor
  · by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
      exact Real.rpow_le_one hx.1.le hx.2.le (by simpa using h0)
    · simp [hx]
  · by_cases hx : x ∈ Set.Ici (1 : ℝ)
    · rw [Set.indicator_of_mem hx, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hx.out])]
      exact Real.rpow_le_one_of_one_le_of_nonpos hx (by simp; linarith)
    · simp [hx]

/-- For `λ > 0`: `s(λ)² = λ`, `λ · λ^w = λ^{w+1}`, `|λ^w| = λ^{Re w}` and `e_{-t}(λ) = λ^{-it}`.
Blueprint: lmm:takesaki-positive-scalar-identities -/
theorem takesaki_positive_scalar_identities {x : ℝ} (hx : 0 < x) (w : ℂ) (t : ℝ) :
    Real.sqrt x ^ 2 = x ∧ (x : ℂ) * (x : ℂ) ^ w = (x : ℂ) ^ (w + 1) ∧
      ‖(x : ℂ) ^ w‖ = x ^ w.re ∧ e[-t] x = (x : ℂ) ^ (-Complex.I * t) := by
  sorry

/-- `u_z 1_{K_n} = 1_{(0,1)} p_{-iz,n}` and `v_z 1_{K_n} = 1_{[1,∞)} p_{-iz-1,n}` pointwise.
Blueprint: lmm:takesaki-functions-identities -/
theorem takesaki_functions_identities (z : ℂ) (n : ℕ) (x : ℝ) :
    u[z] x * (K[n]).indicator 1 x = (Set.Ioo (0 : ℝ) 1).indicator 1 x * p[-Complex.I * z, n] x ∧
      v[z] x * (K[n]).indicator 1 x =
        (Set.Ici (1 : ℝ)).indicator 1 x * p[-Complex.I * z - 1, n] x := by
  sorry

/-- `u_t + s² v_t = 1_{(0,∞)} e_{-t}` pointwise, for real `t`.
Blueprint: lmm:takesaki-functions-lower-sum -/
theorem takesaki_functions_lower_sum (t x : ℝ) :
    u[(t : ℂ)] x + (Real.sqrt x : ℂ) ^ 2 * v[(t : ℂ)] x = (Set.Ioi (0 : ℝ)).indicator e[-t] x := by
  sorry

/-- `s² g_t = u_{t+i}` and `g_t + v_{t+i} = 1_{(0,∞)} e_{-t}` pointwise, for real `t`.
Blueprint: lmm:takesaki-functions-upper-identities -/
theorem takesaki_functions_upper_identities (t x : ℝ) :
    (Real.sqrt x : ℂ) ^ 2 * g[t] x = u[(t : ℂ) + Complex.I] x ∧
      g[t] x + v[(t : ℂ) + Complex.I] x = (Set.Ioi (0 : ℝ)).indicator e[-t] x := by
  sorry

/-- `g_t` is measurable, and `|g_t|`, `|s v_t|`, `|s² v_t|`, `|s g_t|`, `|s² g_t|` are at most `1`.
Blueprint: lmm:takesaki-functions-aux-bounds -/
theorem takesaki_functions_aux_bounds (t : ℝ) :
    Measurable g[t] ∧ ∀ x : ℝ, ‖g[t] x‖ ≤ 1 ∧ ‖(Real.sqrt x : ℂ) * v[(t : ℂ)] x‖ ≤ 1 ∧
      ‖(Real.sqrt x : ℂ) ^ 2 * v[(t : ℂ)] x‖ ≤ 1 ∧ ‖(Real.sqrt x : ℂ) * g[t] x‖ ≤ 1 ∧
      ‖(Real.sqrt x : ℂ) ^ 2 * g[t] x‖ ≤ 1 := by
  sorry

/-! ### The KMS function and its approximants -/

/-- For measurable `f` with `f`, `s f` and `s² f` bounded, and `ξ, η ∈ Dom Δ^{1/2}`,
`⟪Δ^{1/2}ξ, f(Δ) Δ^{1/2}η⟫ = ⟪ξ, (s² f)(Δ) η⟫`.
Blueprint: lmm:modular-sqrt-transfer -/
theorem inner_modularOperatorSqrt_integral {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {f : ℝ → ℂ} (hf : f ∈ Spectral.BddMeasurable ℝ)
    (hsf : (fun x => (Real.sqrt x : ℂ) * f x) ∈ Spectral.BddMeasurable ℝ)
    (hs2f : (fun x => (Real.sqrt x : ℂ) ^ 2 * f x) ∈ Spectral.BddMeasurable ℝ)
    {ξ η : H} (hξ : ξ ∈ (Δs).domain) (hη : η ∈ (Δs).domain) :
    ⟪Δs ⟨ξ, hξ⟩, (μΔ).integral f (Δs ⟨η, hη⟩)⟫_ℂ =
      ⟪ξ, (μΔ).integral (fun x => (Real.sqrt x : ℂ) ^ 2 * f x) η⟫_ℂ := by
  sorry

/-- For `ξ, η ∈ Dom Δ^{1/2}` and `n ≥ 1`, `G^n_{ξ,η}` is entire, hence continuous.
Blueprint: lmm:takesaki-approximants-entire -/
theorem differentiable_takesakiApproximant {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H} (hξ : ξ ∈ (Δs).domain) (hη : η ∈ (Δs).domain)
    {n : ℕ} (hn : 1 ≤ n) :
    Differentiable ℂ Gn[ξ, η, hξ, hη, n] ∧ Continuous Gn[ξ, η, hξ, hη, n] := by
  sorry

/-- On the closed strip, `G^n_{ξ,η}(z) = ⟪ξ, u_z(Δ) E_n η⟫ + ⟪Δ^{1/2}ξ, v_z(Δ) E_n Δ^{1/2}η⟫`.
Blueprint: lmm:takesaki-approximants-strip -/
theorem takesakiApproximant_eq_of_mem_strip {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H} (hξ : ξ ∈ (Δs).domain) (hη : η ∈ (Δs).domain)
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ kmsStrip 1) :
    Gn[ξ, η, hξ, hη, n] z =
      ⟪ξ, (μΔ).integral u[z] (μΔ K[n] η)⟫_ℂ +
        ⟪Δs ⟨ξ, hξ⟩, (μΔ).integral v[z] (μΔ K[n] (Δs ⟨η, hη⟩))⟫_ℂ := by
  sorry

/-- On the closed strip,
`|G_{ξ,η}(z) - G^n_{ξ,η}(z)| ≤ ‖ξ‖ ‖η - E_n η‖ + ‖Δ^{1/2}ξ‖ ‖Δ^{1/2}η - E_n Δ^{1/2}η‖` for
`n ≥ 1`, so `G^n_{ξ,η} → G_{ξ,η}` uniformly on the strip.
Blueprint: lmm:takesaki-approximants-uniform -/
theorem tendstoUniformlyOn_takesakiApproximant {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H} (hξ : ξ ∈ (Δs).domain) (hη : η ∈ (Δs).domain) :
    (∀ n : ℕ, 1 ≤ n → ∀ z ∈ kmsStrip 1,
      ‖G[ξ, η, hξ, hη] z - Gn[ξ, η, hξ, hη, n] z‖ ≤
        ‖ξ‖ * ‖η - μΔ K[n] η‖ +
          ‖Δs ⟨ξ, hξ⟩‖ * ‖Δs ⟨η, hη⟩ - μΔ K[n] (Δs ⟨η, hη⟩)‖) ∧
      TendstoUniformlyOn (fun n : ℕ => Gn[ξ, η, hξ, hη, n]) G[ξ, η, hξ, hη] atTop
        (kmsStrip 1) := by
  sorry

/-- `G_{ξ,η}` is continuous on the closed strip, complex differentiable on the open strip, and
bounded there by `‖ξ‖ ‖η‖ + ‖Δ^{1/2}ξ‖ ‖Δ^{1/2}η‖`.
Blueprint: lmm:takesaki-function-analytic -/
theorem takesakiFunction_analytic {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H} (hξ : ξ ∈ (Δs).domain) (hη : η ∈ (Δs).domain) :
    ContinuousOn G[ξ, η, hξ, hη] (kmsStrip 1) ∧
      DifferentiableOn ℂ G[ξ, η, hξ, hη] (kmsStripInterior 1) ∧
      ∀ z ∈ kmsStrip 1, ‖G[ξ, η, hξ, hη] z‖ ≤ ‖ξ‖ * ‖η‖ + ‖Δs ⟨ξ, hξ⟩‖ * ‖Δs ⟨η, hη⟩‖ := by
  sorry

/-- The lower boundary value: `G_{ξ,η}(t) = ⟪ξ, Δ^{-it}η⟫` for real `t`.
Blueprint: lmm:takesaki-function-lower-boundary -/
theorem takesakiFunction_lower_boundary {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H} (hξ : ξ ∈ (Δs).domain) (hη : η ∈ (Δs).domain) (t : ℝ) :
    G[ξ, η, hξ, hη] (t : ℂ) = ⟪ξ, modularUnitaryGroup hM hΩ C hC (-t) η⟫_ℂ := by
  sorry

/-- The upper boundary value: `G_{ξ,η}(t + i) = ⟪Δ^{1/2}ξ, Δ^{-it} Δ^{1/2}η⟫` for real `t`.
Blueprint: lmm:takesaki-function-upper-boundary -/
theorem takesakiFunction_upper_boundary {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H} (hξ : ξ ∈ (Δs).domain) (hη : η ∈ (Δs).domain) (t : ℝ) :
    G[ξ, η, hξ, hη] ((t : ℂ) + Complex.I) =
      ⟪Δs ⟨ξ, hξ⟩, modularUnitaryGroup hM hΩ C hC (-t) (Δs ⟨η, hη⟩)⟫_ℂ := by
  sorry

/-! ### The boundary values as correlations -/

/-- `⟪a*Ω, Δ^{-it} bΩ⟫ = ⟪Ω, a Δ^{-it} b Δ^{it} Ω⟫` for real `t`. The blueprint takes
`a, b ∈ M`; the identity holds for all bounded `a`, `b`.
Blueprint: lmm:takesaki-lower-boundary-state -/
theorem inner_modularUnitaryGroup_lower_boundary {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (a b : H →L[ℂ] H) (t : ℝ) :
    ⟪star a Ω, modularUnitaryGroup hM hΩ C hC (-t) (b Ω)⟫_ℂ =
      ⟪Ω, a (modularUnitaryGroup hM hΩ C hC (-t) (b (modularUnitaryGroup hM hΩ C hC t Ω)))⟫_ℂ := by
  sorry

/-- For `a, b ∈ M` and real `t`,
`⟪Δ^{1/2} a*Ω, Δ^{-it} Δ^{1/2} bΩ⟫ = ⟪Ω, Δ^{-it} b Δ^{it} a Ω⟫`. The domain memberships
`a*Ω, bΩ ∈ Dom Δ^{1/2}` hold by `modularOperatorSqrt_apply_of_mem`.
Blueprint: lmm:takesaki-upper-boundary-state -/
theorem inner_modularUnitaryGroup_upper_boundary {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {a b : H →L[ℂ] H} (ha : a ∈ M) (hb : b ∈ M) (t : ℝ)
    (ha' : star a Ω ∈ (Δs).domain) (hb' : b Ω ∈ (Δs).domain) :
    ⟪Δs ⟨star a Ω, ha'⟩, modularUnitaryGroup hM hΩ C hC (-t) (Δs ⟨b Ω, hb'⟩)⟫_ℂ =
      ⟪Ω, modularUnitaryGroup hM hΩ C hC (-t) (b (modularUnitaryGroup hM hΩ C hC t (a Ω)))⟫_ℂ := by
  sorry

/-! ### The modular algebra and the modular automorphisms -/

/-- The unital `*`-subalgebra `StarSubalgebra.centralizer ℂ M′` of `B(H)` has underlying set `M`
and is norm-closed; so it is a C*-algebra (`StarSubalgebra.cstarAlgebra`).
Blueprint: lmm:modular-algebra-closed -/
theorem coe_starSubalgebra_centralizer_centralizer {M : Set (H →L[ℂ] H)}
    (hM : IsVonNeumannSet M) :
    ((StarSubalgebra.centralizer ℂ (Set.centralizer M) : StarSubalgebra ℂ (H →L[ℂ] H)) :
        Set (H →L[ℂ] H)) = M ∧
      IsClosed ((StarSubalgebra.centralizer ℂ (Set.centralizer M) :
        StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) := by
  have hstar : ∀ {S : Set (H →L[ℂ] H)}, (∀ a ∈ S, star a ∈ S) → S ∪ star S = S :=
    fun hS => Set.union_eq_left.mpr fun a ha => by simpa using hS _ ha
  have hA : (StarSubalgebra.centralizer ℂ M : Set (H →L[ℂ] H)) = Set.centralizer M := by
    rw [StarSubalgebra.coe_centralizer, hstar hM.1]
  refine ⟨?_, ?_⟩
  · rw [StarSubalgebra.coe_centralizer, ← hA,
      hstar fun a ha => star_mem (s := StarSubalgebra.centralizer ℂ M) ha, hA, hM.2]
  · rw [StarSubalgebra.coe_centralizer]
    exact Set.isClosed_centralizer _

/-- For `t ∈ ℝ`, `σ_t(x) = Δ^{it} x Δ^{-it}` maps `M` into `M`, is linear, unital, multiplicative
and `*`-preserving, with inverse `σ_{-t}`. The blueprint states the algebraic identities for
`x, y ∈ M`; they hold for all bounded `x`, `y`.
Blueprint: lmm:modular-automorphism-well-defined -/
theorem modularAutomorphism_wellDefined {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (t : ℝ) :
    (∀ x ∈ M, U[t] ∘L x ∘L U[-t] ∈ M) ∧
      (∀ (α β : ℂ) (x y : H →L[ℂ] H),
        U[t] ∘L (α • x + β • y) ∘L U[-t] = α • (U[t] ∘L x ∘L U[-t]) + β • (U[t] ∘L y ∘L U[-t])) ∧
      U[t] ∘L ContinuousLinearMap.id ℂ H ∘L U[-t] = ContinuousLinearMap.id ℂ H ∧
      (∀ x y : H →L[ℂ] H,
        U[t] ∘L (x ∘L y) ∘L U[-t] = (U[t] ∘L x ∘L U[-t]) ∘L (U[t] ∘L y ∘L U[-t])) ∧
      (∀ x : H →L[ℂ] H, U[t] ∘L star x ∘L U[-t] = star (U[t] ∘L x ∘L U[-t])) ∧
      ∀ x : H →L[ℂ] H,
        U[-t] ∘L (U[t] ∘L x ∘L U[-t]) ∘L U[t] = x ∧
          U[t] ∘L (U[-t] ∘L x ∘L U[t]) ∘L U[-t] = x := by
  sorry

/-- The *modular algebra* of a von Neumann algebra `M`: the unital `*`-subalgebra
`StarSubalgebra.centralizer ℂ M′` of `B(H)`, whose underlying set is `M`
(`coe_modularAlgebra`) when `M` is a von Neumann algebra. It is norm-closed
(`isClosed_modularAlgebra`), hence a C*-algebra by `StarSubalgebra.cstarAlgebra`.
Blueprint: def:modular-algebra -/
noncomputable def modularAlgebra (M : Set (H →L[ℂ] H)) :
    StarSubalgebra ℂ (H →L[ℂ] H) :=
  StarSubalgebra.centralizer ℂ (Set.centralizer M)

/-- The underlying set of the modular algebra is `M`. -/
theorem coe_modularAlgebra {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M) :
    (modularAlgebra M : Set (H →L[ℂ] H)) = M :=
  (coe_starSubalgebra_centralizer_centralizer hM).1

/-- The modular algebra is norm-closed in `B(H)`, being a centralizer, so
`StarSubalgebra.cstarAlgebra` makes it a C*-algebra. -/
instance isClosed_modularAlgebra (M : Set (H →L[ℂ] H)) :
    IsClosed (modularAlgebra M : Set (H →L[ℂ] H)) := by
  rw [modularAlgebra, StarSubalgebra.coe_centralizer]
  exact Set.isClosed_centralizer _

/-- The modular automorphism `σ_t(x) = Δ^{it} x Δ^{-it}` of the modular algebra, with inverse
`σ_{-t}`.
Blueprint: def:modular-automorphism -/
noncomputable def modularAutomorphism {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (t : ℝ) : modularAlgebra M ≃⋆ₐ[ℂ] modularAlgebra M where
  toFun x := ⟨U[t] ∘L (x : H →L[ℂ] H) ∘L U[-t], by
    rw [← SetLike.mem_coe, coe_modularAlgebra hM]
    exact modularUnitaryGroup_conj_mem_of_mem hM hΩ C hC t
      (by simpa only [← SetLike.mem_coe, coe_modularAlgebra hM] using x.2)⟩
  invFun x := ⟨U[-t] ∘L (x : H →L[ℂ] H) ∘L U[t], by
    rw [← SetLike.mem_coe, coe_modularAlgebra hM]
    have := modularUnitaryGroup_conj_mem_of_mem hM hΩ C hC (-t)
      (by simpa only [← SetLike.mem_coe, coe_modularAlgebra hM] using x.2)
    rwa [neg_neg] at this⟩
  left_inv x := Subtype.ext ((modularAutomorphism_wellDefined hM hΩ C hC t).2.2.2.2.2 x).1
  right_inv x := Subtype.ext ((modularAutomorphism_wellDefined hM hΩ C hC t).2.2.2.2.2 x).2
  map_mul' x y := Subtype.ext ((modularAutomorphism_wellDefined hM hΩ C hC t).2.2.2.1 x y)
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by simp)
  map_star' x := Subtype.ext ((modularAutomorphism_wellDefined hM hΩ C hC t).2.2.2.2.1 x)

/-- `σ_t(x) = Δ^{it} x Δ^{-it}` as bounded operators. -/
@[simp]
theorem coe_modularAutomorphism_apply {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (t : ℝ) (x : modularAlgebra M) :
    ((modularAutomorphism hM hΩ C hC t x : modularAlgebra M) : H →L[ℂ] H) =
      U[t] ∘L (x : H →L[ℂ] H) ∘L U[-t] :=
  rfl

/-- `t ↦ σ_t` is a one-parameter group of `*`-automorphisms of the modular algebra:
`σ_0 = id` and `σ_{s+t} = σ_s ∘ σ_t`.
Blueprint: lmm:modular-automorphism-one-parameter -/
theorem isOneParameterAut_modularAutomorphism {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    Physicslib4.AQFT.IsOneParameterAut (modularAutomorphism hM hΩ C hC) := by
  sorry

/-- **Takesaki's theorem.** For a von Neumann algebra `M` with a cyclic and separating unit
vector `Ω`, the vector state `ω_Ω` on the modular algebra is a KMS state at inverse temperature
`1` for the reversed modular flow `t ↦ σ_{-t}`: for `a, b ∈ M` there is a bounded continuous `F`
on `0 ≤ Im z ≤ 1`, holomorphic inside, with `F(t) = ω_Ω(a σ_{-t}(b))` and
`F(t + i) = ω_Ω(σ_{-t}(b) a)`. In the Bratteli–Robinson convention this says that `ω_Ω` is
`σ`-KMS at `β = -1`.
Blueprint: thrm:takesaki-kms -/
theorem isKMSState_modularAutomorphism {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (hΩ1 : ‖Ω‖ = 1) :
    Physicslib4.AQFT.IsKMSState (fun t => modularAutomorphism hM hΩ C hC (-t)) 1
      (Physicslib4.GNS.vectorState (modularAlgebra M) Ω hΩ1) := by
  sorry

end Physicslib4.Modular
