/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Operators.Modular.TakesakiKMS
import Physicslib4.AQFT.PositiveEnergyHalfPlane
import Physicslib4.Analysis.StripRealBoundary

/-!
# Borchers' theorem: the analytic and algebraic ingredients

Let `M` be a von Neumann algebra on `H` with a cyclic and separating vector `Ω`, modular operator
`Δ`, modular unitary group `Δ^{it}` and modular conjugation `J`, and let `V` be a one-parameter
unitary group with positive energy. This file states the ingredients of the proof of Borchers'
theorem (Florig's argument): the powers `Δ^{-iζ}` on the strip `0 ≤ Im ζ ≤ 1/2`, written with
bounded functions of `Δ`; the Borchers function `F` and its approximants `F_n`, their continuity,
holomorphy and boundary values; and the reality of correlations `⟨yΩ, X xΩ⟩` for self-adjoint
`x ∈ M`, `y ∈ M'`, together with the reflected group `W(t) = J V(-t) J`.

Clauses (B1) `V(t)Ω = Ω` and (B2) `V(t) x V(-t) ∈ M` for `t ≥ 0`, `x ∈ M` are stated explicitly
in each lemma that uses them.

## Notation

* `K[n]`, `p[z, n]` and `e[t]` are as in `Physicslib4.Operators.Modular.TakesakiKMS`; the
  function `s(λ) = √(max(λ, 0))` is written `Real.sqrt`.
* `k[ζ]` is `k_ζ(λ) = 1_{(0,∞)}(λ) λ^{-iζ}/(1 + s(λ))`, with the principal power, and `cfn` is
  `c(λ) = 1_{(0,∞)}(λ)/(1 + s(λ))`.
* `ε[w]` is `ε_w(λ) = 1_{[0,∞)}(λ) e^{iwλ}`, as in `Physicslib4.AQFT.PositiveEnergyHalfPlane`.
* `z♭ = conj z + i/2` is written out.
* Inside statements about `M`, `Ω`, `C`: `μΔ` is the spectral measure of `Δ`, `Δs` is
  `Δ^{1/2}`, `U[t]` is `Δ^{it}` as a bounded operator, `𝒥` is `J`, `𝒥[T]` is `J T J`, and
  `♯[φ, hφ]` is `φ♯ = φ + Δ^{1/2}φ`. These refer to the binders `hM hΩ C hC`.
* Inside statements about `V`: `V[t]` is `V(t)` as a bounded operator and `W[t]` is
  `W(t) = J V(-t) J`; with `hV : IsPositiveEnergy V`, `Ṽ[w]` is `ε_w(P)` for the generator `P`
  of `V`, and `F[τ, φ, ψ, hφ, hψ]`, `Fn[τ, φ, ψ, hφ, hψ, n]` are the Borchers function `F` and
  its approximants `F_n`, extended by `0` off the closed strip `kmsStrip (1/2)`.
  `Fxy[τ]` is `F` with `φ = xΩ`, `ψ = JyΩ`, for binders `hx : x ∈ M`, `hy : y ∈ M'`.
* The hygiene-false notations `F[…]`, `Fn[…]` and `Fxy[…]` bind the variable `z` of the strip.
-/

namespace Physicslib4.Modular

open scoped InnerProductSpace ComplexConjugate
open Physicslib4.Spectral.Unbounded Physicslib4.Spectral.Stone
open Filter Topology MeasureTheory
open Physicslib4.AQFT (kmsStrip kmsStripInterior IsPositiveEnergy)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The interval `K_n = [1/n, n]`. -/
local notation "K[" n "]" => Set.Icc (1 / (n : ℝ)) (n : ℝ)

/-- The function `p_{z,n}(λ) = 1_{K_n}(λ) λ^z`. -/
local notation "p[" z ", " n "]" =>
  Set.indicator (Set.Icc (1 / (n : ℝ)) (n : ℝ)) fun x : ℝ => (x : ℂ) ^ (z : ℂ)

/-- The function `e_t(λ) = e^{it log λ}`. -/
local notation "e[" t "]" => fun x : ℝ => Complex.exp (Complex.I * (t : ℂ) * (Real.log x : ℂ))

/-- The function `k_ζ(λ) = 1_{(0,∞)}(λ) λ^{-iζ}/(1 + s(λ))`. -/
local notation "k[" ζ "]" =>
  Set.indicator (Set.Ioi (0 : ℝ))
    fun x : ℝ => (x : ℂ) ^ (-Complex.I * (ζ : ℂ)) / (1 + (Real.sqrt x : ℂ))

/-- The function `c(λ) = 1_{(0,∞)}(λ)/(1 + s(λ))`. -/
local notation "cfn" =>
  Set.indicator (Set.Ioi (0 : ℝ)) fun x : ℝ => (1 + (Real.sqrt x : ℂ))⁻¹

/-- The function `ε_w(λ) = 1_{[0,∞)}(λ) e^{iwλ}`. -/
local notation "ε[" w "]" =>
  Set.indicator (Set.Ici (0 : ℝ)) fun x : ℝ => Complex.exp (Complex.I * (w : ℂ) * (x : ℂ))

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
/-- The modular conjugation `J`, for the binders `hM hΩ C hC` in scope. -/
local notation "𝒥" => modularConjugation hM hΩ C hC

set_option hygiene false in
/-- The bounded operator `J T J`, for the binders `hM hΩ C hC` in scope. -/
local notation "𝒥[" T "]" => modularConjugationConj hM hΩ C hC T

set_option hygiene false in
/-- `φ♯ = φ + Δ^{1/2}φ` for `φ ∈ Dom Δ^{1/2}`, for the binders `hM hΩ C hC` in scope. -/
local notation "♯[" φ ", " hφ "]" => (φ : H) + modularOperatorSqrt hM hΩ C hC ⟨φ, hφ⟩

set_option hygiene false in
/-- `V(t)` as a bounded operator, for the binder `V` in scope. -/
local notation "V[" t "]" => (V t).toLinearIsometry.toContinuousLinearMap

set_option hygiene false in
/-- The reflected group `W(t) = J V(-t) J`, for the binders `hM hΩ C hC V` in scope. -/
local notation "W[" t "]" =>
  modularConjugationConj hM hΩ C hC (V (-t)).toLinearIsometry.toContinuousLinearMap

set_option hygiene false in
/-- The extension `Ṽ(w) = ε_w(P)` of `V` to the upper half-plane, for the binder
`hV : IsPositiveEnergy V` in scope. -/
local notation "Ṽ[" w "]" => (spectralMeasure
  (stone hV.isOneParameterUnitaryGroup hV.isStronglyContinuous).fst).integral ε[w]

set_option hygiene false in
/-- The Borchers function
`F(z) = ⟪k_{z♭}(Δ)ψ♯, Ṽ(τ e^{2πz}) k_z(Δ)φ♯⟫` on the closed strip `0 ≤ Im z ≤ 1/2`, and `0` off
it. -/
local notation "F[" τ ", " φ ", " ψ ", " hφ ", " hψ "]" =>
  Set.indicator (kmsStrip (1 / 2)) fun z : ℂ =>
    ⟪(spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        k[starRingEnd ℂ z + Complex.I / 2] ♯[ψ, hψ],
      Ṽ[((τ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * z)]
        ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral k[z]
          ♯[φ, hφ])⟫_ℂ

set_option hygiene false in
/-- The approximant
`F_n(z) = ⟪p_{-iz♭,n}(Δ)c(Δ)ψ♯, Ṽ(τ e^{2πz}) p_{-iz,n}(Δ)c(Δ)φ♯⟫` on the closed strip
`0 ≤ Im z ≤ 1/2`, and `0` off it. -/
local notation "Fn[" τ ", " φ ", " ψ ", " hφ ", " hψ ", " n "]" =>
  Set.indicator (kmsStrip (1 / 2)) fun z : ℂ =>
    ⟪(spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        p[-Complex.I * (starRingEnd ℂ z + Complex.I / 2), n]
        ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral cfn ♯[ψ, hψ]),
      Ṽ[((τ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * z)]
        ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          p[-Complex.I * z, n]
          ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral cfn
            ♯[φ, hφ]))⟫_ℂ

set_option hygiene false in
/-- The Borchers function with `φ = xΩ` and `ψ = JyΩ`, for the binders `hM hΩ C hC hV` and
`hx : x ∈ M`, `hy : y ∈ M'` in scope. -/
local notation "Fxy[" τ "]" =>
  F[τ, x Ω, modularConjugation hM hΩ C hC (y Ω),
    (modularOperatorSqrt_apply_of_mem hM hΩ C hC hx).fst,
    (modularOperatorSqrt_apply_of_mem_centralizer hM hΩ C hC hy).fst]

/-- `V` is a half-sided translation for `(M, Ω)`: a one-parameter unitary group with positive
energy (P) that fixes `Ω` (B1) and maps `M` into itself under `x ↦ V(t) x V(-t)` for `t ≥ 0` (B2).
Since `V(t)* = V(-t)`, (B2) is the inclusion `V(t) M V(t)* ⊆ M`. The predicate does not require
`Ω` to be cyclic or separating; Borchers' theorem adds that hypothesis separately.

Implementation note: (P) is the parent structure `IsPositiveEnergy V`, so its fields
`isOneParameterUnitaryGroup`, `isStronglyContinuous` and `isPositive_generator` are available
by projection.

Blueprint: def:half-sided-translation -/
structure IsHalfSidedTranslation (M : Set (H →L[ℂ] H)) (Ω : H) (V : ℝ → (H ≃ₗᵢ[ℂ] H)) : Prop
    extends IsPositiveEnergy V where
  /-- (B1) `V(t)Ω = Ω` for every `t`. -/
  apply_self : ∀ t : ℝ, V t Ω = Ω
  /-- (B2) `V(t) x V(-t) ∈ M` for every `t ≥ 0` and `x ∈ M`. -/
  conj_mem : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ M, V[t] ∘L x ∘L V[-t] ∈ M

/-! ### Powers of `Δ` on the strip -/

/-- `s`, `k_ζ`, `c` and `k_t s` are measurable.

Blueprint: lmm:strip-power-functions-measurable -/
theorem stripPower_functions_measurable (ζ : ℂ) (t : ℝ) :
    Measurable (fun x : ℝ => Real.sqrt x) ∧ Measurable k[ζ] ∧ Measurable cfn ∧
      Measurable (fun x : ℝ => k[(t : ℂ)] x * (Real.sqrt x : ℂ)) := by
  have hs : Measurable (fun x : ℝ => (Real.sqrt x : ℂ)) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have hk : ∀ w : ℂ, Measurable k[w] := fun w =>
    ((Complex.measurable_ofReal.pow_const _).div (measurable_const.add hs)).indicator
      measurableSet_Ioi
  exact ⟨Real.continuous_sqrt.measurable, hk ζ,
    (measurable_const.add hs).inv.indicator measurableSet_Ioi, (hk _).mul hs⟩

/-- For `ζ` in the strip `0 ≤ Im ζ ≤ 1/2` and `λ > 0`, `|λ^{-iζ}| = λ^{Im ζ} ≤ 1 + s(λ)`.

Blueprint: lmm:strip-power-modulus-bound -/
theorem norm_cpow_neg_I_mul_le {ζ : ℂ} (hζ : ζ ∈ kmsStrip (1 / 2)) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (-Complex.I * ζ)‖ = x ^ ζ.im ∧
      ‖(x : ℂ) ^ (-Complex.I * ζ)‖ ≤ 1 + Real.sqrt x := by
  obtain ⟨h0, h1⟩ := hζ
  have heq : ‖(x : ℂ) ^ (-Complex.I * ζ)‖ = x ^ ζ.im := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
  refine ⟨heq, heq ▸ ?_⟩
  rcases le_total x 1 with hx1 | hx1
  · linarith [Real.rpow_le_one hx.le hx1 h0, Real.sqrt_nonneg x]
  · have := Real.rpow_le_rpow_of_exponent_le hx1 h1
    rw [← Real.sqrt_eq_rpow] at this
    linarith

/-- `|c| ≤ 1` and `|k_t s| ≤ 1` for real `t`, and `|k_ζ| ≤ 1` for `ζ` in the strip
`0 ≤ Im ζ ≤ 1/2`.

Blueprint: lmm:strip-power-functions-bounded -/
theorem stripPower_functions_bounded (t : ℝ) (ζ : ℂ) :
    (∀ x : ℝ, ‖cfn x‖ ≤ 1) ∧ (∀ x : ℝ, ‖k[(t : ℂ)] x * (Real.sqrt x : ℂ)‖ ≤ 1) ∧
      (ζ ∈ kmsStrip (1 / 2) → ∀ x : ℝ, ‖k[ζ] x‖ ≤ 1) := by
  sorry

/-- `p_{-iζ,n} c = k_ζ 1_{K_n}`, `k_t (1 + s) = 1_{(0,∞)} e_{-t}` and `k_{t+i/2} = k_t s`
pointwise.

Blueprint: lmm:strip-power-functions-identities -/
theorem stripPower_functions_identities (ζ : ℂ) (n : ℕ) (t x : ℝ) :
    p[-Complex.I * ζ, n] x * cfn x = k[ζ] x * (K[n]).indicator 1 x ∧
      k[(t : ℂ)] x * (1 + (Real.sqrt x : ℂ)) = (Set.Ioi (0 : ℝ)).indicator e[-t] x ∧
      k[(t : ℂ) + Complex.I / 2] x = k[(t : ℂ)] x * (Real.sqrt x : ℂ) := by
  rcases le_or_gt x 0 with hx | hx
  · have hx' : x ∉ Set.Ioi (0 : ℝ) := not_lt.mpr hx
    refine ⟨?_, ?_, ?_⟩ <;> simp [Set.indicator_of_notMem hx']
  · have hx' : x ∈ Set.Ioi (0 : ℝ) := hx
    have hne : (1 + (Real.sqrt x : ℂ)) ≠ 0 := by
      have : (0 : ℝ) < 1 + Real.sqrt x := by positivity
      exact_mod_cast this.ne'
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    refine ⟨?_, ?_, ?_⟩
    · by_cases hK : x ∈ K[n]
      · rw [Set.indicator_of_mem hK, Set.indicator_of_mem hK, Set.indicator_of_mem hx',
          Set.indicator_of_mem hx', Pi.one_apply, mul_one, div_eq_mul_inv]
      · rw [Set.indicator_of_notMem hK, Set.indicator_of_notMem hK, zero_mul, mul_zero]
    · rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx', div_mul_cancel₀ _ hne,
        Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]
      congr 1
      ring
    · rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx']
      have hs : (Real.sqrt x : ℂ) = (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
        rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx.le]
      rw [hs, div_mul_eq_mul_div, ← Complex.cpow_add _ _ hx0]
      congr 2
      push_cast; ring_nf; simp; ring

/-- The lower edge: for `φ ∈ Dom Δ^{1/2}` and real `t`, `k_t(Δ)φ♯ = Δ^{-it}φ`.

Blueprint: lmm:strip-power-lower-boundary -/
theorem stripPower_lower_boundary {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {φ : H} (hφ : φ ∈ (Δs).domain) (t : ℝ) :
    (μΔ).integral k[(t : ℂ)] ♯[φ, hφ] = U[-t] φ := by
  sorry

/-- The upper edge: for `φ ∈ Dom Δ^{1/2}` and real `t`, `k_{t+i/2}(Δ)φ♯ = Δ^{-it}Δ^{1/2}φ`.

Blueprint: lmm:strip-power-upper-boundary -/
theorem stripPower_upper_boundary {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {φ : H} (hφ : φ ∈ (Δs).domain) (t : ℝ) :
    (μΔ).integral k[(t : ℂ) + Complex.I / 2] ♯[φ, hφ] = U[-t] (Δs ⟨φ, hφ⟩) := by
  sorry

/-- Cutting off `k_ζ(Δ)`: `p_{-iζ,n}(Δ)c(Δ)χ = k_ζ(Δ)E_nχ`, and for `ζ` in the strip
`0 ≤ Im ζ ≤ 1/2`, `‖k_ζ(Δ)χ‖ ≤ ‖χ‖` and `‖k_ζ(Δ)χ - p_{-iζ,n}(Δ)c(Δ)χ‖ ≤ ‖χ - E_nχ‖`.

Blueprint: lmm:strip-power-cutoff -/
theorem stripPower_cutoff {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (χ : H) (ζ : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (μΔ).integral p[-Complex.I * ζ, n] ((μΔ).integral cfn χ) = (μΔ).integral k[ζ] (μΔ K[n] χ) ∧
      (ζ ∈ kmsStrip (1 / 2) →
        ‖(μΔ).integral k[ζ] χ‖ ≤ ‖χ‖ ∧
          ‖(μΔ).integral k[ζ] χ - (μΔ).integral p[-Complex.I * ζ, n] ((μΔ).integral cfn χ)‖ ≤
            ‖χ - μΔ K[n] χ‖) := by
  sorry

/-! ### The Borchers function -/

/-- If `a, b` are continuous on `D`, `‖T(z)‖ ≤ 1` on `D` and `z ↦ T(z)χ` is continuous on `D` for
every `χ`, then `z ↦ ⟪a(z), T(z)b(z)⟫` is continuous on `D`.

Blueprint: lmm:sandwich-continuous -/
theorem continuousOn_inner_sandwich {D : Set ℂ} {a b : ℂ → H} {T : ℂ → H →L[ℂ] H}
    (ha : ContinuousOn a D) (hb : ContinuousOn b D) (hT : ∀ z ∈ D, ‖T z‖ ≤ 1)
    (hTc : ∀ χ : H, ContinuousOn (fun z => T z χ) D) :
    ContinuousOn (fun z => ⟪a z, T z (b z)⟫_ℂ) D := by
  intro z₀ hz₀
  have h1 : Filter.Tendsto (fun z => T z (b z) - T z (b z₀)) (nhdsWithin z₀ D) (nhds 0) := by
    refine squeeze_zero_norm' (a := fun z => ‖b z - b z₀‖) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with z hz
      rw [← map_sub]
      exact ((T z).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hT z hz))
    · simpa using ((hb z₀ hz₀).sub (continuousWithinAt_const (b := b z₀))).norm.tendsto
  have key : ContinuousWithinAt (fun z => T z (b z)) D z₀ := by
    simpa [ContinuousWithinAt] using h1.add (hTc (b z₀) z₀ hz₀)
  exact (ha z₀ hz₀).inner key

/-- For `n ≥ 1`, the approximant `F_n` is continuous on the closed strip `0 ≤ Im z ≤ 1/2`.

Blueprint: lmm:borchers-approximants-continuous -/
theorem continuousOn_borchersApproximant {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsPositiveEnergy V)
    {τ : ℝ} (hτ : 0 ≤ τ) {φ ψ : H} (hφ : φ ∈ (Δs).domain) (hψ : ψ ∈ (Δs).domain)
    {n : ℕ} (hn : 1 ≤ n) :
    ContinuousOn Fn[τ, φ, ψ, hφ, hψ, n] (kmsStrip (1 / 2)) := by
  sorry

/-- For `n ≥ 1`, the approximant `F_n` is holomorphic on the open strip `0 < Im z < 1/2`.

Blueprint: lmm:borchers-approximants-holomorphic -/
theorem differentiableOn_borchersApproximant {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsPositiveEnergy V)
    {τ : ℝ} (hτ : 0 ≤ τ) {φ ψ : H} (hφ : φ ∈ (Δs).domain) (hψ : ψ ∈ (Δs).domain)
    {n : ℕ} (hn : 1 ≤ n) :
    DifferentiableOn ℂ Fn[τ, φ, ψ, hφ, hψ, n] (kmsStripInterior (1 / 2)) := by
  sorry

/-- For `n ≥ 1` and `z` in the closed strip,
`|F(z) - F_n(z)| ≤ ‖ψ♯ - E_nψ♯‖ ‖φ♯‖ + ‖ψ♯‖ ‖φ♯ - E_nφ♯‖`, so `F_n → F` uniformly on the strip.

Blueprint: lmm:borchers-approximants-uniform -/
theorem borchersApproximant_tendstoUniformlyOn {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsPositiveEnergy V)
    {τ : ℝ} (hτ : 0 ≤ τ) {φ ψ : H} (hφ : φ ∈ (Δs).domain) (hψ : ψ ∈ (Δs).domain) :
    (∀ n : ℕ, 1 ≤ n → ∀ z ∈ kmsStrip (1 / 2),
      ‖F[τ, φ, ψ, hφ, hψ] z - Fn[τ, φ, ψ, hφ, hψ, n] z‖ ≤
        ‖♯[ψ, hψ] - μΔ K[n] ♯[ψ, hψ]‖ * ‖♯[φ, hφ]‖ +
          ‖♯[ψ, hψ]‖ * ‖♯[φ, hφ] - μΔ K[n] ♯[φ, hφ]‖) ∧
      TendstoUniformlyOn (fun (n : ℕ) (z : ℂ) => Fn[τ, φ, ψ, hφ, hψ, n] z)
        F[τ, φ, ψ, hφ, hψ] atTop (kmsStrip (1 / 2)) := by
  sorry

/-- The Borchers function `F` is continuous on the closed strip `0 ≤ Im z ≤ 1/2`, holomorphic on
the open strip, and bounded there by `‖ψ♯‖ ‖φ♯‖`.

Blueprint: lmm:borchers-function-analytic -/
theorem borchersFunction_analytic {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsPositiveEnergy V)
    {τ : ℝ} (hτ : 0 ≤ τ) {φ ψ : H} (hφ : φ ∈ (Δs).domain) (hψ : ψ ∈ (Δs).domain) :
    ContinuousOn F[τ, φ, ψ, hφ, hψ] (kmsStrip (1 / 2)) ∧
      DifferentiableOn ℂ F[τ, φ, ψ, hφ, hψ] (kmsStripInterior (1 / 2)) ∧
      ∀ z ∈ kmsStrip (1 / 2), ‖F[τ, φ, ψ, hφ, hψ] z‖ ≤ ‖♯[ψ, hψ]‖ * ‖♯[φ, hφ]‖ := by
  sorry

/-- The boundary values of the Borchers function: for real `t`,
`F(t) = ⟪Δ^{-it}Δ^{1/2}ψ, V(τe^{2πt})Δ^{-it}φ⟫` and
`F(t + i/2) = ⟪Δ^{-it}ψ, V(-τe^{2πt})Δ^{-it}Δ^{1/2}φ⟫`.

Blueprint: lmm:borchers-function-boundary -/
theorem borchersFunction_boundary {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsPositiveEnergy V)
    {τ : ℝ} (hτ : 0 ≤ τ) {φ ψ : H} (hφ : φ ∈ (Δs).domain) (hψ : ψ ∈ (Δs).domain) (t : ℝ) :
    F[τ, φ, ψ, hφ, hψ] (t : ℂ) =
        ⟪U[-t] (Δs ⟨ψ, hψ⟩), V (τ * Real.exp (2 * Real.pi * t)) (U[-t] φ)⟫_ℂ ∧
      F[τ, φ, ψ, hφ, hψ] ((t : ℂ) + Complex.I / 2) =
        ⟪U[-t] ψ, V (-(τ * Real.exp (2 * Real.pi * t))) (U[-t] (Δs ⟨φ, hφ⟩))⟫_ℂ := by
  sorry

/-! ### Reality on the boundary -/

/-- `Δ^{1/2}Ω = Ω` and `JΩ = Ω`.

Blueprint: lmm:modular-conjugation-fixes-omega -/
theorem modularConjugation_apply_self {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    (∃ h : Ω ∈ (Δs).domain, Δs ⟨Ω, h⟩ = Ω) ∧ 𝒥 Ω = Ω := by
  obtain ⟨hd, hΔ⟩ := modularOperator_apply_self hM hΩ C hC
  have hev : modularOperator M Ω C ⟨Ω, hd⟩ = ((1 : ℝ) : ℂ) • Ω := by rw [hΔ]; simp
  have hK : μΔ K[(1 : ℕ)] Ω = Ω := by
    simpa using spectralMeasure_singleton_apply_of_eigenvector
      (modularOperator_isSelfAdjoint hM hΩ C hC) hd hev
  obtain ⟨h₁, -, e, -⟩ := modularOperatorSqrt_eq_indicatorCpow hM hΩ C hC le_rfl hK
  have hp : p[(1 / 2 : ℂ), (1 : ℕ)] ∈ Physicslib4.Spectral.BddMeasurable ℝ := by
    refine ⟨(by fun_prop : Measurable fun x : ℝ => (x : ℂ) ^ (1 / 2 : ℂ)).indicator
      measurableSet_Icc, 1, fun x => ?_⟩
    by_cases hx : x ∈ K[(1 : ℕ)]
    · have hx1 : x = 1 := by simpa using hx
      subst hx1; simp
    · rw [Set.indicator_of_notMem hx]; simp
  have hs : Δs ⟨Ω, h₁⟩ = Ω := by
    rw [e, spectralMeasure_integral_apply_of_eigenvector _ hd hev hp]; simp
  refine ⟨⟨h₁, hs⟩, ?_⟩
  obtain ⟨h₂, e₂⟩ := modularOperatorSqrt_apply_of_mem hM hΩ C hC
    (hM.2 ▸ Set.one_mem_centralizer : (1 : H →L[ℂ] H) ∈ M)
  simp only [one_apply_eq_self, star_one] at h₂ e₂
  exact e₂.symm.trans hs

/-- For real `t` and `y ∈ M'`, `Δ^{it} y Δ^{-it} ∈ M'`.

Blueprint: lmm:modular-group-preserves-commutant -/
theorem modularUnitaryGroup_conj_mem_centralizer {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (t : ℝ) {y : H →L[ℂ] H} (hy : y ∈ Set.centralizer M) :
    U[t] ∘L y ∘L U[-t] ∈ Set.centralizer M := by
  have hU := (modularUnitaryGroup_properties hM hΩ C hC).1
  have h : ∀ a b : ℝ, a + b = 0 → ∀ v, modularUnitaryGroup hM hΩ C hC a
      (modularUnitaryGroup hM hΩ C hC b v) = v := fun a b hab v => by
    rw [← hU.map_add, hab, hU.map_zero]
  intro x hx
  ext v
  have hxy := congrArg (fun w => modularUnitaryGroup hM hΩ C hC t w)
    (DFunLike.congr_fun (hy _ (modularUnitaryGroup_conj_mem_of_mem hM hΩ C hC (-t) hx))
      (modularUnitaryGroup hM hΩ C hC (-t) v))
  simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry] at hxy ⊢
  rw [h (-(-t)) (-t) (by ring), h t (-t) (by ring), neg_neg] at hxy
  exact hxy

/-- For `y ∈ M'`, `J y Ω ∈ Dom Δ^{1/2}` and `Δ^{1/2} J y Ω = y* Ω`.

Blueprint: lmm:commutant-vector-modular-sqrt -/
theorem modularOperatorSqrt_apply_of_mem_centralizer {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {y : H →L[ℂ] H} (hy : y ∈ Set.centralizer M) :
    ∃ h : 𝒥 (y Ω) ∈ (Δs).domain, Δs ⟨𝒥 (y Ω), h⟩ = star y Ω := by
  obtain ⟨hJ, hconj⟩ := modularConjugation_involution hM hΩ C hC
  obtain ⟨-, h, he, -⟩ := tomitaAdjoint_apply_of_mem_centralizer hM hΩ C hC hy
  rw [← hconj] at h
  have hs : (𝒥).symm (y Ω) = 𝒥 (y Ω) := (𝒥).symm_apply_eq.2 (hJ _).symm
  have h' : (𝒥).symm (y Ω) ∈ (Δs).domain := h
  refine ⟨hs ▸ h', ?_⟩
  have happ : ∀ {P Q : H →ₗ.[ℂ] H} (hPQ : P = Q) (ψ : H) (hP : ψ ∈ P.domain)
      (hQ : ψ ∈ Q.domain), P ⟨ψ, hP⟩ = Q ⟨ψ, hQ⟩ := by
    rintro _ _ rfl _ _ _; rfl
  rw [← happ hconj (y Ω) h] at he
  rw [← he]
  change _ = 𝒥 (𝒥 (Δs ⟨(𝒥).symm (y Ω), h'⟩))
  rw [hJ]
  exact congrArg Δs (Subtype.ext hs.symm)

/-- Under (B2), `V(-t) y V(t) ∈ M'` for `t ≥ 0` and `y ∈ M'`.

Blueprint: lmm:commutant-reverse-endomorphism -/
theorem commutant_reverse_endomorphism {M : Set (H →L[ℂ] H)} {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : IsOneParameterUnitaryGroup V)
    (hB2 : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ M, V[t] ∘L x ∘L V[-t] ∈ M)
    {t : ℝ} (ht : 0 ≤ t) {y : H →L[ℂ] H} (hy : y ∈ Set.centralizer M) :
    V[-t] ∘L y ∘L V[t] ∈ Set.centralizer M := by
  rw [Set.mem_centralizer_iff] at hy ⊢
  intro x hx
  have h2 : ∀ ψ, V (-t) (V t ψ) = ψ := fun ψ => by
    rw [← hV.map_add, neg_add_cancel, hV.map_zero]
  ext ψ
  have key := congrArg (fun T : H →L[ℂ] H => V (-t) (T (V t ψ))) (hy _ (hB2 t ht x hx))
  simpa [h2] using key

/-- The adjoint of the reflected group: `W(t)* = J V(t) J`.

Blueprint: lmm:reflected-group-adjoint -/
theorem reflectedGroup_adjoint {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsOneParameterUnitaryGroup V)
    (t : ℝ) :
    ContinuousLinearMap.adjoint W[t] = 𝒥[V[t]] := by
  have hJ := (modularConjugation_involution hM hΩ C hC).1
  have hJi : ∀ a b, ⟪𝒥 a, 𝒥 b⟫_ℂ = ⟪b, a⟫_ℂ := fun a b =>
    (inner_map_map_of_conjLinearIsometry (𝒥).toLinearIsometry a b).trans (inner_conj_symm _ _)
  have hV2 : ∀ ψ, V (-t) (V t ψ) = ψ := fun ψ => by
    rw [← hV.map_add, neg_add_cancel, hV.map_zero]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  change ⟪𝒥 (V t (𝒥 x)), y⟫_ℂ = ⟪x, 𝒥 (V (-t) (𝒥 y))⟫_ℂ
  rw [← hJ y, hJi, ← hJ x, hJi, hJ, hJ, ← LinearIsometryEquiv.inner_map_map (V (-t)), hV2]

/-- Under (B1), for `t ≥ 0`, `W(t)` is unitary and `W(t)Ω = Ω`.

Blueprint: lmm:reflected-group-unitary -/
theorem reflectedGroup_unitary {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsOneParameterUnitaryGroup V)
    (hB1 : ∀ t : ℝ, V t Ω = Ω) {t : ℝ} (ht : 0 ≤ t) :
    W[t] ∈ unitary (H →L[ℂ] H) ∧ W[t] Ω = Ω := by
  sorry

/-- Under (B2), for `t ≥ 0` and `x ∈ M`, `W(t) x W(t)* ∈ M`.

Blueprint: lmm:reflected-group-endomorphism -/
theorem reflectedGroup_conj_mem {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsOneParameterUnitaryGroup V)
    (hB2 : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ M, V[t] ∘L x ∘L V[-t] ∈ M)
    {t : ℝ} (ht : 0 ≤ t) {x : H →L[ℂ] H} (hx : x ∈ M) :
    W[t] ∘L x ∘L ContinuousLinearMap.adjoint W[t] ∈ M := by
  sorry

/-- If `X` is unitary, `XΩ = Ω` and `X x X* ∈ M` for `x ∈ M`, then `⟪yΩ, X xΩ⟫` is real for
self-adjoint `x ∈ M` and `y ∈ M'`.

Blueprint: lmm:real-correlation -/
theorem inner_unitary_apply_im_eq_zero {M : Set (H →L[ℂ] H)} {Ω : H} {X : H →L[ℂ] H}
    (hX : X ∈ unitary (H →L[ℂ] H)) (hXΩ : X Ω = Ω)
    (hXM : ∀ x ∈ M, X ∘L x ∘L ContinuousLinearMap.adjoint X ∈ M)
    {x y : H →L[ℂ] H} (hx : x ∈ M) (hxs : IsSelfAdjoint x)
    (hy : y ∈ Set.centralizer M) (hys : IsSelfAdjoint y) :
    (⟪y Ω, X (x Ω)⟫_ℂ).im = 0 := by
  set x' := X ∘L x ∘L ContinuousLinearMap.adjoint X with hx'
  have hXs : ContinuousLinearMap.adjoint X ∘L X = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hX.1
  have hXΩ' : ContinuousLinearMap.adjoint X Ω = Ω := by
    simpa [hXΩ] using DFunLike.congr_fun hXs Ω
  have h1 : X (x Ω) = x' Ω := by simp [hx', hXΩ']
  have hxs' : ContinuousLinearMap.adjoint x' = x' := by
    have := hxs.star_eq
    rw [ContinuousLinearMap.star_eq_adjoint] at this
    simp [hx', ContinuousLinearMap.adjoint_comp, this, ContinuousLinearMap.comp_assoc]
  have hys' : ContinuousLinearMap.adjoint y = y := by
    have := hys.star_eq
    rwa [ContinuousLinearMap.star_eq_adjoint] at this
  have hcomm : x' * y = y * x' := (Set.mem_centralizer_iff.mp hy) x' (hXM x hx)
  rw [h1, ← Complex.conj_eq_iff_im, inner_conj_symm]
  calc ⟪x' Ω, y Ω⟫_ℂ = ⟪Ω, x' (y Ω)⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_left x' (y Ω) Ω, hxs']
    _ = ⟪Ω, y (x' Ω)⟫_ℂ := congrArg _ (DFunLike.congr_fun hcomm Ω)
    _ = ⟪y Ω, x' Ω⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_left y (x' Ω) Ω, hys']

/-- With `X` as in `inner_unitary_apply_im_eq_zero`, self-adjoint `x ∈ M`, `y ∈ M'` and real
`t`, `⟪Δ^{-it}yΩ, X Δ^{-it}xΩ⟫` is real.

Blueprint: lmm:modular-rotated-correlation-real -/
theorem inner_modularRotated_im_eq_zero {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {X : H →L[ℂ] H}
    (hX : X ∈ unitary (H →L[ℂ] H)) (hXΩ : X Ω = Ω)
    (hXM : ∀ x ∈ M, X ∘L x ∘L ContinuousLinearMap.adjoint X ∈ M)
    {x y : H →L[ℂ] H} (hx : x ∈ M) (hxs : IsSelfAdjoint x)
    (hy : y ∈ Set.centralizer M) (hys : IsSelfAdjoint y) (t : ℝ) :
    (⟪U[-t] (y Ω), X (U[-t] (x Ω))⟫_ℂ).im = 0 := by
  sorry

/-- Under (B1) and (B2), for self-adjoint `x ∈ M`, `y ∈ M'`, `τ ≥ 0` and real `t`,
`⟪Δ^{-it}JyΩ, V(-τ)Δ^{-it}JxΩ⟫ = conj ⟪Δ^{-it}yΩ, W(τ)Δ^{-it}xΩ⟫`, and both sides are real.

Blueprint: lmm:borchers-upper-boundary-real -/
theorem borchers_upper_boundary_real {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsOneParameterUnitaryGroup V)
    (hB1 : ∀ t : ℝ, V t Ω = Ω) (hB2 : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ M, V[t] ∘L x ∘L V[-t] ∈ M)
    {x y : H →L[ℂ] H} (hx : x ∈ M) (hxs : IsSelfAdjoint x)
    (hy : y ∈ Set.centralizer M) (hys : IsSelfAdjoint y) {τ : ℝ} (hτ : 0 ≤ τ) (t : ℝ) :
    ⟪U[-t] (𝒥 (y Ω)), V (-τ) (U[-t] (𝒥 (x Ω)))⟫_ℂ =
        conj ⟪U[-t] (y Ω), W[τ] (U[-t] (x Ω))⟫_ℂ ∧
      (⟪U[-t] (y Ω), W[τ] (U[-t] (x Ω))⟫_ℂ).im = 0 := by
  sorry

/-! ### The Borchers function on the edges -/

/-- For self-adjoint `x ∈ M`, `y ∈ M'` and `τ ≥ 0`, the Borchers function with `φ = xΩ` and
`ψ = JyΩ` has, for real `t`,
`F(t) = ⟪yΩ, Δ^{it}V(τe^{2πt})Δ^{-it} xΩ⟫ = ⟪Δ^{-it}yΩ, V(τe^{2πt})Δ^{-it}xΩ⟫` and
`F(t + i/2) = ⟪Δ^{-it}JyΩ, V(-τe^{2πt})Δ^{-it}JxΩ⟫`; in particular
`F(0) = ⟪yΩ, V(τ)xΩ⟫` and `F(i/2) = ⟪JyΩ, V(-τ)JxΩ⟫`.

Blueprint: lmm:borchers-function-special-values -/
theorem borchersFunction_special_values {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsPositiveEnergy V)
    {τ : ℝ} (hτ : 0 ≤ τ) {x y : H →L[ℂ] H} (hx : x ∈ M) (hxs : IsSelfAdjoint x)
    (hy : y ∈ Set.centralizer M) (hys : IsSelfAdjoint y) :
    (∀ t : ℝ,
      F[τ, x Ω, 𝒥 (y Ω), (modularOperatorSqrt_apply_of_mem hM hΩ C hC hx).fst,
          (modularOperatorSqrt_apply_of_mem_centralizer hM hΩ C hC hy).fst] (t : ℂ) =
          ⟪y Ω, U[t] (V (τ * Real.exp (2 * Real.pi * t)) (U[-t] (x Ω)))⟫_ℂ ∧
        F[τ, x Ω, 𝒥 (y Ω), (modularOperatorSqrt_apply_of_mem hM hΩ C hC hx).fst,
          (modularOperatorSqrt_apply_of_mem_centralizer hM hΩ C hC hy).fst] (t : ℂ) =
          ⟪U[-t] (y Ω), V (τ * Real.exp (2 * Real.pi * t)) (U[-t] (x Ω))⟫_ℂ ∧
        F[τ, x Ω, 𝒥 (y Ω), (modularOperatorSqrt_apply_of_mem hM hΩ C hC hx).fst,
          (modularOperatorSqrt_apply_of_mem_centralizer hM hΩ C hC hy).fst]
            ((t : ℂ) + Complex.I / 2) =
          ⟪U[-t] (𝒥 (y Ω)), V (-(τ * Real.exp (2 * Real.pi * t))) (U[-t] (𝒥 (x Ω)))⟫_ℂ) ∧
      F[τ, x Ω, 𝒥 (y Ω), (modularOperatorSqrt_apply_of_mem hM hΩ C hC hx).fst,
          (modularOperatorSqrt_apply_of_mem_centralizer hM hΩ C hC hy).fst] 0 =
        ⟪y Ω, V τ (x Ω)⟫_ℂ ∧
      F[τ, x Ω, 𝒥 (y Ω), (modularOperatorSqrt_apply_of_mem hM hΩ C hC hx).fst,
          (modularOperatorSqrt_apply_of_mem_centralizer hM hΩ C hC hy).fst] (Complex.I / 2) =
        ⟪𝒥 (y Ω), V (-τ) (𝒥 (x Ω))⟫_ℂ := by
  sorry

/-! ### Determination by matrix coefficients -/

/-- Bounded operators `A, B` with `⟪yΩ, A xΩ⟫ = ⟪yΩ, B xΩ⟫` for all self-adjoint `x ∈ M` and
`y ∈ M'` are equal.

Blueprint: lmm:eq-of-self-adjoint-matrix-coefficients -/
theorem eq_of_selfAdjoint_matrix_coefficients {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) {A B : H →L[ℂ] H}
    (h : ∀ x ∈ M, IsSelfAdjoint x → ∀ y ∈ Set.centralizer M, IsSelfAdjoint y →
      ⟪y Ω, A (x Ω)⟫_ℂ = ⟪y Ω, B (x Ω)⟫_ℂ) :
    A = B := by
  sorry

/-! ### Borchers' theorem -/

/-- For a half-sided translation `V`, self-adjoint `x ∈ M`, `y ∈ M'` and `τ ≥ 0`, the Borchers
function with `φ = xΩ`, `ψ = JyΩ` is real on the lower edge: `F(t) ∈ ℝ` for real `t`.

Blueprint: lmm:borchers-function-lower-edge-real -/
theorem borchersFunction_lower_edge_real {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsHalfSidedTranslation M Ω V)
    {τ : ℝ} (hτ : 0 ≤ τ) {x y : H →L[ℂ] H} (hx : x ∈ M) (hxs : IsSelfAdjoint x)
    (hy : y ∈ Set.centralizer M) (hys : IsSelfAdjoint y) (t : ℝ) :
    (Fxy[τ] (t : ℂ)).im = 0 := by
  sorry

/-- For a half-sided translation `V`, self-adjoint `x ∈ M`, `y ∈ M'` and `τ ≥ 0`, the Borchers
function with `φ = xΩ`, `ψ = JyΩ` is real on the upper edge, and `F(i/2) = ⟪yΩ, W(τ)xΩ⟫`.

Blueprint: lmm:borchers-function-upper-edge-real -/
theorem borchersFunction_upper_edge_real {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsHalfSidedTranslation M Ω V)
    {τ : ℝ} (hτ : 0 ≤ τ) {x y : H →L[ℂ] H} (hx : x ∈ M) (hxs : IsSelfAdjoint x)
    (hy : y ∈ Set.centralizer M) (hys : IsSelfAdjoint y) :
    (∀ t : ℝ, (Fxy[τ] ((t : ℂ) + Complex.I / 2)).im = 0) ∧
      Fxy[τ] (Complex.I / 2) = ⟪y Ω, W[τ] (x Ω)⟫_ℂ := by
  sorry

/-- For a half-sided translation `V`, self-adjoint `x ∈ M`, `y ∈ M'`, `τ ≥ 0` and real `s`,
`⟪yΩ, Δ^{is}V(τe^{2πs})Δ^{-is}xΩ⟫ = ⟪yΩ, V(τ)xΩ⟫ = ⟪yΩ, W(τ)xΩ⟫`.

Blueprint: lmm:borchers-function-constant -/
theorem borchersFunction_constant {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsHalfSidedTranslation M Ω V)
    {τ : ℝ} (hτ : 0 ≤ τ) {x y : H →L[ℂ] H} (hx : x ∈ M) (hxs : IsSelfAdjoint x)
    (hy : y ∈ Set.centralizer M) (hys : IsSelfAdjoint y) (s : ℝ) :
    ⟪y Ω, U[s] (V (τ * Real.exp (2 * Real.pi * s)) (U[-s] (x Ω)))⟫_ℂ = ⟪y Ω, V τ (x Ω)⟫_ℂ ∧
      ⟪y Ω, V τ (x Ω)⟫_ℂ = ⟪y Ω, W[τ] (x Ω)⟫_ℂ := by
  sorry

/-- Dilation for nonnegative times: for a half-sided translation `V`, `t ≥ 0` and real `s`,
`Δ^{is} V(t) Δ^{-is} = V(e^{-2πs} t)`.

Blueprint: lmm:borchers-dilation-nonneg -/
theorem borchers_dilation_nonneg {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsHalfSidedTranslation M Ω V)
    {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    U[s] ∘L V[t] ∘L U[-s] = V[Real.exp (-(2 * Real.pi * s)) * t] := by
  sorry

/-- Reflection for nonnegative times: for a half-sided translation `V` and `τ ≥ 0`,
`J V(-τ) J = V(τ)`.

Blueprint: lmm:borchers-reflection-nonneg -/
theorem borchers_reflection_nonneg {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsHalfSidedTranslation M Ω V)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    𝒥[V[-τ]] = V[τ] := by
  sorry

/-- Dilation for all times: for a half-sided translation `V` and all real `s, t`,
`Δ^{is} V(t) Δ^{-is} = V(e^{-2πs} t)`.

Blueprint: lmm:borchers-dilation-all -/
theorem borchers_dilation_all {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsHalfSidedTranslation M Ω V)
    (s t : ℝ) :
    U[s] ∘L V[t] ∘L U[-s] = V[Real.exp (-(2 * Real.pi * s)) * t] := by
  sorry

/-- Reflection for all times: for a half-sided translation `V` and all real `t`,
`J V(t) J = V(-t)`.

Blueprint: lmm:borchers-reflection-all -/
theorem borchers_reflection_all {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsHalfSidedTranslation M Ω V)
    (t : ℝ) :
    𝒥[V[t]] = V[-t] := by
  sorry

/-- **Borchers' theorem.** Let `M` be a von Neumann algebra with a cyclic and separating vector
`Ω`, modular unitary group `Δ^{is}` and modular conjugation `J`, and let `V` be a half-sided
translation for `(M, Ω)`. Then for all real `s, t`,
`Δ^{is} V(t) Δ^{-is} = V(e^{-2πs} t)` and `J V(t) J = V(-t)`.

This is Theorem II.9 of Borchers (Comm. Math. Phys. 143 (1992)).

Blueprint: thrm:borchers -/
theorem borchers {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsHalfSidedTranslation M Ω V) :
    (∀ s t : ℝ, U[s] ∘L V[t] ∘L U[-s] = V[Real.exp (-(2 * Real.pi * s)) * t]) ∧
      ∀ t : ℝ, 𝒥[V[t]] = V[-t] := by
  sorry

end Physicslib4.Modular
