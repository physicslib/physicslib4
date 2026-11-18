/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.PositiveEnergy
import Physicslib4.AQFT.KMS
import Physicslib4.AQFT.PositiveEnergyHolomorphic

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
  have key : ∀ b : ℝ, 0 < b → x * Real.exp (-(b * x)) ≤ 1 / (b * Real.exp 1) := by
    intro b hb
    have h1 := Real.add_one_le_exp (b * x - 1)
    rw [Real.exp_sub] at h1
    have h2 := (le_div_iff₀ (Real.exp_pos 1)).1
      (by linarith : b * x ≤ Real.exp (b * x) / Real.exp 1)
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    nlinarith
  refine ⟨key a ha, ?_⟩
  have h3 : x ^ 2 * Real.exp (-(a * x)) = (x * Real.exp (-(a / 2 * x))) ^ 2 := by
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; ring_nf
  have h4 := pow_le_pow_left₀ (by positivity) (key (a / 2) (by positivity)) 2
  rw [h3]
  refine h4.trans (le_of_eq ?_)
  field_simp
  ring

/-- `ε_w` and `δ_w` are measurable; `|ε_w| ≤ 1` if `Im w ≥ 0`; and `|δ_w| ≤ 1/(ce)` if
`c = Im w > 0`.

Blueprint: lmm:half-plane-exp-bounds -/
theorem halfPlaneExp_bounds (w : ℂ) :
    Measurable ε[w] ∧ Measurable δ[w] ∧ (0 ≤ w.im → ∀ x : ℝ, ‖ε[w] x‖ ≤ 1) ∧
      (0 < w.im → ∀ x : ℝ, ‖δ[w] x‖ ≤ 1 / (w.im * Real.exp 1)) := by
  have hre : ∀ x : ℝ, (Complex.I * w * (x : ℂ)).re = -(w.im * x) := fun x => by
    simp [Complex.mul_re]
  refine ⟨(by fun_prop : Measurable _).indicator measurableSet_Ici,
    (by fun_prop : Measurable _).indicator measurableSet_Ici, fun hw x => ?_, fun hw x => ?_⟩
  · by_cases hx : x ∈ Set.Ici (0 : ℝ)
    · rw [Set.indicator_of_mem hx, Complex.norm_exp, hre, Real.exp_le_one_iff, neg_nonpos]
      exact mul_nonneg hw hx
    · rw [Set.indicator_of_notMem hx, norm_zero]; exact zero_le_one
  · by_cases hx : x ∈ Set.Ici (0 : ℝ)
    · rw [Set.indicator_of_mem hx, norm_mul, norm_mul, Complex.norm_exp, hre, Complex.norm_I,
        one_mul, Complex.norm_real, Real.norm_of_nonneg hx]
      exact (mul_exp_neg_le hw hx).1
    · rw [Set.indicator_of_notMem hx, norm_zero]; positivity

/-- The Taylor estimate: for `c = Im w > 0` and `|h| ≤ c/2`,
`|ε_{w+h}(λ) - ε_w(λ) - h δ_w(λ)| ≤ 16|h|²/(ce)²` for every `λ`.

Blueprint: lmm:half-plane-exp-taylor -/
theorem halfPlaneExp_taylor {w h : ℂ} (hw : 0 < w.im) (hh : ‖h‖ ≤ w.im / 2) (x : ℝ) :
    ‖ε[w + h] x - ε[w] x - h * δ[w] x‖ ≤ 16 / (w.im * Real.exp 1) ^ 2 * ‖h‖ ^ 2 := by
  by_cases hx : 0 ≤ x
  · simp only [Set.indicator_of_mem (Set.mem_Ici.2 hx)]
    set u := Complex.I * h * (x : ℂ) with hu_def
    have key : Complex.exp (Complex.I * (w + h) * x) - Complex.exp (Complex.I * w * x) -
        h * (Complex.I * x * Complex.exp (Complex.I * w * x)) =
        Complex.exp (Complex.I * w * x) * (Complex.exp u - 1 - u) := by
      rw [show Complex.I * (w + h) * x = Complex.I * w * x + u by ring, Complex.exp_add]; ring
    rw [key, norm_mul, Complex.norm_exp]
    have hre : (Complex.I * w * x).re = -(w.im * x) := by simp
    have hu : ‖u‖ = ‖h‖ * x := by simp [u, abs_of_nonneg hx]
    have hr : ‖Complex.exp u - 1 - u‖ ≤ ‖u‖ ^ 2 * Real.exp ‖u‖ := by
      have := Complex.norm_exp_sub_sum_le_norm_mul_exp u 2
      simpa [Finset.sum_range_succ, sub_sub] using this
    rw [hre, hu] at *
    have hb := (mul_exp_neg_le (a := w.im / 2) (by positivity) hx).2
    have he : Real.exp (-(w.im * x)) * Real.exp (‖h‖ * x) ≤ Real.exp (-(w.im / 2 * x)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
    calc Real.exp (-(w.im * x)) * ‖Complex.exp u - 1 - u‖
        ≤ Real.exp (-(w.im * x)) * ((‖h‖ * x) ^ 2 * Real.exp (‖h‖ * x)) :=
          mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le
      _ = ‖h‖ ^ 2 * (x ^ 2 * (Real.exp (-(w.im * x)) * Real.exp (‖h‖ * x))) := by ring
      _ ≤ ‖h‖ ^ 2 * (x ^ 2 * Real.exp (-(w.im / 2 * x))) := by gcongr
      _ ≤ ‖h‖ ^ 2 * (4 / (w.im / 2 * Real.exp 1) ^ 2) := by gcongr
      _ = 16 / (w.im * Real.exp 1) ^ 2 * ‖h‖ ^ 2 := by field_simp; ring
  · simp only [Set.indicator_of_notMem (show x ∉ Set.Ici (0 : ℝ) from hx), sub_zero, mul_zero,
      norm_zero]
    positivity

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
  have hbdd : ∀ w : ℂ, 0 ≤ w.im → ε[w] ∈ Spectral.BddMeasurable ℝ := fun w hw =>
    ⟨(halfPlaneExp_bounds w).1, 1, (halfPlaneExp_bounds w).2.2.1 hw⟩
  refine ⟨fun w hw => ⟨(Spectral.ProjectionValuedMeasure.norm_integral_le _ (hbdd w hw)).trans
    (ciSup_le ((halfPlaneExp_bounds w).2.2.1 hw)), fun ψ => ?_⟩, fun t => ?_⟩
  · obtain ⟨hd, he⟩ := Spectral.Unbounded.functionalCalculus_of_bddMeasurable Psa (hbdd w hw)
    exact ⟨hd ▸ Submodule.mem_top, (LinearPMap.ext_iff.1 he).2 (hg := Submodule.mem_top)⟩
  · have hpm := Spectral.Unbounded.pmapIntegral_congr_of_null μP (halfPlaneExp_bounds t).1
      (expFun_mem_bddMeasurable t).1 measurableSet_Iio
      (spectralMeasure_Iio_zero_eq_zero _ hV.isPositive_generator) fun x hx => by
        rw [Set.indicator_of_mem (Set.mem_Ici.2 (not_lt.1 hx)), expFun]
        push_cast; ring_nf
    rw [Spectral.Unbounded.pmapIntegral_of_bddMeasurable _ (hbdd t (by simp)),
      Spectral.Unbounded.pmapIntegral_of_bddMeasurable _ (expFun_mem_bddMeasurable t)] at hpm
    ext ψ
    rw [(stone hV.isOneParameterUnitaryGroup hV.isStronglyContinuous).snd.2.1 t]
    exact (LinearPMap.ext_iff.1 hpm).2 (x := ψ) (hf := Submodule.mem_top)
      (hg := Submodule.mem_top)

/-- On the open upper half-plane, `w ↦ Ṽ(w)` is complex differentiable in the operator norm,
with derivative `δ_w(P)`.

Blueprint: lmm:positive-energy-extension-holomorphic -/
theorem hasDerivAt_positiveEnergyExtension {V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hV : IsPositiveEnergy V)
    {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (fun w' : ℂ => Ṽ[w']) ((μP).integral δ[w]) w := by
  have hbdd : ∀ w' : ℂ, 0 ≤ w'.im → ε[w'] ∈ Spectral.BddMeasurable ℝ := fun w' hw' =>
    ⟨(halfPlaneExp_bounds w').1, 1, (halfPlaneExp_bounds w').2.2.1 hw'⟩
  have hδ : δ[w] ∈ Spectral.BddMeasurable ℝ :=
    ⟨(halfPlaneExp_bounds w).2.1, _, (halfPlaneExp_bounds w).2.2.2 hw⟩
  set C := 16 / (w.im * Real.exp 1) ^ 2
  have key : ∀ h : ℂ, ‖h‖ ≤ w.im / 2 →
      ‖Ṽ[w + h] - Ṽ[w] - h • (μP).integral δ[w]‖ ≤ C * ‖h ^ 2‖ := by
    intro h hh
    have hwh : 0 ≤ (w + h).im := by
      have := Complex.abs_im_le_norm h
      rw [Complex.add_im]; linarith [abs_le.1 this]
    have hmem := (Spectral.BddMeasurable ℝ).sub_mem
      ((Spectral.BddMeasurable ℝ).sub_mem (hbdd _ hwh) (hbdd _ hw.le))
      ((Spectral.BddMeasurable ℝ).smul_mem h hδ)
    have hsub : ∀ f g : ℝ → ℂ, f ∈ Spectral.BddMeasurable ℝ → g ∈ Spectral.BddMeasurable ℝ →
        (μP).integral (f - g) = (μP).integral f - (μP).integral g := by
      intro f g hf hg
      have h1 := Spectral.ProjectionValuedMeasure.integral_add (μP)
        ((Spectral.BddMeasurable ℝ).sub_mem hf hg) hg
      rw [sub_add_cancel] at h1
      rw [h1, add_sub_cancel_right]
    rw [← Spectral.ProjectionValuedMeasure.integral_smul _ _ hδ,
      ← hsub _ _ (hbdd _ hwh) (hbdd _ hw.le),
      ← hsub _ _ ((Spectral.BddMeasurable ℝ).sub_mem (hbdd _ hwh) (hbdd _ hw.le))
        ((Spectral.BddMeasurable ℝ).smul_mem h hδ)]
    refine (Spectral.ProjectionValuedMeasure.norm_integral_le _ hmem).trans (ciSup_le fun x => ?_)
    rw [norm_pow]
    exact halfPlaneExp_taylor hw hh x
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) (half_pos hw)] with h hh
  exact key h (by simpa using hh)

/-- For every `ψ`, `w ↦ Ṽ(w)ψ` is continuous on the closed upper half-plane.

Blueprint: lmm:positive-energy-extension-strongly-continuous -/
theorem continuousOn_positiveEnergyExtension_apply {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : IsPositiveEnergy V) (ψ : H) :
    ContinuousOn (fun w : ℂ => Ṽ[w] ψ) {w : ℂ | 0 ≤ w.im} := by
  have hbdd : ∀ w : ℂ, 0 ≤ w.im → ε[w] ∈ Spectral.BddMeasurable ℝ := fun w hw =>
    ⟨(halfPlaneExp_bounds w).1, 1, (halfPlaneExp_bounds w).2.2.1 hw⟩
  intro w₀ hw₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Filter.Tendsto (fun w : ℂ => ‖Ṽ[w] ψ - Ṽ[w₀] ψ‖ ^ 2)
      (nhdsWithin w₀ {w : ℂ | 0 ≤ w.im}) (nhds 0) := by
    have hev : ∀ᶠ w in nhdsWithin w₀ {w : ℂ | 0 ≤ w.im}, ‖Ṽ[w] ψ - Ṽ[w₀] ψ‖ ^ 2 =
        ∫ x, ‖ε[w] x - ε[w₀] x‖ ^ 2 ∂((μP).assoc ψ) := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hsub : (μP).integral (ε[w] + (-1 : ℂ) • ε[w₀]) = Ṽ[w] - Ṽ[w₀] := by
        rw [Spectral.ProjectionValuedMeasure.integral_add _ (hbdd w hw)
          ((Spectral.BddMeasurable ℝ).smul_mem _ (hbdd w₀ hw₀)),
          Spectral.ProjectionValuedMeasure.integral_smul _ _ (hbdd w₀ hw₀), neg_one_smul,
          ← sub_eq_add_neg]
      rw [← sub_apply, ← hsub, Spectral.Unbounded.norm_sq_integral_apply _
        ((Spectral.BddMeasurable ℝ).add_mem (hbdd w hw)
          ((Spectral.BddMeasurable ℝ).smul_mem _ (hbdd w₀ hw₀)))]
      simp [sub_eq_add_neg]
    refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) ?_
    have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := (μP).assoc ψ) (l := nhdsWithin w₀ {w : ℂ | 0 ≤ w.im})
      (F := fun w x => ‖ε[w] x - ε[w₀] x‖ ^ 2) (f := fun x => ‖ε[w₀] x - ε[w₀] x‖ ^ 2)
      (fun _ => 4) ?_ ?_ (MeasureTheory.integrable_const _) ?_
    · rwa [show (∫ x, ‖ε[w₀] x - ε[w₀] x‖ ^ 2 ∂((μP).assoc ψ)) = 0 by simp] at hlim
    · exact Filter.Eventually.of_forall fun w => (((halfPlaneExp_bounds w).1.sub
        (halfPlaneExp_bounds w₀).1).norm.pow_const 2).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with w hw
      refine MeasureTheory.ae_of_all _ fun x => ?_
      have h1 := (halfPlaneExp_bounds w).2.2.1 hw x
      have h2 := (halfPlaneExp_bounds w₀).2.2.1 hw₀ x
      have h3 : ‖ε[w] x - ε[w₀] x‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith [norm_nonneg (ε[w] x - ε[w₀] x)]
    · refine MeasureTheory.ae_of_all _ fun x => ?_
      have hc : Continuous fun w : ℂ => ε[w] x := by
        by_cases hx : x ∈ Set.Ici (0 : ℝ)
        · simp only [Set.indicator_of_mem hx]; fun_prop
        · simp only [Set.indicator_of_notMem hx]; fun_prop
      exact (((hc.sub continuous_const).norm.pow 2).tendsto w₀).mono_left nhdsWithin_le_nhds
  simpa [Real.sqrt_sq (norm_nonneg _)] using hsq.sqrt

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
  have him (z : ℂ) : ((τ : ℂ) * Complex.exp (2 * Real.pi * z)).im =
      τ * (Real.exp (2 * Real.pi * z.re) * Real.sin (2 * Real.pi * z.im)) := by
    rw [Complex.im_ofReal_mul, Complex.exp_im]; simp
  refine ⟨fun z hz => ?_, fun hτ' z hz => ?_, fun t => ?_⟩
  · rw [him]
    exact mul_nonneg hτ (mul_nonneg (Real.exp_pos _).le
      (Real.sin_nonneg_of_nonneg_of_le_pi (by have := hz.1; positivity)
        (by have := hz.2; nlinarith [Real.pi_pos])))
  · rw [him]
    exact mul_pos hτ' (mul_pos (Real.exp_pos _)
      (Real.sin_pos_of_pos_of_lt_pi (by have := hz.1; positivity)
        (by have := hz.2; nlinarith [Real.pi_pos])))
  · have h : 2 * (Real.pi : ℂ) * ((t : ℂ) + Complex.I / 2) =
        ((2 * Real.pi * t : ℝ) : ℂ) + Real.pi * Complex.I := by push_cast; ring
    rw [h, Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp]
    push_cast; ring

/-- For `τ ≥ 0`, `z ↦ Ṽ(τ e^{2πz})` is complex differentiable in the operator norm on the open
strip `0 < Im z < 1/2`, and `z ↦ Ṽ(τ e^{2πz})ψ` is continuous on the closed strip for every `ψ`.

Blueprint: lmm:dilated-extension-analytic -/
theorem dilatedPositiveEnergyExtension_analytic {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : IsPositiveEnergy V) {τ : ℝ} (hτ : 0 ≤ τ) :
    (∀ z ∈ kmsStripInterior (1 / 2),
      DifferentiableAt ℂ (fun z' : ℂ => Ṽ[(τ : ℂ) * Complex.exp (2 * Real.pi * z')]) z) ∧
      ∀ ψ : H, ContinuousOn (fun z : ℂ => Ṽ[(τ : ℂ) * Complex.exp (2 * Real.pi * z)] ψ)
        (kmsStrip (1 / 2)) := by
  refine ⟨fun z hz => ?_, fun ψ => ?_⟩
  · rcases hτ.eq_or_lt with h0 | hpos
    · subst h0; simp
    · have hd : DifferentiableAt ℂ (fun z' : ℂ => (τ : ℂ) * Complex.exp (2 * Real.pi * z')) z := by
        fun_prop
      exact (hasDerivAt_positiveEnergyExtension hV
        ((dilation_strip_halfPlane hτ).2.1 hpos z hz)).differentiableAt.comp z hd
  · exact (continuousOn_positiveEnergyExtension_apply hV ψ).comp (by fun_prop)
      fun z hz => (dilation_strip_halfPlane hτ).1 z hz

end AQFT
end Physicslib4
