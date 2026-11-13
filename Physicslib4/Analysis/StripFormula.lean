/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The strip formula and Fourier uniqueness

Two results of scalar analysis that van Daele's proof of Tomita's theorem uses.

* `strip_formula` — for f continuous and bounded on the closed strip
  S = {z | -1/2 ≤ Re z ≤ 1/2} and holomorphic on its interior,
  f(0) = ∫ (f(1/2 + it) + f(-1/2 + it)) / (2 cosh(πt)) dt
  (Exercise 13.2.1 of V. F. R. Jones, *von Neumann algebras*).
* `eq_zero_of_integral_exp_mul_eq_zero` — a continuous integrable h : ℝ → ℂ all of whose
  integrals ∫ e^{iθt} h(t) dt vanish is zero.

The proof of the strip formula applies the Cauchy theorem for rectangles to the strip quotient
`stripQuotient f` = dslope f 0 / dslope (sin (π ·)) 0 on [-1/2, 1/2] × [-T, T] and lets T → ∞.
The closed strip is written `Complex.re ⁻¹' Set.Icc (-1/2) (1/2)` and its interior
`Complex.re ⁻¹' Set.Ioo (-1/2) (1/2)`.
-/

namespace Physicslib4

open Complex MeasureTheory Filter Set
open scoped Real Topology Interval FourierTransform

/-- The strip quotient g = dslope f 0 / dslope (z ↦ sin(πz)) 0 of f.

Blueprint: def:strip-quotient -/
noncomputable def stripQuotient (f : ℂ → ℂ) : ℂ → ℂ :=
  dslope f 0 / dslope (fun z => Complex.sin (π * z)) 0

/-- The vertical side integral ∫_{-T}^{T} (f(σ + it) - f(0)) / cosh(πt) dt; the blueprint's
V₊(T) and V₋(T) are the cases σ = 1/2 and σ = -1/2.

Blueprint: def:strip-vertical-integrals -/
noncomputable def stripVerticalIntegral (f : ℂ → ℂ) (σ T : ℝ) : ℂ :=
  ∫ t in -T..T, (f (σ + t * I) - f 0) / (Real.cosh (π * t) : ℂ)

/-- The horizontal side integral H(T) = ∫_{-1/2}^{1/2} g(x + iT) dx - ∫_{-1/2}^{1/2} g(x - iT) dx
of the strip quotient g of f.

Blueprint: def:strip-horizontal-integral -/
noncomputable def stripHorizontalIntegral (f : ℂ → ℂ) (T : ℝ) : ℂ :=
  (∫ x in (-1/2 : ℝ)..1/2, stripQuotient f (x + T * I)) -
    ∫ x in (-1/2 : ℝ)..1/2, stripQuotient f (x - T * I)

/-- 1/cosh x ≤ 2 (1 + x²)⁻¹.

Blueprint: lmm:inv-cosh-le -/
theorem inv_cosh_le (x : ℝ) : 1 / Real.cosh x ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have ha : 0 ≤ |x| := abs_nonneg x
  have hexp : 1 + |x| ^ 2 ≤ Real.exp |x| := by
    have h := Real.sum_le_exp_of_nonneg ha 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    nlinarith [mul_nonneg ha (sq_nonneg (|x| - 3 / 2)), sq_abs x]
  have hc : (1 + x ^ 2) / 2 ≤ Real.cosh x := by
    rw [← Real.cosh_abs, Real.cosh_eq, ← sq_abs x]
    linarith [Real.exp_pos (-|x|)]
  rw [one_div, ← div_eq_mul_inv, ← inv_div]
  exact inv_anti₀ (by positivity) hc

/-- t ↦ 1/cosh t and t ↦ 1/cosh(πt) are integrable on ℝ.

Blueprint: lmm:inv-cosh-pi-integrable -/
theorem integrable_inv_cosh :
    Integrable (fun t : ℝ => 1 / Real.cosh t) ∧
      Integrable (fun t : ℝ => 1 / Real.cosh (π * t)) := by
  have h : Integrable (fun t : ℝ => 1 / Real.cosh t) :=
    (integrable_inv_one_add_sq.const_mul 2).mono'
      (continuous_const.div Real.continuous_cosh
        fun t => (Real.cosh_pos t).ne').aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg (by positivity)]; exact inv_cosh_le t)
  exact ⟨h, h.comp_mul_left' Real.pi_ne_zero⟩

/-- A continuous h : ℝ → ℂ with ‖h t‖ ≤ K / cosh(πt) is integrable.

Blueprint: lmm:cosh-dominated-integrable -/
theorem integrable_of_norm_le_div_cosh {h : ℝ → ℂ} (hc : Continuous h) (K : ℝ)
    (hK : ∀ t, ‖h t‖ ≤ K / Real.cosh (π * t)) : Integrable h :=
  (integrable_inv_cosh.2.const_mul K).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by rw [← div_eq_mul_one_div]; exact hK t)

/-- The derivative of t ↦ 2 arctan(eᵗ) is 1/cosh t.

Blueprint: lmm:hasDerivAt-two-arctan-exp -/
theorem hasDerivAt_two_mul_arctan_exp (t : ℝ) :
    HasDerivAt (fun t => 2 * Real.arctan (Real.exp t)) (1 / Real.cosh t) t := by
  refine (((Real.hasDerivAt_exp t).arctan).const_mul 2).congr_deriv ?_
  rw [Real.cosh_eq, Real.exp_neg]
  have := Real.exp_pos t
  field_simp
  ring

/-- ∫ dt / cosh t = π.

Blueprint: lmm:integral-inv-cosh -/
theorem integral_inv_cosh : ∫ t : ℝ, 1 / Real.cosh t = π := by
  have htop : Tendsto (fun t => 2 * Real.arctan (Real.exp t)) atTop (𝓝 (2 * (π / 2))) :=
    ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      Real.tendsto_exp_atTop).const_mul 2
  have hbot : Tendsto (fun t => 2 * Real.arctan (Real.exp t)) atBot (𝓝 (2 * Real.arctan 0)) :=
    ((Real.continuous_arctan.tendsto 0).comp Real.tendsto_exp_atBot).const_mul 2
  rw [integral_of_hasDerivAt_of_tendsto hasDerivAt_two_mul_arctan_exp integrable_inv_cosh.1
    hbot htop, Real.arctan_zero]
  ring

/-- ∫ dt / cosh(πt) = 1.

Blueprint: lmm:integral-inv-cosh-pi -/
theorem integral_inv_cosh_pi_mul : ∫ t : ℝ, 1 / Real.cosh (π * t) = 1 := by
  rw [MeasureTheory.Measure.integral_comp_mul_left (fun t => 1 / Real.cosh t) π,
    integral_inv_cosh, smul_eq_mul, abs_of_pos (inv_pos.2 Real.pi_pos),
    inv_mul_cancel₀ Real.pi_ne_zero]

/-- sin(π(1/2 + it)) = cosh(πt) and sin(π(-1/2 + it)) = -cosh(πt).

Blueprint: lmm:sin-strip-boundary -/
theorem sin_pi_mul_strip_boundary (t : ℝ) :
    Complex.sin (π * (1 / 2 + t * I)) = Real.cosh (π * t) ∧
      Complex.sin (π * (-1 / 2 + t * I)) = -Real.cosh (π * t) := by
  have h1 : (π : ℂ) * (1 / 2 + t * I) = (π / 2 : ℂ) + (π * t : ℝ) * I := by push_cast; ring
  have h2 : (π : ℂ) * (-1 / 2 + t * I) = -(π / 2 : ℂ) + (π * t : ℝ) * I := by push_cast; ring
  rw [h1, h2, Complex.sin_add_mul_I, Complex.sin_add_mul_I, Complex.sin_neg, Complex.cos_neg,
    Complex.sin_pi_div_two, Complex.cos_pi_div_two, ofReal_cosh]
  constructor <;> ring

/-- |y| ≤ ‖sin(x + iy)‖.

Blueprint: lmm:sin-norm-lower-bound -/
theorem abs_le_norm_sin_add_mul_I (x y : ℝ) : |y| ≤ ‖Complex.sin (x + y * I)‖ := by
  have hsh : |y| ≤ |Real.sinh y| := by
    rw [Real.abs_sinh]; exact Real.self_le_sinh_iff.mpr (abs_nonneg y)
  have hsq : y ^ 2 ≤ ‖Complex.sin (x + y * I)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sin_add_mul_I, ← ofReal_sin, ← ofReal_cosh, ← ofReal_cos,
      ← ofReal_sinh, ← ofReal_mul, ← ofReal_mul, normSq_add_mul_I]
    nlinarith [sq_le_sq.mpr hsh, Real.cosh_sq y, Real.sin_sq_add_cos_sq x, sq_nonneg (Real.sin x)]
  simpa using sq_le_sq.mp hsq

/-- The only zero of sin(πz) in the closed strip is z = 0.

Blueprint: lmm:sin-pi-zero-strip -/
theorem eq_zero_of_sin_pi_mul_eq_zero {z : ℂ} (hz : z ∈ re ⁻¹' Icc (-1 / 2) (1 / 2))
    (h : Complex.sin (π * z) = 0) : z = 0 := by
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hz' : z = k := by
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_left_cancel₀ hπ (by rw [hk]; ring)
  subst hz'
  simp only [Set.mem_preimage, Complex.intCast_re, Set.mem_Icc] at hz
  have h1 : (-1 : ℝ) < k := by linarith [hz.1]
  have h2 : (k : ℝ) < 1 := by linarith [hz.2]
  have : k = 0 := by
    have := Int.cast_lt.mp (by simpa using h1 : ((-1 : ℤ) : ℝ) < k)
    have := Int.cast_lt.mp (by simpa using h2 : (k : ℝ) < ((1 : ℤ) : ℝ))
    omega
  simp [this]

/-- Off 0 and off the zeros of sin(πz), the strip quotient is (f(z) - f(0)) / sin(πz); on the
lines Re z = ±1/2 it is ±(f(z) - f(0)) / cosh(πt).

Blueprint: lmm:strip-quotient-formula -/
theorem stripQuotient_eq (f : ℂ → ℂ) :
    (∀ z : ℂ, z ≠ 0 → Complex.sin (π * z) ≠ 0 →
        stripQuotient f z = (f z - f 0) / Complex.sin (π * z)) ∧
      ∀ t : ℝ,
        stripQuotient f (1 / 2 + t * I) = (f (1 / 2 + t * I) - f 0) / (Real.cosh (π * t) : ℂ) ∧
          stripQuotient f (-1 / 2 + t * I) =
            -((f (-1 / 2 + t * I) - f 0) / (Real.cosh (π * t) : ℂ)) := by
  have key : ∀ z : ℂ, z ≠ 0 → stripQuotient f z = (f z - f 0) / Complex.sin (π * z) := by
    intro z hz
    simp only [stripQuotient, Pi.div_apply, dslope_of_ne _ hz, slope_def_field, sub_zero,
      mul_zero, Complex.sin_zero]
    exact div_div_div_cancel_right₀ hz _ _
  refine ⟨fun z hz _ => key z hz, fun t => ?_⟩
  obtain ⟨h1, h2⟩ := sin_pi_mul_strip_boundary t
  have n1 : (1 / 2 + t * I : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; norm_num at this
  have n2 : (-1 / 2 + t * I : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; norm_num at this
  rw [key _ n1, key _ n2, h1, h2, div_neg]
  exact ⟨rfl, rfl⟩

/-- The denominator dslope (z ↦ sin(πz)) 0 of the strip quotient does not vanish on the strip.

Blueprint: lmm:strip-denominator-ne-zero -/
theorem dslope_sin_pi_mul_ne_zero {z : ℂ} (hz : z ∈ re ⁻¹' Icc (-1 / 2) (1 / 2)) :
    dslope (fun z => Complex.sin (π * z)) 0 z ≠ 0 := by
  rcases eq_or_ne z 0 with rfl | h0
  · have hd : HasDerivAt (fun z : ℂ => Complex.sin (π * z)) (Complex.cos (π * 0) * (π * 1)) 0 :=
      (Complex.hasDerivAt_sin _).comp 0 ((hasDerivAt_id _).const_mul _)
    rw [dslope_same, hd.deriv]
    simp [Real.pi_ne_zero]
  · rw [dslope_of_ne _ h0, slope_def_field, mul_zero, Complex.sin_zero, sub_zero, sub_zero]
    exact div_ne_zero (fun h => h0 (eq_zero_of_sin_pi_mul_eq_zero hz h)) h0

/-- The strip quotient of f is continuous on the closed strip and holomorphic on its interior.

Blueprint: lmm:strip-quotient-regular -/
theorem stripQuotient_regular {f : ℂ → ℂ} (hc : ContinuousOn f (re ⁻¹' Icc (-1 / 2) (1 / 2)))
    (hd : DifferentiableOn ℂ f (re ⁻¹' Ioo (-1 / 2) (1 / 2))) :
    ContinuousOn (stripQuotient f) (re ⁻¹' Icc (-1 / 2) (1 / 2)) ∧
      DifferentiableOn ℂ (stripQuotient f) (re ⁻¹' Ioo (-1 / 2) (1 / 2)) := by
  have hO : re ⁻¹' Ioo (-1 / 2 : ℝ) (1 / 2) ∈ 𝓝 (0 : ℂ) :=
    (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds (by norm_num)
  have hS : re ⁻¹' Icc (-1 / 2 : ℝ) (1 / 2) ∈ 𝓝 (0 : ℂ) :=
    mem_of_superset hO (preimage_mono Ioo_subset_Icc_self)
  have hs : Differentiable ℂ (fun z : ℂ => Complex.sin (π * z)) :=
    Complex.differentiable_sin.comp (differentiable_id.const_mul _)
  have hne := fun z hz => dslope_sin_pi_mul_ne_zero (z := z) hz
  refine ⟨((continuousOn_dslope hS).2 ⟨hc, hd.differentiableAt hO⟩).div
    ((continuousOn_dslope hS).2 ⟨hs.continuous.continuousOn, hs 0⟩) hne,
    ((Complex.differentiableOn_dslope hO).2 hd).div
    ((Complex.differentiableOn_dslope hO).2 hs.differentiableOn)
    fun z hz => hne z (Ioo_subset_Icc_self hz)⟩

/-- On the horizontal lines Im z = ±T, ‖g(x ± iT)‖ ≤ 2M / (πT).

Blueprint: lmm:strip-quotient-horizontal-bound -/
theorem norm_stripQuotient_horizontal_le {f : ℂ → ℂ} {M : ℝ}
    (hM : ∀ z ∈ re ⁻¹' Icc (-1 / 2) (1 / 2), ‖f z‖ ≤ M) {T : ℝ} (hT : 0 < T) {x : ℝ}
    (hx : x ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    ‖stripQuotient f (x + T * I)‖ ≤ 2 * M / (π * T) ∧
      ‖stripQuotient f (x - T * I)‖ ≤ 2 * M / (π * T) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num))
  have key : ∀ s : ℝ, |s| = T → ‖stripQuotient f (x + s * I)‖ ≤ 2 * M / (π * T) := by
    intro s hs
    have hz : (x + s * I : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.im h
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_im, zero_add] at this
      rw [this, abs_zero] at hs; linarith
    have hsin : π * T ≤ ‖Complex.sin (π * (x + s * I))‖ := by
      have h := abs_le_norm_sin_add_mul_I (π * x) (π * s)
      rw [abs_mul, abs_of_pos Real.pi_pos, hs] at h
      convert h using 3; push_cast; ring
    have hpos : 0 < π * T := mul_pos Real.pi_pos hT
    have hne : Complex.sin (π * (x + s * I)) ≠ 0 := fun h => by
      rw [h, norm_zero] at hsin; linarith
    have hnum : ‖f (x + s * I) - f 0‖ ≤ 2 * M := by
      have h1 := hM (x + s * I) (by simpa using hx)
      have h2 := hM 0 (by norm_num)
      linarith [norm_sub_le (f (x + s * I)) (f 0)]
    rw [(stripQuotient_eq f).1 _ hz hne, norm_div]
    exact div_le_div₀ (by linarith) hnum hpos hsin
  refine ⟨key T (abs_of_pos hT), ?_⟩
  have := key (-T) (by rw [abs_neg, abs_of_pos hT])
  simpa [sub_eq_add_neg] using this

/-- The closed rectangle with corners -1/2 - iT and 1/2 + iT lies in the closed strip and the
open rectangle in the open strip, in the form Mathlib's rectangle Cauchy theorem uses.

Blueprint: lmm:strip-rectangle-subset -/
theorem strip_rectangle_subset {T : ℝ} (hT : 0 < T) :
    [[(-1 / 2 - T * I : ℂ).re, (1 / 2 + T * I : ℂ).re]] ×ℂ
        [[(-1 / 2 - T * I : ℂ).im, (1 / 2 + T * I : ℂ).im]] ⊆ re ⁻¹' Icc (-1 / 2) (1 / 2) ∧
      Ioo (min (-1 / 2 - T * I : ℂ).re (1 / 2 + T * I : ℂ).re)
          (max (-1 / 2 - T * I : ℂ).re (1 / 2 + T * I : ℂ).re) ×ℂ
        Ioo (min (-1 / 2 - T * I : ℂ).im (1 / 2 + T * I : ℂ).im)
          (max (-1 / 2 - T * I : ℂ).im (1 / 2 + T * I : ℂ).im) ⊆
        re ⁻¹' Ioo (-1 / 2) (1 / 2) := by
  have hre₁ : (-1 / 2 - T * I : ℂ).re = -1 / 2 := by simp
  have hre₂ : (1 / 2 + T * I : ℂ).re = 1 / 2 := by simp
  have hle : (-1 / 2 : ℝ) ≤ 1 / 2 := by norm_num
  rw [hre₁, hre₂, uIcc_of_le hle, min_eq_left hle, max_eq_right hle]
  exact ⟨fun z hz => (mem_reProdIm.1 hz).1, fun z hz => (mem_reProdIm.1 hz).1⟩

/-- The vertical sides of the rectangle: ∫_{-T}^{T} g(1/2 + it) dt = V₊(T) and
∫_{-T}^{T} g(-1/2 + it) dt = -V₋(T).

Blueprint: lmm:strip-vertical-sides -/
theorem integral_stripQuotient_vertical (f : ℂ → ℂ) (T : ℝ) :
    (∫ t in -T..T, stripQuotient f (1 / 2 + t * I)) = stripVerticalIntegral f (1 / 2) T ∧
      (∫ t in -T..T, stripQuotient f (-1 / 2 + t * I)) =
        -stripVerticalIntegral f (-1 / 2) T := by
  simp only [stripVerticalIntegral, (stripQuotient_eq f).2, intervalIntegral.integral_neg]
  push_cast
  exact ⟨rfl, rfl⟩

/-- The rectangle identity i (V₊(T) + V₋(T)) = H(T).

Blueprint: lmm:strip-rectangle-identity -/
theorem strip_rectangle_identity {f : ℂ → ℂ}
    (hc : ContinuousOn f (re ⁻¹' Icc (-1 / 2) (1 / 2)))
    (hd : DifferentiableOn ℂ f (re ⁻¹' Ioo (-1 / 2) (1 / 2))) {T : ℝ} (hT : 0 < T) :
    I * (stripVerticalIntegral f (1 / 2) T + stripVerticalIntegral f (-1 / 2) T) =
      stripHorizontalIntegral f T := by
  sorry

/-- The horizontal side integral H(T) tends to 0 as T → ∞.

Blueprint: lmm:strip-horizontal-vanish -/
theorem tendsto_stripHorizontalIntegral {f : ℂ → ℂ} {M : ℝ}
    (hM : ∀ z ∈ re ⁻¹' Icc (-1 / 2) (1 / 2), ‖f z‖ ≤ M) :
    Tendsto (stripHorizontalIntegral f) atTop (𝓝 0) := by
  sorry

/-- t ↦ (f(±1/2 + it) - f(0)) / cosh(πt) and t ↦ f(±1/2 + it) / cosh(πt) are integrable.

Blueprint: lmm:strip-boundary-integrable -/
theorem strip_boundary_integrable {f : ℂ → ℂ} {M : ℝ}
    (hc : ContinuousOn f (re ⁻¹' Icc (-1 / 2) (1 / 2)))
    (hM : ∀ z ∈ re ⁻¹' Icc (-1 / 2) (1 / 2), ‖f z‖ ≤ M) :
    Integrable (fun t : ℝ => (f (1 / 2 + t * I) - f 0) / (Real.cosh (π * t) : ℂ)) ∧
      Integrable (fun t : ℝ => f (1 / 2 + t * I) / (Real.cosh (π * t) : ℂ)) ∧
      Integrable (fun t : ℝ => (f (-1 / 2 + t * I) - f 0) / (Real.cosh (π * t) : ℂ)) ∧
      Integrable (fun t : ℝ => f (-1 / 2 + t * I) / (Real.cosh (π * t) : ℂ)) := by
  sorry

/-- V₊(T) + V₋(T) converges to the sum of the two boundary integrals over ℝ as T → ∞.

Blueprint: lmm:strip-vertical-limit -/
theorem tendsto_stripVerticalIntegral {f : ℂ → ℂ} {M : ℝ}
    (hc : ContinuousOn f (re ⁻¹' Icc (-1 / 2) (1 / 2)))
    (hM : ∀ z ∈ re ⁻¹' Icc (-1 / 2) (1 / 2), ‖f z‖ ≤ M) :
    Tendsto (fun T => stripVerticalIntegral f (1 / 2) T + stripVerticalIntegral f (-1 / 2) T)
      atTop
      (𝓝 ((∫ t : ℝ, (f (1 / 2 + t * I) - f 0) / (Real.cosh (π * t) : ℂ)) +
        ∫ t : ℝ, (f (-1 / 2 + t * I) - f 0) / (Real.cosh (π * t) : ℂ))) := by
  sorry

/-- The two boundary integrals of (f(±1/2 + it) - f(0)) / cosh(πt) sum to 0.

Blueprint: lmm:strip-boundary-integral-zero -/
theorem strip_boundary_integral_eq_zero {f : ℂ → ℂ} {M : ℝ}
    (hc : ContinuousOn f (re ⁻¹' Icc (-1 / 2) (1 / 2)))
    (hd : DifferentiableOn ℂ f (re ⁻¹' Ioo (-1 / 2) (1 / 2)))
    (hM : ∀ z ∈ re ⁻¹' Icc (-1 / 2) (1 / 2), ‖f z‖ ≤ M) :
    (∫ t : ℝ, (f (1 / 2 + t * I) - f 0) / (Real.cosh (π * t) : ℂ)) +
      ∫ t : ℝ, (f (-1 / 2 + t * I) - f 0) / (Real.cosh (π * t) : ℂ) = 0 := by
  sorry

/-- ∫ (f(±1/2 + it) - f(0)) / cosh(πt) dt = ∫ f(±1/2 + it) / cosh(πt) dt - f(0).

Blueprint: lmm:strip-boundary-split -/
theorem strip_boundary_integral_sub {f : ℂ → ℂ} {M : ℝ}
    (hc : ContinuousOn f (re ⁻¹' Icc (-1 / 2) (1 / 2)))
    (hM : ∀ z ∈ re ⁻¹' Icc (-1 / 2) (1 / 2), ‖f z‖ ≤ M) :
    (∫ t : ℝ, (f (1 / 2 + t * I) - f 0) / (Real.cosh (π * t) : ℂ)) =
        (∫ t : ℝ, f (1 / 2 + t * I) / (Real.cosh (π * t) : ℂ)) - f 0 ∧
      (∫ t : ℝ, (f (-1 / 2 + t * I) - f 0) / (Real.cosh (π * t) : ℂ)) =
        (∫ t : ℝ, f (-1 / 2 + t * I) / (Real.cosh (π * t) : ℂ)) - f 0 := by
  sorry

/-- The strip formula: for f continuous and bounded on the closed strip and holomorphic on its
interior, f(0) = ∫ (f(1/2 + it) + f(-1/2 + it)) / (2 cosh(πt)) dt.

Blueprint: thrm:strip-formula -/
theorem strip_formula {f : ℂ → ℂ} (hc : ContinuousOn f (re ⁻¹' Icc (-1 / 2) (1 / 2)))
    (hd : DifferentiableOn ℂ f (re ⁻¹' Ioo (-1 / 2) (1 / 2)))
    (hb : ∃ M, ∀ z ∈ re ⁻¹' Icc (-1 / 2) (1 / 2), ‖f z‖ ≤ M) :
    f 0 = ∫ t : ℝ, (f (1 / 2 + t * I) + f (-1 / 2 + t * I)) / (2 * (Real.cosh (π * t) : ℂ)) := by
  sorry

/-- If ∫ e^{iθt} h(t) dt = 0 for every θ, the Fourier transform of h vanishes.

Blueprint: lmm:fourier-transform-eq-zero -/
theorem fourier_eq_zero_of_integral_exp_mul_eq_zero {h : ℝ → ℂ}
    (hh : ∀ θ : ℝ, ∫ t : ℝ, Complex.exp (θ * t * I) * h t = 0) : 𝓕 h = 0 := by
  funext w
  rw [Real.fourier_real_eq_integral_exp_smul, Pi.zero_apply, ← hh (-2 * π * w)]
  congr 1; ext v
  rw [smul_eq_mul]; push_cast; ring_nf

/-- Fourier uniqueness: a continuous integrable h : ℝ → ℂ with ∫ e^{iθt} h(t) dt = 0 for every
θ is zero.

Blueprint: thrm:fourier-uniqueness -/
theorem eq_zero_of_integral_exp_mul_eq_zero {h : ℝ → ℂ} (hc : Continuous h) (hi : Integrable h)
    (hh : ∀ θ : ℝ, ∫ t : ℝ, Complex.exp (θ * t * I) * h t = 0) : h = 0 := by
  have h0 := fourier_eq_zero_of_integral_exp_mul_eq_zero hh
  rw [← hc.fourierInv_fourier_eq hi (h0 ▸ integrable_zero _ _ _), h0]
  funext v
  simp [Real.fourierInv_eq]

end Physicslib4
