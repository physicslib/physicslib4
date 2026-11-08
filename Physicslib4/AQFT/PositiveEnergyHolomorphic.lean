/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.AQFT.PositiveEnergy
import Physicslib4.Spectral.Stone.Exponential
import Physicslib4.Spectral.Unbounded.FunctionalCalculus
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Holomorphic extension under positive energy

If a one-parameter unitary group V has positive energy, every matrix coefficient
t ↦ ⟨χ, V(t)φ⟩ extends to a function holomorphic on the open upper half-plane and bounded and
continuous on the closed upper half-plane (`IsPositiveEnergy.exists_holomorphic_extension`).
This is the form in which the Reeh–Schlieder theorem uses the spectrum condition.

The route is spectral. Writing V(t) = e^(itA) with A positive and self-adjoint, the spectral
measure of A vanishes on (−∞, 0) (`spectralMeasure_Iio_zero_eq_zero`), each matrix coefficient
is a combination of Fourier transforms of finite measures μ^A_ψ by polarization
(`exists_inner_expUnitary_eq_sum`), and the Fourier–Laplace transform z ↦ ∫ e^(izλ) dν(λ) of a
finite measure carried by [0, ∞) is bounded and continuous on {Im z ≥ 0}
(`fourierLaplace_bounded_continuousOn`) and holomorphic on {Im z > 0}
(`differentiableOn_fourierLaplace`).

## Main results

* `spectralMeasure_Ioo_neg_eq_zero` — μ^A((−n, −1/n)) = 0 for A positive.
* `spectralMeasure_Iio_zero_eq_zero` — μ^A((−∞, 0)) = 0 for A positive.
* `exists_inner_expUnitary_eq_sum` — matrix coefficients of e^(itA) by polarization.
* `fourierLaplace_bounded_continuousOn` — the Fourier–Laplace transform on {Im z ≥ 0}.
* `differentiableOn_fourierLaplace` — the Fourier–Laplace transform on {Im z > 0}.
* `IsPositiveEnergy.exists_holomorphic_extension` — the holomorphic extension.
-/

namespace Physicslib4
namespace AQFT

open scoped InnerProductSpace
open MeasureTheory Complex Spectral Spectral.Stone

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
The spectral measure μ^A of a positive self-adjoint operator A vanishes on (−n, −1/n) for
every integer n ≥ 1.

A vector ψ in the range of μ^A((−n, −1/n)) has its distribution μ^A_ψ concentrated on
(−n, −1/n), so ψ lies in Dom(A) with ⟨ψ, Aψ⟩ ≤ −‖ψ‖²/n; positivity of A forces ψ = 0.

Implementation note: μ^A is `Spectral.Unbounded.spectralMeasure hA`, a projection-valued
measure on ℝ, and the integer n ≥ 1 is a natural number with `1 ≤ n`.

Blueprint: lmm:positive-spectral-support-interval
-/
theorem spectralMeasure_Ioo_neg_eq_zero {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hpos : Unbounded.IsPositive A) (n : ℕ) (hn : 1 ≤ n) :
    Unbounded.spectralMeasure hA (Set.Ioo (-(n : ℝ)) (-(1 / (n : ℝ)))) = 0 := by
  set μ := Unbounded.spectralMeasure hA
  set E := Set.Ioo (-(n : ℝ)) (-(1 / (n : ℝ)))
  have hE : MeasurableSet E := measurableSet_Ioo
  have hf : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
  have hpos' : Unbounded.IsPositive (Unbounded.pmapIntegral μ (fun x : ℝ => (x : ℂ))) :=
    (Unbounded.pmapIntegral_spectralMeasure hA).symm ▸ hpos
  have hn' : (0 : ℝ) < 1 / n := by positivity
  ext ψ
  set η := μ E ψ
  have hη : η ∈ Set.range (μ E) := ⟨ψ, rfl⟩
  have hdom := Unbounded.range_subset_integralDomain μ hf hE (c := n) (fun x hx => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨hx.1.le, hx.2.le.trans (by linarith)⟩) hη
  have h1 : 0 ≤ (∫ x, (x : ℂ) ∂(μ.assoc η)).re := (hpos'.2 ⟨η, hdom⟩).trans_eq
    (congrArg Complex.re (Unbounded.inner_self_pmapIntegral μ hf ⟨η, hdom⟩))
  have hae : ∀ᵐ x ∂(μ.assoc η), x ∈ E :=
    (ae_iff (p := fun x => x ∈ E)).mpr (Unbounded.assoc_compl_eq_zero μ hE hη)
  have hint : Integrable (fun x : ℝ => x) (μ.assoc η) := by
    simpa using (MemLp.integrable one_le_two (Unbounded.mem_integralDomain μ |>.mp hdom)).re
  have h2 : ∫ x, x ∂(μ.assoc η) ≤ ∫ _, -(1 / (n : ℝ)) ∂(μ.assoc η) :=
    integral_mono_ae hint (integrable_const _) (hae.mono fun x hx => hx.2.le)
  rw [integral_const, smul_eq_mul, measureReal_def, Unbounded.assoc_univ_eq,
    ENNReal.toReal_ofReal (by positivity)] at h2
  have h3 : (∫ x, (x : ℂ) ∂(μ.assoc η)).re = ∫ x, x ∂(μ.assoc η) := by
    rw [integral_complex_ofReal]; rfl
  simp only [h3] at h1
  have : ‖η‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖η‖]
  simpa using this

/--
The spectral measure μ^A of a positive self-adjoint operator A vanishes on (−∞, 0): the
spectrum of A lies in [0, ∞).

The intervals (−n, −1/n) increase to (−∞, 0), and each carries no spectral weight
(`spectralMeasure_Ioo_neg_eq_zero`), so ⟨ψ, μ^A((−∞, 0))ψ⟩ = 0 for every ψ by continuity of the
measure μ^A_ψ from below; the projection μ^A((−∞, 0)) is therefore zero.

Blueprint: lmm:positive-spectral-support
-/
theorem spectralMeasure_Iio_zero_eq_zero {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hpos : Unbounded.IsPositive A) :
    Unbounded.spectralMeasure hA (Set.Iio 0) = 0 := by
  set μ := Unbounded.spectralMeasure hA
  ext ψ
  have hU : Set.Iio (0 : ℝ) ⊆
      ⋃ n : ℕ, Set.Ioo (-((n + 1 : ℕ) : ℝ)) (-(1 / ((n + 1 : ℕ) : ℝ))) := by
    intro x (hx : x < 0)
    obtain ⟨n, hn⟩ := exists_nat_gt (-x + 1 / (-x))
    have hx' : 0 < 1 / (-x) := one_div_pos.2 (neg_pos.2 hx)
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    refine Set.mem_iUnion.2 ⟨n, ?_, ?_⟩ <;> push_cast at hn1 ⊢
    · linarith
    · have : 1 / (n + 1 : ℝ) < -x := (one_div_lt hn1 (by linarith)).2 (by linarith)
      linarith
  have h0 : μ.assoc ψ (Set.Iio 0) = 0 := measure_mono_null hU (measure_iUnion_null fun n => by
    rw [Unbounded.assoc_apply_eq_norm_sq μ ψ measurableSet_Ioo,
      spectralMeasure_Ioo_neg_eq_zero hA hpos (n + 1) (by omega)]
    simp)
  rw [Unbounded.assoc_apply_eq_norm_sq μ ψ measurableSet_Iio, ENNReal.ofReal_eq_zero] at h0
  have : ‖μ (Set.Iio 0) ψ‖ = 0 := by nlinarith [norm_nonneg (μ (Set.Iio 0) ψ)]
  simpa using this

/--
For a self-adjoint operator A and vectors χ, φ, the matrix coefficient ⟨χ, e^(itA)φ⟩ is a fixed
linear combination of the Fourier transforms ∫ e^(itλ) dμ^A_ψₖ(λ) of four scalar spectral
measures, with vectors ψ₀, …, ψ₃ and constants c₀, …, c₃ independent of t.

The vectors are ψₖ = χ + iᵏφ with the constants of the polarization identity, and each
diagonal term ⟨ψₖ, e^(itA)ψₖ⟩ is ∫ e^(itλ) dμ^A_ψₖ because e^(itA) = ∫ e^(itλ) dμ^A.

Implementation note: e^(itA) is `expUnitary hA t`, and μ^A_ψ is
`(Spectral.Unbounded.spectralMeasure hA).assoc ψ`, the finite measure E ↦ ⟨ψ, μ^A(E)ψ⟩. The
integrand e^(itλ) is written `Complex.exp (Complex.I * t * x)`.

Blueprint: lmm:exp-matrix-coefficient-polarization
-/
theorem exists_inner_expUnitary_eq_sum {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (χ φ : H) :
    ∃ (ψ : Fin 4 → H) (c : Fin 4 → ℂ), ∀ t : ℝ,
      ⟪χ, expUnitary hA t φ⟫_ℂ =
        ∑ k, c k * ∫ x : ℝ, Complex.exp (Complex.I * t * x)
          ∂((Unbounded.spectralMeasure hA).assoc (ψ k)) := by
  refine ⟨![χ + φ, χ - φ, χ + I • φ, χ - I • φ], ![1 / 4, -1 / 4, -I / 4, I / 4], fun t => ?_⟩
  rw [expUnitary_apply]
  set T := (Unbounded.spectralMeasure hA).integral (expFun t)
  have h : ∀ v : H, ∫ x : ℝ, Complex.exp (I * t * x)
      ∂((Unbounded.spectralMeasure hA).assoc v) = ⟪v, T v⟫_ℂ := fun v => by
    rw [ProjectionValuedMeasure.inner_integral _ (expFun_mem_bddMeasurable t)]
    simp [expFun, mul_assoc]
  simp only [Fin.sum_univ_four, h]
  simp [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right]
  linear_combination ((1:ℂ)/2 * (⟪χ, T φ⟫_ℂ - ⟪φ, T χ⟫_ℂ)) * I_sq

/--
**The Fourier–Laplace transform on the closed upper half-plane.** Let ν be a finite positive
Borel measure on ℝ with ν((−∞, 0)) = 0, and G(z) = ∫ e^(izλ) dν(λ). For Im z ≥ 0 the integrand
is ν-integrable, so G(z) is defined; |G(z)| ≤ ν(ℝ); and G is continuous on {Im z ≥ 0}.

For λ ≥ 0 and Im z ≥ 0, |e^(izλ)| = e^(−λ Im z) ≤ 1, and ν is carried by [0, ∞), so the
integrand is dominated by the constant 1; dominated convergence gives continuity.

Implementation note: the three conclusions (integrability, the bound, continuity) are the three
components of the conjunction; ν(ℝ) is `ν.real Set.univ`, and G is written inline as
`fun z => ∫ x, Complex.exp (Complex.I * z * x) ∂ν`.

Blueprint: lmm:fourier-laplace-continuous
-/
theorem fourierLaplace_bounded_continuousOn (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ν (Set.Iio 0) = 0) :
    (∀ z : ℂ, 0 ≤ z.im → Integrable (fun x : ℝ => Complex.exp (Complex.I * z * x)) ν) ∧
    (∀ z : ℂ, 0 ≤ z.im → ‖∫ x : ℝ, Complex.exp (Complex.I * z * x) ∂ν‖ ≤ ν.real Set.univ) ∧
    ContinuousOn (fun z : ℂ => ∫ x : ℝ, Complex.exp (Complex.I * z * x) ∂ν)
      {z : ℂ | 0 ≤ z.im} := by
  have hae : ∀ᵐ x ∂ν, 0 ≤ x := by
    rw [ae_iff]
    exact measure_mono_null (fun x (hx : ¬ 0 ≤ x) => (not_le.mp hx : x < 0)) hν
  have hb : ∀ᵐ x : ℝ ∂ν, ∀ z : ℂ, 0 ≤ z.im → ‖Complex.exp (Complex.I * z * (x : ℂ))‖ ≤ 1 :=
    hae.mono fun x hx z (hz : 0 ≤ z.im) => by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      simp only [mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_im]
      nlinarith
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun x : ℝ => Complex.exp (Complex.I * z * x)) ν :=
    fun z => (by fun_prop : Continuous fun x : ℝ => Complex.exp (Complex.I * z * x))
      |>.aestronglyMeasurable
  refine ⟨fun z hz => (integrable_const (1 : ℝ)).mono' (hmeas z) (hb.mono fun x hx => hx z hz),
    fun z hz => ?_, ?_⟩
  · simpa using norm_integral_le_of_norm_le_const (hb.mono fun x hx => hx z hz)
  · exact continuousOn_of_dominated (fun z _ => hmeas z) (fun z hz => hb.mono fun x hx => hx z hz)
      (integrable_const 1) (ae_of_all _ fun x => by fun_prop)

/--
**Holomorphy of the Fourier–Laplace transform.** For a finite positive Borel measure ν on ℝ with
ν((−∞, 0)) = 0, the function G(z) = ∫ e^(izλ) dν(λ) is holomorphic on the open upper half-plane.

Near a point z₀ with Im z₀ > 0 the z-derivative iλe^(izλ) of the integrand is bounded by
1/(e δ), δ = Im z₀ / 2, for λ ≥ 0, so differentiation under the integral sign applies.

Implementation note: G is written inline as `fun z => ∫ x, Complex.exp (Complex.I * z * x) ∂ν`.

Blueprint: lmm:fourier-laplace-holomorphic
-/
theorem differentiableOn_fourierLaplace (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ν (Set.Iio 0) = 0) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ x : ℝ, Complex.exp (Complex.I * z * x) ∂ν)
      {z : ℂ | 0 < z.im} := by
  have h0 : ∀ᵐ x ∂ν, 0 ≤ x := by
    rw [ae_iff]; convert hν using 2; ext; simp
  intro z₀ hz₀
  have hz₀ : 0 < z₀.im := hz₀
  set δ := z₀.im / 2 with hδ
  have δpos : 0 < δ := by positivity
  have hball : ∀ z ∈ Metric.ball z₀ δ, δ ≤ z.im := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have := (abs_le.1 (abs_im_le_norm (z - z₀))).1
    simp only [sub_im] at this
    linarith
  have hnorm : ∀ z : ℂ, ∀ x : ℝ, ‖Complex.exp (Complex.I * z * x)‖ = Real.exp (-(z.im * x)) := by
    intro z x; rw [Complex.norm_exp]; congr 1; simp
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := z₀)
    (F := fun z x => Complex.exp (Complex.I * z * x))
    (F' := fun z x => Complex.I * x * Complex.exp (Complex.I * z * x))
    (bound := fun _ => 1 / δ) (Metric.ball_mem_nhds z₀ δpos)
    (Filter.Eventually.of_forall fun z => by fun_prop)
    (Integrable.of_bound (by fun_prop) 1 (h0.mono fun x hx => by
      rw [hnorm]; exact Real.exp_le_one_iff.2 (by nlinarith)))
    (by fun_prop)
    (h0.mono fun x hx z hz => by
      have hzδ := hball z hz
      rw [norm_mul, norm_mul, hnorm, norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hx]
      rw [le_div_iff₀ δpos]
      have h1 := Real.add_one_le_exp (x * δ)
      have h2 : Real.exp (-(z.im * x)) ≤ Real.exp (-(x * δ)) :=
        Real.exp_le_exp.2 (by nlinarith)
      have h3 : Real.exp (x * δ) * Real.exp (-(x * δ)) = 1 := by
        rw [← Real.exp_add]; simp
      have h4 := Real.exp_pos (-(x * δ))
      nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hx δpos.le)])
    (integrable_const _)
    (Filter.Eventually.of_forall fun x z _ => by
      have := (((hasDerivAt_id' z).const_mul Complex.I).mul_const (x : ℂ)).cexp
      convert this using 1; ring)
  exact key.2.differentiableAt.differentiableWithinAt

/--
**Holomorphic extension under positive energy.** If a family V of unitaries indexed by ℝ has
positive energy and χ, φ are vectors, then t ↦ ⟨χ, V(t)φ⟩ is the restriction to ℝ of a function
F that is holomorphic on the open upper half-plane and bounded and continuous on the closed upper
half-plane.

By `isPositiveEnergy_iff_exists_exp`, V(t) = e^(itA) with A positive and self-adjoint. The matrix
coefficient is a combination of Fourier transforms of the finite measures μ^A_ψₖ
(`exists_inner_expUnitary_eq_sum`), which vanish on (−∞, 0)
(`spectralMeasure_Iio_zero_eq_zero`), and F is the same combination of their Fourier–Laplace
transforms (`fourierLaplace_bounded_continuousOn`, `differentiableOn_fourierLaplace`).

Implementation note: boundedness is the existence of a constant C with ‖F z‖ ≤ C for Im z ≥ 0,
and the restriction property reads `F t = ⟪χ, V t φ⟫_ℂ` for real t.

Blueprint: lmm:positive-energy-holomorphic
-/
theorem IsPositiveEnergy.exists_holomorphic_extension {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : IsPositiveEnergy V) (χ φ : H) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {z : ℂ | 0 < z.im} ∧
      ContinuousOn F {z : ℂ | 0 ≤ z.im} ∧
      (∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ C) ∧
      ∀ t : ℝ, F t = ⟪χ, V t φ⟫_ℂ := by
  obtain ⟨A, hA, hpos, hVe⟩ := isPositiveEnergy_iff_exists_exp.1 hV
  obtain ⟨ψ, c, hsum⟩ := exists_inner_expUnitary_eq_sum hA χ φ
  set μ := Unbounded.spectralMeasure hA
  have hν : ∀ k, μ.assoc (ψ k) (Set.Iio 0) = 0 := fun k => by
    rw [Unbounded.assoc_apply_eq_norm_sq μ (ψ k) measurableSet_Iio,
      spectralMeasure_Iio_zero_eq_zero hA hpos]
    simp
  refine ⟨fun z => ∑ k, c k * ∫ x : ℝ, Complex.exp (Complex.I * z * x) ∂(μ.assoc (ψ k)),
    ?_, ?_, ⟨∑ k, ‖c k‖ * (μ.assoc (ψ k)).real Set.univ, fun z hz => ?_⟩, fun t => ?_⟩
  · exact DifferentiableOn.fun_sum fun k _ =>
      (differentiableOn_fourierLaplace _ (hν k)).const_mul (c k)
  · exact continuousOn_finsetSum _ fun k _ =>
      ((fourierLaplace_bounded_continuousOn _ (hν k)).2.2).const_smul (c k)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((fourierLaplace_bounded_continuousOn _ (hν k)).2.1 z hz)
      (norm_nonneg _)
  · simp only [hVe, hsum]

end AQFT
end Physicslib4
