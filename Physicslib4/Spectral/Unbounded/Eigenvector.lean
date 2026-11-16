/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Unbounded.FunctionalCalculus

/-!
# Eigenvectors of a self-adjoint operator

For a self-adjoint operator `A` with spectral measure `μ^A`, this file relates the moments of the
distributions `μ^A_ψ` to `A`, and shows that an eigenvector `Aψ = cψ` (with `c ∈ ℝ`) lies in the
range of the spectral projection `μ^A({c})`, so that every bounded function of `A` acts on it by
the scalar `f(c)`.

## Main statements

* `spectralMeasure_moments` — `μ^A_ψ(ℝ) = ‖ψ‖²`, `∫ λ dμ^A_ψ = Re ⟪ψ, Aψ⟫` and
  `∫ λ² dμ^A_ψ = ‖Aψ‖²` for `ψ ∈ Dom A`.
* `spectralMeasure_variance` — `∫ (λ - c)² dμ^A_ψ = ‖Aψ - cψ‖²`.
* `projectionValuedMeasure_apply_of_assoc_eq_zero` — `μ_ψ(E) = 0` gives `μ(E)ψ = 0` and
  `μ(Eᶜ)ψ = ψ`.
* `spectralMeasure_singleton_apply_of_eigenvector` — `μ^A({c})ψ = ψ` for `Aψ = cψ`.
* `spectralMeasure_integral_apply_of_eigenvector` — `f(A)ψ = f(c)ψ` for `Aψ = cψ` and bounded
  measurable `f`.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace
open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

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
  set μ := spectralMeasure hA
  have : IsFiniteMeasure (μ.assoc ψ) := ⟨by rw [assoc_univ_eq]; exact ENNReal.ofReal_lt_top⟩
  have hmeas : Measurable fun x : ℝ => (x : ℂ) := Complex.measurable_ofReal
  have hψ' : ψ ∈ (pmapIntegral μ (fun x : ℝ => (x : ℂ))).domain :=
    (domain_eq_integralDomain_spectralMeasure hA).le hψ
  have key : ∀ (B : H →ₗ.[ℂ] H) (hB : B = pmapIntegral μ (fun x : ℝ => (x : ℂ)))
      (h : ψ ∈ B.domain), B ⟨ψ, h⟩ = pmapIntegral μ (fun x : ℝ => (x : ℂ)) ⟨ψ, hψ'⟩ := by
    rintro B rfl h; rfl
  have hAψ := key A (pmapIntegral_spectralMeasure hA).symm hψ
  have hint : Integrable (fun x : ℝ => (x : ℂ)) (μ.assoc ψ) :=
    (mem_integralDomain μ).1 hψ' |>.integrable one_le_two
  have hsq : ∀ x : ℝ, ‖(x : ℂ)‖ ^ 2 = x ^ 2 := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hinner : ⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ = ((∫ x, x ∂(μ.assoc ψ) : ℝ) : ℂ) := by
    rw [hAψ]
    exact (inner_self_pmapIntegral μ hmeas ⟨ψ, hψ'⟩).trans integral_ofReal
  refine ⟨integrable_const _, ?_, ?_, assoc_univ_eq μ ψ, by rw [hinner, Complex.ofReal_im],
    by rw [hinner, Complex.ofReal_re], ?_⟩
  · simpa using hint.re
  · simpa only [hsq] using ((mem_integralDomain μ).1 hψ').integrable_norm_pow two_ne_zero
  · rw [hAψ]
    exact ((norm_sq_pmapIntegral μ hmeas ⟨ψ, hψ'⟩).trans (by simp only [hsq])).symm

/-- For `c ∈ ℝ` and `ψ ∈ Dom A`, `λ ↦ (λ - c)²` is `μ^A_ψ`-integrable and
`∫ (λ - c)² dμ^A_ψ = ‖Aψ - cψ‖²`.
Blueprint: lmm:spectral-eigenvector-variance -/
theorem spectralMeasure_variance {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (c : ℝ) {ψ : H}
    (hψ : ψ ∈ A.domain) :
    Integrable (fun x : ℝ => (x - c) ^ 2) ((spectralMeasure hA).assoc ψ) ∧
      ∫ x, (x - c) ^ 2 ∂((spectralMeasure hA).assoc ψ) = ‖A ⟨ψ, hψ⟩ - (c : ℂ) • ψ‖ ^ 2 := by
  obtain ⟨h1, hx, hx2, huniv, -, hre, hsq⟩ := spectralMeasure_moments hA hψ
  have hexp : (fun x : ℝ => (x - c) ^ 2) =
      fun x => x ^ 2 - 2 * c * x + c ^ 2 * 1 := by
    ext x; ring
  have hi1 : Integrable (fun x : ℝ => x ^ 2 - 2 * c * x) ((spectralMeasure hA).assoc ψ) :=
    hx2.sub (hx.const_mul (2 * c))
  have hi2 := h1.const_mul (c ^ 2)
  refine ⟨hexp ▸ hi1.add hi2, ?_⟩
  have hone : ∫ _ : ℝ, (1 : ℝ) ∂((spectralMeasure hA).assoc ψ) = ‖ψ‖ ^ 2 := by
    rw [integral_const, smul_eq_mul, mul_one, Measure.real, huniv,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hexp, integral_add hi1 hi2, integral_sub hx2 (hx.const_mul _), integral_const_mul,
    integral_const_mul, hone, hsq, hre, @norm_sub_sq ℂ, inner_smul_right, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [show RCLike.re ((c : ℂ) * ⟪A ⟨ψ, hψ⟩, ψ⟫_ℂ) = c * (⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ).re from by
    change ((c : ℂ) * _).re = _
    rw [Complex.re_ofReal_mul, ← inner_conj_symm, Complex.conj_re]]
  ring

/-- For a projection-valued measure `μ` and measurable `E`, `μ_ψ(E) = ‖μ(E)ψ‖²`; hence
`μ_ψ(E) = 0` gives `μ(E)ψ = 0` and `μ(Eᶜ)ψ = ψ`.
Blueprint: lmm:pvm-null-set-vector -/
theorem projectionValuedMeasure_apply_of_assoc_eq_zero {X : Type*} [MeasurableSpace X]
    (μ : ProjectionValuedMeasure X H) (ψ : H) {E : Set X} (hE : MeasurableSet E) :
    μ.assoc ψ E = ENNReal.ofReal (‖μ E ψ‖ ^ 2) ∧
      (μ.assoc ψ E = 0 → μ E ψ = 0 ∧ μ Eᶜ ψ = ψ) := by
  have h1 := assoc_apply_eq_norm_sq μ ψ hE
  refine ⟨h1, fun h0 => ?_⟩
  have hE0 : μ E ψ = 0 := by
    rw [h1, ENNReal.ofReal_eq_zero] at h0
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h0 (sq_nonneg _)))
  refine ⟨hE0, ?_⟩
  have hempty : μ (∅ : Set X) ψ = 0 :=
    (summable_const_iff (a := μ (∅ : Set X) ψ)).mp
      (μ.hasSum_apply (fun _ : ℕ => (∅ : Set X)) (fun _ => MeasurableSet.empty)
        (by intro k e; simp) ψ).summable
  let F : ℕ → Set X := fun j => if j = 0 then E else if j = 1 then Eᶜ else ∅
  have hF : ∀ j, MeasurableSet (F j) := fun j => by
    simp only [F]; split_ifs
    exacts [hE, hE.compl, MeasurableSet.empty]
  have hdisj : Pairwise (fun i j => Disjoint (F i) (F j)) := by
    intro i j hij
    simp only [F]; split_ifs <;> first | omega | simp [disjoint_compl_right, disjoint_compl_left]
  have hU : (⋃ j, F j) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
    by_cases hx : x ∈ E
    · exact ⟨0, by simp [F, hx]⟩
    · exact ⟨1, by simp [F, hx]⟩
  have hs := μ.hasSum_apply F hF hdisj ψ
  rw [hU, μ.apply_univ] at hs
  have hs' : HasSum (fun j => μ (F j) ψ) (μ Eᶜ ψ) := by
    have : HasSum (fun j => μ (F j) ψ) (∑ j ∈ ({0, 1} : Finset ℕ), μ (F j) ψ) :=
      hasSum_sum_of_ne_finset_zero (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      simp [F, hj.1, hj.2, hempty])
    simpa [F, hE0] using this
  exact (hs.unique hs').symm

/-- If `ψ ∈ Dom A` and `Aψ = cψ` with `c ∈ ℝ`, then `μ^A({c})ψ = ψ`.
Blueprint: lmm:spectral-eigenvector-projection -/
theorem spectralMeasure_singleton_apply_of_eigenvector {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {c : ℝ} {ψ : H} (hψ : ψ ∈ A.domain) (hAψ : A ⟨ψ, hψ⟩ = (c : ℂ) • ψ) :
    spectralMeasure hA {c} ψ = ψ := by
  obtain ⟨hint, heq⟩ := spectralMeasure_variance hA c hψ
  rw [hAψ, sub_self, norm_zero] at heq
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint).1 (by simpa using heq)
  have hnull : (spectralMeasure hA).assoc ψ {c}ᶜ = 0 := by
    rw [Filter.EventuallyEq, ae_iff] at hae
    refine measure_mono_null (fun x hx => ?_) hae
    exact pow_ne_zero 2 (sub_ne_zero.2 hx)
  have := ((projectionValuedMeasure_apply_of_assoc_eq_zero _ ψ
    (measurableSet_singleton c).compl).2 hnull).2
  rwa [compl_compl] at this

/-- If `ψ ∈ Dom A`, `Aψ = cψ` with `c ∈ ℝ`, and `f` is bounded and measurable, then
`f(A)ψ = f(c)ψ`, with `f(A)` the bounded integral `∫ f dμ^A` (equal to the functional calculus
by `functionalCalculus_of_bddMeasurable`).
Blueprint: lmm:spectral-eigenvector-bounded-fc -/
theorem spectralMeasure_integral_apply_of_eigenvector {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {c : ℝ} {ψ : H} (hψ : ψ ∈ A.domain) (hAψ : A ⟨ψ, hψ⟩ = (c : ℂ) • ψ) {f : ℝ → ℂ}
    (hf : f ∈ BddMeasurable ℝ) :
    (spectralMeasure hA).integral f ψ = f c • ψ := by
  set μ := spectralMeasure hA
  have hμ := spectralMeasure_singleton_apply_of_eigenvector hA hψ hAψ
  have hind : ({c} : Set ℝ).indicator (1 : ℝ → ℂ) ∈ BddMeasurable ℝ :=
    ⟨measurable_const.indicator (measurableSet_singleton c), 1, fun x => by
      by_cases hx : x = c <;> simp [hx]⟩
  have key : f * ({c} : Set ℝ).indicator 1 = f c • ({c} : Set ℝ).indicator 1 :=
    funext fun x => by by_cases hx : x = c <;> simp [hx]
  calc μ.integral f ψ = μ.integral f (μ {c} ψ) := by rw [hμ]
    _ = μ.integral (f * ({c} : Set ℝ).indicator 1) ψ := by
      rw [μ.integral_mul hf hind, μ.integral_indicator (measurableSet_singleton c)]; rfl
    _ = f c • ψ := by
      rw [key, μ.integral_smul _ hind, μ.integral_indicator (measurableSet_singleton c),
        smul_apply, hμ]

end Unbounded
end Spectral
end Physicslib4
