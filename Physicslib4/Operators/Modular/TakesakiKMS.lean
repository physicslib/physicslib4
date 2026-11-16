/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Operators.Modular.VanDaele
import Physicslib4.AQFT.KMS
import Physicslib4.GNS.VectorState
import Mathlib.Analysis.Complex.LocallyUniformLimit

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
    (μ : Spectral.ProjectionValuedMeasure X H) (ψ : H) {E : Set X} (hE : MeasurableSet E) :
    μ.assoc ψ E = ENNReal.ofReal (‖μ E ψ‖ ^ 2) ∧
      (μ.assoc ψ E = 0 → μ E ψ = 0 ∧ μ Eᶜ ψ = ψ) := by
  have h1 := Spectral.Unbounded.assoc_apply_eq_norm_sq μ ψ hE
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
    (hf : f ∈ Spectral.BddMeasurable ℝ) :
    (spectralMeasure hA).integral f ψ = f c • ψ := by
  set μ := spectralMeasure hA
  have hμ := spectralMeasure_singleton_apply_of_eigenvector hA hψ hAψ
  have hind : ({c} : Set ℝ).indicator (1 : ℝ → ℂ) ∈ Spectral.BddMeasurable ℝ :=
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

/-! ### The invariance of `Ω` -/

/-- `Ω ∈ Dom Δ` and `ΔΩ = Ω`.
Blueprint: lmm:modular-operator-fixes-omega -/
theorem modularOperator_apply_self {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    ∃ h : Ω ∈ (modularOperator M Ω C).domain, modularOperator M Ω C ⟨Ω, h⟩ = Ω := by
  have h1' : (1 : H →L[ℂ] H) ∈ Set.centralizer M := Set.one_mem_centralizer
  have h1 : (1 : H →L[ℂ] H) ∈ M := hM.2 ▸ Set.one_mem_centralizer
  obtain ⟨hS, hSΩ⟩ := tomitaOperator_apply_of_mem hM hΩ C hC h1
  simp only [one_apply_eq_self, star_one] at hS hSΩ
  have hadj := (mem_tomitaAdjoint_iff hM hΩ C hC Ω Ω).1 (by
    simpa using (tomitaAdjoint_apply_of_mem_centralizer hM hΩ C hC h1').1)
  refine (mem_modularOperator_iff hM hΩ C hC Ω Ω).2 ⟨hS, fun φ => ?_⟩
  rw [hSΩ, ← inner_conj_symm, hadj φ, inner_conj_symm]

/-- `Δ^{it}Ω = Ω` for every `t ∈ ℝ`.
Blueprint: lmm:modular-unitary-group-fixes-omega -/
theorem modularUnitaryGroup_apply_self {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (t : ℝ) :
    modularUnitaryGroup hM hΩ C hC t Ω = Ω := by
  obtain ⟨hem, hen, -, hU, -⟩ := modularUnitaryGroup_eq_functionalCalculus hM hΩ C hC t
  obtain ⟨hd, hΔ⟩ := modularOperator_apply_self hM hΩ C hC
  have h1 : modularUnitaryGroup hM hΩ C hC t Ω =
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral e[t] Ω := by
    rw [← hU]; rfl
  rw [h1, spectralMeasure_integral_apply_of_eigenvector _ hd (c := 1) (by rw [hΔ]; simp)
    ⟨hem, 1, fun x => (hen x).le⟩]
  simp

/-- `J Δ^{it} ψ = Δ^{it} J ψ` for every `t ∈ ℝ` and `ψ ∈ H`.
Blueprint: lmm:modular-conjugation-commutes-unitary-group -/
theorem modularConjugation_modularUnitaryGroup {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (t : ℝ) (ψ : H) :
    modularConjugation hM hΩ C hC (modularUnitaryGroup hM hΩ C hC t ψ) =
      modularUnitaryGroup hM hΩ C hC t (modularConjugation hM hΩ C hC ψ) := by
  have h := (modularConjugation_indicatorCpow_modularConjugation hM hΩ C hC le_rfl 0 t).2.1
    (modularConjugation hM hΩ C hC ψ)
  rwa [(modularConjugation_involution hM hΩ C hC).1] at h

/-- For `x ∈ M`, `xΩ ∈ Dom Δ^{1/2}` and `Δ^{1/2} xΩ = J x* Ω`.
Blueprint: lmm:modular-sqrt-on-algebra -/
theorem modularOperatorSqrt_apply_of_mem {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {x : H →L[ℂ] H} (hx : x ∈ M) :
    ∃ h : x Ω ∈ (Δs).domain, Δs ⟨x Ω, h⟩ = modularConjugation hM hΩ C hC (star x Ω) := by
  obtain ⟨h₁, e⟩ := tomitaOperator_apply_of_mem hM hΩ C hC hx
  obtain ⟨hdom, hS⟩ := tomitaOperator_eq_modularConjugation_sqrt hM hΩ C hC
  have h₂ : x Ω ∈ (Δs).domain := hdom ▸ h₁
  refine ⟨h₂, ?_⟩
  rw [← e, hS _ h₁ h₂, (modularConjugation_involution hM hΩ C hC).1]

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
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  refine ⟨Real.sq_sqrt hx.le, ?_, Complex.norm_cpow_eq_rpow_re_of_pos hx w, ?_⟩
  · rw [Complex.cpow_add _ _ hx0, Complex.cpow_one, mul_comm]
  · rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]
    dsimp only
    congr 1
    ring

/-- `u_z 1_{K_n} = 1_{(0,1)} p_{-iz,n}` and `v_z 1_{K_n} = 1_{[1,∞)} p_{-iz-1,n}` pointwise.
Blueprint: lmm:takesaki-functions-identities -/
theorem takesaki_functions_identities (z : ℂ) (n : ℕ) (x : ℝ) :
    u[z] x * (K[n]).indicator 1 x = (Set.Ioo (0 : ℝ) 1).indicator 1 x * p[-Complex.I * z, n] x ∧
      v[z] x * (K[n]).indicator 1 x =
        (Set.Ici (1 : ℝ)).indicator 1 x * p[-Complex.I * z - 1, n] x := by
  constructor <;> simp only [Set.indicator] <;> split_ifs <;> simp

/-- `u_t + s² v_t = 1_{(0,∞)} e_{-t}` pointwise, for real `t`.
Blueprint: lmm:takesaki-functions-lower-sum -/
theorem takesaki_functions_lower_sum (t x : ℝ) :
    u[(t : ℂ)] x + (Real.sqrt x : ℂ) ^ 2 * v[(t : ℂ)] x = (Set.Ioi (0 : ℝ)).indicator e[-t] x := by
  rcases le_or_gt x 0 with hx | hx
  · simp [Set.indicator, not_lt.mpr hx, Real.sqrt_eq_zero'.mpr hx]
  obtain ⟨hs, hm, -, he⟩ := takesaki_positive_scalar_identities hx (-Complex.I * t - 1) t
  beta_reduce at he
  rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hx), he]
  rcases lt_or_ge x 1 with h1 | h1
  · simp [Set.indicator, hx, h1, not_le.mpr h1]
  · rw [Set.indicator_of_notMem (fun h => absurd h1 (not_le.mpr h.2)),
      Set.indicator_of_mem (Set.mem_Ici.mpr h1), ← Complex.ofReal_pow, hs, hm, zero_add,
      sub_add_cancel]

/-- `s² g_t = u_{t+i}` and `g_t + v_{t+i} = 1_{(0,∞)} e_{-t}` pointwise, for real `t`.
Blueprint: lmm:takesaki-functions-upper-identities -/
theorem takesaki_functions_upper_identities (t x : ℝ) :
    (Real.sqrt x : ℂ) ^ 2 * g[t] x = u[(t : ℂ) + Complex.I] x ∧
      g[t] x + v[(t : ℂ) + Complex.I] x = (Set.Ioi (0 : ℝ)).indicator e[-t] x := by
  rcases le_or_gt x 0 with h0 | h0
  · have h1 : ¬ (1 : ℝ) ≤ x := by linarith
    simp [Set.indicator, not_lt.2 h0, h1]
  obtain ⟨hs, hm, -, he⟩ := takesaki_positive_scalar_identities h0 (-Complex.I * t) t
  have he' : Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (Real.log x : ℂ)) =
      (x : ℂ) ^ (-Complex.I * t) := by rw [← he]; push_cast; ring_nf
  rcases lt_or_ge x 1 with h1 | h1
  · have h1' : ¬ (1 : ℝ) ≤ x := by linarith
    simp only [Set.indicator, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, h0, h1, h1', and_self,
      ite_true, ite_false, add_zero]
    refine ⟨?_, he'.trans he.symm⟩
    rw [he', ← Complex.ofReal_pow, hs, hm]
    congr 1
    linear_combination Complex.I_sq
  · have h1' : ¬ x < 1 := by linarith
    simp only [Set.indicator, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi, h0, h1, h1', and_false,
      ite_true, ite_false, mul_zero, zero_add, true_and]
    refine (congrArg _ ?_).trans he.symm
    linear_combination -Complex.I_sq

/-- `g_t` is measurable, and `|g_t|`, `|s v_t|`, `|s² v_t|`, `|s g_t|`, `|s² g_t|` are at most `1`.
Blueprint: lmm:takesaki-functions-aux-bounds -/
theorem takesaki_functions_aux_bounds (t : ℝ) :
    Measurable g[t] ∧ ∀ x : ℝ, ‖g[t] x‖ ≤ 1 ∧ ‖(Real.sqrt x : ℂ) * v[(t : ℂ)] x‖ ≤ 1 ∧
      ‖(Real.sqrt x : ℂ) ^ 2 * v[(t : ℂ)] x‖ ≤ 1 ∧ ‖(Real.sqrt x : ℂ) * g[t] x‖ ≤ 1 ∧
      ‖(Real.sqrt x : ℂ) ^ 2 * g[t] x‖ ≤ 1 := by
  have hgm : Measurable g[t] :=
    (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp Real.measurable_log))).indicator measurableSet_Ioo
  refine ⟨hgm, fun x => ?_⟩
  have hs : ‖(Real.sqrt x : ℂ)‖ = Real.sqrt x := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg x)]
  by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
  · have hv : v[(t : ℂ)] x = 0 := Set.indicator_of_notMem (fun h => absurd hx.2 (not_lt.mpr h)) _
    have hg : ‖g[t] x‖ = 1 := by
      rw [Set.indicator_of_mem hx, show Complex.I * ((-t : ℝ) : ℂ) * (Real.log x : ℂ) =
        ((-t * Real.log x : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    have hsx : Real.sqrt x ≤ 1 := Real.sqrt_le_one.mpr hx.2.le
    have hsx2 : Real.sqrt x ^ 2 ≤ 1 := by rw [Real.sq_sqrt hx.1.le]; exact hx.2.le
    simp only [hv, mul_zero, norm_zero, zero_le_one, norm_mul, norm_pow, hs, hg, mul_one,
      true_and]
    exact ⟨le_rfl, hsx, hsx2⟩
  · have hg : g[t] x = 0 := Set.indicator_of_notMem hx _
    simp only [hg, norm_zero, zero_le_one, mul_zero, true_and, and_true]
    by_cases h1 : x ∈ Set.Ici (1 : ℝ)
    · have hx0 : (0 : ℝ) < x := by linarith [h1.out]
      have hv : ‖v[(t : ℂ)] x‖ = x⁻¹ := by
        rw [Set.indicator_of_mem h1, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        simp [Real.rpow_neg_one]
      rw [norm_mul, norm_mul, norm_pow, hs, hv, Real.sq_sqrt hx0.le, mul_inv_cancel₀ hx0.ne']
      refine ⟨?_, le_rfl⟩
      rw [← div_eq_mul_inv, div_le_one hx0]
      exact (Real.sqrt_le_left hx0.le).mpr (by nlinarith [h1.out])
    · rw [Set.indicator_of_notMem h1]
      simp

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
  set μ := μΔ
  have hs : Measurable fun x : ℝ => (Real.sqrt x : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have hbdd : ∀ {g : ℝ → ℂ} (_ : g ∈ Spectral.BddMeasurable ℝ) (ψ : H)
      (h : ψ ∈ integralDomain μ g), pmapIntegral μ g ⟨ψ, h⟩ = μ.integral g ψ := by
    intro g hg ψ h
    obtain ⟨-, he⟩ := LinearPMap.ext_iff.1 (pmapIntegral_of_bddMeasurable μ hg)
    exact he (x := ψ) (hf := h) (hg := trivial)
  have hcongr : ∀ {g g' : ℝ → ℂ} (_ : g = g') (h : η ∈ integralDomain μ g)
      (h' : η ∈ integralDomain μ g'), pmapIntegral μ g ⟨η, h⟩ = pmapIntegral μ g' ⟨η, h'⟩ := by
    rintro g _ rfl h h'; rfl
  have hη' : η ∈ integralDomain μ (fun x => (Real.sqrt x : ℂ) * f x) := by
    rw [integralDomain_eq_top_of_bddMeasurable μ hsf]; trivial
  have hη'' : η ∈ integralDomain μ (fun x => (Real.sqrt x : ℂ) ^ 2 * f x) := by
    rw [integralDomain_eq_top_of_bddMeasurable μ hs2f]; trivial
  have hs2 : ((fun x : ℝ => (Real.sqrt x : ℂ)) * fun x => (Real.sqrt x : ℂ) * f x) =
      fun x => (Real.sqrt x : ℂ) ^ 2 * f x := funext fun x => by simp [pow_two, mul_assoc]
  obtain ⟨h1, e1⟩ := integral_apply_pmapIntegral μ hf hs ⟨η, hη⟩
  have hy := (pmapIntegral_mem_integralDomain_iff μ hs hsf.1 ⟨η, hη'⟩).2 (hs2 ▸ hη'')
  obtain ⟨h2, e2⟩ := (pmapIntegral_comp μ hs hsf.1).2 ⟨η, hη'⟩ hy
  have hsym := isSymmetric_pmapIntegral_of_real μ hs (fun x => Complex.ofReal_im _)
  have eA : μ.integral f (Δs ⟨η, hη⟩) = pmapIntegral μ (fun x => (Real.sqrt x : ℂ) * f x)
      ⟨η, hη'⟩ := e1.trans (hcongr (funext fun x => mul_comm _ _) _ _)
  rw [eA]
  refine ((hsym ⟨ξ, hξ⟩ ⟨_, hy⟩).symm).trans ?_
  congr 1
  exact e2.symm.trans ((hcongr hs2 _ hη'').trans (hbdd hs2f η hη''))

/-- For `ξ, η ∈ Dom Δ^{1/2}` and `n ≥ 1`, `G^n_{ξ,η}` is entire, hence continuous.
Blueprint: lmm:takesaki-approximants-entire -/
theorem differentiable_takesakiApproximant {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H} (hξ : ξ ∈ (Δs).domain) (hη : η ∈ (Δs).domain)
    {n : ℕ} (hn : 1 ≤ n) :
    Differentiable ℂ Gn[ξ, η, hξ, hη, n] ∧ Continuous Gn[ξ, η, hξ, hη, n] := by
  have hd : Differentiable ℂ Gn[ξ, η, hξ, hη, n] :=
    ((differentiable_modularOperator_indicatorCpow_apply hM hΩ C hC hn _ _).2.comp
        (differentiable_id.const_mul _)).add
      ((differentiable_modularOperator_indicatorCpow_apply hM hΩ C hC hn _ _).2.comp
        ((differentiable_id.const_mul _).sub_const _))
  exact ⟨hd, hd.continuous⟩

/-- On the closed strip, `G^n_{ξ,η}(z) = ⟪ξ, u_z(Δ) E_n η⟫ + ⟪Δ^{1/2}ξ, v_z(Δ) E_n Δ^{1/2}η⟫`.
Blueprint: lmm:takesaki-approximants-strip -/
theorem takesakiApproximant_eq_of_mem_strip {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H} (hξ : ξ ∈ (Δs).domain) (hη : η ∈ (Δs).domain)
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ kmsStrip 1) :
    Gn[ξ, η, hξ, hη, n] z =
      ⟪ξ, (μΔ).integral u[z] (μΔ K[n] η)⟫_ℂ +
        ⟪Δs ⟨ξ, hξ⟩, (μΔ).integral v[z] (μΔ K[n] (Δs ⟨η, hη⟩))⟫_ℂ := by
  set μ := μΔ
  have hind : ∀ {S : Set ℝ}, MeasurableSet S →
      S.indicator (1 : ℝ → ℂ) ∈ Spectral.BddMeasurable ℝ :=
    fun {S} hS => ⟨measurable_const.indicator hS, 1, fun x => by
      by_cases hx : x ∈ S <;> simp [hx]⟩
  have hmove : ∀ {S : Set ℝ} (hS : MeasurableSet S) {f : ℝ → ℂ}
      (hf : f ∈ Spectral.BddMeasurable ℝ) (a b : H),
      ⟪μ S a, μ.integral f b⟫_ℂ = ⟪a, μ.integral (S.indicator 1 * f) b⟫_ℂ := by
    intro S hS f hf a b
    have hsa : μ S = ContinuousLinearMap.adjoint (μ S) := by
      rw [← Spectral.ProjectionValuedMeasure.integral_indicator μ hS,
        ← Spectral.ProjectionValuedMeasure.integral_conj μ (hind hS)]
      congr 1; funext x; by_cases hx : x ∈ S <;> simp [hx]
    rw [hsa, ContinuousLinearMap.adjoint_inner_left,
      Spectral.ProjectionValuedMeasure.integral_mul μ (hind hS) hf,
      Spectral.ProjectionValuedMeasure.integral_indicator μ hS]
    rfl
  have hK : MeasurableSet K[n] := measurableSet_Icc
  have hcomp : ∀ {f : ℝ → ℂ} (_ : f ∈ Spectral.BddMeasurable ℝ) (b : H),
      μ.integral f (μ K[n] b) = μ.integral (f * K[n].indicator 1) b := by
    intro f hf b
    rw [Spectral.ProjectionValuedMeasure.integral_mul μ hf (hind hK),
      Spectral.ProjectionValuedMeasure.integral_indicator μ hK]
    rfl
  obtain ⟨hum, hvm, hb⟩ := takesaki_functions_bounded z
  have hu : u[z] ∈ Spectral.BddMeasurable ℝ := ⟨hum, 1, fun x => (hb hz x).1⟩
  have hv : v[z] ∈ Spectral.BddMeasurable ℝ := ⟨hvm, 1, fun x => (hb hz x).2⟩
  have hp : ∀ w : ℂ, p[w, n] ∈ Spectral.BddMeasurable ℝ := fun w =>
    ⟨(indicatorCpow_bounds hn w).1, _, fun x => ((indicatorCpow_bounds hn w).2.2 x).1⟩
  have e1 : u[z] * K[n].indicator 1 = (Set.Ioo (0 : ℝ) 1).indicator 1 * p[-Complex.I * z, n] :=
    funext fun x => (takesaki_functions_identities z n x).1
  have e2 : v[z] * K[n].indicator 1 =
      (Set.Ici (1 : ℝ)).indicator 1 * p[-Complex.I * z - 1, n] :=
    funext fun x => (takesaki_functions_identities z n x).2
  change ⟪μ _ ξ, _⟫_ℂ + ⟪μ _ _, _⟫_ℂ = _
  rw [hmove measurableSet_Ioo (hp _), hmove measurableSet_Ici (hp _), hcomp hu, hcomp hv,
    e1, e2]

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
  set μ := μΔ
  have hop : ∀ {f : ℝ → ℂ}, Measurable f → (∀ x, ‖f x‖ ≤ 1) → ∀ a : H,
      ‖μ.integral f a‖ ≤ ‖a‖ := fun {f} hfm hf1 a => by
    simpa using (μ.integral f).le_of_opNorm_le
      ((Spectral.ProjectionValuedMeasure.norm_integral_le μ ⟨hfm, 1, hf1⟩).trans
        (ciSup_le hf1)) a
  have hbound : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ kmsStrip 1,
      ‖G[ξ, η, hξ, hη] z - Gn[ξ, η, hξ, hη, n] z‖ ≤
        ‖ξ‖ * ‖η - μ K[n] η‖ + ‖Δs ⟨ξ, hξ⟩‖ * ‖Δs ⟨η, hη⟩ - μ K[n] (Δs ⟨η, hη⟩)‖ := by
    intro n hn z hz
    obtain ⟨hum, hvm, hb⟩ := takesaki_functions_bounded z
    rw [takesakiApproximant_eq_of_mem_strip hM hΩ C hC hξ hη hn hz, Set.indicator_of_mem hz,
      add_sub_add_comm, ← inner_sub_right, ← inner_sub_right, ← map_sub, ← map_sub]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hop hum (fun x => (hb hz x).1) _) (norm_nonneg _))
    · exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hop hvm (fun x => (hb hz x).2) _) (norm_nonneg _))
  refine ⟨hbound, ?_⟩
  have hlim : Tendsto (fun n : ℕ => ‖ξ‖ * ‖η - μ K[n] η‖ +
      ‖Δs ⟨ξ, hξ⟩‖ * ‖Δs ⟨η, hη⟩ - μ K[n] (Δs ⟨η, hη⟩)‖) atTop (𝓝 0) := by
    have h : ∀ ψ : H, Tendsto (fun n : ℕ => ‖ψ - μ K[n] ψ‖) atTop (𝓝 0) := fun ψ => by
      simpa [dist_eq_norm] using
        (tendsto_const_nhds (x := ψ)).dist (tendsto_modularSpectralProjection hM hΩ C hC ψ)
    simpa using ((h η).const_mul ‖ξ‖).add ((h (Δs ⟨η, hη⟩)).const_mul ‖Δs ⟨ξ, hξ⟩‖)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with n hn h1 z hz
  rw [dist_eq_norm]
  exact (hbound n h1 z hz).trans_lt hn

/-- `G_{ξ,η}` is continuous on the closed strip, complex differentiable on the open strip, and
bounded there by `‖ξ‖ ‖η‖ + ‖Δ^{1/2}ξ‖ ‖Δ^{1/2}η‖`.
Blueprint: lmm:takesaki-function-analytic -/
theorem takesakiFunction_analytic {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H} (hξ : ξ ∈ (Δs).domain) (hη : η ∈ (Δs).domain) :
    ContinuousOn G[ξ, η, hξ, hη] (kmsStrip 1) ∧
      DifferentiableOn ℂ G[ξ, η, hξ, hη] (kmsStripInterior 1) ∧
      ∀ z ∈ kmsStrip 1, ‖G[ξ, η, hξ, hη] z‖ ≤ ‖ξ‖ * ‖η‖ + ‖Δs ⟨ξ, hξ⟩‖ * ‖Δs ⟨η, hη⟩‖ := by
  have hU := (tendstoUniformlyOn_takesakiApproximant hM hΩ C hC hξ hη).2
  have hev : ∀ᶠ n : ℕ in atTop, Differentiable ℂ Gn[ξ, η, hξ, hη, n] :=
    (eventually_ge_atTop 1).mono fun n hn =>
      (differentiable_takesakiApproximant hM hΩ C hC hξ hη hn).1
  have hsub : kmsStripInterior 1 ⊆ kmsStrip 1 := fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hopen : IsOpen (kmsStripInterior 1) :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  refine ⟨hU.continuousOn (hev.mono fun n hn => hn.continuous.continuousOn).frequently,
    TendstoLocallyUniformlyOn.differentiableOn (hU.mono hsub).tendstoLocallyUniformlyOn
      (hev.mono fun n hn => hn.differentiableOn) hopen, fun z hz => ?_⟩
  have hop : ∀ {f : ℝ → ℂ}, Measurable f → (∀ x, ‖f x‖ ≤ 1) → ∀ a : H,
      ‖(μΔ).integral f a‖ ≤ ‖a‖ := fun {f} hfm hf1 a => by
    simpa using ((μΔ).integral f).le_of_opNorm_le
      ((Spectral.ProjectionValuedMeasure.norm_integral_le (μΔ) ⟨hfm, 1, hf1⟩).trans
        (ciSup_le hf1)) a
  obtain ⟨hum, hvm, hb⟩ := takesaki_functions_bounded z
  rw [Set.indicator_of_mem hz]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hop hum (fun x => (hb hz x).1) _) (norm_nonneg _))
  · exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hop hvm (fun x => (hb hz x).2) _) (norm_nonneg _))

/-- The lower boundary value: `G_{ξ,η}(t) = ⟪ξ, Δ^{-it}η⟫` for real `t`.
Blueprint: lmm:takesaki-function-lower-boundary -/
theorem takesakiFunction_lower_boundary {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H} (hξ : ξ ∈ (Δs).domain) (hη : η ∈ (Δs).domain) (t : ℝ) :
    G[ξ, η, hξ, hη] (t : ℂ) = ⟪ξ, modularUnitaryGroup hM hΩ C hC (-t) η⟫_ℂ := by
  set μ := μΔ
  have hind : ∀ {S : Set ℝ}, MeasurableSet S →
      S.indicator (1 : ℝ → ℂ) ∈ Spectral.BddMeasurable ℝ :=
    fun {S} hS => ⟨measurable_const.indicator hS, 1, fun x => by
      by_cases hx : x ∈ S <;> simp [hx]⟩
  obtain ⟨hum, hvm, hb⟩ := takesaki_functions_bounded (t : ℂ)
  have ht : (t : ℂ) ∈ kmsStrip 1 := by simp [kmsStrip]
  obtain ⟨-, hab⟩ := takesaki_functions_aux_bounds t
  have hu : u[(t : ℂ)] ∈ Spectral.BddMeasurable ℝ := ⟨hum, 1, fun x => (hb ht x).1⟩
  have hv : v[(t : ℂ)] ∈ Spectral.BddMeasurable ℝ := ⟨hvm, 1, fun x => (hb ht x).2⟩
  have hs : Measurable fun x : ℝ => (Real.sqrt x : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have hsv : (fun x => (Real.sqrt x : ℂ) * v[(t : ℂ)] x) ∈ Spectral.BddMeasurable ℝ :=
    ⟨hs.mul hvm, 1, fun x => (hab x).2.1⟩
  have hs2v : (fun x => (Real.sqrt x : ℂ) ^ 2 * v[(t : ℂ)] x) ∈ Spectral.BddMeasurable ℝ :=
    ⟨(hs.pow_const 2).mul hvm, 1, fun x => (hab x).2.2.1⟩
  obtain ⟨hem, -, -, hU, -⟩ := modularUnitaryGroup_eq_functionalCalculus hM hΩ C hC (-t)
  have he : e[(-t : ℝ)] ∈ Spectral.BddMeasurable ℝ := ⟨hem, 1, fun x => by
    beta_reduce
    rw [show Complex.I * ((-t : ℝ) : ℂ) * (Real.log x : ℂ) =
      ((-t * Real.log x : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]⟩
  have hsum : u[(t : ℂ)] + (fun x => (Real.sqrt x : ℂ) ^ 2 * v[(t : ℂ)] x) =
      (Set.Ioi (0 : ℝ)).indicator 1 * e[(-t : ℝ)] := funext fun x => by
    rw [Pi.add_apply, takesaki_functions_lower_sum, Pi.mul_apply]
    by_cases hx : x ∈ Set.Ioi (0 : ℝ) <;> simp [hx]
  have hIoi : μ (Set.Ioi 0) = 1 := by
    have h1 := Spectral.ProjectionValuedMeasure.integral_add μ
      (hind (measurableSet_Ioi (a := (0 : ℝ)))) (hind (measurableSet_Iic (a := (0 : ℝ))))
    rw [Spectral.ProjectionValuedMeasure.integral_indicator μ measurableSet_Ioi,
      Spectral.ProjectionValuedMeasure.integral_indicator μ measurableSet_Iic,
      modularOperator_spectralMeasure_Iic_zero hM hΩ C hC, add_zero] at h1
    rw [← h1, ← Spectral.ProjectionValuedMeasure.integral_one μ]
    congr 1
    funext x
    by_cases hx : (0 : ℝ) < x
    · simp [hx]
    · simp [hx, not_lt.mp hx]
  rw [Set.indicator_of_mem ht]
  change ⟪ξ, μ.integral u[(t : ℂ)] η⟫_ℂ + ⟪Δs ⟨ξ, hξ⟩, μ.integral v[(t : ℂ)] (Δs ⟨η, hη⟩)⟫_ℂ = _
  rw [inner_modularOperatorSqrt_integral hM hΩ C hC hv hsv hs2v hξ hη, ← inner_add_right,
    ← add_apply, ← Spectral.ProjectionValuedMeasure.integral_add μ hu hs2v,
    hsum, Spectral.ProjectionValuedMeasure.integral_mul μ (hind measurableSet_Ioi) he,
    Spectral.ProjectionValuedMeasure.integral_indicator μ measurableSet_Ioi, hIoi, one_mul, ← hU]
  rfl

/-- The upper boundary value: `G_{ξ,η}(t + i) = ⟪Δ^{1/2}ξ, Δ^{-it} Δ^{1/2}η⟫` for real `t`.
Blueprint: lmm:takesaki-function-upper-boundary -/
theorem takesakiFunction_upper_boundary {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ η : H} (hξ : ξ ∈ (Δs).domain) (hη : η ∈ (Δs).domain) (t : ℝ) :
    G[ξ, η, hξ, hη] ((t : ℂ) + Complex.I) =
      ⟪Δs ⟨ξ, hξ⟩, modularUnitaryGroup hM hΩ C hC (-t) (Δs ⟨η, hη⟩)⟫_ℂ := by
  set μ := μΔ
  have hz : (t : ℂ) + Complex.I ∈ kmsStrip 1 := by simp [kmsStrip]
  have hs : Measurable fun x : ℝ => (Real.sqrt x : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  obtain ⟨hgm, hgb⟩ := takesaki_functions_aux_bounds t
  obtain ⟨-, hvm, hb⟩ := takesaki_functions_bounded ((t : ℂ) + Complex.I)
  have hg : g[t] ∈ Spectral.BddMeasurable ℝ := ⟨hgm, 1, fun x => (hgb x).1⟩
  have hsg : (fun x => (Real.sqrt x : ℂ) * g[t] x) ∈ Spectral.BddMeasurable ℝ :=
    ⟨hs.mul hgm, 1, fun x => (hgb x).2.2.2.1⟩
  have hs2g : (fun x => (Real.sqrt x : ℂ) ^ 2 * g[t] x) ∈ Spectral.BddMeasurable ℝ :=
    ⟨(hs.pow_const 2).mul hgm, 1, fun x => (hgb x).2.2.2.2⟩
  have hv : v[(t : ℂ) + Complex.I] ∈ Spectral.BddMeasurable ℝ := ⟨hvm, 1, fun x => (hb hz x).2⟩
  have hu : (fun x => (Real.sqrt x : ℂ) ^ 2 * g[t] x) = u[(t : ℂ) + Complex.I] :=
    funext fun x => (takesaki_functions_upper_identities t x).1
  have hsum : g[t] + v[(t : ℂ) + Complex.I] = (Set.Ioi (0 : ℝ)).indicator e[-t] :=
    funext fun x => (takesaki_functions_upper_identities t x).2
  have hind : ∀ {S : Set ℝ}, MeasurableSet S →
      S.indicator (1 : ℝ → ℂ) ∈ Spectral.BddMeasurable ℝ :=
    fun {S} hS => ⟨measurable_const.indicator hS, 1, fun x => by
      by_cases hx : x ∈ S <;> simp [hx]⟩
  obtain ⟨hem, hen, -, heU, -⟩ := modularUnitaryGroup_eq_functionalCalculus hM hΩ C hC (-t)
  have hpos : μ (Set.Ioi (0 : ℝ)) = 1 := by
    have h := Spectral.ProjectionValuedMeasure.integral_add μ
      (hind (measurableSet_Ioi (a := (0 : ℝ)))) (hind (measurableSet_Iic (a := (0 : ℝ))))
    rw [Spectral.ProjectionValuedMeasure.integral_indicator μ measurableSet_Ioi,
      Spectral.ProjectionValuedMeasure.integral_indicator μ measurableSet_Iic,
      modularOperator_spectralMeasure_Iic_zero hM hΩ C hC, add_zero] at h
    rw [← h, ← Spectral.ProjectionValuedMeasure.integral_one μ]
    congr 1
    funext x
    by_cases hx : (0 : ℝ) < x <;> simp [Set.indicator, hx, not_lt.mp]
  have hI : μ.integral ((Set.Ioi (0 : ℝ)).indicator e[-t]) = U[-t] := by
    have he : (Set.Ioi (0 : ℝ)).indicator e[-t] =
        (Set.Ioi (0 : ℝ)).indicator 1 * fun x : ℝ =>
          Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (Real.log x : ℂ)) := by
      funext x
      by_cases hx : x ∈ Set.Ioi (0 : ℝ) <;> simp [hx]
    rw [he, Spectral.ProjectionValuedMeasure.integral_mul μ (hind measurableSet_Ioi)
      ⟨hem, 1, fun x => (hen x).le⟩,
      Spectral.ProjectionValuedMeasure.integral_indicator μ measurableSet_Ioi, hpos, one_mul,
      heU]
  rw [Set.indicator_of_mem hz, ← hu,
    ← inner_modularOperatorSqrt_integral hM hΩ C hC hg hsg hs2g hξ hη, ← inner_add_right,
    ← add_apply, ← Spectral.ProjectionValuedMeasure.integral_add μ hg hv, hsum, hI]
  rfl

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
  have hU := modularUnitaryGroup_properties hM hΩ C hC
  have h : ∀ a b : ℝ, a + b = 0 → ∀ v, modularUnitaryGroup hM hΩ C hC a
      (modularUnitaryGroup hM hΩ C hC b v) = v := fun a b hab v => by
    rw [← hU.1.map_add, hab, hU.1.map_zero]
  have h₁ := h t (-t) (add_neg_cancel t)
  have h₂ := h (-t) t (neg_add_cancel t)
  refine ⟨fun x hx => modularUnitaryGroup_conj_mem_of_mem hM hΩ C hC t hx,
    fun α β x y => ?_, ?_, fun x y => ?_, fun x => ?_, fun x => ⟨?_, ?_⟩⟩
  · ext v; simp
  · ext v; simp [h₁]
  · ext v; simp [h₂]
  · rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, (hU.2.2 t).1,
      (hU.2.2 (-t)).1, neg_neg, ContinuousLinearMap.comp_assoc]
  · ext v; simp [h₂]
  · ext v; simp [h₁]

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
  have hU := (modularUnitaryGroup_properties hM hΩ C hC).1
  refine ⟨fun a => Subtype.ext ?_, fun s t a => Subtype.ext ?_⟩
  · ext v; simp [hU.map_zero]
  · ext v; simp [hU.map_add, neg_add_rev]

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
