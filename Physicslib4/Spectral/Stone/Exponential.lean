/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Stone.Basic

/-!
# Exponentiating a self-adjoint operator

For a self-adjoint operator `A`, the functional calculus applied to the bounded functions
`λ ↦ e^{itλ}` gives a strongly continuous one-parameter unitary group `t ↦ e^{itA}` whose
infinitesimal generator is `A` (blueprint §10.4.3, Proposition `prpstn:hall-10.14`).

## Main definitions

* `expFun t` — the function `λ ↦ e^{itλ}` on `ℝ`.
* `expUnitary hA t` — the unitary `e^{itA}`, the bounded integral of `expFun t` against the
  spectral measure of `A`.

## Main statements

* `isOneParameterUnitaryGroup_expUnitary`, `isStronglyContinuous_expUnitary`.
* `tendsto_generatorQuotient_expUnitary` — the derivative of `e^{itA}` at `0` on `Dom(A)`.
* `generator_expUnitary` — the generator of `t ↦ e^{itA}` is `A`.
-/

namespace Physicslib4
namespace Spectral
namespace Stone

open scoped InnerProductSpace LinearPMap Topology
open Filter MeasureTheory Unbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/--
The function `f_t(λ) = e^{itλ}` on `ℝ`.

Blueprint reference: `def:exp-unitary-group`.
-/
noncomputable def expFun (t : ℝ) (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))

/-- `f_t` is bounded and measurable. -/
theorem expFun_mem_bddMeasurable (t : ℝ) : expFun t ∈ BddMeasurable ℝ :=
  ⟨by unfold expFun; fun_prop, 1, fun x => (Complex.norm_exp_I_mul_ofReal _).le⟩

/--
For a projection-valued measure `μ` on `ℝ` (in particular the spectral measure of a
self-adjoint operator), the bounded integral of `f_t(λ) = e^{itλ}` is unitary.

Blueprint reference: `lmm:exp-unitary`.
-/
theorem integral_expFun_mem_unitary (μ : ProjectionValuedMeasure ℝ H) (t : ℝ) :
    μ.integral (expFun t) ∈ unitary (H →L[ℂ] H) := by
  have hf := expFun_mem_bddMeasurable t
  have hn : ∀ x, ‖expFun t x‖ = 1 := fun x => Complex.norm_exp_I_mul_ofReal _
  have hg : (fun x => (starRingEnd ℂ) (expFun t x)) ∈ BddMeasurable ℝ :=
    ⟨Complex.continuous_conj.measurable.comp hf.1, 1, fun x => by simp [hn]⟩
  have h1 : (fun x => (starRingEnd ℂ) (expFun t x)) * expFun t = 1 := funext fun x => by
    simp [Complex.conj_mul', hn]
  have h2 : expFun t * (fun x => (starRingEnd ℂ) (expFun t x)) = 1 := funext fun x => by
    simp [Complex.mul_conj', hn]
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint,
    ← ProjectionValuedMeasure.integral_conj μ hf, ← ProjectionValuedMeasure.integral_mul μ hg hf,
    ← ProjectionValuedMeasure.integral_mul μ hf hg, h1, h2, ProjectionValuedMeasure.integral_one]
  exact ⟨rfl, rfl⟩

/--
The unitary `e^{itA} = f_t(A) = ∫ e^{itλ} dμ^A(λ)`, the bounded integral of `f_t` against the
spectral measure of `A`, packaged as a linear isometry equivalence. That it is the functional
calculus `f_t(A)` is `functionalCalculus_expFun`.

Blueprint reference: `def:exp-unitary-group`.
-/
noncomputable def expUnitary (hA : IsSelfAdjoint A) (t : ℝ) : H ≃ₗᵢ[ℂ] H :=
  Unitary.linearIsometryEquiv
    ⟨(Unbounded.spectralMeasure hA).integral (expFun t), integral_expFun_mem_unitary _ t⟩

theorem expUnitary_apply (hA : IsSelfAdjoint A) (t : ℝ) (ψ : H) :
    expUnitary hA t ψ = (Unbounded.spectralMeasure hA).integral (expFun t) ψ :=
  rfl

/--
`e^{itA}` is the functional calculus `f_t(A)`, defined on all of `H`.

Blueprint reference: `def:exp-unitary-group`.
-/
theorem functionalCalculus_expFun (hA : IsSelfAdjoint A) (t : ℝ) :
    Unbounded.functionalCalculus hA (expFun t) =
      ((expUnitary hA t).toLinearIsometry.toLinearMap.toPMap ⊤) :=
  (functionalCalculus_of_bddMeasurable hA (expFun_mem_bddMeasurable t)).2

/--
The group law: `e^{i0A} = 1` and `e^{i(s+t)A} = e^{isA} e^{itA}`.

Blueprint reference: `lmm:exp-group-law`.
-/
theorem isOneParameterUnitaryGroup_expUnitary (hA : IsSelfAdjoint A) :
    IsOneParameterUnitaryGroup (expUnitary hA) := by
  have h0 : expFun 0 = 1 := funext fun x => by simp [expFun]
  have hadd : ∀ s t, expFun (s + t) = expFun s * expFun t := fun s t => funext fun x => by
    simp only [expFun, Pi.mul_apply, ← Complex.exp_add]
    congr 1; push_cast; ring
  refine ⟨fun ψ => ?_, fun s t ψ => ?_⟩
  · rw [expUnitary_apply, h0, ProjectionValuedMeasure.integral_one]; rfl
  · rw [expUnitary_apply, expUnitary_apply, expUnitary_apply, hadd,
      ProjectionValuedMeasure.integral_mul _ (expFun_mem_bddMeasurable s)
        (expFun_mem_bddMeasurable t)]
    rfl

/--
`t ↦ e^{itA}` is strongly continuous.

Blueprint reference: `lmm:exp-strongly-continuous`.
-/
theorem isStronglyContinuous_expUnitary (hA : IsSelfAdjoint A) :
    IsStronglyContinuous (expUnitary hA) := by
  intro ψ
  set μ := Unbounded.spectralMeasure hA
  have hcont : ∀ x : ℝ, Continuous fun s : ℝ => expFun s x := fun x => by
    unfold expFun; fun_prop
  have hnorm : ∀ s x, ‖expFun s x‖ = 1 := fun s x => by
    rw [expFun, mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have key : ∀ s t, ‖expUnitary hA s ψ - expUnitary hA t ψ‖ ^ 2 =
      ∫ x, ‖expFun s x - expFun t x‖ ^ 2 ∂(μ.assoc ψ) := fun s t => by
    have hs := expFun_mem_bddMeasurable s
    have ht := expFun_mem_bddMeasurable t
    have h : expFun s - expFun t = expFun s + (-1 : ℂ) • expFun t := by
      rw [neg_one_smul, sub_eq_add_neg]
    have := norm_sq_integral_apply (μ := μ) ((BddMeasurable ℝ).sub_mem hs ht) ψ
    rw [h, μ.integral_add hs ((BddMeasurable ℝ).smul_mem _ ht), μ.integral_smul _ ht,
      ← h] at this
    simpa [expUnitary_apply, sub_eq_add_neg] using this
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hint : Tendsto (fun s => ∫ x, ‖expFun s x - expFun t x‖ ^ 2 ∂(μ.assoc ψ)) (𝓝 t)
      (𝓝 (∫ x, ‖expFun t x - expFun t x‖ ^ 2 ∂(μ.assoc ψ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 4) ?_ ?_
      (integrable_const _) ?_
    · exact Eventually.of_forall fun s =>
        Continuous.aestronglyMeasurable (by unfold expFun; fun_prop)
    · refine Eventually.of_forall fun s => ae_of_all _ fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : ‖expFun s x - expFun t x‖ ≤ 2 := by
        calc _ ≤ ‖expFun s x‖ + ‖expFun t x‖ := norm_sub_le _ _
          _ = 2 := by rw [hnorm, hnorm]; norm_num
      nlinarith [norm_nonneg (expFun s x - expFun t x)]
    · exact ae_of_all _ fun x =>
        (((hcont x).sub continuous_const).norm.pow 2).tendsto t
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    integral_zero] at hint
  have := (Real.continuous_sqrt.tendsto 0).comp hint
  rw [Real.sqrt_zero] at this
  refine this.congr fun s => ?_
  simp only [Function.comp_apply, ← key, Real.sqrt_sq (norm_nonneg _)]

/-- For bounded measurable `g`, `W_{g - f} = W_f`. -/
private theorem integralDomain_sub_of_bddMeasurable (μ : ProjectionValuedMeasure ℝ H)
    {f g : ℝ → ℂ} (hg : g ∈ BddMeasurable ℝ) :
    integralDomain μ (g - f) = integralDomain μ f := by
  have hg' : ∀ ψ : H, MemLp g 2 (μ.assoc ψ) := fun ψ => by
    rw [← mem_integralDomain, integralDomain_eq_top_of_bddMeasurable μ hg]; trivial
  ext ψ
  refine ⟨fun h => ?_, fun h => (hg' ψ).sub h⟩
  simpa using (hg' ψ).sub h

/-- For an arbitrary PVM, `∫ (g - f) dμ = ∫ g dμ - ∫ f dμ` when `g` is bounded. -/
private theorem pmapIntegral_sub_of_bddMeasurable (μ : ProjectionValuedMeasure ℝ H)
    {f g : ℝ → ℂ} (hf : Measurable f) (hg : g ∈ BddMeasurable ℝ) :
    pmapIntegral μ (g - f) = pmapIntegral μ g - pmapIntegral μ f := by
  have hgm := measurable_of_mem_bddMeasurable hg
  refine (eq_pmapIntegral_of_inner_self μ (hgm.sub hf) _ ?_ fun ψ => ?_).symm
  · rw [LinearPMap.sub_domain, pmapIntegral_domain, pmapIntegral_domain,
      integralDomain_eq_top_of_bddMeasurable μ hg, top_inf_eq,
      integralDomain_sub_of_bddMeasurable μ hg]
  · have h1 : MemLp g 2 (μ.assoc ψ) := ψ.2.1
    have h2 : MemLp f 2 (μ.assoc ψ) := ψ.2.2
    rw [LinearPMap.sub_apply, inner_sub_right]
    refine (congrArg₂ _ (inner_self_pmapIntegral μ hgm ⟨ψ, ψ.2.1⟩)
      (inner_self_pmapIntegral μ hf ⟨ψ, ψ.2.2⟩)).trans ?_
    rw [Pi.sub_def, integral_sub (h1.integrable one_le_two) (h2.integrable one_le_two)]

/--
Subtracting an unbounded function from a bounded one: for measurable `f` and bounded
measurable `g`, `(g - f)(A) = g(A) - f(A)` as unbounded operators. The domain of the right
side is `H ⊓ W_f = W_f`, so this says both `W_{g - f} = W_f` and
`(g - f)(A) ψ = g(A) ψ - f(A) ψ` on `W_f`.

Blueprint reference: `lmm:functional-calculus-sub-bounded`.
-/
theorem functionalCalculus_sub_of_bddMeasurable (hA : IsSelfAdjoint A) {f g : ℝ → ℂ}
    (hf : Measurable f) (hg : g ∈ BddMeasurable ℝ) :
    Unbounded.functionalCalculus hA (g - f) =
      Unbounded.functionalCalculus hA g - Unbounded.functionalCalculus hA f :=
  pmapIntegral_sub_of_bddMeasurable _ hf hg

/--
The norm identity for the difference quotient: for `ψ ∈ Dom(A)` and every `t`, with
`g_t(λ) = (1/i)(e^{itλ} - 1)/t`,
`‖(1/i)(e^{itA}ψ - ψ)/t - Aψ‖² = ∫ |g_t(λ) - λ|² dμ^A_ψ(λ)`.
The blueprint states it for `t ≠ 0`; it also holds at `t = 0`, where both sides are `‖Aψ‖²`
by the convention `0⁻¹ = 0`, so no hypothesis on `t` is needed.

Blueprint reference: `lmm:exp-quotient-norm-identity`.
-/
theorem norm_sq_generatorQuotient_expUnitary_sub (hA : IsSelfAdjoint A) (ψ : A.domain)
    (t : ℝ) :
    ‖generatorQuotient (expUnitary hA) ψ t - A ψ‖ ^ 2 =
      ∫ x, ‖(Complex.I * (t : ℂ))⁻¹ * (expFun t x - 1) - (x : ℂ)‖ ^ 2
        ∂((Unbounded.spectralMeasure hA).assoc (ψ : H)) := by
  set μ := Unbounded.spectralMeasure hA
  set ι : ℝ → ℂ := fun x => (x : ℂ)
  set g : ℝ → ℂ := (Complex.I * (t : ℂ))⁻¹ • (expFun t - 1) with hg_def
  have hexp := expFun_mem_bddMeasurable t
  have h1 : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := ⟨measurable_const, 1, fun _ => by simp⟩
  have hg : g ∈ BddMeasurable ℝ :=
    (BddMeasurable ℝ).smul_mem _ ((BddMeasurable ℝ).sub_mem hexp h1)
  have hι : Measurable ι := Complex.measurable_ofReal
  have hintg : μ.integral g = (Complex.I * (t : ℂ))⁻¹ • (μ.integral (expFun t) - 1) := by
    rw [hg_def, ProjectionValuedMeasure.integral_smul _ _ ((BddMeasurable ℝ).sub_mem hexp h1),
      sub_eq_add_neg, ProjectionValuedMeasure.integral_add _ hexp ((BddMeasurable ℝ).neg_mem h1),
      ← neg_one_smul ℂ (1 : ℝ → ℂ), ProjectionValuedMeasure.integral_smul _ _ h1,
      ProjectionValuedMeasure.integral_one, neg_one_smul, ← sub_eq_add_neg]
  have hsub := functionalCalculus_sub_of_bddMeasurable hA hι hg
  have hψι : (ψ : H) ∈ integralDomain μ ι := by
    rw [← domain_eq_integralDomain_spectralMeasure hA]; exact ψ.2
  have hψg : (ψ : H) ∈ (Unbounded.functionalCalculus hA g).domain := by
    rw [(functionalCalculus_of_bddMeasurable hA hg).1]; trivial
  have hψ : (ψ : H) ∈
      (Unbounded.functionalCalculus hA g - Unbounded.functionalCalculus hA ι).domain :=
    ⟨hψg, hψι⟩
  have hψ' : (ψ : H) ∈ integralDomain μ (g - ι) := by
    rw [← Unbounded.functionalCalculus_domain, hsub]; exact hψ
  let φ : integralDomain μ (g - ι) := ⟨ψ, hψ'⟩
  have key : pmapIntegral μ (g - ι) φ =
      generatorQuotient (expUnitary hA) ψ t - A ψ := by
    have e1 := (LinearPMap.ext_iff.mp hsub).2 (x := (ψ : H)) (hf := hψ') (hg := hψ)
    change pmapIntegral μ (g - ι) _ = _ at e1
    refine e1.trans ?_
    rw [LinearPMap.sub_apply]
    have e2 := (LinearPMap.ext_iff.mp (functionalCalculus_of_bddMeasurable hA hg).2).2
      (x := (ψ : H)) (hf := hψg) (hg := Submodule.mem_top)
    have e3 := (LinearPMap.ext_iff.mp (functionalCalculus_id hA)).2
      (x := (ψ : H)) (hf := hψι) (hg := ψ.2)
    rw [e2, e3]
    change μ.integral g (ψ : H) - A ψ = _
    rw [hintg]
    rfl
  have hn := norm_sq_pmapIntegral μ (hg.1.sub hι) φ
  rw [key] at hn
  exact hn

/--
The derivative of `e^{itA}` at `0`: for `ψ ∈ Dom(A)`, `(1/i)(e^{itA}ψ - ψ)/t → Aψ` as
`t → 0`, `t ≠ 0`.

Blueprint reference: `lmm:exp-derivative-at-zero`.
-/
theorem tendsto_generatorQuotient_expUnitary (hA : IsSelfAdjoint A) (ψ : A.domain) :
    Tendsto (generatorQuotient (expUnitary hA) ψ) (𝓝[≠] 0) (𝓝 (A ψ)) := by
  set μ := (Unbounded.spectralMeasure hA).assoc (ψ : H)
  have hmem : MemLp (fun x : ℝ => (x : ℂ)) 2 μ :=
    (mem_integralDomain _).1 (domain_eq_integralDomain_spectralMeasure hA ▸ ψ.2)
  have hint : Integrable (fun x : ℝ => (3 * ‖(x : ℂ)‖) ^ 2) μ := by
    simpa [mul_pow] using (hmem.integrable_norm_pow two_ne_zero).const_mul (3 ^ 2)
  have hlim : ∀ x : ℝ, Tendsto (fun t : ℝ => (Complex.I * (t : ℂ))⁻¹ * (expFun t x - 1))
      (𝓝[≠] 0) (𝓝 (x : ℂ)) := by
    intro x
    have h1 : HasDerivAt (fun s : ℝ => Complex.I * ((s * x : ℝ) : ℂ)) (Complex.I * x) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).mul_const x).ofReal_comp).const_mul Complex.I
    have h2 := (h1.cexp).tendsto_slope_zero.const_mul Complex.I⁻¹
    simp only [zero_add, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h2
    rw [← mul_assoc, inv_mul_cancel₀ Complex.I_ne_zero, one_mul] at h2
    refine h2.congr fun t => ?_
    simp [expFun, Complex.real_smul, mul_assoc]
    ring
  have hint0 : Tendsto
      (fun t : ℝ => ∫ x, ‖(Complex.I * (t : ℂ))⁻¹ * (expFun t x - 1) - (x : ℂ)‖ ^ 2 ∂μ)
      (𝓝[≠] 0) (𝓝 0) := by
    have hexp : ∀ y : ℝ, ‖Complex.exp (Complex.I * (y : ℂ)) - 1‖ ≤ 2 * |y| := by
      intro y
      rcases le_or_gt |y| 1 with hy | hy
      · simpa using Complex.norm_exp_sub_one_le (x := Complex.I * y) (by simpa using hy)
      · calc _ ≤ ‖Complex.exp (Complex.I * (y : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ 2 * |y| := by
            rw [mul_comm, Complex.norm_exp_ofReal_mul_I, norm_one]; linarith
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[≠] (0 : ℝ))
      (F := fun t x => ‖(Complex.I * (t : ℂ))⁻¹ * (expFun t x - 1) - (x : ℂ)‖ ^ 2)
      (f := fun _ => 0) (fun x : ℝ => (3 * ‖(x : ℂ)‖) ^ 2) ?_ ?_ hint ?_
    · simpa using this
    · refine Eventually.of_forall fun t => ?_
      exact (Continuous.aestronglyMeasurable (by fun_prop [expFun]))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      refine Eventually.of_forall fun x => ?_
      have hle : ‖(Complex.I * (t : ℂ))⁻¹ * (expFun t x - 1)‖ ≤ 2 * ‖(x : ℂ)‖ := by
        have := hexp (t * x)
        have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
        rw [norm_mul, norm_inv, norm_mul, Complex.norm_I, one_mul, inv_mul_le_iff₀
          (norm_pos_iff.2 ht')]
        simp only [expFun, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul] at this ⊢
        rw [abs_mul] at this
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
      calc _ ≤ _ + _ := norm_sub_le _ _
        _ ≤ _ := by linarith
    · refine Eventually.of_forall fun x => ?_
      have := ((hlim x).sub_const (x : ℂ)).norm.pow 2
      simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq := hint0.sqrt
  simp only [Real.sqrt_zero] at hsq
  refine hsq.congr fun t => ?_
  rw [← norm_sq_generatorQuotient_expUnitary_sub hA ψ t, Real.sqrt_sq (norm_nonneg _)]

/--
**Exponentiating a self-adjoint operator.** For self-adjoint `A`, `t ↦ e^{itA}` is a strongly
continuous one-parameter unitary group whose infinitesimal generator is `A`, with equality of
domains. The last conjunct is points 2 and 3 of the blueprint proposition together.

Blueprint reference: `prpstn:hall-10.14`.
-/
theorem generator_expUnitary (hA : IsSelfAdjoint A) :
    IsOneParameterUnitaryGroup (expUnitary hA) ∧ IsStronglyContinuous (expUnitary hA) ∧
      generator (expUnitary hA) = A := by
  have hU := isOneParameterUnitaryGroup_expUnitary hA
  have key (ψ : A.domain) :
      ∃ h : (ψ : H) ∈ (generator (expUnitary hA)).domain,
        generator (expUnitary hA) ⟨ψ, h⟩ = A ψ :=
    (exists_generator_eq_iff _ _ _).2 (tendsto_generatorQuotient_expUnitary hA ψ)
  have hle : A ≤ generator (expUnitary hA) := by
    refine ⟨fun ψ hψ => (key ⟨ψ, hψ⟩).1, fun x y hxy => ?_⟩
    obtain ⟨h, hx⟩ := key x
    rw [← hx]
    congr 1
    exact Subtype.ext hxy
  exact ⟨hU, isStronglyContinuous_expUnitary hA,
    (eq_of_isSelfAdjoint_of_isSymmetric_of_le hA (isSymmetric_generator hU) hle).symm⟩

end Stone
end Spectral
end Physicslib4
