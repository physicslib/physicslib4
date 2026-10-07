/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Stone.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

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

/-- `‖e^{isλ}‖ = 1`. -/
private theorem norm_expFun (s x : ℝ) : ‖expFun s x‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

/-- `f_t` is bounded and measurable. -/
theorem expFun_mem_bddMeasurable (t : ℝ) : expFun t ∈ BddMeasurable ℝ :=
  ⟨by unfold expFun; fun_prop, 1, fun x => (norm_expFun t x).le⟩

/--
For a projection-valued measure `μ` on `ℝ` (in particular the spectral measure of a
self-adjoint operator), the bounded integral of `f_t(λ) = e^{itλ}` is unitary.

Blueprint reference: `lmm:exp-unitary`.
-/
theorem integral_expFun_mem_unitary (μ : ProjectionValuedMeasure ℝ H) (t : ℝ) :
    μ.integral (expFun t) ∈ unitary (H →L[ℂ] H) := by
  have hf := expFun_mem_bddMeasurable t
  have hn := norm_expFun t
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

/-- For bounded measurable `f, g`, `∫ (f - g) dμ = ∫ f dμ - ∫ g dμ`. -/
private theorem integral_sub_of_mem_bddMeasurable (μ : ProjectionValuedMeasure ℝ H)
    {f g : ℝ → ℂ} (hf : f ∈ BddMeasurable ℝ) (hg : g ∈ BddMeasurable ℝ) :
    μ.integral (f - g) = μ.integral f - μ.integral g := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ g, μ.integral_add hf ((BddMeasurable ℝ).smul_mem _ hg),
    μ.integral_smul _ hg, neg_one_smul, ← sub_eq_add_neg]

/-- If `‖f t - a‖² → 0` then `f t → a`. -/
private theorem tendsto_of_norm_sub_sq_tendsto_zero {α E : Type*} [SeminormedAddCommGroup E]
    {l : Filter α} {f : α → E} {a : E} (h : Tendsto (fun t => ‖f t - a‖ ^ 2) l (𝓝 0)) :
    Tendsto f l (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.sqrt_sq (norm_nonneg _)] using h.sqrt

/--
Dominated convergence in the form used for `e^{itA}`: if `G t → g` pointwise with
`‖G t - g‖ ≤ b` and `b²` integrable, then `∫ ‖G t - g‖² → 0`.
-/
private theorem tendsto_integral_norm_sub_sq {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {ν : Measure ℝ} {G : α → ℝ → ℂ} {g : ℝ → ℂ} {b : ℝ → ℝ} (hG : ∀ t, Continuous (G t))
    (hg : Continuous g) (hb : Integrable (fun x => b x ^ 2) ν) (hle : ∀ t x, ‖G t x - g x‖ ≤ b x)
    (hlim : ∀ x, Tendsto (fun t => G t x) l (𝓝 (g x))) :
    Tendsto (fun t => ∫ x, ‖G t x - g x‖ ^ 2 ∂ν) l (𝓝 0) := by
  have hm (t : α) : Continuous fun x => ‖G t x - g x‖ ^ 2 := ((hG t).sub hg).norm.pow 2
  have := tendsto_integral_filter_of_dominated_convergence (l := l) (μ := ν)
    (F := fun t x => ‖G t x - g x‖ ^ 2) (f := fun x => ‖g x - g x‖ ^ 2) _
    (.of_forall fun t => (hm t).aestronglyMeasurable)
    (.of_forall fun t => ae_of_all _ fun x => ?_) hb
    (ae_of_all _ fun x => ((hlim x).sub_const (g x)).norm.pow 2)
  · simpa only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero] using this
  · rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hle t x) 2

/-- The norm identity `‖e^{isA}ψ - e^{itA}ψ‖² = ∫ |e^{isλ} - e^{itλ}|² dμ^A_ψ(λ)`. -/
private theorem norm_sq_expUnitary_sub (hA : IsSelfAdjoint A) (ψ : H) (s t : ℝ) :
    ‖expUnitary hA s ψ - expUnitary hA t ψ‖ ^ 2 =
      ∫ x, ‖expFun s x - expFun t x‖ ^ 2 ∂((Unbounded.spectralMeasure hA).assoc ψ) := by
  have hs := expFun_mem_bddMeasurable s
  have ht := expFun_mem_bddMeasurable t
  rw [expUnitary_apply, expUnitary_apply, ← sub_apply,
    ← integral_sub_of_mem_bddMeasurable _ hs ht,
    norm_sq_integral_apply _ ((BddMeasurable ℝ).sub_mem hs ht)]
  rfl

/--
`t ↦ e^{itA}` is strongly continuous.

Blueprint reference: `lmm:exp-strongly-continuous`.
-/
theorem isStronglyContinuous_expUnitary (hA : IsSelfAdjoint A) :
    IsStronglyContinuous (expUnitary hA) := fun ψ =>
  continuous_iff_continuousAt.2 fun t => tendsto_of_norm_sub_sq_tendsto_zero <| by
    simp_rw [norm_sq_expUnitary_sub]
    refine tendsto_integral_norm_sub_sq (b := fun _ => 2) (fun s => by fun_prop [expFun])
      (by fun_prop [expFun]) (integrable_const _) (fun s x => ?_)
      (fun x => (by fun_prop [expFun] : Continuous fun s => expFun s x).tendsto t)
    linarith [norm_sub_le (expFun s x) (expFun t x), norm_expFun s x, norm_expFun t x]

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
For bounded measurable `g` and `ψ ∈ Dom(A)`, `‖g(A)ψ - Aψ‖² = ∫ |g(λ) - λ|² dμ^A_ψ(λ)`.
-/
private theorem norm_sq_integral_apply_sub (hA : IsSelfAdjoint A) {g : ℝ → ℂ}
    (hg : g ∈ BddMeasurable ℝ) (ψ : A.domain) :
    ‖(Unbounded.spectralMeasure hA).integral g ψ - A ψ‖ ^ 2 =
      ∫ x, ‖g x - x‖ ^ 2 ∂((Unbounded.spectralMeasure hA).assoc (ψ : H)) := by
  have hsub := functionalCalculus_sub_of_bddMeasurable hA Complex.measurable_ofReal hg
  have hψg : (ψ : H) ∈ (Unbounded.functionalCalculus hA g).domain := by
    rw [(functionalCalculus_of_bddMeasurable hA hg).1]; trivial
  have hψι : (ψ : H) ∈ (Unbounded.functionalCalculus hA fun x : ℝ => (x : ℂ)).domain := by
    rw [functionalCalculus_id]; exact ψ.2
  have hψ : (ψ : H) ∈ integralDomain (Unbounded.spectralMeasure hA) (g - (↑)) := by
    rw [← Unbounded.functionalCalculus_domain, hsub]; exact ⟨hψg, hψι⟩
  have e1 := (LinearPMap.ext_iff.mp hsub).2 (x := (ψ : H)) (hf := hψ) (hg := ⟨hψg, hψι⟩)
  have e2 := (LinearPMap.ext_iff.mp (functionalCalculus_of_bddMeasurable hA hg).2).2
    (x := (ψ : H)) (hf := hψg) (hg := Submodule.mem_top)
  have e3 := (LinearPMap.ext_iff.mp (functionalCalculus_id hA)).2
    (x := (ψ : H)) (hf := hψι) (hg := ψ.2)
  rw [LinearPMap.sub_apply, e2, e3] at e1
  have hn := norm_sq_pmapIntegral _ (hg.1.sub Complex.measurable_ofReal)
    (⟨ψ, hψ⟩ : integralDomain (Unbounded.spectralMeasure hA) (g - (↑)))
  exact (congrArg (‖·‖ ^ 2) e1).symm.trans hn

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
  have hexp := expFun_mem_bddMeasurable t
  have h1 : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := ⟨measurable_const, 1, fun _ => by simp⟩
  have hd := (BddMeasurable ℝ).sub_mem hexp h1
  have := norm_sq_integral_apply_sub hA ((BddMeasurable ℝ).smul_mem (Complex.I * t)⁻¹ hd) ψ
  rwa [ProjectionValuedMeasure.integral_smul _ _ hd, integral_sub_of_mem_bddMeasurable _ hexp h1,
    ProjectionValuedMeasure.integral_one] at this

/-- The pointwise limit `(it)⁻¹(e^{itλ} - 1) → λ` as `t → 0`, `t ≠ 0`. -/
private theorem tendsto_expFun_quotient (x : ℝ) :
    Tendsto (fun t : ℝ => (Complex.I * (t : ℂ))⁻¹ * (expFun t x - 1)) (𝓝[≠] 0) (𝓝 (x : ℂ)) := by
  have h1 : HasDerivAt (fun s : ℝ => Complex.I * ((s * x : ℝ) : ℂ)) (Complex.I * x) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const x).ofReal_comp).const_mul Complex.I
  have h2 := (h1.cexp).tendsto_slope_zero.const_mul Complex.I⁻¹
  simp only [zero_add, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h2
  rw [← mul_assoc, inv_mul_cancel₀ Complex.I_ne_zero, one_mul] at h2
  refine h2.congr fun t => ?_
  simp [expFun, Complex.real_smul, mul_assoc]
  ring

/-- The bound `|(it)⁻¹(e^{itλ} - 1)| ≤ |λ|`. -/
private theorem norm_expFun_quotient_le (t x : ℝ) :
    ‖(Complex.I * (t : ℂ))⁻¹ * (expFun t x - 1)‖ ≤ ‖(x : ℂ)‖ := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_I, one_mul,
    inv_mul_le_iff₀ (norm_pos_iff.2 (Complex.ofReal_ne_zero.2 ht)), Complex.norm_real,
    Complex.norm_real, ← norm_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/--
The derivative of `e^{itA}` at `0`: for `ψ ∈ Dom(A)`, `(1/i)(e^{itA}ψ - ψ)/t → Aψ` as
`t → 0`, `t ≠ 0`.

Blueprint reference: `lmm:exp-derivative-at-zero`.
-/
theorem tendsto_generatorQuotient_expUnitary (hA : IsSelfAdjoint A) (ψ : A.domain) :
    Tendsto (generatorQuotient (expUnitary hA) ψ) (𝓝[≠] 0) (𝓝 (A ψ)) := by
  have hmem : MemLp (fun x : ℝ => (x : ℂ)) 2 ((Unbounded.spectralMeasure hA).assoc (ψ : H)) :=
    (mem_integralDomain _).1 (domain_eq_integralDomain_spectralMeasure hA ▸ ψ.2)
  refine tendsto_of_norm_sub_sq_tendsto_zero ?_
  simp_rw [norm_sq_generatorQuotient_expUnitary_sub hA ψ]
  refine tendsto_integral_norm_sub_sq (b := fun x => 2 * ‖(x : ℂ)‖) (fun t => by fun_prop [expFun])
    (by fun_prop) ?_ (fun t x => ?_) tendsto_expFun_quotient
  · simpa [mul_pow] using (hmem.integrable_norm_pow two_ne_zero).const_mul (2 ^ 2)
  · linarith [norm_sub_le ((Complex.I * (t : ℂ))⁻¹ * (expFun t x - 1)) (x : ℂ),
      norm_expFun_quotient_le t x]

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
