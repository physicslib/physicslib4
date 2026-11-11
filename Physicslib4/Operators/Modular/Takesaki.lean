/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Operators.Modular.Modular
import Physicslib4.Spectral.Unbounded.Spectrum
import Physicslib4.Spectral.Stone.Exponential

/-!
# Takesaki's lemma: the commutant extension lemma and the resolvent of `Δ`

For a von Neumann algebra `M` with a cyclic and separating vector `Ω`, this file states the
commutant extension lemma (a vector `ψ` with `‖b' ψ‖ ≤ c ‖b' Ω‖` for all `b' ∈ M'` is `a Ω` for a
unique `a ∈ M` with `‖a‖ ≤ c`) and the resolvent of the modular operator `Δ` off `[0, ∞)`.

For `z ∉ [0, ∞)` the resolvent function is `r_z = 1_{[0, ∞)} · (z - ι)⁻¹`, written inline as
`(Set.Ici 0).indicator fun t => (z - t)⁻¹`, and `d(z)` is the distance from `z` to `[0, ∞)`,
written `Metric.infDist z (ofReal '' Set.Ici 0)`. The bounded operator `r_z(Δ)` is the bounded
integral `(spectralMeasure _).integral r_z`, which is the functional calculus of `r_z` by
`modularResolvent_bounded`.
-/

namespace Physicslib4.Modular

open scoped InnerProductSpace ComplexConjugate
open Physicslib4.Spectral.Unbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
Under the commutant bound `‖b' ψ‖ ≤ c ‖b' Ω‖`, `b' Ω ↦ b' ψ` is a well-defined linear map
`T₀ : M' Ω → H`, unique, with `‖T₀ η‖ ≤ c ‖η‖`.

Implementation note: `M' Ω` is written as the span of `{b' Ω | b' ∈ M'}`, which is that set
since `M'` is a linear subspace.

Blueprint: lmm:commutant-extension-well-defined
-/
theorem commutantExtension_linearMap {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) {ψ : H} {c : ℝ} (hc : 0 ≤ c)
    (hψ : ∀ b ∈ Set.centralizer M, ‖b ψ‖ ≤ c * ‖b Ω‖) :
    (∃! T₀ : Submodule.span ℂ ((fun b => b Ω) '' Set.centralizer M) →ₗ[ℂ] H,
      ∀ (b : H →L[ℂ] H) (hb : b ∈ Set.centralizer M),
        T₀ ⟨b Ω, Submodule.subset_span ⟨b, hb, rfl⟩⟩ = b ψ) ∧
      ∀ T₀ : Submodule.span ℂ ((fun b => b Ω) '' Set.centralizer M) →ₗ[ℂ] H,
        (∀ (b : H →L[ℂ] H) (hb : b ∈ Set.centralizer M),
          T₀ ⟨b Ω, Submodule.subset_span ⟨b, hb, rfl⟩⟩ = b ψ) →
        ∀ η, ‖T₀ η‖ ≤ c * ‖(η : H)‖ := by
  set V := Submodule.span ℂ ((fun b => b Ω) '' Set.centralizer M)
  have hsmul : ∀ (a : ℂ) b, b ∈ Set.centralizer M → a • b ∈ Set.centralizer M :=
    fun a b hb m hm => by rw [smul_mul_assoc, mul_smul_comm, hb m hm]
  have hrep : ∀ η : V, ∃ b ∈ Set.centralizer M, b Ω = (η : H) := by
    rintro ⟨η, hη⟩
    induction hη using Submodule.span_induction with
    | mem x hx => obtain ⟨b, hb, rfl⟩ := hx; exact ⟨b, hb, rfl⟩
    | zero => exact ⟨0, Set.zero_mem_centralizer, rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨b, hb, hbx⟩ := hx; obtain ⟨b', hb', hby⟩ := hy
      exact ⟨b + b', Set.add_mem_centralizer hb hb', by simp [hbx, hby]⟩
    | smul a x _ hx =>
      obtain ⟨b, hb, hbx⟩ := hx
      exact ⟨a • b, hsmul a b hb, by simp [hbx]⟩
  have hwd : ∀ b ∈ Set.centralizer M, ∀ b' ∈ Set.centralizer M, b Ω = b' Ω → b ψ = b' ψ := by
    intro b hb b' hb' h
    have hsub : b - b' ∈ Set.centralizer M := by
      simpa [sub_eq_add_neg] using Set.add_mem_centralizer hb (hsmul (-1) b' hb')
    have h1 := hψ (b - b') hsub
    simp only [sub_apply, h, sub_self, norm_zero, mul_zero] at h1
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)
  have hbound : ∀ T₀ : V →ₗ[ℂ] H, (∀ (b : H →L[ℂ] H) (hb : b ∈ Set.centralizer M),
      T₀ ⟨b Ω, Submodule.subset_span ⟨b, hb, rfl⟩⟩ = b ψ) → ∀ η, ‖T₀ η‖ ≤ c * ‖(η : H)‖ := by
    intro T₀ hT₀ η
    obtain ⟨b, hb, hη⟩ := hrep η
    have : η = ⟨b Ω, Submodule.subset_span ⟨b, hb, rfl⟩⟩ := Subtype.ext hη.symm
    rw [this, hT₀ b hb]
    exact hψ b hb
  refine ⟨?_, hbound⟩
  choose f hf hfΩ using hrep
  refine ⟨{ toFun := fun η => f η ψ, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro x y
    rw [← add_apply]
    exact hwd _ (hf _) _ (Set.add_mem_centralizer (hf x) (hf y)) (by simp [hfΩ])
  · intro a x
    rw [RingHom.id_apply, ← smul_apply]
    exact hwd _ (hf _) _ (hsmul a _ (hf x)) (by simp [hfΩ])
  · intro b hb
    exact hwd _ (hf _) _ hb (hfΩ _)
  · intro T₁ hT₁
    ext η
    exact (congrArg T₁ (Subtype.ext (hfΩ η).symm)).trans (hT₁ _ (hf η))

/--
Under the commutant bound, there is a unique bounded `T` with `T (b' Ω) = b' ψ` for all
`b' ∈ M'`, and `‖T‖ ≤ c`.

Implementation note: extending `T₀` of `commutantExtension_linearMap` is stated as
`T (b' Ω) = b' ψ` for all `b' ∈ M'`.

Blueprint: lmm:commutant-extension-bounded
-/
theorem commutantExtension_bounded {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) {ψ : H} {c : ℝ} (hc : 0 ≤ c)
    (hψ : ∀ b ∈ Set.centralizer M, ‖b ψ‖ ≤ c * ‖b Ω‖) :
    ∃ T : H →L[ℂ] H, (∀ b ∈ Set.centralizer M, T (b Ω) = b ψ) ∧ ‖T‖ ≤ c ∧
      ∀ T' : H →L[ℂ] H, (∀ b ∈ Set.centralizer M, T' (b Ω) = b ψ) → T' = T := by
  set S := Submodule.span ℂ ((fun b => b Ω) '' Set.centralizer M)
  obtain ⟨⟨T₀, hT₀, -⟩, hbd⟩ := commutantExtension_linearMap hM hΩ hc hψ
  let T₁ : S →L[ℂ] H := T₀.mkContinuous c (hbd T₀ hT₀)
  have hdr : DenseRange S.subtypeL := (hΩ.2.mono Submodule.subset_span).denseRange_val
  have hui : IsUniformInducing S.subtypeL := isUniformEmbedding_subtype_val.isUniformInducing
  let T := T₁.extend S.subtypeL
  have hT : ∀ b ∈ Set.centralizer M, T (b Ω) = b ψ := fun b hb =>
    (ContinuousLinearMap.extend_eq T₁ hdr hui ⟨b Ω, Submodule.subset_span ⟨b, hb, rfl⟩⟩).trans
      (hT₀ b hb)
  refine ⟨T, hT, ?_, fun T' hT' => ContinuousLinearMap.ext (congrFun
    (hΩ.2.denseRange_val.equalizer T'.continuous T.continuous
      (funext fun ⟨_, hx⟩ => by
        obtain ⟨b, hb, rfl⟩ := hx
        exact (hT' b hb).trans (hT b hb).symm)))⟩
  calc ‖T‖ ≤ (1 : NNReal) * ‖T₁‖ :=
        ContinuousLinearMap.opNorm_extend_le (N := 1) T₁ hdr fun x => by simp
    _ ≤ c := by rw [NNReal.coe_one, one_mul]; exact T₀.mkContinuous_norm_le hc _

/--
A bounded `T` with `T (b' Ω) = b' ψ` for all `b' ∈ M'` commutes with every `d' ∈ M'`, and so
lies in `M'' = M`.

Implementation note: `T` is the operator of `commutantExtension_bounded`, characterized by its
values on `M' Ω`; the commutant bound is not needed for this step.

Blueprint: lmm:commutant-extension-in-algebra
-/
theorem commutantExtension_mem {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) {ψ : H} (T : H →L[ℂ] H)
    (hT : ∀ b ∈ Set.centralizer M, T (b Ω) = b ψ) :
    (∀ d ∈ Set.centralizer M, T * d = d * T) ∧ T ∈ M := by
  have key : ∀ d ∈ Set.centralizer M, T * d = d * T := fun d hd =>
    DFunLike.coe_injective <| Continuous.ext_on hΩ.2 (T * d).continuous
      (d * T).continuous <| by
        rintro _ ⟨b, hb, rfl⟩
        change T (d (b Ω)) = d (T (b Ω))
        rw [hT b hb]
        exact hT _ (Set.mul_mem_centralizer hd hb)
  exact ⟨key, hM.2 ▸ Set.mem_centralizer_iff.mpr fun d hd => (key d hd).symm⟩

/--
The commutant extension lemma: if `‖b' ψ‖ ≤ c ‖b' Ω‖` for all `b' ∈ M'`, then `ψ = a Ω` for a
unique `a ∈ M`, and `‖a‖ ≤ c`.

Blueprint: lmm:commutant-extension
-/
theorem commutantExtension {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) {ψ : H} {c : ℝ} (hc : 0 ≤ c)
    (hψ : ∀ b ∈ Set.centralizer M, ‖b ψ‖ ≤ c * ‖b Ω‖) :
    ∃ a ∈ M, a Ω = ψ ∧ ‖a‖ ≤ c ∧ ∀ a' ∈ M, a' Ω = ψ → a' = a := by
  obtain ⟨T, hT, hTc, -⟩ := commutantExtension_bounded hM hΩ hc hψ
  have hTΩ : T Ω = ψ := hT 1 Set.one_mem_centralizer
  have hTM := (commutantExtension_mem hM hΩ T hT).2
  refine ⟨T, hTM, hTΩ, hTc, fun a' ha' h => ?_⟩
  obtain ⟨A, hA⟩ := (isVonNeumannSet_centralizer hM).2.2.1
  rw [← hA] at ha' hTM
  exact sub_eq_zero.mp <| (isSeparatingVector_of_isCyclicSeparatingVector hΩ).1 _
    (hA ▸ sub_mem ha' hTM) (by rw [sub_apply, h, hTΩ, sub_self])

/--
For `z ∉ [0, ∞)`: `d(z) > 0`, `r_z` is measurable, `|r_z| ≤ 1/d(z)`, `conj r_z = r_{z̄}` and
`(z - λ) r_z(λ) = 1_{[0, ∞)}(λ)`.

Blueprint: lmm:resolvent-function-props
-/
theorem resolventFunction_properties {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) :
    0 < Metric.infDist z (((↑) : ℝ → ℂ) '' Set.Ici 0) ∧
      Measurable ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) ∧
      (∀ t : ℝ, ‖(Set.Ici (0 : ℝ)).indicator (fun t : ℝ => (z - t)⁻¹) t‖ ≤
        1 / Metric.infDist z (((↑) : ℝ → ℂ) '' Set.Ici 0)) ∧
      (∀ t : ℝ, conj ((Set.Ici (0 : ℝ)).indicator (fun t : ℝ => (z - t)⁻¹) t) =
        (Set.Ici (0 : ℝ)).indicator (fun t : ℝ => (conj z - t)⁻¹) t) ∧
      ∀ t : ℝ, (z - t) * (Set.Ici (0 : ℝ)).indicator (fun t : ℝ => (z - t)⁻¹) t =
        (Set.Ici (0 : ℝ)).indicator 1 t := by
  set S : Set ℂ := ((↑) : ℝ → ℂ) '' Set.Ici 0
  have hS : IsClosed S := Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ isClosed_Ici
  have hd : 0 < Metric.infDist z S :=
    (hS.notMem_iff_infDist_pos ⟨0, 0, Set.self_mem_Ici, rfl⟩).1 hz
  have hne : ∀ t : ℝ, 0 ≤ t → z - t ≠ 0 := fun t ht h =>
    hz ⟨t, ht, (sub_eq_zero.1 h).symm⟩
  refine ⟨hd, ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · exact (Measurable.inv (by fun_prop)).indicator measurableSet_Ici
  · by_cases ht : t ∈ Set.Ici (0 : ℝ)
    · rw [Set.indicator_of_mem ht, norm_inv, one_div]
      refine inv_anti₀ hd ?_
      rw [← dist_eq_norm]
      exact Metric.infDist_le_dist_of_mem ⟨t, ht, rfl⟩
    · rw [Set.indicator_of_notMem ht, norm_zero]
      positivity
  · by_cases ht : t ∈ Set.Ici (0 : ℝ)
    · simp [Set.indicator_of_mem ht, map_inv₀, map_sub, Complex.conj_ofReal]
    · simp [Set.indicator_of_notMem ht]
  · by_cases ht : t ∈ Set.Ici (0 : ℝ)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, mul_inv_cancel₀ (hne t ht)]
      rfl
    · simp [Set.indicator_of_notMem ht]

/--
For `z ∉ [0, ∞)`, `r_z(Δ)` is the bounded operator `∫ r_z dμ^Δ` on all of `H`, with
`‖r_z(Δ)‖ ≤ 1/d(z)` and `r_z(Δ)* = r_{z̄}(Δ)`.

Blueprint: lmm:modular-resolvent-bounded
-/
theorem modularResolvent_bounded {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) :
    functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC)
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) =
      (((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) : H →ₗ[ℂ] H).toPMap ⊤) ∧
    ‖(spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹)‖ ≤
      1 / Metric.infDist z (((↑) : ℝ → ℂ) '' Set.Ici 0) ∧
    ContinuousLinearMap.adjoint
        ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹)) =
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (conj z - t)⁻¹) := by
  obtain ⟨-, hmeas, hbd, hconj, -⟩ := resolventFunction_properties hz
  have hf : ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) ∈
      Spectral.BddMeasurable ℝ := ⟨hmeas, _, hbd⟩
  set μ := spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)
  refine ⟨(functionalCalculus_of_bddMeasurable _ hf).2,
    (μ.norm_integral_le hf).trans (ciSup_le hbd), ?_⟩
  rw [← μ.integral_conj hf]
  exact congrArg μ.integral (funext hconj)

/--
For `z ∈ ℂ`, `W_{z - ι} = Dom Δ` and `(z - ι)(Δ) ψ = z ψ - Δ ψ` for `ψ ∈ Dom Δ`.

Blueprint: lmm:modular-z-minus-fc
-/
theorem modularOperator_functionalCalculus_const_sub {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (z : ℂ) :
    (functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC)
        fun t : ℝ => z - t).domain = (modularOperator M Ω C).domain ∧
      ∀ (ψ : H) (h₁ : ψ ∈ (functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC)
          fun t : ℝ => z - t).domain) (h₂ : ψ ∈ (modularOperator M Ω C).domain),
        functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC) (fun t : ℝ => z - t)
          ⟨ψ, h₁⟩ = z • ψ - modularOperator M Ω C ⟨ψ, h₂⟩ := by
  set hA := modularOperator_isSelfAdjoint hM hΩ C hC
  have hg : (fun _ : ℝ => z) ∈ Spectral.BddMeasurable ℝ :=
    ⟨measurable_const, ‖z‖, fun _ => le_rfl⟩
  have hsub : functionalCalculus hA (fun t : ℝ => z - t) =
      functionalCalculus hA (fun _ : ℝ => z) - modularOperator M Ω C := by
    have h :=
      Spectral.Stone.functionalCalculus_sub_of_bddMeasurable hA Complex.measurable_ofReal hg
    rwa [functionalCalculus_id hA] at h
  obtain ⟨hgdom, hgval⟩ := functionalCalculus_of_bddMeasurable hA hg
  have hdom : (functionalCalculus hA fun t : ℝ => z - t).domain =
      (modularOperator M Ω C).domain := by
    rw [hsub, LinearPMap.sub_domain, hgdom, top_inf_eq]
  refine ⟨hdom, fun ψ h₁ h₂ => ?_⟩
  have hψg : ψ ∈ (functionalCalculus hA fun _ : ℝ => z).domain := by rw [hgdom]; trivial
  have e1 := (LinearPMap.ext_iff.mp hsub).2 (x := ψ) (hf := h₁) (hg := ⟨hψg, h₂⟩)
  have e2 := (LinearPMap.ext_iff.mp hgval).2 (x := ψ) (hf := hψg) (hg := Submodule.mem_top)
  have hconst : (Spectral.Unbounded.spectralMeasure hA).integral (fun _ : ℝ => z) = z • 1 := by
    rw [show (fun _ : ℝ => z) = z • (1 : ℝ → ℂ) by ext; simp,
      Spectral.ProjectionValuedMeasure.integral_smul _ _ (f := 1)
        ⟨measurable_const, 1, fun _ => by simp⟩,
      Spectral.ProjectionValuedMeasure.integral_one]
  have e2' : functionalCalculus hA (fun _ : ℝ => z) ⟨ψ, hψg⟩ = z • ψ := by
    rw [e2]
    change (Spectral.Unbounded.spectralMeasure hA).integral (fun _ : ℝ => z) ψ = z • ψ
    rw [hconst]; simp
  rw [e1, LinearPMap.sub_apply]
  exact congrArg (· - _) e2'

/--
`1_{[0, ∞)}(Δ) = 𝟙`.

Blueprint: lmm:modular-indicator-nonneg-one
-/
theorem modularOperator_functionalCalculus_indicator_Ici {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC) ((Set.Ici (0 : ℝ)).indicator 1) =
      (LinearMap.id : H →ₗ[ℂ] H).toPMap ⊤ := by
  have hpos := (modularOperator_properties hM hΩ C hC).1
  have hone : (1 : ℝ → ℂ) ∈ Spectral.BddMeasurable ℝ := ⟨measurable_const, 1, fun _ => by simp⟩
  refine (pmapIntegral_congr_of_null _ (g := 1) (measurable_const.indicator measurableSet_Ici)
    measurable_const measurableSet_Iio
    (spectralMeasure_Iio_zero_eq_zero_of_isPositive _ hpos) fun x hx => ?_).trans ?_
  · exact Set.indicator_of_mem (Set.mem_Ici.2 (not_lt.1 hx)) _
  · rw [pmapIntegral_of_bddMeasurable _ hone, Spectral.ProjectionValuedMeasure.integral_one]
    rfl

/--
For `z ∉ [0, ∞)` and `ξ ∈ H`, `r_z(Δ) ξ ∈ Dom Δ` and `z r_z(Δ) ξ - Δ r_z(Δ) ξ = ξ`.

Blueprint: lmm:modular-resolvent-right-inverse
-/
theorem modularResolvent_rightInverse {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) (ξ : H) :
    ∃ h : (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) ξ ∈ (modularOperator M Ω C).domain,
      z • (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) ξ -
        modularOperator M Ω C ⟨_, h⟩ = ξ := by
  set hA := modularOperator_isSelfAdjoint hM hΩ C hC
  set μ := spectralMeasure hA
  set r : ℝ → ℂ := (Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹
  obtain ⟨-, hrm, hrb, -, hgr⟩ := resolventFunction_properties hz
  have hr : r ∈ Spectral.BddMeasurable ℝ := ⟨hrm, _, hrb⟩
  have hgm : Measurable fun t : ℝ => z - (t : ℂ) := by fun_prop
  have hfun : (fun t : ℝ => z - (t : ℂ)) * r = (Set.Ici (0 : ℝ)).indicator 1 := funext hgr
  have hξ : ξ ∈ integralDomain μ r := by
    rw [integralDomain_eq_top_of_bddMeasurable μ hr]; trivial
  have hpr : pmapIntegral μ r ⟨ξ, hξ⟩ = μ.integral r ξ := by
    obtain ⟨-, hext⟩ := LinearPMap.ext_iff.mp (pmapIntegral_of_bddMeasurable μ hr)
    rw [@hext ξ hξ Submodule.mem_top]; rfl
  have hη : pmapIntegral μ r ⟨ξ, hξ⟩ ∈ integralDomain μ (fun t : ℝ => z - (t : ℂ)) := by
    refine (pmapIntegral_mem_integralDomain_iff μ hgm hrm ⟨ξ, hξ⟩).2 ?_
    have h1 : (Set.Ici (0 : ℝ)).indicator (1 : ℝ → ℂ) ∈ Spectral.BddMeasurable ℝ :=
      ⟨measurable_const.indicator measurableSet_Ici, 1, fun t => by
        by_cases ht : t ∈ Set.Ici (0 : ℝ) <;> simp [ht]⟩
    rw [hfun, integralDomain_eq_top_of_bddMeasurable μ h1]
    trivial
  obtain ⟨hfg, hcomp⟩ := (pmapIntegral_comp μ hgm hrm).2 ⟨ξ, hξ⟩ hη
  obtain ⟨hdom, hval⟩ := modularOperator_functionalCalculus_const_sub hM hΩ C hC z
  have hηD : μ.integral r ξ ∈ (modularOperator M Ω C).domain := by
    rw [← hpr, ← hdom]; exact hη
  refine ⟨hηD, ?_⟩
  have hI := modularOperator_functionalCalculus_indicator_Ici hM hΩ C hC
  rw [← hfun] at hI
  have hξ1 := (LinearPMap.ext_iff.mp hI).2 (x := ξ) (hf := hfg) (hg := Submodule.mem_top)
  have h₁ : μ.integral r ξ ∈ (functionalCalculus hA fun t : ℝ => z - t).domain := by
    rw [hdom]; exact hηD
  rw [← hval _ h₁ hηD]
  calc functionalCalculus hA (fun t : ℝ => z - t) ⟨μ.integral r ξ, h₁⟩
      = pmapIntegral μ (fun t : ℝ => z - (t : ℂ)) ⟨_, hη⟩ :=
        congrArg (functionalCalculus hA _) (Subtype.ext hpr.symm)
    _ = ξ := hcomp.symm.trans hξ1

/--
For `z ∉ [0, ∞)` and `ψ ∈ Dom Δ`, `r_z(Δ) (z ψ - Δ ψ) = ψ`.

Blueprint: lmm:modular-resolvent-left-inverse
-/
theorem modularResolvent_leftInverse {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0)
    (ψ : (modularOperator M Ω C).domain) :
    (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹)
        (z • (ψ : H) - modularOperator M Ω C ψ) = ψ := by
  set hA := modularOperator_isSelfAdjoint hM hΩ C hC
  set μ := spectralMeasure hA
  obtain ⟨-, hmeas, hbd, -, hmul⟩ := resolventFunction_properties hz
  obtain ⟨hdom, hval⟩ := modularOperator_functionalCalculus_const_sub hM hΩ C hC z
  have hψ : (ψ : H) ∈ integralDomain μ fun t : ℝ => z - t := by
    rw [← functionalCalculus_domain hA, hdom]; exact ψ.2
  obtain ⟨hψ', e⟩ := integral_apply_pmapIntegral μ (u := (Set.Ici (0 : ℝ)).indicator
    fun t : ℝ => (z - t)⁻¹) ⟨hmeas, _, hbd⟩ (by fun_prop) ⟨ψ, hψ⟩
  have e1 : pmapIntegral μ (fun t : ℝ => z - t) ⟨ψ, hψ⟩ = z • (ψ : H) - modularOperator M Ω C ψ :=
    hval ψ hψ ψ.2
  rw [← e1]
  refine e.trans ?_
  have key : ∀ (f : ℝ → ℂ) (hf : f = (Set.Ici (0 : ℝ)).indicator 1)
      (h : (ψ : H) ∈ integralDomain μ f), pmapIntegral μ f ⟨ψ, h⟩ = ψ := by
    rintro f rfl h
    exact (LinearPMap.ext_iff.mp (modularOperator_functionalCalculus_indicator_Ici hM hΩ C hC)).2
      (x := ψ) (hf := h) (hg := Submodule.mem_top)
  exact key _ (funext fun t => (mul_comm _ _).trans (hmul t)) hψ'

/--
Every `z ∉ [0, ∞)` is in the resolvent set of `Δ`, with `(Δ - z𝟙)⁻¹ = -r_z(Δ)`; so
`(z - Δ)⁻¹ = r_z(Δ)` is bounded, `‖(z - Δ)⁻¹‖ ≤ 1/d(z)` and `((z - Δ)⁻¹)* = (z̄ - Δ)⁻¹`.

Implementation note: `(Δ - z𝟙)⁻¹ = -r_z(Δ)` is stated as: a bounded `B` is the resolvent
(`IsResolvent`) exactly when `B = -r_z(Δ)`.

Blueprint: crllr:modular-resolvent
-/
theorem modularResolvent_isResolvent {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) :
    z ∈ pmapResolventSet (modularOperator M Ω C) ∧
    (∀ B : H →L[ℂ] H, IsResolvent (modularOperator M Ω C) z B ↔
      B = -(spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹)) ∧
    ‖(spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹)‖ ≤
      1 / Metric.infDist z (((↑) : ℝ → ℂ) '' Set.Ici 0) ∧
    ContinuousLinearMap.adjoint
        ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹)) =
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (conj z - t)⁻¹) := by
  set R := (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
    ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹)
  have hres : IsResolvent (modularOperator M Ω C) z (-R) := by
    refine ⟨fun ψ => ?_, fun ψ => ?_, fun ψ => ?_⟩
    · exact (modularOperator M Ω C).domain.neg_mem
        (modularResolvent_rightInverse hM hΩ C hC hz ψ).1
    · obtain ⟨h, hψ⟩ := modularResolvent_rightInverse hM hΩ C hC hz ψ
      have hneg : (⟨(-R) ψ, (modularOperator M Ω C).domain.neg_mem h⟩ :
          (modularOperator M Ω C).domain) = -⟨R ψ, h⟩ := rfl
      rw [hneg, LinearPMap.map_neg, neg_apply, smul_neg, neg_sub_neg]
      exact hψ
    · have := modularResolvent_leftInverse hM hΩ C hC hz ψ
      rw [neg_apply, ← neg_sub, map_neg, neg_neg]
      exact this
  obtain ⟨-, hnorm, hadj⟩ := modularResolvent_bounded hM hΩ C hC hz
  exact ⟨⟨_, hres⟩, fun B => ⟨fun hB => (existsUnique_isResolvent ⟨_, hres⟩).unique hB hres,
    fun hB => hB ▸ hres⟩, hnorm, hadj⟩

/-! ### Takesaki's lemma

For `z ∉ [0, ∞)` and `a' ∈ M'`, the blueprint fixes `c = ‖a'‖ / √(2(|z| - Re z))`,
`ψ = (z - Δ)⁻¹ a' Ω`, `𝓑_c = {a ∈ M | ‖a‖ ≤ c}`, `𝒦_c = closure (𝓑_c Ω)` and
`G(u, v; a) = Re ⟪u, a' Ω⟫ - Re (z ⟪u, a Ω⟫ - ⟪a* Ω, v⟫)`. These are written inline:
`ψ` is `(spectralMeasure _).integral r_z (a' Ω)`, `𝒦_c` is
`closure ((fun a => a Ω) '' {a ∈ M | ‖a‖ ≤ c})`, and `G` is expanded. Where a statement uses no
property of the value of `c`, `c` is an arbitrary real number.

For `h ∈ M`, `ε > 0` and `s ∈ ℝ`, the shifted power `P_ε^s = f_s(h* h)` with
`f_s(t) = (ε + max t 0)^s` is written `P[h, ε, s]` (local notation for the continuous functional
calculus `cfc`), `u_ε = h P_ε^{-1/2}`, `x_ε = P_ε^{-1/4} h*`, `p_ε = ‖x_ε* Ω‖` and
`q_ε = ‖x_ε Ω‖`.
-/

/-- The shifted power `P_ε^s = f_s(h* h)`, `f_s(t) = (ε + max t 0)^s`, in the continuous
functional calculus. -/
local notation "P[" h ", " ε ", " s "]" =>
  cfc (fun t : ℝ => (ε + max t 0) ^ (s : ℝ)) (star h * h)

/--
For `z ∉ [0, ∞)`, `|z| - Re z > 0` and `|z p - q| ≥ √(2(|z| - Re z) p q)` for real `p, q ≥ 0`.

Blueprint: lmm:takesaki-elementary-inequality
-/
theorem takesaki_elementary_inequality {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) :
    0 < ‖z‖ - z.re ∧ ∀ p q : ℝ, 0 ≤ p → 0 ≤ q →
      Real.sqrt (2 * (‖z‖ - z.re) * p * q) ≤ ‖z * (p : ℂ) - (q : ℂ)‖ := by
  have hr : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hr0 : 0 ≤ ‖z‖ := norm_nonneg z
  refine ⟨?_, fun p q hp hq => ?_⟩
  · by_contra h
    have ha : ‖z‖ ≤ z.re := by linarith
    have hb : z.im = 0 := by nlinarith [sq_nonneg z.im]
    exact hz ⟨z.re, Set.mem_Ici.mpr (hr0.trans ha), Complex.ext (by simp) (by simp [hb])⟩
  · have hw : ‖z * (p : ℂ) - (q : ℂ)‖ ^ 2 = ‖z‖ ^ 2 * p ^ 2 - 2 * z.re * p * q + q ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hr]; simp; ring
    rw [← Real.sqrt_sq (norm_nonneg (z * (p : ℂ) - (q : ℂ)))]
    exact Real.sqrt_le_sqrt (by rw [hw]; nlinarith [sq_nonneg (‖z‖ * p - q)])

/--
`𝒦_c = closure {a Ω | a ∈ M, ‖a‖ ≤ c}` is closed and convex, and contains `0` when `c ≥ 0`.

Blueprint: lmm:takesaki-ball-closed-convex
-/
theorem takesakiBall_closure_isClosed_convex {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M)
    (Ω : H) {c : ℝ} (hc : 0 ≤ c) :
    IsClosed (closure ((fun a : H →L[ℂ] H => a Ω) '' {a ∈ M | ‖a‖ ≤ c})) ∧
      Convex ℝ (closure ((fun a : H →L[ℂ] H => a Ω) '' {a ∈ M | ‖a‖ ≤ c})) ∧
      (0 : H) ∈ closure ((fun a : H →L[ℂ] H => a Ω) '' {a ∈ M | ‖a‖ ≤ c}) := by
  obtain ⟨A, hA⟩ := (isVonNeumannSet_centralizer hM).2.2.1
  have hconv : Convex ℝ {a ∈ M | ‖a‖ ≤ c} := by
    have : {a ∈ M | ‖a‖ ≤ c} = M ∩ Metric.closedBall 0 c := by
      ext a; simp
    rw [this, ← hA]
    exact (A.toSubalgebra.toSubmodule.restrictScalars ℝ).convex.inter (convex_closedBall 0 c)
  refine ⟨isClosed_closure, (hconv.linear_image
    ((ContinuousLinearMap.apply ℂ H Ω).toLinearMap.restrictScalars ℝ)).closure,
    subset_closure ⟨0, ⟨?_, by simpa using hc⟩, by simp⟩⟩
  rw [← hA]
  exact zero_mem A

/--
Every `ξ ∈ 𝒦_c` satisfies `‖b' ξ‖ ≤ c ‖b' Ω‖` for all `b' ∈ M'`.

Blueprint: lmm:takesaki-ball-closure-bound
-/
theorem takesakiBall_closure_bound {M : Set (H →L[ℂ] H)} {Ω : H} {c : ℝ} {ξ : H}
    (hξ : ξ ∈ closure ((fun a : H →L[ℂ] H => a Ω) '' {a ∈ M | ‖a‖ ≤ c})) :
    ∀ b ∈ Set.centralizer M, ‖b ξ‖ ≤ c * ‖b Ω‖ := by
  intro b hb
  refine closure_minimal (t := {x | ‖b x‖ ≤ c * ‖b Ω‖}) ?_
    (isClosed_le (by fun_prop) continuous_const) hξ
  rintro _ ⟨a, ⟨ha, hac⟩, rfl⟩
  have hab : b (a Ω) = a (b Ω) := by
    simpa using congrArg (fun T : H →L[ℂ] H => T Ω) (Set.mem_centralizer_iff.1 hb a ha).symm
  change ‖b (a Ω)‖ ≤ c * ‖b Ω‖
  rw [hab]
  exact (a.le_opNorm _).trans (mul_le_mul_of_nonneg_right hac (norm_nonneg _))

/--
A point `ξ` outside a nonempty closed convex `K ⊆ H` is strictly separated from `K`:
`Re ⟪φ, k⟫ + γ ≤ Re ⟪φ, ξ⟫` for all `k ∈ K`, for some `φ` and `γ > 0`.

Blueprint: lmm:takesaki-separation
-/
theorem exists_re_inner_add_le_of_not_mem_convex {K : Set H} (hne : K.Nonempty)
    (hcl : IsClosed K) (hconv : Convex ℝ K) {ξ : H} (hξ : ξ ∉ K) :
    ∃ φ : H, ∃ γ > 0, ∀ k ∈ K, (⟪φ, k⟫_ℂ).re + γ ≤ (⟪φ, ξ⟫_ℂ).re := by
  let _ := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨k₀, hk₀, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hconv ξ
  have hle := (norm_eq_iInf_iff_real_inner_le_zero hconv hk₀).1 hmin
  have hne0 : ξ - k₀ ≠ 0 := sub_ne_zero.2 fun h => hξ (h ▸ hk₀)
  refine ⟨ξ - k₀, ‖ξ - k₀‖ ^ 2, pow_pos (norm_pos_iff.2 hne0) 2, fun k hk => ?_⟩
  have h1 := hle k hk
  rw [real_inner_eq_re_inner, inner_sub_right, map_sub] at h1
  have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) (ξ - k₀)
  rw [inner_sub_right, map_sub] at h2
  change RCLike.re ⟪ξ - k₀, k⟫_ℂ + _ ≤ RCLike.re ⟪ξ - k₀, ξ⟫_ℂ
  linarith

/--
For `χ = (z̄ - Δ)⁻¹ φ`: `χ ∈ Dom Δ ⊆ Dom S`, `z̄ χ - Δ χ = φ` and `⟪φ, ψ⟫ = ⟪χ, a' Ω⟫`.

Blueprint: lmm:takesaki-transfer-resolvent
-/
theorem takesaki_transfer_resolvent {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) (a' : H →L[ℂ] H)
    (φ χ : H) (hχ : χ = (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
      ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (conj z - t)⁻¹) φ) :
    ∃ h : χ ∈ (modularOperator M Ω C).domain,
      χ ∈ (linearizedTomitaPre M Ω C).closure.domain ∧
      conj z • χ - modularOperator M Ω C ⟨χ, h⟩ = φ ∧
      ⟪φ, (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) (a' Ω)⟫_ℂ = ⟪χ, a' Ω⟫_ℂ := by
  sorry

/--
For `χ = (z̄ - Δ)⁻¹ φ` and `a ∈ M`, `⟪φ, a Ω⟫ = z ⟪χ, a Ω⟫ - ⟪a* Ω, S χ⟫`, and hence
`Re ⟪φ, ψ⟫ - Re ⟪φ, a Ω⟫ = G(χ, S χ; a)`.

Blueprint: lmm:takesaki-transfer
-/
theorem takesaki_transfer {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) (a' : H →L[ℂ] H)
    (φ χ : H) (hχ : χ = (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
      ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (conj z - t)⁻¹) φ) :
    ∃ hS : χ ∈ (linearizedTomitaPre M Ω C).closure.domain, ∀ a ∈ M,
      ⟪φ, a Ω⟫_ℂ = z * ⟪χ, a Ω⟫_ℂ - ⟪star a Ω, tomitaOperator M Ω C ⟨χ, hS⟩⟫_ℂ ∧
      (⟪φ, (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) (a' Ω)⟫_ℂ).re -
          (⟪φ, a Ω⟫_ℂ).re =
        (⟪χ, a' Ω⟫_ℂ).re -
          (z * ⟪χ, a Ω⟫_ℂ - ⟪star a Ω, tomitaOperator M Ω C ⟨χ, hS⟩⟫_ℂ).re := by
  sorry

/--
`M Ω` is a core for `S`: for `χ ∈ Dom S` there are `h_n ∈ M` with `h_n Ω → χ` and
`h_n* Ω → S χ`.

Blueprint: lmm:tomita-core
-/
theorem tomitaOperator_exists_seq_tendsto {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (χ : (linearizedTomitaPre M Ω C).closure.domain) :
    ∃ h : ℕ → H →L[ℂ] H, (∀ n, h n ∈ M) ∧
      Filter.Tendsto (fun n => h n Ω) Filter.atTop (nhds (χ : H)) ∧
      Filter.Tendsto (fun n => star (h n) Ω) Filter.atTop (nhds (tomitaOperator M Ω C χ)) := by
  sorry

/--
`G` is Lipschitz in `(u, v)`, uniformly in `a ∈ 𝓑_c`:
`|G(u, v; a) - G(u₁, v₁; a)| ≤ (‖a' Ω‖ + |z| c ‖Ω‖) ‖u - u₁‖ + c ‖Ω‖ ‖v - v₁‖`.

Blueprint: lmm:takesaki-G-lipschitz
-/
theorem takesakiG_lipschitz {M : Set (H →L[ℂ] H)} {Ω : H} (z : ℂ) (a' : H →L[ℂ] H) {c : ℝ}
    (u v u₁ v₁ : H) {a : H →L[ℂ] H} (ha : a ∈ M) (hac : ‖a‖ ≤ c) :
    |((⟪u, a' Ω⟫_ℂ).re - (z * ⟪u, a Ω⟫_ℂ - ⟪star a Ω, v⟫_ℂ).re) -
        ((⟪u₁, a' Ω⟫_ℂ).re - (z * ⟪u₁, a Ω⟫_ℂ - ⟪star a Ω, v₁⟫_ℂ).re)| ≤
      (‖a' Ω‖ + ‖z‖ * c * ‖Ω‖) * ‖u - u₁‖ + c * ‖Ω‖ * ‖v - v₁‖ := by
  sorry

/--
For `χ ∈ Dom S` and `δ > 0` there is `h ∈ M` with `|G(χ, S χ; a) - G(h Ω, h* Ω; a)| < δ` for
every `a ∈ 𝓑_c`.

Blueprint: lmm:takesaki-uniform-approximation
-/
theorem takesakiG_uniform_approximation {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (z : ℂ) (a' : H →L[ℂ] H) (c : ℝ)
    (χ : (linearizedTomitaPre M Ω C).closure.domain) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h ∈ M, ∀ a ∈ M, ‖a‖ ≤ c →
      |((⟪(χ : H), a' Ω⟫_ℂ).re -
          (z * ⟪(χ : H), a Ω⟫_ℂ - ⟪star a Ω, tomitaOperator M Ω C χ⟫_ℂ).re) -
        ((⟪h Ω, a' Ω⟫_ℂ).re - (z * ⟪h Ω, a Ω⟫_ℂ - ⟪star a Ω, star h Ω⟫_ℂ).re)| < δ := by
  sorry

/--
For self-adjoint `x ∈ M` and `f : ℝ → ℝ`, the continuous functional calculus `f(x)` lies in `M`.

Blueprint: lmm:cfc-mem-von-neumann
-/
theorem cfc_mem_of_isVonNeumannSet {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M)
    {x : H →L[ℂ] H} (hx : x ∈ M) (hsa : IsSelfAdjoint x) (f : ℝ → ℝ) : cfc f x ∈ M := by
  rw [← hM.2]
  exact fun d hd => ((Commute.cfc_real (hd x hx) f).eq).symm

/--
For `h ∈ M` and `ε > 0`, `P_ε^s ∈ M`. The other conjuncts of the blueprint lemma are
`takesakiShiftedPow_isSelfAdjoint`, `takesakiShiftedPow_mul`, `takesakiShiftedPow_zero`,
`takesakiShiftedPow_commute` and `takesakiShiftedPow_norm_le`.

Blueprint: lmm:takesaki-shifted-powers
-/
theorem takesakiShiftedPow_mem {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M)
    {h : H →L[ℂ] H} (hh : h ∈ M) {ε : ℝ} (hε : 0 < ε) (s : ℝ) : P[h, ε, s] ∈ M := by
  obtain ⟨A, hA⟩ := (isVonNeumannSet_centralizer hM).2.2.1
  have hP : star h * h ∈ M := by
    rw [← hA] at hh ⊢
    exact mul_mem (star_mem hh) hh
  exact cfc_mem_of_isVonNeumannSet hM hP (IsSelfAdjoint.star_mul_self h) _

/--
`P_ε^s` is self-adjoint (a conjunct of `takesakiShiftedPow_mem`).

Blueprint: lmm:takesaki-shifted-powers
-/
theorem takesakiShiftedPow_isSelfAdjoint (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    IsSelfAdjoint (P[h, ε, s]) :=
  cfc_predicate _ _

/--
`P_ε^s P_ε^t = P_ε^{s+t}` (a conjunct of `takesakiShiftedPow_mem`).

Blueprint: lmm:takesaki-shifted-powers
-/
theorem takesakiShiftedPow_mul (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) (s t : ℝ) :
    P[h, ε, s] * P[h, ε, t] = P[h, ε, s + t] := by
  have hpos : ∀ x : ℝ, 0 < ε + max x 0 := fun x => add_pos_of_pos_of_nonneg hε (le_max_right _ _)
  have hc : ∀ r : ℝ, Continuous fun x : ℝ => (ε + max x 0) ^ r := fun r =>
    (continuous_const.add (continuous_id.max continuous_const)).rpow_const
      fun x => Or.inl (hpos x).ne'
  rw [← cfc_mul _ _ _ (hc s).continuousOn (hc t).continuousOn]
  exact cfc_congr fun x _ => (Real.rpow_add (hpos x) s t).symm

/--
`P_ε^0 = 𝟙` (a conjunct of `takesakiShiftedPow_mem`).

Blueprint: lmm:takesaki-shifted-powers
-/
theorem takesakiShiftedPow_zero (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) :
    P[h, ε, 0] = 1 := by
  simp only [Real.rpow_zero]
  exact cfc_const_one ℝ (star h * h)

/--
`P_ε^s` commutes with `P = h* h` (a conjunct of `takesakiShiftedPow_mem`).

Blueprint: lmm:takesaki-shifted-powers
-/
theorem takesakiShiftedPow_commute (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    P[h, ε, s] * (star h * h) = (star h * h) * P[h, ε, s] :=
  ((Commute.refl _).cfc_real _).eq

/--
`‖P_ε^s‖ ≤ ε^s` for `s ≤ 0` (a conjunct of `takesakiShiftedPow_mem`).

Blueprint: lmm:takesaki-shifted-powers
-/
theorem takesakiShiftedPow_norm_le (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : s ≤ 0) :
    ‖P[h, ε, s]‖ ≤ ε ^ s := by
  refine norm_cfc_le (Real.rpow_pos_of_pos hε s).le fun t _ => ?_
  have hpos : 0 < ε + max t 0 := by positivity
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos s)]
  exact Real.rpow_le_rpow_of_nonpos hε (le_add_of_nonneg_right (le_max_right t 0)) hs

/--
The approximate polar decomposition: `u_ε, x_ε ∈ M`, `x_ε* = h P_ε^{-1/4}`, `h* = P_ε^{1/4} x_ε`,
`h* u_ε = x_ε x_ε*` and `u_ε h* = x_ε* x_ε`.

Blueprint: lmm:takesaki-approximate-polar
-/
theorem takesaki_approximate_polar {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M)
    {h : H →L[ℂ] H} (hh : h ∈ M) {ε : ℝ} (hε : 0 < ε) :
    h * P[h, ε, -(1/2)] ∈ M ∧ P[h, ε, -(1/4)] * star h ∈ M ∧
      star (P[h, ε, -(1/4)] * star h) = h * P[h, ε, -(1/4)] ∧
      star h = P[h, ε, 1/4] * (P[h, ε, -(1/4)] * star h) ∧
      star h * (h * P[h, ε, -(1/2)]) =
        (P[h, ε, -(1/4)] * star h) * star (P[h, ε, -(1/4)] * star h) ∧
      (h * P[h, ε, -(1/2)]) * star h =
        star (P[h, ε, -(1/4)] * star h) * (P[h, ε, -(1/4)] * star h) := by
  obtain ⟨A, hA⟩ := (isVonNeumannSet_centralizer hM).2.2.1
  have hQQ : P[h, ε, -(1/4)] * P[h, ε, -(1/4)] = P[h, ε, -(1/2)] := by
    rw [takesakiShiftedPow_mul h hε]; norm_num
  have hstar : star (P[h, ε, -(1/4)] * star h) = h * P[h, ε, -(1/4)] := by
    rw [star_mul, star_star, (takesakiShiftedPow_isSelfAdjoint h hε _).star_eq]
  have hP := takesakiShiftedPow_commute h hε (-(1/4))
  have hQ : ∀ s : ℝ, P[h, ε, s] ∈ A := fun s => by
    rw [← SetLike.mem_coe, hA]; exact takesakiShiftedPow_mem hM hh hε s
  rw [← hA] at hh
  refine ⟨?_, ?_, hstar, ?_, ?_, ?_⟩
  · rw [← hA]; exact mul_mem hh (hQ _)
  · rw [← hA]; exact mul_mem (hQ _) (star_mem hh)
  · rw [← mul_assoc, takesakiShiftedPow_mul h hε, show (1/4 : ℝ) + -(1/4) = 0 by norm_num,
      takesakiShiftedPow_zero h hε, one_mul]
  · rw [hstar, ← hQQ]
    calc star h * (h * (P[h, ε, -(1/4)] * P[h, ε, -(1/4)]))
        = (star h * h * P[h, ε, -(1/4)]) * P[h, ε, -(1/4)] := by noncomm_ring
      _ = P[h, ε, -(1/4)] * star h * (h * P[h, ε, -(1/4)]) := by
        rw [← hP]; noncomm_ring
  · rw [hstar, ← hQQ]; noncomm_ring

/--
`‖u_ε‖ ≤ 1` and `‖x_ε‖² ≤ ‖h‖`.

Blueprint: lmm:takesaki-approx-polar-norms
-/
theorem takesaki_approx_polar_norms (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) :
    ‖h * P[h, ε, -(1/2)]‖ ≤ 1 ∧ ‖P[h, ε, -(1/4)] * star h‖ ^ 2 ≤ ‖h‖ := by
  have hpos : ∀ x : ℝ, 0 < ε + max x 0 := fun x => add_pos_of_pos_of_nonneg hε (le_max_right _ _)
  have hc : ∀ r : ℝ, Continuous fun x : ℝ => (ε + max x 0) ^ r := fun r =>
    (continuous_const.add (continuous_id.max continuous_const)).rpow_const
      fun x => Or.inl (hpos x).ne'
  have hspec : ∀ x ∈ spectrum ℝ (star h * h), 0 ≤ x ∧ x ≤ ‖h‖ ^ 2 := fun x hx =>
    ⟨spectrum_nonneg_of_nonneg (star_mul_self_nonneg h) hx, by
      have := spectrum.norm_le_norm_mul_of_mem hx
      rw [CStarRing.norm_star_mul_self, Real.norm_of_nonneg
        (spectrum_nonneg_of_nonneg (star_mul_self_nonneg h) hx)] at this
      have h1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      nlinarith [norm_nonneg h, mul_self_nonneg ‖h‖]⟩
  -- `R P R = cfc (f_s · id · f_s) P`
  have hsand : ∀ s : ℝ, P[h, ε, s] * (star h * h) * P[h, ε, s] =
      cfc (fun x : ℝ => (ε + max x 0) ^ s * x * (ε + max x 0) ^ s) (star h * h) := by
    intro s
    rw [cfc_mul (fun x : ℝ => (ε + max x 0) ^ s * x) (fun x : ℝ => (ε + max x 0) ^ s) _
        ((hc s).mul continuous_id).continuousOn (hc s).continuousOn,
      cfc_mul (fun x : ℝ => (ε + max x 0) ^ s) (fun x : ℝ => x) _ (hc s).continuousOn
        continuous_id.continuousOn, cfc_id' ℝ (star h * h)]
  have hR : ∀ s : ℝ, star (P[h, ε, s]) = P[h, ε, s] := fun s =>
    (cfc_predicate (fun t : ℝ => (ε + max t 0) ^ s) (star h * h)).star_eq
  refine ⟨?_, ?_⟩
  · have h2 : ‖h * P[h, ε, -(1/2)]‖ * ‖h * P[h, ε, -(1/2)]‖ ≤ 1 := by
      rw [← CStarRing.norm_star_mul_self, star_mul, hR, mul_assoc, ← mul_assoc (star h),
        ← mul_assoc, hsand]
      refine norm_cfc_le zero_le_one fun x hx => ?_
      obtain ⟨hx0, -⟩ := hspec x hx
      have hb := hpos x
      rw [max_eq_left hx0] at hb ⊢
      have hb2 : ((ε + x) ^ (-(1/2) : ℝ)) ^ 2 * (ε + x) = 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]; norm_num
        rw [Real.rpow_neg_one, inv_mul_cancel₀ hb.ne']
      have hb0 : 0 ≤ (ε + x) ^ (-(1/2) : ℝ) := Real.rpow_nonneg hb.le _
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
    nlinarith [norm_nonneg (h * P[h, ε, -(1/2)])]
  · rw [sq, ← norm_star (P[h, ε, -(1/4)] * star h), ← CStarRing.norm_star_mul_self, star_star,
      star_mul, star_star, hR, mul_assoc, ← mul_assoc (star h), ← mul_assoc, hsand]
    refine norm_cfc_le (norm_nonneg h) fun x hx => ?_
    obtain ⟨hx0, hxh⟩ := hspec x hx
    have hb := hpos x
    rw [max_eq_left hx0] at hb ⊢
    have ha4 : ((ε + x) ^ (-(1/4) : ℝ)) ^ 4 * (ε + x) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]; norm_num
      rw [Real.rpow_neg_one, inv_mul_cancel₀ hb.ne']
    have ha0 : 0 ≤ (ε + x) ^ (-(1/4) : ℝ) := Real.rpow_nonneg hb.le _
    have hf0 : 0 ≤ (ε + x) ^ (-(1/4) : ℝ) * x * (ε + x) ^ (-(1/4) : ℝ) := by positivity
    rw [Real.norm_of_nonneg hf0, ← pow_le_pow_iff_left₀ hf0 (norm_nonneg h) two_ne_zero]
    have : ((ε + x) ^ (-(1/4) : ℝ) * x * (ε + x) ^ (-(1/4) : ℝ)) ^ 2 =
        ((ε + x) ^ (-(1/4) : ℝ)) ^ 4 * x ^ 2 := by ring
    rw [this]
    nlinarith [mul_nonneg (mul_nonneg (pow_nonneg ha0 4) hε.le) hx0]

/--
`‖P_ε^{1/4} Ω‖² ≤ p_ε² + √ε ‖Ω‖²`.

Blueprint: lmm:takesaki-shifted-root-bound
-/
theorem takesaki_shifted_root_bound (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) (Ω : H) :
    ‖P[h, ε, 1/4] Ω‖ ^ 2 ≤
      ‖star (P[h, ε, -(1/4)] * star h) Ω‖ ^ 2 + Real.sqrt ε * ‖Ω‖ ^ 2 := by
  sorry

/--
For `a' ∈ M'`, `h ∈ M` and `ε > 0`, `|⟪h Ω, a' Ω⟫| ≤ ‖a'‖ (p_ε + ε^{1/4} ‖Ω‖) q_ε`.

Blueprint: lmm:takesaki-numerator-bound
-/
theorem takesaki_numerator_bound {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M) (Ω : H)
    {a' : H →L[ℂ] H} (ha' : a' ∈ Set.centralizer M) {h : H →L[ℂ] H} (hh : h ∈ M)
    {ε : ℝ} (hε : 0 < ε) :
    ‖⟪h Ω, a' Ω⟫_ℂ‖ ≤ ‖a'‖ * (‖star (P[h, ε, -(1/4)] * star h) Ω‖ + ε ^ (1/4 : ℝ) * ‖Ω‖) *
      ‖(P[h, ε, -(1/4)] * star h) Ω‖ := by
  sorry

/--
For `w ∈ ℂ` and `c ≥ 0` there is `s ∈ ℂ` with `|s| ≤ c` and `Re (s w) = c |w|`.

Blueprint: lmm:complex-rotation-choice
-/
theorem exists_norm_le_re_mul_eq_mul_norm (w : ℂ) {c : ℝ} (hc : 0 ≤ c) :
    ∃ s : ℂ, ‖s‖ ≤ c ∧ (s * w).re = c * ‖w‖ := by
  rcases eq_or_ne w 0 with rfl | hw
  · exact ⟨0, by simpa using hc, by simp⟩
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  refine ⟨((c / ‖w‖ : ℝ) : ℂ) * starRingEnd ℂ w, le_of_eq ?_, ?_⟩
  · rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hc (norm_nonneg _)), div_mul_cancel₀ _ hn]
  · rw [mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    field_simp

/--
For `s ∈ ℂ`, `⟪h Ω, s u_ε Ω⟫ = s p_ε²` and `⟪(s u_ε)* Ω, h* Ω⟫ = s q_ε²`.

Blueprint: lmm:takesaki-test-inner-products
-/
theorem takesaki_test_inner_products (h : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε) (Ω : H) (s : ℂ) :
    ⟪h Ω, (s • (h * P[h, ε, -(1/2)])) Ω⟫_ℂ =
        s * ((‖star (P[h, ε, -(1/4)] * star h) Ω‖ ^ 2 : ℝ) : ℂ) ∧
      ⟪star (s • (h * P[h, ε, -(1/2)])) Ω, star h Ω⟫_ℂ =
        s * ((‖(P[h, ε, -(1/4)] * star h) Ω‖ ^ 2 : ℝ) : ℂ) := by
  sorry

/--
For `h ∈ M` and `ε > 0` there is `a ∈ 𝓑_c` with
`Re (z ⟪h Ω, a Ω⟫ - ⟪a* Ω, h* Ω⟫) ≥ ‖a'‖ p_ε q_ε`.

Blueprint: lmm:takesaki-test-element
-/
theorem takesaki_test_element {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M) (Ω : H)
    {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) (a' : H →L[ℂ] H) {h : H →L[ℂ] H}
    (hh : h ∈ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ M, ‖a‖ ≤ ‖a'‖ / Real.sqrt (2 * (‖z‖ - z.re)) ∧
      ‖a'‖ * ‖star (P[h, ε, -(1/4)] * star h) Ω‖ * ‖(P[h, ε, -(1/4)] * star h) Ω‖ ≤
        (z * ⟪h Ω, a Ω⟫_ℂ - ⟪star a Ω, star h Ω⟫_ℂ).re := by
  sorry

/--
The key estimate: for `h ∈ M` and `δ > 0` there is `a ∈ 𝓑_c` with `G(h Ω, h* Ω; a) ≤ δ`.

Blueprint: lmm:takesaki-key-estimate
-/
theorem takesaki_key_estimate {M : Set (H →L[ℂ] H)} (hM : IsVonNeumannSet M) (Ω : H)
    {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) {a' : H →L[ℂ] H}
    (ha' : a' ∈ Set.centralizer M) {h : H →L[ℂ] H} (hh : h ∈ M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a ∈ M, ‖a‖ ≤ ‖a'‖ / Real.sqrt (2 * (‖z‖ - z.re)) ∧
      (⟪h Ω, a' Ω⟫_ℂ).re - (z * ⟪h Ω, a Ω⟫_ℂ - ⟪star a Ω, star h Ω⟫_ℂ).re ≤ δ := by
  sorry

/--
The resolvent vector `ψ = (z - Δ)⁻¹ a' Ω` lies in `𝒦_c`.

Blueprint: lmm:takesaki-resolvent-in-ball-closure
-/
theorem takesaki_resolvent_mem_ball_closure {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) {a' : H →L[ℂ] H}
    (ha' : a' ∈ Set.centralizer M) :
    (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) (a' Ω) ∈
      closure ((fun a : H →L[ℂ] H => a Ω) ''
        {a ∈ M | ‖a‖ ≤ ‖a'‖ / Real.sqrt (2 * (‖z‖ - z.re))}) := by
  sorry

/--
Takesaki's lemma: for `z ∉ [0, ∞)` and `a' ∈ M'`, `(z - Δ)⁻¹ a' Ω = a Ω` for a unique `a ∈ M`,
and `‖a‖ ≤ ‖a'‖ / √(2(|z| - Re z))`.

Implementation note: uniqueness is among all `ã ∈ M` with `ã Ω = (z - Δ)⁻¹ a' Ω`, as in
`commutantExtension`.

Blueprint: thrm:takesaki-lemma
-/
theorem takesaki_lemma {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0) {a' : H →L[ℂ] H}
    (ha' : a' ∈ Set.centralizer M) :
    ∃ a ∈ M, a Ω = (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) (a' Ω) ∧
      ‖a‖ ≤ ‖a'‖ / Real.sqrt (2 * (‖z‖ - z.re)) ∧
      ∀ ã ∈ M, ã Ω = (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (z - t)⁻¹) (a' Ω) → ã = a := by
  sorry

end Physicslib4.Modular
