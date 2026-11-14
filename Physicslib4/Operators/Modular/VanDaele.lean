/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Operators.Modular.TomitaAdjoint

/-!
# Complex powers of the modular operator

For a von Neumann algebra `M` with a cyclic and separating vector `Ω` and a reference conjugation
`C`, let `Δ` be the modular operator and `μ` its spectral measure. This file sets up the
spectral projections `E_n = μ(K_n)` for `K_n = [1/n, n]`, the subspace `H₀` of vectors with
`E_n ξ = ξ` for some `n ≥ 1`, the modular unitary group `Δ^{it} = e^{it log Δ}`, and the bounded
complex powers `p_{z,n}(Δ)`, where `p_{z,n}(λ) = 1_{K_n}(λ) λ^z`.

## Notation

* `K[n]` is the interval `[1/n, n]`.
* `p[z, n]` is `p_{z,n} = 1_{K_n} · λ^z`, with `λ^z` the principal power `(λ : ℂ) ^ z`.
* `q[z, n]` is `q_{z,n} = 1_{K_n} · (log λ) λ^z`, with `log` the function `Real.log`.
* `e[t]` is `e_t(λ) = e^{it log λ}`.

The spectral projection `E_n` is written `spectralMeasure _ K[n]`, the bounded operator
`p_{z,n}(Δ)` is written as the bounded integral `(spectralMeasure _).integral p[z, n]`
(they agree with the functional calculus by `modularOperator_indicatorCpow`), and `ξ ∈ H₀` is
written as the condition `spectralMeasure _ K[n] ξ = ξ` for some `n ≥ 1`.
-/

namespace Physicslib4.Modular

open scoped InnerProductSpace ComplexConjugate
open Physicslib4.Spectral.Unbounded Physicslib4.Spectral.Stone
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The interval `K_n = [1/n, n]`. -/
local notation "K[" n "]" => Set.Icc (1 / (n : ℝ)) (n : ℝ)

/-- The function `p_{z,n}(λ) = 1_{K_n}(λ) λ^z`. -/
local notation "p[" z ", " n "]" =>
  Set.indicator (Set.Icc (1 / (n : ℝ)) (n : ℝ)) fun x : ℝ => (x : ℂ) ^ (z : ℂ)

/-- The function `q_{z,n}(λ) = 1_{K_n}(λ) (log λ) λ^z`. -/
local notation "q[" z ", " n "]" =>
  Set.indicator (Set.Icc (1 / (n : ℝ)) (n : ℝ)) fun x : ℝ => (Real.log x : ℂ) * (x : ℂ) ^ (z : ℂ)

/-- The function `e_t(λ) = e^{it log λ}`. -/
local notation "e[" t "]" => fun x : ℝ => Complex.exp (Complex.I * (t : ℂ) * (Real.log x : ℂ))

/-! ### The spectral measure of `Δ` and the unitary group `Δ^{it}` -/

/-- `μ((-∞, 0]) = 0` for the spectral measure `μ` of `Δ`.
Blueprint: lmm:modular-spectral-support -/
theorem modularOperator_spectralMeasure_Iic_zero {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) (Set.Iic 0) = 0 := by
  obtain ⟨hpos, -, -, hker, -⟩ := modularOperator_properties hM hΩ C hC
  set hA := modularOperator_isSelfAdjoint hM hΩ C hC
  ext ψ
  have h := MeasureTheory.measure_union_le (μ := (spectralMeasure hA).assoc ψ)
    (Set.Iio (0 : ℝ)) {0}
  rw [Set.Iio_union_right, assoc_apply_eq_norm_sq _ ψ measurableSet_Iic,
    assoc_apply_eq_norm_sq _ ψ measurableSet_Iio,
    assoc_apply_eq_norm_sq _ ψ (measurableSet_singleton 0),
    spectralMeasure_Iio_zero_eq_zero_of_isPositive hA hpos,
    spectralMeasure_singleton_zero hA hker] at h
  simp only [zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, ENNReal.ofReal_zero, add_zero, nonpos_iff_eq_zero,
    ENNReal.ofReal_eq_zero] at h
  have : ‖spectralMeasure hA (Set.Iic 0) ψ‖ = 0 := by
    nlinarith [norm_nonneg (spectralMeasure hA (Set.Iic 0) ψ)]
  simpa using this

/-- `1_{(0, ∞)}(Δ) = 𝟙`.
Blueprint: lmm:modular-indicator-positive-one -/
theorem modularOperator_functionalCalculus_indicator_Ioi {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC) ((Set.Ioi (0 : ℝ)).indicator 1) =
      (LinearMap.id : H →ₗ[ℂ] H).toPMap ⊤ := by
  have hone : (1 : ℝ → ℂ) ∈ Spectral.BddMeasurable ℝ := ⟨measurable_const, 1, fun _ => by simp⟩
  refine (pmapIntegral_congr_of_null _ (g := 1) (measurable_const.indicator measurableSet_Ioi)
    measurable_const measurableSet_Iic
    (modularOperator_spectralMeasure_Iic_zero hM hΩ C hC) fun x hx => ?_).trans ?_
  · exact Set.indicator_of_mem (Set.mem_Ioi.2 (not_le.1 hx)) _
  · rw [pmapIntegral_of_bddMeasurable _ hone, Spectral.ProjectionValuedMeasure.integral_one]
    rfl

/-- `log Δ = ℓ(Δ)`, with `ℓ = Real.log`, is self-adjoint.
Blueprint: lmm:modular-log-self-adjoint -/
theorem isSelfAdjoint_modularOperator_log {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    IsSelfAdjoint (functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC)
      fun x => (Real.log x : ℂ)) :=
  (isSelfAdjoint_functionalCalculus_of_real _ Real.measurable_log).1

/-- The modular unitary group `Δ^{it} = e^{it log Δ}`, the unitary `expUnitary` of the
self-adjoint operator `log Δ`.
Blueprint: def:modular-unitary-group -/
noncomputable def modularUnitaryGroup {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (t : ℝ) : H ≃ₗᵢ[ℂ] H :=
  expUnitary (isSelfAdjoint_modularOperator_log hM hΩ C hC) t

/-- `t ↦ Δ^{it}` is a strongly continuous one-parameter unitary group with
`(Δ^{it})* = (Δ^{it})⁻¹ = Δ^{-it}`; each `Δ^{it}` is unitary by its type.
Blueprint: lmm:modular-unitary-group-props -/
theorem modularUnitaryGroup_properties {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    IsOneParameterUnitaryGroup (modularUnitaryGroup hM hΩ C hC) ∧
      IsStronglyContinuous (modularUnitaryGroup hM hΩ C hC) ∧
      ∀ t : ℝ,
        ContinuousLinearMap.adjoint
            (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap =
          (modularUnitaryGroup hM hΩ C hC (-t)).toLinearIsometry.toContinuousLinearMap ∧
        (modularUnitaryGroup hM hΩ C hC t).symm = modularUnitaryGroup hM hΩ C hC (-t) := by
  have hU := isOneParameterUnitaryGroup_expUnitary (isSelfAdjoint_modularOperator_log hM hΩ C hC)
  refine ⟨hU, isStronglyContinuous_expUnitary _, fun t => ⟨hU.adjoint_eq t, ?_⟩⟩
  ext x
  refine (modularUnitaryGroup hM hΩ C hC t).injective ?_
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact ((hU.map_add t (-t) x).symm.trans (by rw [add_neg_cancel, hU.map_zero])).symm

/-- `e_t` is measurable of modulus one, `Δ^{it} = e_t(Δ) = ∫ e_t dμ`, and `e_t(λ) = λ^{it}` for
`λ > 0`.
Blueprint: lmm:modular-unitary-group-fc -/
theorem modularUnitaryGroup_eq_functionalCalculus {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (t : ℝ) :
    Measurable e[t] ∧ (∀ x : ℝ, ‖e[t] x‖ = 1) ∧
      functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC) e[t] =
        (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toLinearMap.toPMap ⊤ ∧
      (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap =
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral e[t] ∧
      ∀ x : ℝ, 0 < x → e[t] x = (x : ℂ) ^ (Complex.I * t) := by
  set hΔ := modularOperator_isSelfAdjoint hM hΩ C hC
  have hfun : expFun t ∘ Real.log = e[t] := by
    funext x; simp only [Function.comp_apply, expFun]; push_cast; ring_nf
  have hmeas : Measurable e[t] := hfun ▸ (expFun_mem_bddMeasurable t).1.comp Real.measurable_log
  have hnorm : ∀ x : ℝ, ‖e[t] x‖ = 1 := fun x => by
    rw [← hfun]; exact Complex.norm_exp_I_mul_ofReal _
  have hbdd : e[t] ∈ Spectral.BddMeasurable ℝ := ⟨hmeas, 1, fun x => (hnorm x).le⟩
  have hfc : functionalCalculus hΔ e[t] =
      (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toLinearMap.toPMap ⊤ := by
    obtain ⟨hfA, -, hcomp⟩ := functionalCalculus_functionalCalculus hΔ Real.measurable_log
    rw [← hfun, ← hcomp _ (expFun_mem_bddMeasurable t).1, functionalCalculus_expFun]
    rfl
  refine ⟨hmeas, hnorm, hfc, ?_, fun x hx => ?_⟩
  · have h := hfc.symm.trans (functionalCalculus_of_bddMeasurable hΔ hbdd).2
    ext ξ
    obtain ⟨-, hx⟩ := LinearPMap.ext_iff.1 h
    simpa using @hx ξ Submodule.mem_top Submodule.mem_top
  · rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
    ring_nf

/-! ### The spectral projections `E_n` and the subspace `H₀` -/

/-- For `1 ≤ n ≤ m`, `E_m E_n = E_n E_m = E_n`, so `E_n ξ = ξ` implies `E_m ξ = ξ`; and `H₀` is a
linear subspace: `E_k ξ = ξ` and `E_l η = η` give `E_{max k l}(αξ + βη) = αξ + βη`.
Blueprint: lmm:modular-spectral-projections-nested -/
theorem modularSpectralProjection_nested {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[m] *
        spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] =
      spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ∧
    spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] *
        spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[m] =
      spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ∧
    (∀ ξ : H, spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ξ = ξ →
      spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[m] ξ = ξ) ∧
    ∀ (k l : ℕ), 1 ≤ k → 1 ≤ l → ∀ (ξ η : H) (α β : ℂ),
      spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[k] ξ = ξ →
      spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[l] η = η →
      spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[max k l] (α • ξ + β • η) =
        α • ξ + β • η := by
  set μ := spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)
  have key : ∀ {n m : ℕ}, 1 ≤ n → n ≤ m →
      μ K[m] * μ K[n] = μ K[n] ∧ μ K[n] * μ K[m] = μ K[n] := by
    intro n m hn hnm
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hsub : K[n] ⊆ K[m] := Set.Icc_subset_Icc (one_div_le_one_div_of_le hn0 hnm') hnm'
    rw [← μ.apply_inter measurableSet_Icc measurableSet_Icc,
      ← μ.apply_inter measurableSet_Icc measurableSet_Icc, Set.inter_eq_right.2 hsub,
      Set.inter_eq_left.2 hsub]
    exact ⟨rfl, rfl⟩
  have fix : ∀ {n m : ℕ}, 1 ≤ n → n ≤ m → ∀ ξ : H, μ K[n] ξ = ξ → μ K[m] ξ = ξ := by
    intro n m hn hnm ξ hξ
    rw [← hξ]
    exact congrArg (fun T => T ξ) (key hn hnm).1
  refine ⟨(key hn hnm).1, (key hn hnm).2, fix hn hnm, fun k l hk hl ξ η α β hξ hη => ?_⟩
  have h1 := fix hk (le_max_left k l) ξ hξ
  have h2 := fix hl (le_max_right k l) η hη
  rw [Nat.cast_max] at h1 h2
  rw [map_add, map_smul, map_smul, h1, h2]

/-- `E_n ψ → ψ` as `n → ∞`, for every `ψ`.
Blueprint: lmm:modular-spectral-projections-converge -/
theorem tendsto_modularSpectralProjection {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (ψ : H) :
    Tendsto (fun n : ℕ => spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ψ)
      atTop (𝓝 ψ) := by
  set hA := modularOperator_isSelfAdjoint hM hΩ C hC
  have hI := modularOperator_functionalCalculus_indicator_Ioi hM hΩ C hC
  have hψ : ψ ∈ (functionalCalculus hA ((Set.Ioi (0 : ℝ)).indicator 1)).domain := by
    rw [hI]; trivial
  have hval : functionalCalculus hA ((Set.Ioi (0 : ℝ)).indicator 1) ⟨ψ, hψ⟩ = ψ := by
    obtain ⟨-, h⟩ := LinearPMap.ext_iff.1 hI
    exact h (x := ψ) (hf := hψ) (hg := trivial)
  have key := tendsto_integral_apply_of_dominated (spectralMeasure hA)
    (h := (Set.Ioi (0 : ℝ)).indicator (1 : ℝ → ℂ))
    (measurable_const.indicator measurableSet_Ioi) ⟨ψ, hψ⟩
    (hn := fun n : ℕ => K[n + 1].indicator (1 : ℝ → ℂ))
    (fun n => ⟨measurable_const.indicator measurableSet_Icc, 1, fun x =>
      (norm_indicator_le_norm_self _ _).trans (by simp)⟩)
    (fun x => ?_) (fun n x => ?_)
  · rw [← tendsto_add_atTop_iff_nat 1]
    convert key using 2 with n
    · rw [Spectral.ProjectionValuedMeasure.integral_indicator _ measurableSet_Icc]
      push_cast; rfl
    · exact hval.symm
  · rcases le_or_gt x 0 with hx | hx
    · rw [Set.indicator_of_notMem (show x ∉ Set.Ioi (0 : ℝ) from not_lt.2 hx)]
      refine tendsto_const_nhds.congr fun n => (Set.indicator_of_notMem ?_ _).symm
      exact fun h => (lt_of_lt_of_le (by positivity) h.1).not_ge hx
    · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hx)]
      obtain ⟨N, hN⟩ := exists_nat_gt (max x x⁻¹)
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      have h1 : x < n + 1 := by linarith [le_max_left x x⁻¹]
      have h2 : x⁻¹ < n + 1 := by linarith [le_max_right x x⁻¹]
      refine (Set.indicator_of_mem
        (show x ∈ Set.Icc (1 / ((n : ℝ) + 1)) (n + 1) from ⟨?_, h1.le⟩) _).symm
      rw [one_div]
      exact (inv_lt_of_inv_lt₀ hx h2).le
  · exact norm_indicator_le_of_subset (show Set.Icc (1 / ((n : ℝ) + 1)) (n + 1) ⊆ Set.Ioi 0 from
      fun y hy => lt_of_lt_of_le (by positivity) hy.1) _ _

/-- `H₀ = {ξ | E_n ξ = ξ for some n ≥ 1}` is dense in `H`.
Blueprint: lmm:modular-H0-dense -/
theorem dense_modularSpectralSubspace {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    Dense {ξ : H | ∃ n : ℕ, 1 ≤ n ∧
      spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ξ = ξ} := by
  refine fun ψ => mem_closure_of_tendsto (tendsto_modularSpectralProjection hM hΩ C hC ψ) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact ⟨n, hn, congrArg (fun T : H →L[ℂ] H => T ψ)
    (modularSpectralProjection_nested hM hΩ C hC hn le_rfl).1⟩

/-! ### The functions `p_{z,n}`, `q_{z,n}` and `e_t` -/

/-- For `n ≥ 1` and `λ ∈ K_n`, `λ > 0` and `|log λ| ≤ log n`.
Blueprint: lmm:log-power-on-interval -/
theorem pos_abs_log_le_of_mem_Icc {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ K[n]) :
    0 < x ∧ |Real.log x| ≤ Real.log n := by
  have h1 : 0 < 1 / (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hx0 : 0 < x := h1.trans_le hx.1
  refine ⟨hx0, abs_le.2 ⟨?_, Real.log_le_log hx0 hx.2⟩⟩
  have := Real.log_le_log h1 hx.1
  rwa [one_div, Real.log_inv] at this

/-- For `n ≥ 1`, `λ ∈ K_n` and `z ∈ ℂ`, `λ^z = exp(z log λ)` and `|λ^z| ≤ n^{|Re z|}`.
Blueprint: lmm:cpow-on-interval -/
theorem cpow_of_mem_Icc {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ K[n]) (z : ℂ) :
    (x : ℂ) ^ z = Complex.exp (z * Real.log x) ∧ ‖(x : ℂ) ^ z‖ ≤ (n : ℝ) ^ |z.re| := by
  obtain ⟨hx0, hlog⟩ := pos_abs_log_le_of_mem_Icc hn hx
  refine ⟨?_, ?_⟩
  · rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx0.ne'),
      ← Complex.ofReal_log hx0.le, mul_comm]
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Real.rpow_def_of_pos hx0,
      Real.rpow_def_of_pos (by exact_mod_cast hn)]
    refine Real.exp_le_exp.mpr ?_
    calc Real.log x * z.re ≤ |Real.log x * z.re| := le_abs_self _
      _ = |Real.log x| * |z.re| := abs_mul _ _
      _ ≤ Real.log n * |z.re| := mul_le_mul_of_nonneg_right hlog (abs_nonneg _)

/-- `p_{z,n}` and `q_{z,n}` are measurable, `|p_{z,n}| ≤ n^{|Re z|}` and
`|q_{z,n}| ≤ (log n) n^{|Re z|}`.
Blueprint: lmm:modular-power-function-bounds -/
theorem indicatorCpow_bounds {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    Measurable p[z, n] ∧ Measurable q[z, n] ∧
      ∀ x : ℝ, ‖p[z, n] x‖ ≤ (n : ℝ) ^ |z.re| ∧
        ‖q[z, n] x‖ ≤ Real.log n * (n : ℝ) ^ |z.re| := by
  have hmc : Measurable fun x : ℝ => (x : ℂ) ^ z :=
    Complex.measurable_ofReal.pow_const z
  refine ⟨hmc.indicator measurableSet_Icc,
    ((Complex.measurable_ofReal.comp Real.measurable_log).mul hmc).indicator measurableSet_Icc,
    fun x => ?_⟩
  have h0 : (0 : ℝ) ≤ (n : ℝ) ^ |z.re| := Real.rpow_nonneg (Nat.cast_nonneg n) _
  by_cases hx : x ∈ K[n]
  · obtain ⟨-, hlog⟩ := pos_abs_log_le_of_mem_Icc hn hx
    have hc := (cpow_of_mem_Icc hn hx z).2
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact ⟨hc, mul_le_mul hlog hc (norm_nonneg _) ((abs_nonneg _).trans hlog)⟩
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, norm_zero]
    exact ⟨h0, mul_nonneg (Real.log_nonneg (by exact_mod_cast hn)) h0⟩

/-- `p_{z,n} p_{w,n} = p_{z+w,n}` pointwise, and `p_{0,n} = 1_{K_n}`.
Blueprint: lmm:modular-power-function-identities -/
theorem indicatorCpow_mul {n : ℕ} (hn : 1 ≤ n) (z w : ℂ) :
    (∀ x : ℝ, p[z, n] x * p[w, n] x = p[z + w, n] x) ∧
      p[0, n] = (K[n]).indicator 1 := by
  refine ⟨fun x => ?_, funext fun x => ?_⟩
  · by_cases hx : x ∈ K[n]
    · have hx0 := (pos_abs_log_le_of_mem_Icc hn hx).1
      simp only [Set.indicator_of_mem hx]
      exact (Complex.cpow_add z w (Complex.ofReal_ne_zero.mpr hx0.ne')).symm
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  · by_cases hx : x ∈ K[n]
    · simp only [Set.indicator_of_mem hx, Complex.cpow_zero, Pi.one_apply]
    · simp only [Set.indicator_of_notMem hx]

/-- `conj (p_{z,n}(λ)) = p_{conj z,n}(λ)`.
Blueprint: lmm:modular-power-function-conj -/
theorem indicatorCpow_conj {n : ℕ} (hn : 1 ≤ n) (z : ℂ) (x : ℝ) :
    conj (p[z, n] x) = p[conj z, n] x := by
  by_cases hx : x ∈ K[n]
  · have hx0 := (pos_abs_log_le_of_mem_Icc hn hx).1
    have harg : (x : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hx0.le]; exact Real.pi_ne_zero.symm
    simp only [Set.indicator_of_mem hx]
    rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]
  · simp only [Set.indicator_of_notMem hx, map_zero]

/-- `p_{z+it,n}(λ) = e_t(λ) p_{z,n}(λ)`.
Blueprint: lmm:modular-power-function-shift -/
theorem indicatorCpow_add_I_mul {n : ℕ} (hn : 1 ≤ n) (z : ℂ) (t x : ℝ) :
    p[z + Complex.I * t, n] x = e[t] x * p[z, n] x := by
  by_cases hx : x ∈ K[n]
  · have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pos_abs_log_le_of_mem_Icc hn hx).1.ne'
    simp only [Set.indicator_of_mem hx]
    rw [Complex.cpow_add _ _ hx0, mul_comm, Complex.cpow_def_of_ne_zero hx0 (Complex.I * t),
      ← Complex.ofReal_log (pos_abs_log_le_of_mem_Icc hn hx).1.le, mul_comm (Real.log x : ℂ)]
  · simp only [Set.indicator_of_notMem hx, mul_zero]

/-- For `1 ≤ n ≤ m`, `p_{z,m}(λ) 1_{K_n}(λ) = p_{z,n}(λ)`.
Blueprint: lmm:modular-power-function-restrict -/
theorem indicatorCpow_mul_indicator {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) (z : ℂ) (x : ℝ) :
    p[z, m] x * (K[n]).indicator 1 x = p[z, n] x := by
  by_cases hx : x ∈ K[n]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hxm : x ∈ K[m] :=
      ⟨(one_div_le_one_div_of_le hn0 hnm').trans hx.1, hx.2.trans hnm'⟩
    simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hxm, Pi.one_apply, mul_one]
  · simp only [Set.indicator_of_notMem hx, mul_zero]

/-- For `|h| log n ≤ 1`, `|p_{z+h,n}(λ) - p_{z,n}(λ) - h q_{z,n}(λ)| ≤ n^{|Re z|} (log n)² |h|²`.
Blueprint: lmm:modular-power-taylor -/
theorem indicatorCpow_taylor {n : ℕ} (hn : 1 ≤ n) (z h : ℂ) (hh : ‖h‖ * Real.log n ≤ 1)
    (x : ℝ) :
    ‖p[z + h, n] x - p[z, n] x - h * q[z, n] x‖ ≤
      (n : ℝ) ^ |z.re| * Real.log n ^ 2 * ‖h‖ ^ 2 := by
  by_cases hx : x ∈ K[n]
  · obtain ⟨hx0, hlog⟩ := pos_abs_log_le_of_mem_Icc hn hx
    have hx0' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
    simp only [Set.indicator_of_mem hx]
    have key : (x : ℂ) ^ (z + h) - (x : ℂ) ^ z - h * ((Real.log x : ℂ) * (x : ℂ) ^ z) =
        (x : ℂ) ^ z * (Complex.exp ((Real.log x : ℂ) * h) - 1 - (Real.log x : ℂ) * h) := by
      rw [Complex.cpow_add _ _ hx0', Complex.cpow_def_of_ne_zero hx0' h,
        ← Complex.ofReal_log hx0.le]
      ring
    have hhL : ‖(Real.log x : ℂ) * h‖ ≤ ‖h‖ * Real.log n := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_left hlog (norm_nonneg _)
    rw [key, norm_mul]
    calc _ ≤ (n : ℝ) ^ |z.re| * ‖(Real.log x : ℂ) * h‖ ^ 2 :=
          mul_le_mul (cpow_of_mem_Icc hn hx z).2
            (Complex.norm_exp_sub_one_sub_id_le (hhL.trans hh)) (norm_nonneg _)
            (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ ≤ (n : ℝ) ^ |z.re| * (‖h‖ * Real.log n) ^ 2 := by gcongr
      _ = _ := by ring
  · simp only [Set.indicator_of_notMem hx, sub_zero, mul_zero, norm_zero]
    positivity

/-! ### The bounded operators `p_{z,n}(Δ)` -/

/-- `p_{z,n}(Δ)` is defined on all of `H` and equals `∫ p_{z,n} dμ`, with
`‖p_{z,n}(Δ)‖ ≤ n^{|Re z|}` and `p_{z,n}(Δ)* = p_{conj z,n}(Δ)`; in particular
`‖p_{z,n}(Δ)‖ ≤ n^{1/2}` when `|Re z| ≤ 1/2`.
Blueprint: lmm:modular-power-operators -/
theorem modularOperator_indicatorCpow {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    (functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC) p[z, n]).domain = ⊤ ∧
      functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC) p[z, n] =
        (((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n] :
          H →ₗ[ℂ] H).toPMap ⊤) ∧
      ‖(spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n]‖ ≤
        (n : ℝ) ^ |z.re| ∧
      ContinuousLinearMap.adjoint
          ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n]) =
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[conj z, n] ∧
      (|z.re| ≤ 1 / 2 →
        ‖(spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n]‖ ≤
          (n : ℝ) ^ (1 / 2 : ℝ)) := by
  set hA := modularOperator_isSelfAdjoint hM hΩ C hC
  obtain ⟨hmeas, -, hbd⟩ := indicatorCpow_bounds hn z
  have hf : p[z, n] ∈ Spectral.BddMeasurable ℝ := ⟨hmeas, _, fun x => (hbd x).1⟩
  have hnorm : ‖(spectralMeasure hA).integral p[z, n]‖ ≤ (n : ℝ) ^ |z.re| :=
    ((spectralMeasure hA).norm_integral_le hf).trans
      (ciSup_le fun x => (hbd x).1)
  obtain ⟨h1, h2⟩ := functionalCalculus_of_bddMeasurable hA hf
  refine ⟨h1, h2, hnorm, ?_, fun hz => hnorm.trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith))⟩
  rw [← (spectralMeasure hA).integral_conj hf]
  exact congrArg _ (funext fun x => indicatorCpow_conj hn z x)

/-- `p_{z,n}(Δ) p_{w,n}(Δ) = p_{z+w,n}(Δ)` and `p_{0,n}(Δ) = E_n`; hence
`E_n p_{z,n}(Δ) = p_{z,n}(Δ) E_n = p_{z,n}(Δ)`, `p_{z,n}(Δ)` maps into `Range(E_n)`, and
`p_{z,n}(Δ) p_{-z,n}(Δ) ξ = ξ` when `E_n ξ = ξ`.
Blueprint: lmm:modular-power-operators-multiplicative -/
theorem modularOperator_indicatorCpow_mul {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {n : ℕ} (hn : 1 ≤ n) (z w : ℂ) :
    (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n] *
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[w, n] =
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z + w, n] ∧
    (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[0, n] =
      spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ∧
    spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] *
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n] =
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n] ∧
    (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n] *
        spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] =
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n] ∧
    (∀ ψ : H, (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n] ψ ∈
      LinearMap.range
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] : H →ₗ[ℂ] H)) ∧
    ∀ ξ : H, spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ξ = ξ →
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n]
        ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[-z, n] ξ) =
        ξ := by
  set μ := spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)
  have hb : ∀ z : ℂ, p[z, n] ∈ Spectral.BddMeasurable ℝ := fun z =>
    let ⟨hm, _, hbd⟩ := indicatorCpow_bounds hn z
    ⟨hm, _, fun x => (hbd x).1⟩
  have hmul : ∀ z w : ℂ, μ.integral p[z, n] * μ.integral p[w, n] = μ.integral p[z + w, n] :=
    fun z w => by
      rw [← μ.integral_mul (hb z) (hb w)]
      exact congrArg _ (funext (indicatorCpow_mul hn z w).1)
  have h0 : μ.integral p[0, n] = μ K[n] := by
    rw [(indicatorCpow_mul hn 0 0).2, μ.integral_indicator measurableSet_Icc]
  have hE : μ K[n] * μ.integral p[z, n] = μ.integral p[z, n] := by rw [← h0, hmul, zero_add]
  refine ⟨hmul z w, h0, hE, by rw [← h0, hmul, add_zero],
    fun ψ => ⟨μ.integral p[z, n] ψ, by simpa using DFunLike.congr_fun hE ψ⟩, fun ξ hξ => ?_⟩
  exact (DFunLike.congr_fun (hmul z (-z)) ξ).trans (by rw [add_neg_cancel, h0, hξ])

/-- `Δ^{it} p_{z,n}(Δ) = p_{z,n}(Δ) Δ^{it} = p_{z+it,n}(Δ)`; in particular `Δ^{it}` commutes with
`E_n` and maps `Range(E_n)` into itself, and `p_{x+it,n}(Δ) = Δ^{it} p_{x,n}(Δ)` for real `x`.
Blueprint: lmm:modular-power-unitary-group -/
theorem modularUnitaryGroup_indicatorCpow {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {n : ℕ} (hn : 1 ≤ n) (z : ℂ) (t : ℝ) :
    (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap *
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n] =
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        p[z + Complex.I * t, n] ∧
    (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n] *
        (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap =
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        p[z + Complex.I * t, n] ∧
    (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap *
        spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] =
      spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] *
        (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap ∧
    (∀ ψ ∈ LinearMap.range
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] : H →ₗ[ℂ] H),
      modularUnitaryGroup hM hΩ C hC t ψ ∈
        LinearMap.range
          (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] : H →ₗ[ℂ] H)) ∧
    ∀ x : ℝ,
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          p[(x : ℂ) + Complex.I * t, n] =
        (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap *
          (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[x, n] := by
  set μ := spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)
  obtain ⟨hem, hen, -, hU, -⟩ := modularUnitaryGroup_eq_functionalCalculus hM hΩ C hC t
  have he : e[t] ∈ Spectral.BddMeasurable ℝ := ⟨hem, 1, fun x => (hen x).le⟩
  have hb : ∀ z : ℂ, p[z, n] ∈ Spectral.BddMeasurable ℝ := fun z =>
    let ⟨hm, _, hbd⟩ := indicatorCpow_bounds hn z
    ⟨hm, _, fun x => (hbd x).1⟩
  have hl : ∀ z : ℂ, (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap *
      μ.integral p[z, n] = μ.integral p[z + Complex.I * t, n] := fun z => by
    rw [hU, ← μ.integral_mul he (hb z)]
    exact congrArg _ (funext fun x => (indicatorCpow_add_I_mul hn z t x).symm)
  have hr : ∀ z : ℂ, μ.integral p[z, n] *
      (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap =
      μ.integral p[z + Complex.I * t, n] := fun z => by
    rw [hU, ← μ.integral_mul (hb z) he]
    exact congrArg _ (funext fun x =>
      ((indicatorCpow_add_I_mul hn z t x).trans (mul_comm _ _)).symm)
  have h0 := (modularOperator_indicatorCpow_mul hM hΩ C hC hn 0 0).2.1
  have hE : (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap * μ K[n] =
      μ K[n] * (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap := by
    rw [← h0, hl, hr]
  refine ⟨hl z, hr z, hE, ?_, fun x => (hl x).symm⟩
  rintro _ ⟨ψ, rfl⟩
  exact ⟨modularUnitaryGroup hM hΩ C hC t ψ, (DFunLike.congr_fun hE ψ).symm⟩

/-- For `1 ≤ n ≤ m` and `E_n ξ = ξ`, `p_{z,m}(Δ) ξ = p_{z,n}(Δ) ξ`.
Blueprint: lmm:modular-power-consistent -/
theorem modularOperator_indicatorCpow_consistent {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) (z : ℂ) {ξ : H}
    (hξ : spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ξ = ξ) :
    (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, m] ξ =
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n] ξ := by
  sorry

/-- If `h` is measurable with `h(λ) = λ^z` on `K_n` and `E_n ξ = ξ`, then `ξ ∈ Dom h(Δ)` and
`h(Δ) ξ = p_{z,n}(Δ) ξ`.
Blueprint: lmm:modular-power-agrees-fc -/
theorem modularOperator_functionalCalculus_eq_indicatorCpow {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {n : ℕ} (hn : 1 ≤ n) (z : ℂ) {h : ℝ → ℂ} (hmeas : Measurable h)
    (hK : ∀ x ∈ K[n], h x = (x : ℂ) ^ z) {ξ : H}
    (hξ : spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ξ = ξ) :
    ∃ hdom : ξ ∈ (functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC) h).domain,
      functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC) h ⟨ξ, hdom⟩ =
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n] ξ := by
  sorry

/-- If `E_n ξ = ξ`, then `ξ ∈ Dom Δ^{1/2} ∩ Dom Δ^{-1/2}`, `Δ^{1/2} ξ = p_{1/2,n}(Δ) ξ` and
`Δ^{-1/2} ξ = p_{-1/2,n}(Δ) ξ`.
Blueprint: lmm:modular-power-half -/
theorem modularOperatorSqrt_eq_indicatorCpow {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {n : ℕ} (hn : 1 ≤ n) {ξ : H}
    (hξ : spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ξ = ξ) :
    ∃ (h₁ : ξ ∈ (modularOperatorSqrt hM hΩ C hC).domain)
      (h₂ : ξ ∈ (modularOperatorInvSqrt hM hΩ C hC).domain),
      modularOperatorSqrt hM hΩ C hC ⟨ξ, h₁⟩ =
          (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
            p[(1 / 2 : ℂ), n] ξ ∧
        modularOperatorInvSqrt hM hΩ C hC ⟨ξ, h₂⟩ =
          (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
            p[(-1 / 2 : ℂ), n] ξ := by
  sorry

/-- If `E_n ξ = ξ`, then `ξ ∈ Dom S` with `S ξ = J p_{1/2,n}(Δ) ξ`, and `C ξ ∈ Dom (S′)*` with
`(S′)* C ξ = J p_{-1/2,n}(Δ) ξ`, that is, `ξ ∈ Dom S*` with `S* ξ = J p_{-1/2,n}(Δ) ξ`.
Blueprint: crllr:modular-H0-tomita-domains -/
theorem tomita_mem_domains_of_modularSpectralSubspace {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {n : ℕ} (hn : 1 ≤ n) {ξ : H}
    (hξ : spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ξ = ξ) :
    (∃ h : ξ ∈ (linearizedTomitaPre M Ω C).closure.domain,
      tomitaOperator M Ω C ⟨ξ, h⟩ =
        modularConjugation hM hΩ C hC
          ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
            p[(1 / 2 : ℂ), n] ξ)) ∧
    ∃ h : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
      (linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, h⟩ =
        modularConjugation hM hΩ C hC
          ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
            p[(-1 / 2 : ℂ), n] ξ) := by
  sorry

/-! ### Holomorphy of `z ↦ p_{z,n}(Δ)` -/

/-- For `|h| log n ≤ 1`, `‖p_{z+h,n}(Δ) - p_{z,n}(Δ) - h q_{z,n}(Δ)‖ ≤ n^{|Re z|} (log n)² |h|²`.
Blueprint: lmm:modular-power-difference-bound -/
theorem norm_modularOperator_indicatorCpow_taylor {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {n : ℕ} (hn : 1 ≤ n) (z h : ℂ) (hh : ‖h‖ * Real.log n ≤ 1) :
    ‖(spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z + h, n] -
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n] -
        h • (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral q[z, n]‖ ≤
      (n : ℝ) ^ |z.re| * Real.log n ^ 2 * ‖h‖ ^ 2 := by
  sorry

/-- `z ↦ p_{z,n}(Δ)` is complex differentiable in operator norm with derivative `q_{z,n}(Δ)`, and
is continuous.
Blueprint: thrm:modular-power-holomorphic -/
theorem hasDerivAt_modularOperator_indicatorCpow {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {n : ℕ} (hn : 1 ≤ n) :
    (∀ z : ℂ, HasDerivAt
      (fun w : ℂ => (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[w, n])
      ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral q[z, n]) z) ∧
    Continuous (fun w : ℂ =>
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[w, n]) := by
  sorry

/-- `z ↦ p_{z,n}(Δ) ξ` is complex differentiable and `z ↦ ⟪η, p_{z,n}(Δ) ξ⟫` is entire.
Blueprint: crllr:modular-power-vector-entire -/
theorem differentiable_modularOperator_indicatorCpow_apply {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {n : ℕ} (hn : 1 ≤ n) (ξ η : H) :
    Differentiable ℂ (fun z : ℂ =>
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n] ξ) ∧
    Differentiable ℂ (fun z : ℂ =>
      ⟪η, (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n] ξ⟫_ℂ) := by
  sorry

/-- `z ↦ ⟪η, p_{z,n}(Δ) a p_{-z,n}(Δ) ξ⟫` is entire.
Blueprint: crllr:modular-power-matrix-coefficients -/
theorem differentiable_inner_modularOperator_indicatorCpow_conj {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {n : ℕ} (hn : 1 ≤ n) (ξ η : H) (a : H →L[ℂ] H) :
    Differentiable ℂ (fun z : ℂ =>
      ⟪η, (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n]
        (a ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[-z, n]
          ξ))⟫_ℂ) := by
  sorry

/-! ### Conjugation by `J` -/

/-- For bounded measurable `f`, `J f(Δ) J = (f̄ ∘ ι⁻)(Δ)`, with `ι⁻` Mathlib's `x ↦ x⁻¹` on `ℝ`
(`0⁻¹ = 0`); stated pointwise as `J (f(Δ) (J ψ))`.
Blueprint: lmm:modular-conjugation-bounded-fc -/
theorem modularConjugation_integral_modularConjugation {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {f : ℝ → ℂ} (hf : f ∈ Physicslib4.Spectral.BddMeasurable ℝ) (ψ : H) :
    modularConjugation hM hΩ C hC
        ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral f
          (modularConjugation hM hΩ C hC ψ)) =
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        (fun x => conj (f x⁻¹)) ψ := by
  sorry

/-- `1_{K_n}(ι⁻(λ)) = 1_{K_n}(λ)`.
Blueprint: lmm:modular-inverse-scalar-identities -/
theorem indicator_Icc_inv {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    (K[n]).indicator (1 : ℝ → ℂ) x⁻¹ = (K[n]).indicator (1 : ℝ → ℂ) x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmem : x⁻¹ ∈ K[n] ↔ x ∈ K[n] := by
    simp only [Set.mem_Icc, one_div]
    rcases le_or_gt x 0 with hx | hx
    · have := inv_pos.2 hn0
      constructor <;> rintro ⟨h1, -⟩ <;> [linarith [inv_nonpos.2 hx]; linarith]
    · rw [inv_le_inv₀ hn0 hx, inv_le_comm₀ hx hn0]
      exact And.comm
  simp only [Set.indicator_apply, hmem, Pi.one_apply]

/-- `conj (p_{z,n}(ι⁻(λ))) = p_{-conj z,n}(λ)`.
Blueprint: lmm:modular-inverse-power-function -/
theorem conj_indicatorCpow_inv {n : ℕ} (hn : 1 ≤ n) (z : ℂ) (x : ℝ) :
    conj (p[z, n] x⁻¹) = p[-conj z, n] x := by
  have hmem : x⁻¹ ∈ K[n] ↔ x ∈ K[n] := by
    have h := indicator_Icc_inv hn x
    simp only [Set.indicator_apply, Pi.one_apply] at h
    split_ifs at h with h1 h2 h2
    · exact iff_of_true h1 h2
    · exact absurd h one_ne_zero
    · exact absurd h zero_ne_one
    · exact iff_of_false h1 h2
  by_cases hx : x ∈ K[n]
  · have hx0 := (pos_abs_log_le_of_mem_Icc hn hx).1
    have harg : (x : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hx0.le]; exact Real.pi_ne_zero.symm
    rw [Set.indicator_of_mem (hmem.2 hx), Set.indicator_of_mem hx, Complex.ofReal_inv,
      Complex.inv_cpow _ _ harg, map_inv₀, Complex.cpow_neg, Complex.cpow_conj _ _ harg,
      Complex.conj_ofReal]
  · rw [Set.indicator_of_notMem (mt hmem.1 hx), Set.indicator_of_notMem hx, map_zero]

/-- `conj (e_t(ι⁻(λ))) = e_t(λ)`.
Blueprint: lmm:modular-inverse-unitary-function -/
theorem conj_exp_log_inv (t x : ℝ) :
    conj (e[t] x⁻¹) = e[t] x := by
  simp only [Real.log_inv, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1; push_cast; ring

/-- `J E_n J = E_n`; hence `E_n ξ = ξ` implies `E_n J ξ = J ξ`, and `J H₀ = H₀`.
Blueprint: lmm:modular-conjugation-spectral-projections -/
theorem modularConjugation_spectralMeasure_Icc {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {n : ℕ} (hn : 1 ≤ n) :
    (∀ ψ : H, modularConjugation hM hΩ C hC
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n]
          (modularConjugation hM hΩ C hC ψ)) =
      spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ψ) ∧
    (∀ ξ : H, spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ξ = ξ →
      spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n]
          (modularConjugation hM hΩ C hC ξ) =
        modularConjugation hM hΩ C hC ξ) ∧
    modularConjugation hM hΩ C hC ''
        {ξ : H | ∃ m : ℕ, 1 ≤ m ∧
          spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[m] ξ = ξ} =
      {ξ : H | ∃ m : ℕ, 1 ≤ m ∧
        spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[m] ξ = ξ} := by
  sorry

/-- `J p_{z,n}(Δ) J = p_{-conj z,n}(Δ)` and `J Δ^{it} J = Δ^{it}`; in particular
`J p_{x,n}(Δ) J = p_{-x,n}(Δ)` for real `x`. Stated pointwise.
Blueprint: lmm:modular-conjugation-powers -/
theorem modularConjugation_indicatorCpow_modularConjugation {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {n : ℕ} (hn : 1 ≤ n) (z : ℂ) (t : ℝ) :
    (∀ ψ : H, modularConjugation hM hΩ C hC
        ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[z, n]
          (modularConjugation hM hΩ C hC ψ)) =
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[-conj z, n] ψ) ∧
    (∀ ψ : H, modularConjugation hM hΩ C hC
        (modularUnitaryGroup hM hΩ C hC t (modularConjugation hM hΩ C hC ψ)) =
      modularUnitaryGroup hM hΩ C hC t ψ) ∧
    ∀ (x : ℝ) (ψ : H), modularConjugation hM hΩ C hC
        ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[x, n]
          (modularConjugation hM hΩ C hC ψ)) =
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[-x, n] ψ := by
  sorry

/-! ### The Tomita operator on `M Ω` -/

/-- For `c ∈ M`, `c Ω ∈ Dom S` and `S (c Ω) = c* Ω`.
Blueprint: lmm:tomita-operator-on-algebra -/
theorem tomitaOperator_apply_of_mem {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {c : H →L[ℂ] H} (hc : c ∈ M) :
    ∃ h : c Ω ∈ (linearizedTomitaPre M Ω C).closure.domain,
      tomitaOperator M Ω C ⟨c Ω, h⟩ = star c Ω := by
  sorry

/-! ### Conjugation of bounded operators by `J` and van Daele triples -/

/-- The bounded operator `J T J : ψ ↦ J (T (J ψ))`.
Blueprint: def:modular-conjugation-conjugate -/
noncomputable def modularConjugationConj {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (((modularConjugation hM hΩ C hC).toContinuousLinearEquiv : H →SL[starRingEnd ℂ] H).comp
    T).comp ((modularConjugation hM hΩ C hC).toContinuousLinearEquiv : H →SL[starRingEnd ℂ] H)

/-- `(λ, a', a)` is a van Daele triple: `λ > 0`, `a' ∈ M′`, `a ∈ M`,
`a Ω ∈ Dom S ∩ Dom S*` and `a' Ω = λ S (a Ω) + λ⁻¹ S* (a Ω)`.
Blueprint: def:van-daele-triple -/
def IsVanDaeleTriple (M : Set (H →L[ℂ] H)) (Ω : H) (C : H ≃ₗᵢ⋆[ℂ] H) (l : ℝ)
    (a' a : H →L[ℂ] H) : Prop :=
  0 < l ∧ a' ∈ Set.centralizer M ∧ a ∈ M ∧
    ∃ (hS : a Ω ∈ (linearizedTomitaPre M Ω C).closure.domain)
      (hS' : C (a Ω) ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain),
      a' Ω = (l : ℂ) • tomitaOperator M Ω C ⟨a Ω, hS⟩ +
        (l⁻¹ : ℂ) • (linearizedTomitaPre M Ω C).closure.adjoint ⟨C (a Ω), hS'⟩

/-! ### The functions `g_λ`, `v_λ` and `k_λ` -/

/-- `g_λ(t) = λ / (1 + λ² t)` for `t > 0` and `0` otherwise.
Blueprint: def:van-daele-g -/
noncomputable def vanDaeleG (l : ℝ) : ℝ → ℂ :=
  (Set.Ioi (0 : ℝ)).indicator fun t => ((l / (1 + l ^ 2 * t) : ℝ) : ℂ)

/-- `v_λ(t) = λ √t / (1 + λ² t)` for `t > 0` and `0` otherwise.
Blueprint: def:van-daele-v -/
noncomputable def vanDaeleV (l : ℝ) : ℝ → ℂ :=
  (Set.Ioi (0 : ℝ)).indicator fun t => ((l * Real.sqrt t / (1 + l ^ 2 * t) : ℝ) : ℂ)

/-- `k_λ(t) = λ t / (1 + λ² t)` for `t > 0` and `0` otherwise.
Blueprint: def:van-daele-k -/
noncomputable def vanDaeleK (l : ℝ) : ℝ → ℂ :=
  (Set.Ioi (0 : ℝ)).indicator fun t => ((l * t / (1 + l ^ 2 * t) : ℝ) : ℂ)

/-- For `λ > 0`, `g_λ`, `v_λ`, `k_λ` are measurable and real, with `0 ≤ g_λ ≤ λ`,
`0 ≤ v_λ ≤ 1/2` and `0 ≤ k_λ ≤ λ⁻¹`.
Blueprint: lmm:van-daele-functions-bounded -/
theorem vanDaele_functions_bounded {l : ℝ} (hl : 0 < l) :
    Measurable (vanDaeleG l) ∧ Measurable (vanDaeleV l) ∧ Measurable (vanDaeleK l) ∧
      ∀ t : ℝ,
        ((vanDaeleG l t).im = 0 ∧ 0 ≤ (vanDaeleG l t).re ∧ (vanDaeleG l t).re ≤ l) ∧
        ((vanDaeleV l t).im = 0 ∧ 0 ≤ (vanDaeleV l t).re ∧ (vanDaeleV l t).re ≤ 1 / 2) ∧
        ((vanDaeleK l t).im = 0 ∧ 0 ≤ (vanDaeleK l t).re ∧ (vanDaeleK l t).re ≤ l⁻¹) := by
  sorry

/-- With `s(t) = √t` and `r(t) = (√t)⁻¹`: `s g_λ = v_λ`, `v_λ s = k_λ`, `k_λ r = v_λ`,
`v_λ r = g_λ` and `λ k_λ + λ⁻¹ g_λ = 1_{(0, ∞)}`.
Blueprint: lmm:van-daele-functions-identities -/
theorem vanDaele_functions_identities {l : ℝ} (hl : 0 < l) (t : ℝ) :
    ((Real.sqrt t : ℝ) : ℂ) * vanDaeleG l t = vanDaeleV l t ∧
      vanDaeleV l t * ((Real.sqrt t : ℝ) : ℂ) = vanDaeleK l t ∧
      vanDaeleK l t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) = vanDaeleV l t ∧
      vanDaeleV l t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) = vanDaeleG l t ∧
      (l : ℂ) * vanDaeleK l t + (l⁻¹ : ℂ) * vanDaeleG l t =
        (Set.Ioi (0 : ℝ)).indicator 1 t := by
  sorry

/-- If measurable `f`, `h` agree on `(0, ∞)`, then `W_f = W_h` and `f(Δ) = h(Δ)`.
Blueprint: lmm:modular-fc-congr-positive -/
theorem modularOperator_functionalCalculus_congr_pos {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {f h : ℝ → ℂ} (hf : Measurable f) (hh : Measurable h)
    (hfh : ∀ t : ℝ, 0 < t → f t = h t) :
    integralDomain (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)) f =
        integralDomain (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)) h ∧
      functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC) f =
        functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC) h := by
  sorry

/-- For `λ > 0` and `z = -λ⁻²`: `z ∉ [0, ∞)`, `√(2(|z| - Re z)) = 2λ⁻¹`, and
`-λ⁻¹ r_z(t) = g_λ(t)` for `t > 0`.
Blueprint: lmm:van-daele-resolvent-point -/
theorem vanDaele_resolvent_point {l : ℝ} (hl : 0 < l) :
    -((l : ℂ) ^ 2)⁻¹ ∉ ((↑) : ℝ → ℂ) '' Set.Ici 0 ∧
      Real.sqrt (2 * (‖-((l : ℂ) ^ 2)⁻¹‖ - (-((l : ℂ) ^ 2)⁻¹).re)) = 2 * l⁻¹ ∧
      ∀ t : ℝ, 0 < t →
        -(l⁻¹ : ℂ) * (Set.Ici (0 : ℝ)).indicator (fun t : ℝ => (-((l : ℂ) ^ 2)⁻¹ - t)⁻¹) t =
          vanDaeleG l t := by
  sorry

/-- For `λ > 0` and `z = -λ⁻²`, `g_λ(Δ) = -λ⁻¹ (z - Δ)⁻¹`, a bounded operator on all of `H`.
Blueprint: lmm:van-daele-g-resolvent -/
theorem modularOperator_vanDaeleG_eq_resolvent {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} (hl : 0 < l) :
    functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC) (vanDaeleG l) =
        (((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          (vanDaeleG l) : H →ₗ[ℂ] H).toPMap ⊤) ∧
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleG l) =
        -(l⁻¹ : ℂ) • (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          ((Set.Ici (0 : ℝ)).indicator fun t : ℝ => (-((l : ℂ) ^ 2)⁻¹ - t)⁻¹) := by
  sorry

/-- For `ξ ∈ Dom Δ^{1/2}`, `g_λ(Δ) Δ^{1/2} ξ = v_λ(Δ) ξ` and `v_λ(Δ) Δ^{1/2} ξ = k_λ(Δ) ξ`; for
`ξ ∈ Dom Δ^{-1/2}`, `k_λ(Δ) Δ^{-1/2} ξ = v_λ(Δ) ξ` and `v_λ(Δ) Δ^{-1/2} ξ = g_λ(Δ) ξ`.
Blueprint: lmm:van-daele-fc-products -/
theorem modularOperator_vanDaele_products {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} (hl : 0 < l) :
    (∀ ξ : (modularOperatorSqrt hM hΩ C hC).domain,
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleG l)
          (modularOperatorSqrt hM hΩ C hC ξ) =
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleV l) ξ ∧
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleV l)
          (modularOperatorSqrt hM hΩ C hC ξ) =
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleK l) ξ) ∧
    ∀ ξ : (modularOperatorInvSqrt hM hΩ C hC).domain,
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleK l)
          (modularOperatorInvSqrt hM hΩ C hC ξ) =
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleV l) ξ ∧
      (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleV l)
          (modularOperatorInvSqrt hM hΩ C hC ξ) =
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleG l) ξ := by
  sorry

/-- For `ψ ∈ Dom Δ^{-1/2}`, `g_λ(Δ) ψ ∈ Dom Δ^{1/2} ∩ Dom Δ^{-1/2}` with
`Δ^{1/2} g_λ(Δ) ψ = k_λ(Δ) Δ^{-1/2} ψ` and `Δ^{-1/2} g_λ(Δ) ψ = g_λ(Δ) Δ^{-1/2} ψ`.
Blueprint: lmm:van-daele-g-domains -/
theorem modularOperator_vanDaeleG_domains {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} (hl : 0 < l) (ψ : (modularOperatorInvSqrt hM hΩ C hC).domain) :
    ∃ (h₁ : (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleG l) ψ ∈
        (modularOperatorSqrt hM hΩ C hC).domain)
      (h₂ : (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleG l) ψ ∈
        (modularOperatorInvSqrt hM hΩ C hC).domain),
      modularOperatorSqrt hM hΩ C hC ⟨_, h₁⟩ =
          (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleK l)
            (modularOperatorInvSqrt hM hΩ C hC ψ) ∧
        modularOperatorInvSqrt hM hΩ C hC ⟨_, h₂⟩ =
          (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleG l)
            (modularOperatorInvSqrt hM hΩ C hC ψ) := by
  sorry

/-- For `λ > 0`, `λ k_λ(Δ) + λ⁻¹ g_λ(Δ) = 𝟙`.
Blueprint: lmm:van-daele-partition-of-unity -/
theorem modularOperator_vanDaele_partition_of_unity {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} (hl : 0 < l) :
    (l : ℂ) • (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          (vanDaeleK l) +
        (l⁻¹ : ℂ) • (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          (vanDaeleG l) = 1 := by
  sorry

/-- For `b' ∈ M′`, `b' Ω ∈ Dom S* = Dom Δ^{-1/2}`, `S* (b' Ω) = J Δ^{-1/2} b' Ω = b'* Ω` and
`Δ^{-1/2} b' Ω = J (b'* Ω)`.
Blueprint: lmm:tomita-adjoint-on-commutant -/
theorem tomitaAdjoint_apply_of_mem_centralizer {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {b' : H →L[ℂ] H} (hb' : b' ∈ Set.centralizer M) :
    (∃ h : C (b' Ω) ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain,
      (linearizedTomitaPre M Ω C).closure.adjoint ⟨C (b' Ω), h⟩ = star b' Ω) ∧
    ∃ h : b' Ω ∈ (modularOperatorInvSqrt hM hΩ C hC).domain,
      modularConjugation hM hΩ C hC (modularOperatorInvSqrt hM hΩ C hC ⟨b' Ω, h⟩) =
          star b' Ω ∧
        modularOperatorInvSqrt hM hΩ C hC ⟨b' Ω, h⟩ =
          modularConjugation hM hΩ C hC (star b' Ω) := by
  sorry

/-- For `λ > 0` and `a' ∈ M′` there is `a ∈ M` with `a Ω = g_λ(Δ) a'* Ω` and `‖a‖ ≤ ‖a'‖ / 2`.
Blueprint: lmm:van-daele-element -/
theorem exists_vanDaele_element {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} (hl : 0 < l) {a' : H →L[ℂ] H}
    (ha' : a' ∈ Set.centralizer M) :
    ∃ a ∈ M, a Ω = (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        (vanDaeleG l) (star a' Ω) ∧ ‖a‖ ≤ ‖a'‖ / 2 := by
  sorry

/-- If `a ∈ M` and `a Ω = g_λ(Δ) a'* Ω`, then with `φ = J (a' Ω)`,
`a Ω ∈ Dom Δ^{1/2} ∩ Dom Δ^{-1/2}`, `a Ω = v_λ(Δ) φ`, `Δ^{1/2} a Ω = k_λ(Δ) φ` and
`Δ^{-1/2} a Ω = g_λ(Δ) φ`.
Blueprint: lmm:van-daele-element-formulas -/
theorem vanDaele_element_formulas {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} (hl : 0 < l) {a' a : H →L[ℂ] H}
    (ha' : a' ∈ Set.centralizer M) (ha : a ∈ M)
    (haΩ : a Ω = (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
      (vanDaeleG l) (star a' Ω)) :
    ∃ (h₁ : a Ω ∈ (modularOperatorSqrt hM hΩ C hC).domain)
      (h₂ : a Ω ∈ (modularOperatorInvSqrt hM hΩ C hC).domain),
      a Ω = (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleV l)
          (modularConjugation hM hΩ C hC (a' Ω)) ∧
        modularOperatorSqrt hM hΩ C hC ⟨a Ω, h₁⟩ =
          (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleK l)
            (modularConjugation hM hΩ C hC (a' Ω)) ∧
        modularOperatorInvSqrt hM hΩ C hC ⟨a Ω, h₂⟩ =
          (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleG l)
            (modularConjugation hM hΩ C hC (a' Ω)) := by
  sorry

/-- For `λ > 0` and `a' ∈ M′` there is `a` with `(λ, a', a)` a van Daele triple,
`‖a‖ ≤ ‖a'‖ / 2` and `a Ω = g_λ(Δ) a'* Ω`.
Blueprint: lmm:van-daele-commutant-equation -/
theorem exists_isVanDaeleTriple {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} (hl : 0 < l) {a' : H →L[ℂ] H}
    (ha' : a' ∈ Set.centralizer M) :
    ∃ a : H →L[ℂ] H, IsVanDaeleTriple M Ω C l a' a ∧ ‖a‖ ≤ ‖a'‖ / 2 ∧
      a Ω = (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        (vanDaeleG l) (star a' Ω) := by
  sorry

/-! ### Van Daele's approximation and sesquilinear identities -/

/-- For `ξ ∈ Dom Δ^{1/2} ∩ Dom Δ^{-1/2}` and `φ = Δ^{1/2} ξ + Δ^{-1/2} ξ`, `v_1(Δ) φ = ξ`,
`k_1(Δ) φ = Δ^{1/2} ξ` and `g_1(Δ) φ = Δ^{-1/2} ξ`.
Blueprint: lmm:van-daele-inversion -/
theorem modularOperator_vanDaele_inversion {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ : H} (h₁ : ξ ∈ (modularOperatorSqrt hM hΩ C hC).domain)
    (h₂ : ξ ∈ (modularOperatorInvSqrt hM hΩ C hC).domain) :
    (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleV 1)
        (modularOperatorSqrt hM hΩ C hC ⟨ξ, h₁⟩ + modularOperatorInvSqrt hM hΩ C hC ⟨ξ, h₂⟩) =
      ξ ∧
    (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleK 1)
        (modularOperatorSqrt hM hΩ C hC ⟨ξ, h₁⟩ + modularOperatorInvSqrt hM hΩ C hC ⟨ξ, h₂⟩) =
      modularOperatorSqrt hM hΩ C hC ⟨ξ, h₁⟩ ∧
    (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral (vanDaeleG 1)
        (modularOperatorSqrt hM hΩ C hC ⟨ξ, h₁⟩ + modularOperatorInvSqrt hM hΩ C hC ⟨ξ, h₂⟩) =
      modularOperatorInvSqrt hM hΩ C hC ⟨ξ, h₂⟩ := by
  sorry

/-- Every `φ ∈ H` is a limit `J (a'_n Ω) → φ` with `a'_n ∈ M′`.
Blueprint: lmm:modular-conjugation-commutant-dense -/
theorem exists_tendsto_modularConjugation_centralizer {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (φ : H) :
    ∃ a' : ℕ → H →L[ℂ] H, (∀ n, a' n ∈ Set.centralizer M) ∧
      Tendsto (fun n => modularConjugation hM hΩ C hC (a' n Ω)) atTop (𝓝 φ) := by
  sorry

/-- For `ξ ∈ Dom Δ^{1/2} ∩ Dom Δ^{-1/2}` there are `a_n ∈ M` with
`a_n Ω ∈ Dom Δ^{1/2} ∩ Dom Δ^{-1/2}`, `a_n Ω → ξ`, `Δ^{1/2} a_n Ω → Δ^{1/2} ξ` and
`Δ^{-1/2} a_n Ω → Δ^{-1/2} ξ`.
Blueprint: crllr:van-daele-approximation -/
theorem exists_tendsto_modularOperatorSqrt_of_mem {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ : H} (h₁ : ξ ∈ (modularOperatorSqrt hM hΩ C hC).domain)
    (h₂ : ξ ∈ (modularOperatorInvSqrt hM hΩ C hC).domain) :
    ∃ a : ℕ → H →L[ℂ] H, (∀ n, a n ∈ M) ∧
      ∃ (ha₁ : ∀ n, a n Ω ∈ (modularOperatorSqrt hM hΩ C hC).domain)
        (ha₂ : ∀ n, a n Ω ∈ (modularOperatorInvSqrt hM hΩ C hC).domain),
        Tendsto (fun n => a n Ω) atTop (𝓝 ξ) ∧
        Tendsto (fun n => modularOperatorSqrt hM hΩ C hC ⟨a n Ω, ha₁ n⟩) atTop
          (𝓝 (modularOperatorSqrt hM hΩ C hC ⟨ξ, h₁⟩)) ∧
        Tendsto (fun n => modularOperatorInvSqrt hM hΩ C hC ⟨a n Ω, ha₂ n⟩) atTop
          (𝓝 (modularOperatorInvSqrt hM hΩ C hC ⟨ξ, h₂⟩)) := by
  sorry

/-- For `ξ ∈ Dom S ∩ Dom S*` there are `a_n ∈ M` with `a_n Ω ∈ Dom S ∩ Dom S*`, `a_n Ω → ξ`,
`S (a_n Ω) → S ξ` and `S* (a_n Ω) → S* ξ`.
Blueprint: crllr:van-daele-approximation-tomita -/
theorem exists_tendsto_tomitaOperator_of_mem {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ : H} (hS : ξ ∈ (linearizedTomitaPre M Ω C).closure.domain)
    (hS' : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain) :
    ∃ a : ℕ → H →L[ℂ] H, (∀ n, a n ∈ M) ∧
      ∃ (haS : ∀ n, a n Ω ∈ (linearizedTomitaPre M Ω C).closure.domain)
        (haS' : ∀ n, C (a n Ω) ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain),
        Tendsto (fun n => a n Ω) atTop (𝓝 ξ) ∧
        Tendsto (fun n => tomitaOperator M Ω C ⟨a n Ω, haS n⟩) atTop
          (𝓝 (tomitaOperator M Ω C ⟨ξ, hS⟩)) ∧
        Tendsto (fun n => (linearizedTomitaPre M Ω C).closure.adjoint ⟨C (a n Ω), haS' n⟩) atTop
          (𝓝 ((linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, hS'⟩)) := by
  sorry

/-- If `ξ ∈ Dom S*`, then `S* ξ ∈ Dom S*` and `S* S* ξ = ξ`.
Blueprint: lmm:tomita-adjoint-involution -/
theorem tomitaAdjoint_involutive {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {ξ : H}
    (hξ : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain) :
    ∃ h : C ((linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, hξ⟩) ∈
        (linearizedTomitaPre M Ω C).closure.adjoint.domain,
      (linearizedTomitaPre M Ω C).closure.adjoint
        ⟨C ((linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, hξ⟩), h⟩ = ξ := by
  sorry

/-- For `a, x, y ∈ M` with `y Ω ∈ Dom S*`, `⟪a S(x Ω), S*(y Ω)⟫ = ⟪x* y Ω, S(a Ω)⟫`.
Blueprint: lmm:van-daele-first-term -/
theorem inner_tomitaOperator_tomitaAdjoint_of_mem {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {a x y : H →L[ℂ] H} (ha : a ∈ M) (hx : x ∈ M) (hy : y ∈ M)
    (haS : a Ω ∈ (linearizedTomitaPre M Ω C).closure.domain)
    (hxS : x Ω ∈ (linearizedTomitaPre M Ω C).closure.domain)
    (hyS' : C (y Ω) ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain) :
    ⟪a (tomitaOperator M Ω C ⟨x Ω, hxS⟩),
        (linearizedTomitaPre M Ω C).closure.adjoint ⟨C (y Ω), hyS'⟩⟫_ℂ =
      ⟪(star x * y) Ω, tomitaOperator M Ω C ⟨a Ω, haS⟩⟫_ℂ := by
  sorry

/-- For `a, x, y ∈ M` with `x Ω, a Ω ∈ Dom S*`, `⟪a S*(x Ω), S(y Ω)⟫ = ⟪x* y Ω, S*(a Ω)⟫`.
Blueprint: lmm:van-daele-second-term -/
theorem inner_tomitaAdjoint_tomitaOperator_of_mem {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {a x y : H →L[ℂ] H} (ha : a ∈ M) (hx : x ∈ M) (hy : y ∈ M)
    (haS' : C (a Ω) ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain)
    (hxS' : C (x Ω) ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain)
    (hyS : y Ω ∈ (linearizedTomitaPre M Ω C).closure.domain) :
    ⟪a ((linearizedTomitaPre M Ω C).closure.adjoint ⟨C (x Ω), hxS'⟩),
        tomitaOperator M Ω C ⟨y Ω, hyS⟩⟫_ℂ =
      ⟪(star x * y) Ω, (linearizedTomitaPre M Ω C).closure.adjoint ⟨C (a Ω), haS'⟩⟫_ℂ := by
  sorry

/-- For a van Daele triple `(λ, a', a)` and `x, y ∈ M` with `x Ω, y Ω ∈ Dom S*`,
`λ ⟪a S(x Ω), S*(y Ω)⟫ + λ⁻¹ ⟪a S*(x Ω), S(y Ω)⟫ = ⟪y Ω, a' x Ω⟫`.
Blueprint: lmm:van-daele-identity-algebra -/
theorem IsVanDaeleTriple.inner_identity_of_mem {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} {a' a : H →L[ℂ] H} (htriple : IsVanDaeleTriple M Ω C l a' a)
    {x y : H →L[ℂ] H} (hx : x ∈ M) (hy : y ∈ M)
    (hxS : x Ω ∈ (linearizedTomitaPre M Ω C).closure.domain)
    (hxS' : C (x Ω) ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain)
    (hyS : y Ω ∈ (linearizedTomitaPre M Ω C).closure.domain)
    (hyS' : C (y Ω) ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain) :
    (l : ℂ) * ⟪a (tomitaOperator M Ω C ⟨x Ω, hxS⟩),
        (linearizedTomitaPre M Ω C).closure.adjoint ⟨C (y Ω), hyS'⟩⟫_ℂ +
      (l⁻¹ : ℂ) * ⟪a ((linearizedTomitaPre M Ω C).closure.adjoint ⟨C (x Ω), hxS'⟩),
        tomitaOperator M Ω C ⟨y Ω, hyS⟩⟫_ℂ =
      ⟪y Ω, a' (x Ω)⟫_ℂ := by
  sorry

/-- For a van Daele triple `(λ, a', a)` and `ξ, η ∈ Dom S ∩ Dom S*`,
`λ ⟪a S ξ, S* η⟫ + λ⁻¹ ⟪a S* ξ, S η⟫ = ⟪η, a' ξ⟫`.
Blueprint: lmm:van-daele-sesquilinear-identity -/
theorem IsVanDaeleTriple.inner_identity {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} {a' a : H →L[ℂ] H} (htriple : IsVanDaeleTriple M Ω C l a' a)
    {ξ η : H} (hξS : ξ ∈ (linearizedTomitaPre M Ω C).closure.domain)
    (hξS' : C ξ ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain)
    (hηS : η ∈ (linearizedTomitaPre M Ω C).closure.domain)
    (hηS' : C η ∈ (linearizedTomitaPre M Ω C).closure.adjoint.domain) :
    (l : ℂ) * ⟪a (tomitaOperator M Ω C ⟨ξ, hξS⟩),
        (linearizedTomitaPre M Ω C).closure.adjoint ⟨C η, hηS'⟩⟫_ℂ +
      (l⁻¹ : ℂ) * ⟪a ((linearizedTomitaPre M Ω C).closure.adjoint ⟨C ξ, hξS'⟩),
        tomitaOperator M Ω C ⟨η, hηS⟩⟫_ℂ =
      ⟪η, a' ξ⟫_ℂ := by
  sorry

/-- For `ξ ∈ Dom Δ^{-1/2}`, `J ξ ∈ Dom S` and `S (J ξ) = Δ^{-1/2} ξ`; for `ξ ∈ Dom Δ^{1/2}`,
`J ξ ∈ Dom S*` and `S* (J ξ) = Δ^{1/2} ξ`.
Blueprint: lmm:tomita-operators-after-conjugation -/
theorem tomitaOperator_modularConjugation {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    (∀ ξ : (modularOperatorInvSqrt hM hΩ C hC).domain,
      ∃ h : modularConjugation hM hΩ C hC ξ ∈ (linearizedTomitaPre M Ω C).closure.domain,
        tomitaOperator M Ω C ⟨modularConjugation hM hΩ C hC ξ, h⟩ =
          modularOperatorInvSqrt hM hΩ C hC ξ) ∧
    ∀ ξ : (modularOperatorSqrt hM hΩ C hC).domain,
      ∃ h : C (modularConjugation hM hΩ C hC ξ) ∈
          (linearizedTomitaPre M Ω C).closure.adjoint.domain,
        (linearizedTomitaPre M Ω C).closure.adjoint ⟨C (modularConjugation hM hΩ C hC ξ), h⟩ =
          modularOperatorSqrt hM hΩ C hC ξ := by
  sorry

/-- For a van Daele triple `(λ, a', a)` and `ξ, η ∈ Dom Δ^{1/2} ∩ Dom Δ^{-1/2}`,
`⟪η, J a' J ξ⟫ = λ ⟪Δ^{1/2} η, a Δ^{-1/2} ξ⟫ + λ⁻¹ ⟪Δ^{-1/2} η, a Δ^{1/2} ξ⟫`.
Blueprint: crllr:van-daele-rearranged-identity -/
theorem IsVanDaeleTriple.inner_modularConjugationConj {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} {a' a : H →L[ℂ] H} (htriple : IsVanDaeleTriple M Ω C l a' a)
    {ξ η : H} (hξ₁ : ξ ∈ (modularOperatorSqrt hM hΩ C hC).domain)
    (hξ₂ : ξ ∈ (modularOperatorInvSqrt hM hΩ C hC).domain)
    (hη₁ : η ∈ (modularOperatorSqrt hM hΩ C hC).domain)
    (hη₂ : η ∈ (modularOperatorInvSqrt hM hΩ C hC).domain) :
    ⟪η, modularConjugationConj hM hΩ C hC a' ξ⟫_ℂ =
      (l : ℂ) * ⟪modularOperatorSqrt hM hΩ C hC ⟨η, hη₁⟩,
          a (modularOperatorInvSqrt hM hΩ C hC ⟨ξ, hξ₂⟩)⟫_ℂ +
        (l⁻¹ : ℂ) * ⟪modularOperatorInvSqrt hM hΩ C hC ⟨η, hη₂⟩,
          a (modularOperatorSqrt hM hΩ C hC ⟨ξ, hξ₁⟩)⟫_ℂ := by
  sorry

/-- For a van Daele triple `(λ, a', a)`, `n ≥ 1` and `E_n ξ = ξ`, `E_n η = η`,
`⟪η, J a' J ξ⟫ = λ ⟪p_{1/2,n}(Δ) η, a p_{-1/2,n}(Δ) ξ⟫ + λ⁻¹ ⟪p_{-1/2,n}(Δ) η, a p_{1/2,n}(Δ) ξ⟫`.
Blueprint: crllr:van-daele-rearranged-identity-H0 -/
theorem IsVanDaeleTriple.inner_modularConjugationConj_indicatorCpow {M : Set (H →L[ℂ] H)}
    {Ω : H} (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} {a' a : H →L[ℂ] H} (htriple : IsVanDaeleTriple M Ω C l a' a)
    {n : ℕ} (hn : 1 ≤ n) {ξ η : H}
    (hξ : spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ξ = ξ)
    (hη : spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] η = η) :
    ⟪η, modularConjugationConj hM hΩ C hC a' ξ⟫_ℂ =
      (l : ℂ) * ⟪(spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
            p[(1 / 2 : ℂ), n] η,
          a ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
            p[(-1 / 2 : ℂ), n] ξ)⟫_ℂ +
        (l⁻¹ : ℂ) * ⟪(spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
            p[(-1 / 2 : ℂ), n] η,
          a ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
            p[(1 / 2 : ℂ), n] ξ)⟫_ℂ := by
  sorry

/-! ### Tomita's theorem: the strip function and the integral formula -/

/-- `J T J` is the unique bounded operator with `(J T J) ψ = J (T (J ψ))`, and `‖J T J‖ ≤ ‖T‖`.
Blueprint: lmm:modular-conjugation-bounded-conjugate -/
theorem modularConjugationConj_apply {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (T : H →L[ℂ] H) :
    (∀ ψ : H, modularConjugationConj hM hΩ C hC T ψ =
      modularConjugation hM hΩ C hC (T (modularConjugation hM hΩ C hC ψ))) ∧
    ‖modularConjugationConj hM hΩ C hC T‖ ≤ ‖T‖ ∧
    ∀ T' : H →L[ℂ] H,
      (∀ ψ : H, T' ψ = modularConjugation hM hΩ C hC (T (modularConjugation hM hΩ C hC ψ))) →
      T' = modularConjugationConj hM hΩ C hC T := by
  sorry

/-- `J (J T J) J = T` and `(J T J)(J T′ J) = J (T T′) J`.
Blueprint: lmm:modular-conjugation-bounded-conjugate-identities -/
theorem modularConjugationConj_identities {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (T T' : H →L[ℂ] H) :
    modularConjugationConj hM hΩ C hC (modularConjugationConj hM hΩ C hC T) = T ∧
      modularConjugationConj hM hΩ C hC T * modularConjugationConj hM hΩ C hC T' =
        modularConjugationConj hM hΩ C hC (T * T') := by
  sorry

/-- For `λ > 0` and `|s| ≤ 1`, `λ^s ≤ max(λ, λ⁻¹)`.
Blueprint: lmm:van-daele-rpow-le-max -/
theorem rpow_le_max_inv {l s : ℝ} (hl : 0 < l) (hs : |s| ≤ 1) : l ^ s ≤ max l l⁻¹ := by
  sorry

/-- For `λ > 0`, `z ↦ λ^{2z}` is entire, `λ^0 = 1`, and `|λ^{2z}| = λ^{2 Re z} ≤ max(λ, λ⁻¹)` for
`|Re z| ≤ 1/2`.
Blueprint: lmm:van-daele-phase-strip -/
theorem vanDaele_phase_strip {l : ℝ} (hl : 0 < l) :
    Differentiable ℂ (fun z : ℂ => (l : ℂ) ^ (2 * z)) ∧ (l : ℂ) ^ (2 * (0 : ℂ)) = 1 ∧
      ∀ z : ℂ, |z.re| ≤ 1 / 2 →
        ‖(l : ℂ) ^ (2 * z)‖ = l ^ (2 * z.re) ∧ l ^ (2 * z.re) ≤ max l l⁻¹ := by
  sorry

/-- For `λ > 0`, `λ^{2(1/2 + it)} = λ λ^{2it}`, `λ^{2(-1/2 + it)} = λ⁻¹ λ^{2it}`, `|λ^{2it}| = 1`,
and `t ↦ λ^{2it}` is continuous.
Blueprint: lmm:van-daele-phase-boundary -/
theorem vanDaele_phase_boundary {l : ℝ} (hl : 0 < l) :
    (∀ t : ℝ,
      (l : ℂ) ^ (2 * ((1 / 2 : ℂ) + Complex.I * t)) = l * (l : ℂ) ^ (2 * (Complex.I * t)) ∧
      (l : ℂ) ^ (2 * ((-1 / 2 : ℂ) + Complex.I * t)) =
        (l⁻¹ : ℂ) * (l : ℂ) ^ (2 * (Complex.I * t)) ∧
      ‖(l : ℂ) ^ (2 * (Complex.I * t))‖ = 1) ∧
    Continuous (fun t : ℝ => (l : ℂ) ^ (2 * (Complex.I * t))) := by
  sorry

/-- For `λ = e^{θ/2}`, `λ > 0` and `λ^{2it} = e^{iθt}`.
Blueprint: lmm:van-daele-phase-fourier -/
theorem vanDaele_phase_fourier (θ : ℝ) :
    0 < Real.exp (θ / 2) ∧
      ∀ t : ℝ, ((Real.exp (θ / 2) : ℝ) : ℂ) ^ (2 * (Complex.I * t)) =
        Complex.exp (Complex.I * θ * t) := by
  sorry

/-- `⟪η, Δ^{it} J a′ J Δ^{-it} ξ⟫ = ⟪Δ^{-it} η, J a′ J Δ^{-it} ξ⟫`, continuous in `t`.
Blueprint: lmm:van-daele-integrand-continuous -/
theorem continuous_inner_modularUnitaryGroup_conj {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (a' : H →L[ℂ] H) (ξ η : H) :
    (∀ t : ℝ, ⟪η, modularUnitaryGroup hM hΩ C hC t
        (modularConjugationConj hM hΩ C hC a'
          (modularUnitaryGroup hM hΩ C hC (-t) ξ))⟫_ℂ =
      ⟪modularUnitaryGroup hM hΩ C hC (-t) η,
        modularConjugationConj hM hΩ C hC a' (modularUnitaryGroup hM hΩ C hC (-t) ξ)⟫_ℂ) ∧
    Continuous (fun t : ℝ => ⟪η, modularUnitaryGroup hM hΩ C hC t
        (modularConjugationConj hM hΩ C hC a'
          (modularUnitaryGroup hM hΩ C hC (-t) ξ))⟫_ℂ) := by
  sorry

/-- `|⟪η, Δ^{it} J a′ J Δ^{-it} ξ⟫| ≤ ‖a′‖ ‖ξ‖ ‖η‖`.
Blueprint: lmm:van-daele-integrand-bound -/
theorem norm_inner_modularUnitaryGroup_conj_le {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (a' : H →L[ℂ] H) (ξ η : H) (t : ℝ) :
    ‖⟪η, modularUnitaryGroup hM hΩ C hC t
      (modularConjugationConj hM hΩ C hC a'
        (modularUnitaryGroup hM hΩ C hC (-t) ξ))⟫_ℂ‖ ≤
      ‖a'‖ * ‖ξ‖ * ‖η‖ := by
  sorry

/-- `F(t) = λ^{2it} ⟪η, Δ^{it} J a′ J Δ^{-it} ξ⟫ / (2 cosh πt)` is continuous, bounded by
`‖a′‖ ‖ξ‖ ‖η‖ / (2 cosh πt)`, and integrable.
Blueprint: lmm:van-daele-integrand-integrable -/
theorem vanDaele_integrand_integrable {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} (hl : 0 < l) (a' : H →L[ℂ] H) (ξ η : H) :
    Continuous (fun t : ℝ => (l : ℂ) ^ (2 * (Complex.I * t)) *
        ⟪η, modularUnitaryGroup hM hΩ C hC t
          (modularConjugationConj hM hΩ C hC a'
            (modularUnitaryGroup hM hΩ C hC (-t) ξ))⟫_ℂ /
        ((2 * Real.cosh (Real.pi * t) : ℝ) : ℂ)) ∧
    (∀ t : ℝ, ‖(l : ℂ) ^ (2 * (Complex.I * t)) *
        ⟪η, modularUnitaryGroup hM hΩ C hC t
          (modularConjugationConj hM hΩ C hC a'
            (modularUnitaryGroup hM hΩ C hC (-t) ξ))⟫_ℂ /
        ((2 * Real.cosh (Real.pi * t) : ℝ) : ℂ)‖ ≤
      ‖a'‖ * ‖ξ‖ * ‖η‖ / (2 * Real.cosh (Real.pi * t))) ∧
    MeasureTheory.Integrable (fun t : ℝ => (l : ℂ) ^ (2 * (Complex.I * t)) *
        ⟪η, modularUnitaryGroup hM hΩ C hC t
          (modularConjugationConj hM hΩ C hC a'
            (modularUnitaryGroup hM hΩ C hC (-t) ξ))⟫_ℂ /
        ((2 * Real.cosh (Real.pi * t) : ℝ) : ℂ)) := by
  sorry

/-- `f(z) = λ^{2z} ⟪η, p_{z,n}(Δ) a p_{-z,n}(Δ) ξ⟫` is entire, hence continuous.
Blueprint: lmm:van-daele-strip-function-entire -/
theorem differentiable_vanDaele_strip_function {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n)
    (a : H →L[ℂ] H) (ξ η : H) :
    Differentiable ℂ (fun z : ℂ => (l : ℂ) ^ (2 * z) *
        ⟪η, (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
            p[z, n]
          (a ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
            p[-z, n] ξ))⟫_ℂ) ∧
    Continuous (fun z : ℂ => (l : ℂ) ^ (2 * z) *
        ⟪η, (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
            p[z, n]
          (a ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
            p[-z, n] ξ))⟫_ℂ) := by
  sorry

/-- `|f(z)| ≤ max(λ, λ⁻¹) n ‖a‖ ‖ξ‖ ‖η‖` for `|Re z| ≤ 1/2`.
Blueprint: lmm:van-daele-strip-function-bounded -/
theorem norm_vanDaele_strip_function_le {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n)
    (a : H →L[ℂ] H) (ξ η : H) {z : ℂ} (hz : |z.re| ≤ 1 / 2) :
    ‖(l : ℂ) ^ (2 * z) *
      ⟪η, (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          p[z, n]
        (a ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          p[-z, n] ξ))⟫_ℂ‖ ≤
      max l l⁻¹ * n * ‖a‖ * ‖ξ‖ * ‖η‖ := by
  sorry

/-- If `E_n ξ = ξ` and `E_n η = η`, then `f(0) = ⟪η, a ξ⟫`.
Blueprint: lmm:van-daele-strip-function-zero -/
theorem vanDaele_strip_function_zero {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n)
    (a : H →L[ℂ] H) {ξ η : H}
    (hξ : spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ξ = ξ)
    (hη : spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] η = η) :
    (l : ℂ) ^ (2 * (0 : ℂ)) *
      ⟪η, (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          p[(0 : ℂ), n]
        (a ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          p[-(0 : ℂ), n] ξ))⟫_ℂ =
      ⟪η, a ξ⟫_ℂ := by
  sorry

/-- `⟪η, p_{x+it,n}(Δ) a p_{-(x+it),n}(Δ) ξ⟫ = ⟪p_{x,n}(Δ) Δ^{-it} η, a p_{-x,n}(Δ) Δ^{-it} ξ⟫`.
Blueprint: lmm:van-daele-strip-function-shift -/
theorem inner_modularOperator_indicatorCpow_conj_add_I_mul {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {n : ℕ} (hn : 1 ≤ n)
    (a : H →L[ℂ] H) (ξ η : H) (x t : ℝ) :
    ⟪η, (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        p[(x : ℂ) + Complex.I * t, n]
      (a ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
        p[-((x : ℂ) + Complex.I * t), n] ξ))⟫_ℂ =
      ⟪(spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[(x : ℂ), n]
          (modularUnitaryGroup hM hΩ C hC (-t) η),
        a ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral p[-(x : ℂ), n]
          (modularUnitaryGroup hM hΩ C hC (-t) ξ))⟫_ℂ := by
  sorry

/-- For a van Daele triple `(λ, a′, a)` and `E_n ξ = ξ`, `E_n η = η`,
`f(1/2 + it) + f(-1/2 + it) = λ^{2it} ⟪η, Δ^{it} J a′ J Δ^{-it} ξ⟫`.
Blueprint: lmm:van-daele-strip-function-boundary -/
theorem IsVanDaeleTriple.strip_function_boundary {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} {a' a : H →L[ℂ] H}
    (htriple : IsVanDaeleTriple M Ω C l a' a) {n : ℕ} (hn : 1 ≤ n) {ξ η : H}
    (hξ : spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ξ = ξ)
    (hη : spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] η = η) (t : ℝ) :
    (l : ℂ) ^ (2 * ((1 / 2 : ℂ) + Complex.I * t)) *
      ⟪η, (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          p[((1 / 2 : ℂ) + Complex.I * t), n]
        (a ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
          p[-((1 / 2 : ℂ) + Complex.I * t), n] ξ))⟫_ℂ +
      (l : ℂ) ^ (2 * ((-1 / 2 : ℂ) + Complex.I * t)) *
        ⟪η, (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
            p[((-1 / 2 : ℂ) + Complex.I * t), n]
          (a ((spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC)).integral
            p[-((-1 / 2 : ℂ) + Complex.I * t), n] ξ))⟫_ℂ =
      (l : ℂ) ^ (2 * (Complex.I * t)) *
        ⟪η, modularUnitaryGroup hM hΩ C hC t
          (modularConjugationConj hM hΩ C hC a'
            (modularUnitaryGroup hM hΩ C hC (-t) ξ))⟫_ℂ := by
  sorry

/-- For a van Daele triple `(λ, a′, a)` and `E_n ξ = ξ`, `E_n η = η`,
`⟪η, a ξ⟫ = ∫ λ^{2it} ⟪η, Δ^{it} J a′ J Δ^{-it} ξ⟫ / (2 cosh πt) dt`.
Blueprint: prpstn:van-daele-integral-formula-H0 -/
theorem IsVanDaeleTriple.inner_eq_integral_of_spectral {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} {a' a : H →L[ℂ] H}
    (htriple : IsVanDaeleTriple M Ω C l a' a) {n : ℕ} (hn : 1 ≤ n) {ξ η : H}
    (hξ : spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ξ = ξ)
    (hη : spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] η = η) :
    ⟪η, a ξ⟫_ℂ = ∫ t : ℝ, (l : ℂ) ^ (2 * (Complex.I * t)) *
        ⟪η, modularUnitaryGroup hM hΩ C hC t
          (modularConjugationConj hM hΩ C hC a'
            (modularUnitaryGroup hM hΩ C hC (-t) ξ))⟫_ℂ /
        ((2 * Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
  sorry

/-- If `ξ_m → ξ` and `η_m → η`, then `λ^{2it} ⟪η_m, Δ^{it} J a′ J Δ^{-it} ξ_m⟫ / (2 cosh πt)`
converges to the same expression for `ξ, η`.
Blueprint: lmm:van-daele-integrand-vector-limit -/
theorem tendsto_vanDaele_integrand {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} (hl : 0 < l) (a' : H →L[ℂ] H) (t : ℝ)
    {ξs ηs : ℕ → H} {ξ η : H} (hξ : Tendsto ξs atTop (𝓝 ξ)) (hη : Tendsto ηs atTop (𝓝 η)) :
    Tendsto (fun m : ℕ => (l : ℂ) ^ (2 * (Complex.I * t)) *
          ⟪ηs m, modularUnitaryGroup hM hΩ C hC t
            (modularConjugationConj hM hΩ C hC a'
              (modularUnitaryGroup hM hΩ C hC (-t) (ξs m)))⟫_ℂ /
          ((2 * Real.cosh (Real.pi * t) : ℝ) : ℂ))
      atTop (𝓝 ((l : ℂ) ^ (2 * (Complex.I * t)) *
          ⟪η, modularUnitaryGroup hM hΩ C hC t
            (modularConjugationConj hM hΩ C hC a'
              (modularUnitaryGroup hM hΩ C hC (-t) ξ))⟫_ℂ /
          ((2 * Real.cosh (Real.pi * t) : ℝ) : ℂ))) := by
  sorry

/-- If `ξ_m → ξ`, `η_m → η` and `‖ξ_m‖ ‖η_m‖ ≤ K`, then
`∫ λ^{2it} ⟪η_m, Δ^{it} J a′ J Δ^{-it} ξ_m⟫ / (2 cosh πt) dt` converges to the same integral for
`ξ, η`.
Blueprint: lmm:van-daele-integral-continuity -/
theorem tendsto_vanDaele_integral {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} (hl : 0 < l) (a' : H →L[ℂ] H)
    {ξs ηs : ℕ → H} {ξ η : H} (hξ : Tendsto ξs atTop (𝓝 ξ)) (hη : Tendsto ηs atTop (𝓝 η))
    {K : ℝ} (hK : ∀ m, ‖ξs m‖ * ‖ηs m‖ ≤ K) :
    Tendsto (fun m : ℕ => ∫ t : ℝ, (l : ℂ) ^ (2 * (Complex.I * t)) *
          ⟪ηs m, modularUnitaryGroup hM hΩ C hC t
            (modularConjugationConj hM hΩ C hC a'
              (modularUnitaryGroup hM hΩ C hC (-t) (ξs m)))⟫_ℂ /
          ((2 * Real.cosh (Real.pi * t) : ℝ) : ℂ))
      atTop (𝓝 (∫ t : ℝ, (l : ℂ) ^ (2 * (Complex.I * t)) *
          ⟪η, modularUnitaryGroup hM hΩ C hC t
            (modularConjugationConj hM hΩ C hC a'
              (modularUnitaryGroup hM hΩ C hC (-t) ξ))⟫_ℂ /
          ((2 * Real.cosh (Real.pi * t) : ℝ) : ℂ))) := by
  sorry

/-- `ψ_m = E_{m+1} ψ` satisfies `E_{m+1} ψ_m = ψ_m` and `‖ψ_m‖ ≤ ‖ψ‖`, and `ψ_m → ψ`.
Blueprint: lmm:modular-spectral-approximants -/
theorem modularSpectralProjection_approximants {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (ψ : H) :
    (∀ m : ℕ, spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[(m + 1 : ℕ)]
        (spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[(m + 1 : ℕ)] ψ) =
        spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[(m + 1 : ℕ)] ψ ∧
      ‖spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[(m + 1 : ℕ)] ψ‖ ≤ ‖ψ‖) ∧
    Tendsto
      (fun m : ℕ => spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[(m + 1 : ℕ)] ψ)
      atTop (𝓝 ψ) := by
  sorry

/-- For a van Daele triple `(λ, a′, a)` and all `ξ, η`,
`⟪η, a ξ⟫ = ∫ λ^{2it} ⟪η, Δ^{it} J a′ J Δ^{-it} ξ⟫ / (2 cosh πt) dt`.
Blueprint: prpstn:van-daele-integral-formula -/
theorem IsVanDaeleTriple.inner_eq_integral {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} {a' a : H →L[ℂ] H}
    (htriple : IsVanDaeleTriple M Ω C l a' a) (ξ η : H) :
    ⟪η, a ξ⟫_ℂ = ∫ t : ℝ, (l : ℂ) ^ (2 * (Complex.I * t)) *
        ⟪η, modularUnitaryGroup hM hΩ C hC t
          (modularConjugationConj hM hΩ C hC a'
            (modularUnitaryGroup hM hΩ C hC (-t) ξ))⟫_ℂ /
        ((2 * Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
  sorry

/-- `h(t) = ⟪η, (Δ^{it} J a′ J Δ^{-it} b′ - b′ Δ^{it} J a′ J Δ^{-it}) ξ⟫ / (2 cosh πt)` equals
`(⟪η, Δ^{it} J a′ J Δ^{-it} b′ ξ⟫ - ⟪b′* η, Δ^{it} J a′ J Δ^{-it} ξ⟫) / (2 cosh πt)`, and is
continuous and integrable.
Blueprint: lmm:van-daele-commutator-integrand -/
theorem vanDaele_commutator_integrand {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (a' b' : H →L[ℂ] H) (ξ η : H) :
    (∀ t : ℝ, ⟪η, modularUnitaryGroup hM hΩ C hC t
          (modularConjugationConj hM hΩ C hC a'
            (modularUnitaryGroup hM hΩ C hC (-t) (b' ξ))) -
        b' (modularUnitaryGroup hM hΩ C hC t
          (modularConjugationConj hM hΩ C hC a'
            (modularUnitaryGroup hM hΩ C hC (-t) ξ)))⟫_ℂ /
        ((2 * Real.cosh (Real.pi * t) : ℝ) : ℂ) =
      (⟪η, modularUnitaryGroup hM hΩ C hC t
          (modularConjugationConj hM hΩ C hC a'
            (modularUnitaryGroup hM hΩ C hC (-t) (b' ξ)))⟫_ℂ -
        ⟪star b' η, modularUnitaryGroup hM hΩ C hC t
          (modularConjugationConj hM hΩ C hC a'
            (modularUnitaryGroup hM hΩ C hC (-t) ξ))⟫_ℂ) /
        ((2 * Real.cosh (Real.pi * t) : ℝ) : ℂ)) ∧
    Continuous (fun t : ℝ => ⟪η, modularUnitaryGroup hM hΩ C hC t
            (modularConjugationConj hM hΩ C hC a'
              (modularUnitaryGroup hM hΩ C hC (-t) (b' ξ))) -
          b' (modularUnitaryGroup hM hΩ C hC t
            (modularConjugationConj hM hΩ C hC a'
              (modularUnitaryGroup hM hΩ C hC (-t) ξ)))⟫_ℂ /
          ((2 * Real.cosh (Real.pi * t) : ℝ) : ℂ)) ∧
    MeasureTheory.Integrable (fun t : ℝ => ⟪η, modularUnitaryGroup hM hΩ C hC t
            (modularConjugationConj hM hΩ C hC a'
              (modularUnitaryGroup hM hΩ C hC (-t) (b' ξ))) -
          b' (modularUnitaryGroup hM hΩ C hC t
            (modularConjugationConj hM hΩ C hC a'
              (modularUnitaryGroup hM hΩ C hC (-t) ξ)))⟫_ℂ /
          ((2 * Real.cosh (Real.pi * t) : ℝ) : ℂ)) := by
  sorry

/-- For a van Daele triple `(λ, a′, a)` and `b′ ∈ M′`, `∫ λ^{2it} h(t) dt = 0`.
Blueprint: lmm:van-daele-commutator-integral-zero -/
theorem IsVanDaeleTriple.integral_commutator_eq_zero {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {l : ℝ} {a' a : H →L[ℂ] H}
    (htriple : IsVanDaeleTriple M Ω C l a' a) {b' : H →L[ℂ] H} (hb' : b' ∈ Set.centralizer M)
    (ξ η : H) :
    ∫ t : ℝ, (l : ℂ) ^ (2 * (Complex.I * t)) *
      (⟪η, modularUnitaryGroup hM hΩ C hC t
            (modularConjugationConj hM hΩ C hC a'
              (modularUnitaryGroup hM hΩ C hC (-t) (b' ξ))) -
          b' (modularUnitaryGroup hM hΩ C hC t
            (modularConjugationConj hM hΩ C hC a'
              (modularUnitaryGroup hM hΩ C hC (-t) ξ)))⟫_ℂ /
          ((2 * Real.cosh (Real.pi * t) : ℝ) : ℂ)) = 0 := by
  sorry

/-- For `a′, b′ ∈ M′` and every `θ`, `∫ e^{iθt} h(t) dt = 0`.
Blueprint: lmm:van-daele-commutator-fourier -/
theorem integral_exp_mul_vanDaele_commutator_eq_zero {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {a' b' : H →L[ℂ] H} (ha' : a' ∈ Set.centralizer M)
    (hb' : b' ∈ Set.centralizer M) (ξ η : H) (θ : ℝ) :
    ∫ t : ℝ, Complex.exp (Complex.I * θ * t) *
      (⟪η, modularUnitaryGroup hM hΩ C hC t
            (modularConjugationConj hM hΩ C hC a'
              (modularUnitaryGroup hM hΩ C hC (-t) (b' ξ))) -
          b' (modularUnitaryGroup hM hΩ C hC t
            (modularConjugationConj hM hΩ C hC a'
              (modularUnitaryGroup hM hΩ C hC (-t) ξ)))⟫_ℂ /
          ((2 * Real.cosh (Real.pi * t) : ℝ) : ℂ)) = 0 := by
  sorry

/-- For `a′, b′ ∈ M′`, `Δ^{it} J a′ J Δ^{-it}` commutes with `b′`.
Blueprint: lmm:van-daele-conjugate-commutes -/
theorem modularUnitaryGroup_conj_commute {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {a' b' : H →L[ℂ] H} (ha' : a' ∈ Set.centralizer M)
    (hb' : b' ∈ Set.centralizer M) (t : ℝ) :
    ((modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap ∘L
      modularConjugationConj hM hΩ C hC a' ∘L
      (modularUnitaryGroup hM hΩ C hC (-t)).toLinearIsometry.toContinuousLinearMap) * b' =
      b' * ((modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap ∘L
        modularConjugationConj hM hΩ C hC a' ∘L
        (modularUnitaryGroup hM hΩ C hC (-t)).toLinearIsometry.toContinuousLinearMap) := by
  sorry

/-- For `a′ ∈ M′`, `Δ^{it} J a′ J Δ^{-it} ∈ M`; in particular `J a′ J ∈ M`.
Blueprint: lmm:van-daele-conjugate-in-algebra -/
theorem modularUnitaryGroup_conj_mem {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {a' : H →L[ℂ] H} (ha' : a' ∈ Set.centralizer M) (t : ℝ) :
    ((modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap ∘L
      modularConjugationConj hM hΩ C hC a' ∘L
      (modularUnitaryGroup hM hΩ C hC (-t)).toLinearIsometry.toContinuousLinearMap) ∈ M ∧
      modularConjugationConj hM hΩ C hC a' ∈ M := by
  sorry

/-- For `x ∈ M`, `J x J ∈ M′`.
Blueprint: crllr:van-daele-algebra-conjugate -/
theorem modularConjugationConj_mem_centralizer {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {x : H →L[ℂ] H} (hx : x ∈ M) :
    modularConjugationConj hM hΩ C hC x ∈ Set.centralizer M := by
  sorry

/-- `{J x J | x ∈ M} = M′`.
Blueprint: lmm:tomita-modular-conjugation-commutant -/
theorem modularConjugationConj_image {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    (fun x => modularConjugationConj hM hΩ C hC x) '' M = Set.centralizer M := by
  sorry

/-- For every `s` and `x ∈ M`, `Δ^{is} x Δ^{-is} ∈ M`.
Blueprint: lmm:tomita-modular-automorphism-subset -/
theorem modularUnitaryGroup_conj_mem_of_mem {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (s : ℝ) {x : H →L[ℂ] H} (hx : x ∈ M) :
    ((modularUnitaryGroup hM hΩ C hC s).toLinearIsometry.toContinuousLinearMap ∘L
      x ∘L (modularUnitaryGroup hM hΩ C hC (-s)).toLinearIsometry.toContinuousLinearMap) ∈ M := by
  sorry

/-- For every `t`, `{Δ^{it} x Δ^{-it} | x ∈ M} = M`.
Blueprint: lmm:tomita-modular-automorphism -/
theorem modularUnitaryGroup_conj_image {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (t : ℝ) :
    (fun x => (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap ∘L
        x ∘L (modularUnitaryGroup hM hΩ C hC (-t)).toLinearIsometry.toContinuousLinearMap) '' M =
      M := by
  sorry

/-- Tomita's theorem: `J M J = M′` and `Δ^{it} M Δ^{-it} = M` for every real `t`.
Blueprint: thrm:tomita -/
theorem tomita_theorem {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    (fun x => modularConjugationConj hM hΩ C hC x) '' M = Set.centralizer M ∧
      ∀ t : ℝ,
        (fun x => (modularUnitaryGroup hM hΩ C hC t).toLinearIsometry.toContinuousLinearMap ∘L
          x ∘L (modularUnitaryGroup hM hΩ C hC (-t)).toLinearIsometry.toContinuousLinearMap) '' M =
          M := by
  sorry

end Physicslib4.Modular
