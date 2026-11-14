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
  sorry

/-- `1_{(0, ∞)}(Δ) = 𝟙`.
Blueprint: lmm:modular-indicator-positive-one -/
theorem modularOperator_functionalCalculus_indicator_Ioi {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC) ((Set.Ioi (0 : ℝ)).indicator 1) =
      (LinearMap.id : H →ₗ[ℂ] H).toPMap ⊤ := by
  sorry

/-- `log Δ = ℓ(Δ)`, with `ℓ = Real.log`, is self-adjoint.
Blueprint: lmm:modular-log-self-adjoint -/
theorem isSelfAdjoint_modularOperator_log {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    IsSelfAdjoint (functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC)
      fun x => (Real.log x : ℂ)) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- `E_n ψ → ψ` as `n → ∞`, for every `ψ`.
Blueprint: lmm:modular-spectral-projections-converge -/
theorem tendsto_modularSpectralProjection {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (ψ : H) :
    Tendsto (fun n : ℕ => spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ψ)
      atTop (𝓝 ψ) := by
  sorry

/-- `H₀ = {ξ | E_n ξ = ξ for some n ≥ 1}` is dense in `H`.
Blueprint: lmm:modular-H0-dense -/
theorem dense_modularSpectralSubspace {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    Dense {ξ : H | ∃ n : ℕ, 1 ≤ n ∧
      spectralMeasure (modularOperator_isSelfAdjoint hM hΩ C hC) K[n] ξ = ξ} := by
  sorry

/-! ### The functions `p_{z,n}`, `q_{z,n}` and `e_t` -/

/-- For `n ≥ 1` and `λ ∈ K_n`, `λ > 0` and `|log λ| ≤ log n`.
Blueprint: lmm:log-power-on-interval -/
theorem pos_abs_log_le_of_mem_Icc {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ K[n]) :
    0 < x ∧ |Real.log x| ≤ Real.log n := by
  sorry

/-- For `n ≥ 1`, `λ ∈ K_n` and `z ∈ ℂ`, `λ^z = exp(z log λ)` and `|λ^z| ≤ n^{|Re z|}`.
Blueprint: lmm:cpow-on-interval -/
theorem cpow_of_mem_Icc {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ K[n]) (z : ℂ) :
    (x : ℂ) ^ z = Complex.exp (z * Real.log x) ∧ ‖(x : ℂ) ^ z‖ ≤ (n : ℝ) ^ |z.re| := by
  sorry

/-- `p_{z,n}` and `q_{z,n}` are measurable, `|p_{z,n}| ≤ n^{|Re z|}` and
`|q_{z,n}| ≤ (log n) n^{|Re z|}`.
Blueprint: lmm:modular-power-function-bounds -/
theorem indicatorCpow_bounds {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    Measurable p[z, n] ∧ Measurable q[z, n] ∧
      ∀ x : ℝ, ‖p[z, n] x‖ ≤ (n : ℝ) ^ |z.re| ∧
        ‖q[z, n] x‖ ≤ Real.log n * (n : ℝ) ^ |z.re| := by
  sorry

/-- `p_{z,n} p_{w,n} = p_{z+w,n}` pointwise, and `p_{0,n} = 1_{K_n}`.
Blueprint: lmm:modular-power-function-identities -/
theorem indicatorCpow_mul {n : ℕ} (hn : 1 ≤ n) (z w : ℂ) :
    (∀ x : ℝ, p[z, n] x * p[w, n] x = p[z + w, n] x) ∧
      p[0, n] = (K[n]).indicator 1 := by
  sorry

/-- `conj (p_{z,n}(λ)) = p_{conj z,n}(λ)`.
Blueprint: lmm:modular-power-function-conj -/
theorem indicatorCpow_conj {n : ℕ} (hn : 1 ≤ n) (z : ℂ) (x : ℝ) :
    conj (p[z, n] x) = p[conj z, n] x := by
  sorry

/-- `p_{z+it,n}(λ) = e_t(λ) p_{z,n}(λ)`.
Blueprint: lmm:modular-power-function-shift -/
theorem indicatorCpow_add_I_mul {n : ℕ} (hn : 1 ≤ n) (z : ℂ) (t x : ℝ) :
    p[z + Complex.I * t, n] x = e[t] x * p[z, n] x := by
  sorry

/-- For `1 ≤ n ≤ m`, `p_{z,m}(λ) 1_{K_n}(λ) = p_{z,n}(λ)`.
Blueprint: lmm:modular-power-function-restrict -/
theorem indicatorCpow_mul_indicator {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) (z : ℂ) (x : ℝ) :
    p[z, m] x * (K[n]).indicator 1 x = p[z, n] x := by
  sorry

/-- For `|h| log n ≤ 1`, `|p_{z+h,n}(λ) - p_{z,n}(λ) - h q_{z,n}(λ)| ≤ n^{|Re z|} (log n)² |h|²`.
Blueprint: lmm:modular-power-taylor -/
theorem indicatorCpow_taylor {n : ℕ} (hn : 1 ≤ n) (z h : ℂ) (hh : ‖h‖ * Real.log n ≤ 1)
    (x : ℝ) :
    ‖p[z + h, n] x - p[z, n] x - h * q[z, n] x‖ ≤
      (n : ℝ) ^ |z.re| * Real.log n ^ 2 * ‖h‖ ^ 2 := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- `conj (p_{z,n}(ι⁻(λ))) = p_{-conj z,n}(λ)`.
Blueprint: lmm:modular-inverse-power-function -/
theorem conj_indicatorCpow_inv {n : ℕ} (hn : 1 ≤ n) (z : ℂ) (x : ℝ) :
    conj (p[z, n] x⁻¹) = p[-conj z, n] x := by
  sorry

/-- `conj (e_t(ι⁻(λ))) = e_t(λ)`.
Blueprint: lmm:modular-inverse-unitary-function -/
theorem conj_exp_log_inv (t x : ℝ) :
    conj (e[t] x⁻¹) = e[t] x := by
  sorry

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

end Physicslib4.Modular
