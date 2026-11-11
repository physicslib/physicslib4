/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Unbounded.Polar

/-!
# Operators commuting with a unitary, and bounded approximants of a closed operator

This file states the general operator-theory lemmas behind van Daele's proof that the antilinear
adjoint of the Tomita operator is the closure of `F₀`.

* A unitary `U` *commutes with* a partial linear map `A` (`UnitaryCommutes U A`) when `U` and
  `U⁻¹` map `Dom A` into `Dom A` and commute with `A` there. The double conjugate
  `(UC)(CAC⁻¹)(UC)⁻¹` is `antiunitaryConj (C.trans U) (antiunitaryConj C A)`.
* For a closed, densely defined `c` with `D = c†c`, the bounded approximants are
  `R_n = h_n(D)` and `K_n = k_n(D)` with `h_n(λ) = n / (n + √λ)` and `k_n(λ) = √λ · h_n(λ)`,
  written inline through `functionalCalculus`.
* The square of a function of a self-adjoint operator, the product `A^{-1/2} A^{-1/2} = A⁻¹`, and
  the square root of `A⁻¹`.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace LinearPMap
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
A unitary `U` commutes with `A` when `U` and `U⁻¹` map `Dom A` into `Dom A` and commute with `A`
there.

Blueprint: def:unitary-commutes
-/
def UnitaryCommutes (U : H ≃ₗᵢ[ℂ] H) (A : H →ₗ.[ℂ] H) : Prop :=
  (∀ x (hx : x ∈ A.domain), ∃ h : U x ∈ A.domain, A ⟨U x, h⟩ = U (A ⟨x, hx⟩)) ∧
    ∀ x (hx : x ∈ A.domain), ∃ h : U.symm x ∈ A.domain, A ⟨U.symm x, h⟩ = U.symm (A ⟨x, hx⟩)

/-!
### Operators commuting with a unitary
-/

/--
If the unitary `U` commutes with `A`, then `(UC)(CAC⁻¹)(UC)⁻¹ = A`, including domains.

Blueprint: lmm:commuting-unitary-double-conjugate
-/
theorem antiunitaryConj_trans_antiunitaryConj_of_commute (U : H ≃ₗᵢ[ℂ] H) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) {A : H →ₗ.[ℂ] H}
    (hU : UnitaryCommutes U A) :
    antiunitaryConj (C.trans U) (antiunitaryConj C A) = A := by
  sorry

/--
If `A` is self-adjoint and the unitary `U` commutes with `A`, then
`(UC)(C f(A) C⁻¹)(UC)⁻¹ = f(A)`, including domains, for every real measurable `f`.

Blueprint: lmm:unitary-conjugate-functional-calculus
-/
theorem antiunitaryConj_trans_functionalCalculus_of_commute (U : H ≃ₗᵢ[ℂ] H)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x) {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hU : UnitaryCommutes U A)
    {f : ℝ → ℝ} (hf : Measurable f) :
    antiunitaryConj (C.trans U) (antiunitaryConj C (functionalCalculus hA fun x => (f x : ℂ))) =
      functionalCalculus hA fun x => (f x : ℂ) := by
  sorry

/--
If `V⁻¹` maps `Dom c` into `Dom c` with `c V⁻¹ = V⁻¹ c`, then `V` maps `Dom c†` into `Dom c†`
with `c† V = V c†`.

Blueprint: lmm:commuting-unitary-adjoint-half
-/
theorem adjoint_commute_of_symm_commute {c : H →ₗ.[ℂ] H} (hc : HasDenseDomain c)
    (V : H ≃ₗᵢ[ℂ] H)
    (hV : ∀ x (hx : x ∈ c.domain),
      ∃ h : V.symm x ∈ c.domain, c ⟨V.symm x, h⟩ = V.symm (c ⟨x, hx⟩)) :
    ∀ x (hx : x ∈ c†.domain), ∃ h : V x ∈ c†.domain, c† ⟨V x, h⟩ = V (c† ⟨x, hx⟩) := by
  sorry

/--
If the unitary `U` commutes with a densely defined `c`, then `U` commutes with `c†`.

Blueprint: lmm:commuting-unitary-adjoint
-/
theorem adjoint_commute_of_commute {c : H →ₗ.[ℂ] H} (hc : HasDenseDomain c) (U : H ≃ₗᵢ[ℂ] H)
    (hU : UnitaryCommutes U c) :
    UnitaryCommutes U c† := by
  sorry

/--
If the unitary `U` commutes with a densely defined `c`, then `U` commutes with `c†c`.

Blueprint: lmm:commuting-unitary-adjoint-product
-/
theorem adjointMulSelf_commute_of_commute {c : H →ₗ.[ℂ] H} (hc : HasDenseDomain c)
    (U : H ≃ₗᵢ[ℂ] H)
    (hU : UnitaryCommutes U c) :
    UnitaryCommutes U (adjointMulSelf c) := by
  sorry

/--
If the unitary `U` commutes with a closed, densely defined `c` and `D = c†c`, then
`U f(D) = f(D) U` for every bounded real measurable `f`.

Blueprint: lmm:commuting-unitary-bounded-function
-/
theorem functionalCalculus_adjointMulSelf_commute_of_commute {c : H →ₗ.[ℂ] H}
    (hc : HasDenseDomain c) (hcl : c.IsClosed) (U : H ≃ₗᵢ[ℂ] H)
    (hU : UnitaryCommutes U c)
    {f : ℝ → ℝ} (hf : (fun x => (f x : ℂ)) ∈ BddMeasurable ℝ) :
    ∀ ψ : (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1 fun x => (f x : ℂ)).domain,
      ∃ h : U ψ ∈
          (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1 fun x => (f x : ℂ)).domain,
        functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1 (fun x => (f x : ℂ))
            ⟨U ψ, h⟩ =
          U (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
            (fun x => (f x : ℂ)) ψ) := by
  sorry

/-!
### Bounded approximants of a closed operator

For a closed, densely defined `c`, `D = c†c`, `h_n(λ) = n / (n + √λ)`, `k_n(λ) = √λ · h_n(λ)`,
`R_n = h_n(D)` and `K_n = k_n(D)`.
-/

/--
For `n ≥ 1`, `h_n` and `k_n` are continuous and measurable, `0 < h_n ≤ 1`, `0 ≤ k_n ≤ n` and
`k_n ≤ √·`; pointwise, `h_n → 1` and `k_n → √·` as `n → ∞`.

Blueprint: lmm:approximant-functions
-/
theorem approximant_functions :
    (∀ n : ℕ, 1 ≤ n →
      Continuous (fun x : ℝ => (n / (n + Real.sqrt x) : ℝ)) ∧
      Measurable (fun x : ℝ => (n / (n + Real.sqrt x) : ℝ)) ∧
      Continuous (fun x : ℝ => (Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ)) ∧
      Measurable (fun x : ℝ => (Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ)) ∧
      ∀ x : ℝ, 0 < (n / (n + Real.sqrt x) : ℝ) ∧ (n / (n + Real.sqrt x) : ℝ) ≤ 1 ∧
        0 ≤ Real.sqrt x * (n / (n + Real.sqrt x)) ∧
        Real.sqrt x * (n / (n + Real.sqrt x)) ≤ n ∧
        Real.sqrt x * (n / (n + Real.sqrt x)) ≤ Real.sqrt x) ∧
    ∀ x : ℝ, Tendsto (fun n : ℕ => (n / (n + Real.sqrt x) : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => (Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ)) atTop
        (𝓝 (Real.sqrt x)) := by
  sorry

/--
For `n ≥ 1`, `R_n` and `K_n` are defined on all of `H`, `R_n` is self-adjoint, `‖R_n‖ ≤ 1` and
`‖K_n‖ ≤ n`.

Blueprint: lmm:approximant-bounded
-/
theorem approximant_bounded {c : H →ₗ.[ℂ] H} (hc : HasDenseDomain c) (hcl : c.IsClosed)
    (n : ℕ) (hn : 1 ≤ n) :
    (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        fun x => ((n / (n + Real.sqrt x) : ℝ) : ℂ)).domain = ⊤ ∧
    (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        fun x => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ)).domain = ⊤ ∧
    IsSelfAdjoint (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        fun x => ((n / (n + Real.sqrt x) : ℝ) : ℂ)) ∧
    (∀ ψ : (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        fun x => ((n / (n + Real.sqrt x) : ℝ) : ℂ)).domain,
      ‖functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        (fun x => ((n / (n + Real.sqrt x) : ℝ) : ℂ)) ψ‖ ≤ ‖(ψ : H)‖) ∧
    ∀ ψ : (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        fun x => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ)).domain,
      ‖functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        (fun x => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ)) ψ‖ ≤ n * ‖(ψ : H)‖ := by
  sorry

/--
For `n ≥ 1` and `ψ ∈ H`, `R_n ψ ∈ Dom |c| = Dom c`, `|c| R_n ψ = K_n ψ` and
`‖c R_n ψ‖ = ‖K_n ψ‖ ≤ n ‖ψ‖`.

Blueprint: lmm:approximant-range
-/
theorem approximant_range {c : H →ₗ.[ℂ] H} (hc : HasDenseDomain c) (hcl : c.IsClosed)
    (n : ℕ) (hn : 1 ≤ n) (ψ : H) :
    ∃ hR : ψ ∈ (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        fun x => ((n / (n + Real.sqrt x) : ℝ) : ℂ)).domain,
    ∃ hK : ψ ∈ (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        fun x => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ)).domain,
    ∃ h₁ : functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        (fun x => ((n / (n + Real.sqrt x) : ℝ) : ℂ)) ⟨ψ, hR⟩ ∈ (absoluteValue c hc hcl).domain,
    ∃ h₂ : functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        (fun x => ((n / (n + Real.sqrt x) : ℝ) : ℂ)) ⟨ψ, hR⟩ ∈ c.domain,
      absoluteValue c hc hcl ⟨_, h₁⟩ =
          functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
            (fun x => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ)) ⟨ψ, hK⟩ ∧
        ‖c ⟨_, h₂⟩‖ = ‖functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
            (fun x => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ)) ⟨ψ, hK⟩‖ ∧
        ‖functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
            (fun x => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ)) ⟨ψ, hK⟩‖ ≤
          n * ‖ψ‖ := by
  sorry

/--
`R_n φ → φ` for every `φ ∈ H`, and `K_n ψ → |c| ψ` for every `ψ ∈ Dom c`, as `n → ∞`.

Blueprint: lmm:approximant-convergence
-/
theorem approximant_convergence {c : H →ₗ.[ℂ] H} (hc : HasDenseDomain c) (hcl : c.IsClosed) :
    (∀ φ : H, ∃ hR : ∀ n : ℕ, φ ∈ (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        fun x => ((n / (n + Real.sqrt x) : ℝ) : ℂ)).domain,
      Tendsto (fun n : ℕ => functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        (fun x => ((n / (n + Real.sqrt x) : ℝ) : ℂ)) ⟨φ, hR n⟩) atTop (𝓝 φ)) ∧
    ∀ ψ (hψ : ψ ∈ c.domain),
      ∃ hK : ∀ n : ℕ, ψ ∈ (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
          fun x => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ)).domain,
      ∃ h : ψ ∈ (absoluteValue c hc hcl).domain,
        Tendsto (fun n : ℕ => functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
            (fun x => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ)) ⟨ψ, hK n⟩) atTop
          (𝓝 (absoluteValue c hc hcl ⟨ψ, h⟩)) := by
  sorry

/--
For `n ≥ 1` there is a unique bounded `x_n` with `x_n ψ = c R_n ψ` for every `ψ`; it has
`‖x_n‖ ≤ n` and `x_n† φ = R_n c† φ` for every `φ ∈ Dom c†`.

Blueprint: lmm:approximant-operator
-/
theorem approximant_operator {c : H →ₗ.[ℂ] H} (hc : HasDenseDomain c) (hcl : c.IsClosed)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ x : H →L[ℂ] H,
      (∀ ψ : (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
          fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)).domain,
        ∃ h : functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
            (fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)) ψ ∈ c.domain,
          x ψ = c ⟨_, h⟩) ∧
      (∀ y : H →L[ℂ] H,
        (∀ ψ : (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
            fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)).domain,
          ∃ h : functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
              (fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)) ψ ∈ c.domain,
            y ψ = c ⟨_, h⟩) → y = x) ∧
      ‖x‖ ≤ n ∧
      ∀ φ : c†.domain,
        ∃ h : c† φ ∈ (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
            fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)).domain,
          ContinuousLinearMap.adjoint x φ =
            functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
              (fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)) ⟨_, h⟩ := by
  sorry

/--
If the unitary `U` commutes with `c`, then `U x_n = x_n U`, where `x_n` is the bounded operator
with `x_n ψ = c R_n ψ`.

Blueprint: lmm:approximant-operator-commutes
-/
theorem approximant_operator_commute {c : H →ₗ.[ℂ] H} (hc : HasDenseDomain c)
    (hcl : c.IsClosed) (U : H ≃ₗᵢ[ℂ] H)
    (hU : UnitaryCommutes U c)
    (n : ℕ) (hn : 1 ≤ n) (x : H →L[ℂ] H)
    (hx : ∀ ψ : (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
        fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)).domain,
      ∃ h : functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
          (fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)) ψ ∈ c.domain,
        x ψ = c ⟨_, h⟩) :
    ∀ ψ : H, U (x ψ) = x (U ψ) := by
  sorry

/-!
### Squares, inverse square roots and the square root of the inverse
-/

/--
For a self-adjoint `A` and a measurable real `f`, `W_{f²} ⊆ W_f` and `f(A) f(A) = (f²)(A)`,
including domains.

Blueprint: lmm:fc-domain-square
-/
theorem pmapMul_functionalCalculus_self {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {f : ℝ → ℝ}
    (hf : Measurable f) :
    integralDomain (spectralMeasure hA) (fun x => ((f x ^ 2 : ℝ) : ℂ)) ≤
        integralDomain (spectralMeasure hA) (fun x => (f x : ℂ)) ∧
      pmapMul (functionalCalculus hA fun x => (f x : ℂ))
          (functionalCalculus hA fun x => (f x : ℂ)) =
        functionalCalculus hA fun x => ((f x ^ 2 : ℝ) : ℂ) := by
  sorry

/--
For a positive, self-adjoint, injective `A`, `A^{-1/2} A^{-1/2} = A⁻¹`, including domains.

Blueprint: lmm:inverse-square-root-product
-/
theorem pmapMul_inv_sqrt_functionalCalculus {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hpos : IsPositive A) (hinj : ker A = ⊥) :
    pmapMul (functionalCalculus hA fun x => (((Real.sqrt x)⁻¹ : ℝ) : ℂ))
        (functionalCalculus hA fun x => (((Real.sqrt x)⁻¹ : ℝ) : ℂ)) =
      A.inverse := by
  sorry

/--
For a positive, self-adjoint, injective `A`, `A⁻¹` is self-adjoint and
`(A⁻¹)^{1/2} = s(A⁻¹) = A^{-1/2}`.

Blueprint: lmm:sqrt-of-inverse
-/
theorem sqrt_functionalCalculus_inverse {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hpos : IsPositive A) (hinj : ker A = ⊥) :
    ∃ h : IsSelfAdjoint A.inverse,
      functionalCalculus h (fun x => ((Real.sqrt x : ℝ) : ℂ)) =
        functionalCalculus hA fun x => (((Real.sqrt x)⁻¹ : ℝ) : ℂ) := by
  sorry

end Unbounded
end Spectral
end Physicslib4
