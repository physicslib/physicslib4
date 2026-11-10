/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Operators.Modular.Tomita
import Physicslib4.Spectral.Unbounded.Polar

/-!
# The modular operator and the modular conjugation

For a von Neumann algebra `M` with a cyclic and separating vector `Ω` and a reference
conjugation `C` (an antiunitary involution), let `S′` be the closure of the linearized Tomita
pre-operator and `S = C S′` the Tomita operator. This file defines the modular operator
`Δ = S′† S′`, its square root `Δ^{1/2} = |S′|`, its inverse square root `Δ^{-1/2}`, and the modular
conjugation `J = C V`, where `V` is the unitary of the polar decomposition `S′ = V |S′|`. It
states the properties of `Δ` and `J`, their independence of `C`, the relations `S = J Δ^{1/2}`
and `S⁻¹ = S`, and the identities `J² = 1`, `J Δ^{1/2} J = Δ^{-1/2}` and `J Δ J = Δ⁻¹`.

The Tomita operator `tomitaOperator M Ω C` is antilinear and is a function on the domain of `S′`,
not a `LinearPMap`; statements about it are pointwise.
-/

namespace Physicslib4.Modular

open scoped InnerProductSpace
open Physicslib4.Spectral.Unbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
The hypotheses of the polar decomposition for `S′`: it is closed and densely defined, its kernel
is `{0}` and its range is dense, in the forms used by `Polar.lean`.

Blueprint: def:modular-conjugation
-/
theorem linearizedTomita_closure_polar_hyps {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    HasDenseDomain (linearizedTomitaPre M Ω C).closure ∧
      (linearizedTomitaPre M Ω C).closure.IsClosed ∧
      ker (linearizedTomitaPre M Ω C).closure = ⊥ ∧
      Dense (range (linearizedTomitaPre M Ω C).closure : Set H) := by
  obtain ⟨hcl, hD, hinj, hR⟩ := linearizedTomita_closure_properties hM hΩ C hC
  refine ⟨hD, hcl, (Submodule.eq_bot_iff _).mpr fun x hx => ?_, ?_⟩
  · obtain ⟨h, h0⟩ := mem_ker.mp hx
    have := @hinj ⟨x, h⟩ 0 (by rw [h0, LinearPMap.map_zero])
    exact congrArg Subtype.val this
  · rw [range, LinearMap.coe_range]
    exact hR

/--
The modular operator `Δ = S′† S′` of `(M, Ω)`, where `S′` is the closure of the linearized
Tomita pre-operator. Its square root `s(Δ)` is `modularOperatorSqrt`, which is `|S′|` by
definition of `absoluteValue`.

Blueprint: def:modular-operator
-/
noncomputable def modularOperator (M : Set (H →L[ℂ] H)) (Ω : H) (C : H ≃ₗᵢ⋆[ℂ] H) :
    H →ₗ.[ℂ] H :=
  adjointMulSelf (linearizedTomitaPre M Ω C).closure

/--
The modular operator is self-adjoint, by von Neumann's theorem.

Blueprint: thrm:modular-operator-properties
-/
theorem modularOperator_isSelfAdjoint {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) : IsSelfAdjoint (modularOperator M Ω C) :=
  (isSelfAdjoint_adjointMulSelf (linearizedTomita_closure_polar_hyps hM hΩ C hC).1
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).2.1).1

/--
The square root `Δ^{1/2} = s(Δ) = |S′|` of the modular operator.

Blueprint: def:modular-operator
-/
noncomputable def modularOperatorSqrt {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) : H →ₗ.[ℂ] H :=
  absoluteValue (linearizedTomitaPre M Ω C).closure
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).1
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).2.1

/--
The inverse square root `Δ^{-1/2} = r(Δ)` of the modular operator, with `r(λ) = λ^{-1/2}` for
`λ > 0` and `r(λ) = 0` otherwise (written `(√λ)⁻¹`).

Blueprint: lmm:tomita-inverse-as-product
-/
noncomputable def modularOperatorInvSqrt {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) : H →ₗ.[ℂ] H :=
  functionalCalculus (modularOperator_isSelfAdjoint hM hΩ C hC)
    fun x => (((Real.sqrt x)⁻¹ : ℝ) : ℂ)

/--
The modular conjugation `J = C V`, where `V` is a unitary of the polar decomposition
`S′ = V |S′| = V Δ^{1/2}` (`polar_decomposition`, chosen classically; it is unique by
`existsUnique_polarIsometry`).

Blueprint: def:modular-conjugation
-/
noncomputable def modularConjugation {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) : H ≃ₗᵢ⋆[ℂ] H :=
  (Classical.choose (polar_decomposition (linearizedTomita_closure_polar_hyps hM hΩ C hC).1
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).2.1
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).2.2.1
    (linearizedTomita_closure_polar_hyps hM hΩ C hC).2.2.2)).trans C

/--
`Δ` is positive, self-adjoint, densely defined and injective; `Dom Δ^{1/2} = Dom S` and
`‖Δ^{1/2} ψ‖ = ‖S ψ‖` for `ψ ∈ Dom S`.

Blueprint: thrm:modular-operator-properties
-/
theorem modularOperator_properties {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    IsPositive (modularOperator M Ω C) ∧ IsSelfAdjoint (modularOperator M Ω C) ∧
      HasDenseDomain (modularOperator M Ω C) ∧ ker (modularOperator M Ω C) = ⊥ ∧
      (modularOperatorSqrt hM hΩ C hC).domain = (linearizedTomitaPre M Ω C).closure.domain ∧
      ∀ (ψ : H) (h₁ : ψ ∈ (modularOperatorSqrt hM hΩ C hC).domain)
        (h₂ : ψ ∈ (linearizedTomitaPre M Ω C).closure.domain),
        ‖modularOperatorSqrt hM hΩ C hC ⟨ψ, h₁⟩‖ = ‖tomitaOperator M Ω C ⟨ψ, h₂⟩‖ := by
  sorry

/--
`ψ ∈ Dom Δ` with `Δ ψ = χ` if and only if `ψ ∈ Dom S` and `⟪S φ, S ψ⟫ = ⟪χ, φ⟫` for every
`φ ∈ Dom S`.

Blueprint: lmm:modular-operator-intrinsic
-/
theorem mem_modularOperator_iff {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (ψ χ : H) :
    (∃ h : ψ ∈ (modularOperator M Ω C).domain, modularOperator M Ω C ⟨ψ, h⟩ = χ) ↔
      ∃ h : ψ ∈ (linearizedTomitaPre M Ω C).closure.domain,
        ∀ φ : (linearizedTomitaPre M Ω C).closure.domain,
          ⟪tomitaOperator M Ω C φ, tomitaOperator M Ω C ⟨ψ, h⟩⟫_ℂ = ⟪χ, (φ : H)⟫_ℂ := by
  sorry

/--
`J` is antiunitary (by its type) and `S = J Δ^{1/2}`: `Dom S = Dom Δ^{1/2}` and
`S ψ = J (Δ^{1/2} ψ)`.

Blueprint: thrm:modular-conjugation-polar
-/
theorem tomitaOperator_eq_modularConjugation_sqrt {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    (linearizedTomitaPre M Ω C).closure.domain = (modularOperatorSqrt hM hΩ C hC).domain ∧
      ∀ (ψ : H) (h₁ : ψ ∈ (linearizedTomitaPre M Ω C).closure.domain)
        (h₂ : ψ ∈ (modularOperatorSqrt hM hΩ C hC).domain),
        tomitaOperator M Ω C ⟨ψ, h₁⟩ =
          modularConjugation hM hΩ C hC (modularOperatorSqrt hM hΩ C hC ⟨ψ, h₂⟩) := by
  sorry

/--
`J` is the only continuous map `K : H → H` with `K (Δ^{1/2} ψ) = S ψ` for all
`ψ ∈ Dom Δ^{1/2}`.

Blueprint: lmm:modular-conjugation-intrinsic
-/
theorem eq_modularConjugation_of_continuous {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) (K : H → H) (hK : Continuous K)
    (hKS : ∀ (ψ : H) (h₁ : ψ ∈ (linearizedTomitaPre M Ω C).closure.domain)
      (h₂ : ψ ∈ (modularOperatorSqrt hM hΩ C hC).domain),
      K (modularOperatorSqrt hM hΩ C hC ⟨ψ, h₂⟩) = tomitaOperator M Ω C ⟨ψ, h₁⟩) :
    ∀ x, K x = modularConjugation hM hΩ C hC x := by
  sorry

/--
`Δ`, `Δ^{1/2}` and `J` are the same for every choice of the reference conjugation: for
antiunitary involutions `C₁` and `C₂`, the modular operators and their square roots are equal and
the modular conjugations agree pointwise.

Blueprint: thrm:modular-objects-independent-of-c
-/
theorem modular_objects_independent_of_conjugation {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C₁ C₂ : H ≃ₗᵢ⋆[ℂ] H)
    (hC₁ : ∀ x, C₁ (C₁ x) = x) (hC₂ : ∀ x, C₂ (C₂ x) = x) :
    modularOperator M Ω C₁ = modularOperator M Ω C₂ ∧
      modularOperatorSqrt hM hΩ C₁ hC₁ = modularOperatorSqrt hM hΩ C₂ hC₂ ∧
      ∀ x, modularConjugation hM hΩ C₁ hC₁ x = modularConjugation hM hΩ C₂ hC₂ x := by
  sorry

/--
`S` is injective and `S⁻¹ = S`: `Range S = Dom S` and `S (S x) = x` for `x ∈ Dom S`.

Implementation note: `S` is antilinear, so Mathlib's `LinearPMap.inverse` does not apply; the
identity `S⁻¹ = S` is stated through injectivity, the range, and the pointwise involution.

Blueprint: lmm:tomita-inverse-is-self
-/
theorem tomitaOperator_inverse_eq_self {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    Function.Injective (tomitaOperator M Ω C) ∧
      Set.range (tomitaOperator M Ω C) = (linearizedTomitaPre M Ω C).closure.domain ∧
      ∀ x, ∃ h : tomitaOperator M Ω C x ∈ (linearizedTomitaPre M Ω C).closure.domain,
        tomitaOperator M Ω C ⟨_, h⟩ = x := by
  sorry

/--
With `P = J Δ^{-1/2} J⁻¹` (`antiunitaryConj`), `S = J⁻¹ P`: `Dom S = Dom P` and
`S ψ = J⁻¹ (P ψ)`.

Blueprint: lmm:tomita-inverse-as-product
-/
theorem tomitaOperator_eq_symm_conj_invSqrt {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    (linearizedTomitaPre M Ω C).closure.domain =
        (antiunitaryConj (modularConjugation hM hΩ C hC)
          (modularOperatorInvSqrt hM hΩ C hC)).domain ∧
      ∀ (ψ : H) (h₁ : ψ ∈ (linearizedTomitaPre M Ω C).closure.domain)
        (h₂ : ψ ∈ (antiunitaryConj (modularConjugation hM hΩ C hC)
          (modularOperatorInvSqrt hM hΩ C hC)).domain),
        tomitaOperator M Ω C ⟨ψ, h₁⟩ = (modularConjugation hM hΩ C hC).symm
          (antiunitaryConj (modularConjugation hM hΩ C hC)
            (modularOperatorInvSqrt hM hΩ C hC) ⟨ψ, h₂⟩) := by
  sorry

/--
With `P = J Δ^{-1/2} J⁻¹`, `P` is positive and self-adjoint, `C J⁻¹` is unitary, and
`S′ = (C J⁻¹) P`.

Blueprint: lmm:tomita-inverse-polar
-/
theorem linearizedTomita_closure_eq_unitary_conj_invSqrt {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    IsPositive (antiunitaryConj (modularConjugation hM hΩ C hC)
        (modularOperatorInvSqrt hM hΩ C hC)) ∧
      IsSelfAdjoint (antiunitaryConj (modularConjugation hM hΩ C hC)
        (modularOperatorInvSqrt hM hΩ C hC)) ∧
      ∃ U : H ≃ₗᵢ[ℂ] H, (∀ x, U x = C ((modularConjugation hM hΩ C hC).symm x)) ∧
        (linearizedTomitaPre M Ω C).closure = U.toLinearEquiv.toLinearMap.compPMap
          (antiunitaryConj (modularConjugation hM hΩ C hC)
            (modularOperatorInvSqrt hM hΩ C hC)) := by
  sorry

/--
`J (J φ) = φ` for every `φ`, and `J Δ^{1/2} J = Δ^{-1/2}`. Since `J⁻¹ = J`, the operator
`J Δ^{1/2} J` is the antiunitary conjugate `J Δ^{1/2} J⁻¹` (`antiunitaryConj`).

Blueprint: thrm:modular-conjugation-involution
-/
theorem modularConjugation_involution {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    (∀ φ, modularConjugation hM hΩ C hC (modularConjugation hM hΩ C hC φ) = φ) ∧
      antiunitaryConj (modularConjugation hM hΩ C hC) (modularOperatorSqrt hM hΩ C hC) =
        modularOperatorInvSqrt hM hΩ C hC := by
  sorry

/--
`J Δ J = Δ⁻¹`, with `J Δ J = J Δ J⁻¹` (`antiunitaryConj`, as `J⁻¹ = J`) and `Δ⁻¹` Mathlib's
`LinearPMap.inverse`.

Blueprint: crllr:modular-conjugation-inverts
-/
theorem modularConjugation_conj_modularOperator {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω) (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : ∀ x, C (C x) = x) :
    antiunitaryConj (modularConjugation hM hΩ C hC) (modularOperator M Ω C) =
      (modularOperator M Ω C).inverse := by
  sorry

end Physicslib4.Modular
