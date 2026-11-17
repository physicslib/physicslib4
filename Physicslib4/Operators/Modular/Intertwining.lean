/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Operators.Modular.VanDaele
import Physicslib4.Spectral.Unbounded.UnitaryConjugation

/-!
# Unitaries intertwining modular objects

Let `(M₁, Ω₁)` and `(M₂, Ω₂)` be von Neumann algebras on `H` with cyclic and separating vectors,
with reference conjugations `C₁`, `C₂` (antiunitary involutions, chosen independently). A unitary
`V` with `V M₁ V⁻¹ = M₂` and `V Ω₁ = Ω₂` carries the Tomita operator, the modular operator, its
square root, the modular unitary group and the modular conjugation of the first pair onto those
of the second. The special case `M₁ = M₂`, `Ω₁ = Ω₂` says that a unitary that preserves `M` and
fixes `Ω` commutes with all of them.

Conventions:
* `V M₁ V⁻¹ = M₂` is `(fun a => V ∘L a ∘L V⁻¹) '' M₁ = M₂`.
* For an unbounded linear operator, "`B = V A V⁻¹`, including domains" is the graph identity
  `B.graph = A.graph.map Φ_V`, with `Φ_V (φ, ψ) = (V φ, V ψ)` written `Φ[V]` (local notation).
* The Tomita operator is a function on a subtype of `H`, so its intertwining is stated pointwise
  together with the domain condition; the bounded objects `Δ^{it}` and `J` are intertwined
  pointwise.
-/

namespace Physicslib4.Modular

open scoped InnerProductSpace
open Physicslib4.Spectral.Unbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The map `Φ_V (φ, ψ) = (V φ, V ψ)` of `H × H` induced by a unitary `V`. -/
local notation "Φ[" V "]" =>
  LinearMap.prodMap (LinearEquiv.toLinearMap (LinearIsometryEquiv.toLinearEquiv V))
    (LinearEquiv.toLinearMap (LinearIsometryEquiv.toLinearEquiv V))

/-- The conjugate `V a V⁻¹` of a bounded operator `a` by a unitary `V`. -/
local notation "conj[" V "] " a =>
  ContinuousLinearMap.comp (LinearIsometry.toContinuousLinearMap
    (LinearIsometryEquiv.toLinearIsometry V))
    (ContinuousLinearMap.comp a (LinearIsometry.toContinuousLinearMap
      (LinearIsometryEquiv.toLinearIsometry (LinearIsometryEquiv.symm V))))

/-- `V` intertwines the Tomita pre-operators: `Γ(S₀,₂) = Φ_V(Γ(S₀,₁))`, that is,
`Dom S₀,₂ = V (Dom S₀,₁)` and `S₀,₂ V ψ = V S₀,₁ ψ` for `ψ ∈ Dom S₀,₁`.

Blueprint: lmm:unitary-intertwines-tomita-pre-operators -/
theorem tomitaPre_graph_unitary_intertwine {M₁ M₂ : Set (H →L[ℂ] H)} {Ω₁ Ω₂ : H}
    (hM₁ : IsVonNeumannSet M₁) (hM₂ : IsVonNeumannSet M₂)
    (hΩ₁ : IsCyclicSeparatingVector M₁ Ω₁) (hΩ₂ : IsCyclicSeparatingVector M₂ Ω₂)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M₁ = M₂) (hVΩ : V Ω₁ = Ω₂) :
    Set.range (fun x : tomitaPreDomain M₂ Ω₂ => ((x : H), tomitaPre M₂ Ω₂ x)) =
      Prod.map V V ''
        Set.range (fun x : tomitaPreDomain M₁ Ω₁ => ((x : H), tomitaPre M₁ Ω₁ x)) := by
  sorry

/-- `V` intertwines the Tomita operators: `V S₁ V⁻¹ = S₂`, including domains. That is,
`ψ ∈ Dom S₁` if and only if `V ψ ∈ Dom S₂`, and then `S₂ V ψ = V S₁ ψ`.

Blueprint: lmm:unitary-intertwines-tomita-operator -/
theorem tomitaOperator_unitary_intertwine {M₁ M₂ : Set (H →L[ℂ] H)} {Ω₁ Ω₂ : H}
    (hM₁ : IsVonNeumannSet M₁) (hM₂ : IsVonNeumannSet M₂)
    (hΩ₁ : IsCyclicSeparatingVector M₁ Ω₁) (hΩ₂ : IsCyclicSeparatingVector M₂ Ω₂)
    (C₁ C₂ : H ≃ₗᵢ⋆[ℂ] H) (hC₁ : ∀ x, C₁ (C₁ x) = x) (hC₂ : ∀ x, C₂ (C₂ x) = x)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M₁ = M₂) (hVΩ : V Ω₁ = Ω₂) :
    (∀ ψ : H, ψ ∈ (linearizedTomitaPre M₁ Ω₁ C₁).closure.domain ↔
        V ψ ∈ (linearizedTomitaPre M₂ Ω₂ C₂).closure.domain) ∧
      ∀ (ψ : H) (h₁ : ψ ∈ (linearizedTomitaPre M₁ Ω₁ C₁).closure.domain)
        (h₂ : V ψ ∈ (linearizedTomitaPre M₂ Ω₂ C₂).closure.domain),
        tomitaOperator M₂ Ω₂ C₂ ⟨V ψ, h₂⟩ = V (tomitaOperator M₁ Ω₁ C₁ ⟨ψ, h₁⟩) := by
  sorry

/-- `V` intertwines the modular operators: for all `ψ, χ`, `V ψ ∈ Dom Δ₂` with `Δ₂ V ψ = V χ` if
and only if `ψ ∈ Dom Δ₁` with `Δ₁ ψ = χ`. Consequently `V Δ₁ V⁻¹ = Δ₂`, including domains.

Blueprint: lmm:unitary-intertwines-modular-operator -/
theorem modularOperator_unitary_intertwine {M₁ M₂ : Set (H →L[ℂ] H)} {Ω₁ Ω₂ : H}
    (hM₁ : IsVonNeumannSet M₁) (hM₂ : IsVonNeumannSet M₂)
    (hΩ₁ : IsCyclicSeparatingVector M₁ Ω₁) (hΩ₂ : IsCyclicSeparatingVector M₂ Ω₂)
    (C₁ C₂ : H ≃ₗᵢ⋆[ℂ] H) (hC₁ : ∀ x, C₁ (C₁ x) = x) (hC₂ : ∀ x, C₂ (C₂ x) = x)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M₁ = M₂) (hVΩ : V Ω₁ = Ω₂) :
    (∀ ψ χ : H,
      (∃ h : V ψ ∈ (modularOperator M₂ Ω₂ C₂).domain, modularOperator M₂ Ω₂ C₂ ⟨V ψ, h⟩ = V χ) ↔
        ∃ h : ψ ∈ (modularOperator M₁ Ω₁ C₁).domain, modularOperator M₁ Ω₁ C₁ ⟨ψ, h⟩ = χ) ∧
      (modularOperator M₂ Ω₂ C₂).graph = (modularOperator M₁ Ω₁ C₁).graph.map Φ[V] := by
  sorry

/-- `V` intertwines functions of the modular operators: `V f(Δ₁) V⁻¹ = f(Δ₂)`, including domains,
for every real measurable `f`. In particular `V Δ₁^{1/2} V⁻¹ = Δ₂^{1/2}`, including domains.

Blueprint: lmm:unitary-intertwines-modular-sqrt -/
theorem modularOperator_functionalCalculus_unitary_intertwine
    {M₁ M₂ : Set (H →L[ℂ] H)} {Ω₁ Ω₂ : H}
    (hM₁ : IsVonNeumannSet M₁) (hM₂ : IsVonNeumannSet M₂)
    (hΩ₁ : IsCyclicSeparatingVector M₁ Ω₁) (hΩ₂ : IsCyclicSeparatingVector M₂ Ω₂)
    (C₁ C₂ : H ≃ₗᵢ⋆[ℂ] H) (hC₁ : ∀ x, C₁ (C₁ x) = x) (hC₂ : ∀ x, C₂ (C₂ x) = x)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M₁ = M₂) (hVΩ : V Ω₁ = Ω₂) :
    (∀ f : ℝ → ℝ, Measurable f →
      (functionalCalculus (modularOperator_isSelfAdjoint hM₂ hΩ₂ C₂ hC₂)
          fun x => (f x : ℂ)).graph =
        (functionalCalculus (modularOperator_isSelfAdjoint hM₁ hΩ₁ C₁ hC₁)
          fun x => (f x : ℂ)).graph.map Φ[V]) ∧
      (modularOperatorSqrt hM₂ hΩ₂ C₂ hC₂).graph =
        (modularOperatorSqrt hM₁ hΩ₁ C₁ hC₁).graph.map Φ[V] := by
  sorry

/-- `V` intertwines the modular unitary groups: `V Δ₁^{it} V⁻¹ = Δ₂^{it}` for every `t ∈ ℝ`.

Blueprint: lmm:unitary-intertwines-modular-unitary-group -/
theorem modularUnitaryGroup_unitary_intertwine {M₁ M₂ : Set (H →L[ℂ] H)} {Ω₁ Ω₂ : H}
    (hM₁ : IsVonNeumannSet M₁) (hM₂ : IsVonNeumannSet M₂)
    (hΩ₁ : IsCyclicSeparatingVector M₁ Ω₁) (hΩ₂ : IsCyclicSeparatingVector M₂ Ω₂)
    (C₁ C₂ : H ≃ₗᵢ⋆[ℂ] H) (hC₁ : ∀ x, C₁ (C₁ x) = x) (hC₂ : ∀ x, C₂ (C₂ x) = x)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M₁ = M₂) (hVΩ : V Ω₁ = Ω₂) :
    ∀ (t : ℝ) (ψ : H), V (modularUnitaryGroup hM₁ hΩ₁ C₁ hC₁ t (V.symm ψ)) =
      modularUnitaryGroup hM₂ hΩ₂ C₂ hC₂ t ψ := by
  sorry

/-- `V` intertwines the modular conjugations: `V J₁ V⁻¹ φ = J₂ φ` for every `φ ∈ H`.

Blueprint: lmm:unitary-intertwines-modular-conjugation -/
theorem modularConjugation_unitary_intertwine {M₁ M₂ : Set (H →L[ℂ] H)} {Ω₁ Ω₂ : H}
    (hM₁ : IsVonNeumannSet M₁) (hM₂ : IsVonNeumannSet M₂)
    (hΩ₁ : IsCyclicSeparatingVector M₁ Ω₁) (hΩ₂ : IsCyclicSeparatingVector M₂ Ω₂)
    (C₁ C₂ : H ≃ₗᵢ⋆[ℂ] H) (hC₁ : ∀ x, C₁ (C₁ x) = x) (hC₂ : ∀ x, C₂ (C₂ x) = x)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M₁ = M₂) (hVΩ : V Ω₁ = Ω₂) :
    ∀ φ : H, V (modularConjugation hM₁ hΩ₁ C₁ hC₁ (V.symm φ)) =
      modularConjugation hM₂ hΩ₂ C₂ hC₂ φ := by
  sorry

/-- A unitary `V` between standard pairs, `V M₁ V⁻¹ = M₂` and `V Ω₁ = Ω₂`, intertwines the
modular objects, including domains: `V S₁ V⁻¹ = S₂`, `V Δ₁ V⁻¹ = Δ₂`,
`V Δ₁^{1/2} V⁻¹ = Δ₂^{1/2}`, `V Δ₁^{it} V⁻¹ = Δ₂^{it}` for `t ∈ ℝ`, and `V J₁ V⁻¹ = J₂`.

Blueprint: thrm:unitary-intertwines-modular-objects -/
theorem modular_objects_unitary_intertwine {M₁ M₂ : Set (H →L[ℂ] H)} {Ω₁ Ω₂ : H}
    (hM₁ : IsVonNeumannSet M₁) (hM₂ : IsVonNeumannSet M₂)
    (hΩ₁ : IsCyclicSeparatingVector M₁ Ω₁) (hΩ₂ : IsCyclicSeparatingVector M₂ Ω₂)
    (C₁ C₂ : H ≃ₗᵢ⋆[ℂ] H) (hC₁ : ∀ x, C₁ (C₁ x) = x) (hC₂ : ∀ x, C₂ (C₂ x) = x)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M₁ = M₂) (hVΩ : V Ω₁ = Ω₂) :
    ((∀ ψ : H, ψ ∈ (linearizedTomitaPre M₁ Ω₁ C₁).closure.domain ↔
        V ψ ∈ (linearizedTomitaPre M₂ Ω₂ C₂).closure.domain) ∧
      ∀ (ψ : H) (h₁ : ψ ∈ (linearizedTomitaPre M₁ Ω₁ C₁).closure.domain)
        (h₂ : V ψ ∈ (linearizedTomitaPre M₂ Ω₂ C₂).closure.domain),
        tomitaOperator M₂ Ω₂ C₂ ⟨V ψ, h₂⟩ = V (tomitaOperator M₁ Ω₁ C₁ ⟨ψ, h₁⟩)) ∧
    (modularOperator M₂ Ω₂ C₂).graph = (modularOperator M₁ Ω₁ C₁).graph.map Φ[V] ∧
    (modularOperatorSqrt hM₂ hΩ₂ C₂ hC₂).graph =
      (modularOperatorSqrt hM₁ hΩ₁ C₁ hC₁).graph.map Φ[V] ∧
    (∀ (t : ℝ) (ψ : H), V (modularUnitaryGroup hM₁ hΩ₁ C₁ hC₁ t (V.symm ψ)) =
      modularUnitaryGroup hM₂ hΩ₂ C₂ hC₂ t ψ) ∧
    ∀ φ : H, V (modularConjugation hM₁ hΩ₁ C₁ hC₁ (V.symm φ)) =
      modularConjugation hM₂ hΩ₂ C₂ hC₂ φ := by
  sorry

/-- A unitary `V` with `V M V⁻¹ = M` and `V Ω = Ω` commutes with the modular objects of `(M, Ω)`:
it commutes with `Δ` and with `Δ^{1/2}` (`UnitaryCommutes`), `V` maps `Dom S` onto itself
(`V ψ ∈ Dom S ↔ ψ ∈ Dom S`) with `S V ψ = V S ψ`, and `V Δ^{it} = Δ^{it} V` for `t ∈ ℝ` and
`V J = J V`.

Blueprint: crllr:unitary-commutes-modular-objects -/
theorem modular_objects_unitary_commute {M : Set (H →L[ℂ] H)} {Ω : H}
    (hM : IsVonNeumannSet M) (hΩ : IsCyclicSeparatingVector M Ω)
    (C : H ≃ₗᵢ⋆[ℂ] H) (hC : ∀ x, C (C x) = x)
    (V : H ≃ₗᵢ[ℂ] H) (hV : (fun a => conj[V] a) '' M = M) (hVΩ : V Ω = Ω) :
    UnitaryCommutes V (modularOperator M Ω C) ∧
    UnitaryCommutes V (modularOperatorSqrt hM hΩ C hC) ∧
    ((∀ ψ : H, V ψ ∈ (linearizedTomitaPre M Ω C).closure.domain ↔
        ψ ∈ (linearizedTomitaPre M Ω C).closure.domain) ∧
      ∀ (ψ : H) (h : ψ ∈ (linearizedTomitaPre M Ω C).closure.domain)
        (h' : V ψ ∈ (linearizedTomitaPre M Ω C).closure.domain),
        tomitaOperator M Ω C ⟨V ψ, h'⟩ = V (tomitaOperator M Ω C ⟨ψ, h⟩)) ∧
    (∀ (t : ℝ) (ψ : H), V (modularUnitaryGroup hM hΩ C hC t ψ) =
      modularUnitaryGroup hM hΩ C hC t (V ψ)) ∧
    ∀ ψ : H, V (modularConjugation hM hΩ C hC ψ) = modularConjugation hM hΩ C hC (V ψ) := by
  sorry

end Physicslib4.Modular
