/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Unbounded.FunctionalCalculus
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# One-parameter unitary groups and their infinitesimal generators

This file sets up the objects of Stone's theorem (blueprint §10.4).

## Main definitions

* `IsOneParameterUnitaryGroup U` — `U : ℝ → (H ≃ₗᵢ[ℂ] H)` satisfies `U 0 = 1` and
  `U (s + t) = U s U t`.
* `IsStronglyContinuous U` — every orbit `t ↦ U t ψ` is continuous.
* `generatorQuotient U ψ t` — the difference quotient `(1/i) (U t ψ - ψ)/t`.
* `generator U` — the infinitesimal generator, an unbounded operator whose domain is the set
  of `ψ` for which the punctured limit of `generatorQuotient U ψ t` as `t → 0` exists, and
  whose value is that limit.

The generator is defined for any family `U`; the group law is assumed only in the results
that need it.
-/

namespace Physicslib4
namespace Spectral
namespace Stone

open scoped InnerProductSpace LinearPMap Topology
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/--
A *one-parameter unitary group* on `H`: a family `U t` of unitary operators, `t ∈ ℝ`, with
`U 0 = 1` and `U (s + t) = U s U t`. Unitaries are modelled as linear isometry equivalences,
as elsewhere in the project.

Blueprint reference: `def:hall-10.11`.
-/
structure IsOneParameterUnitaryGroup (U : ℝ → (H ≃ₗᵢ[ℂ] H)) : Prop where
  /-- `U 0 = 1`. -/
  map_zero : ∀ ψ : H, U 0 ψ = ψ
  /-- The group law `U (s + t) = U s U t`. -/
  map_add : ∀ (s t : ℝ) (ψ : H), U (s + t) ψ = U s (U t ψ)

/--
A family `U` is *strongly continuous* if `s ↦ U s ψ` is continuous for every `ψ`, i.e.
`‖U t ψ - U s ψ‖ → 0` as `s → t`, for every `t`.

Blueprint reference: `def:hall-10.11`.
-/
def IsStronglyContinuous (U : ℝ → (H ≃ₗᵢ[ℂ] H)) : Prop :=
  ∀ ψ : H, Continuous fun t : ℝ => U t ψ

/--
The difference quotient `(1/i) (U t ψ - ψ)/t` whose punctured limit at `0` defines the
infinitesimal generator.

Blueprint reference: `def:hall-10.13`.
-/
noncomputable def generatorQuotient (U : ℝ → (H ≃ₗᵢ[ℂ] H)) (ψ : H) (t : ℝ) : H :=
  (Complex.I * (t : ℂ))⁻¹ • (U t ψ - ψ)

theorem generatorQuotient_add (U : ℝ → (H ≃ₗᵢ[ℂ] H)) (φ ψ : H) (t : ℝ) :
    generatorQuotient U (φ + ψ) t = generatorQuotient U φ t + generatorQuotient U ψ t := by
  simp only [generatorQuotient, map_add, ← smul_add]
  congr 1
  abel

theorem generatorQuotient_smul (U : ℝ → (H ≃ₗᵢ[ℂ] H)) (c : ℂ) (ψ : H) (t : ℝ) :
    generatorQuotient U (c • ψ) t = c • generatorQuotient U ψ t := by
  simp only [generatorQuotient, map_smul, ← smul_sub, smul_comm c]

/--
The domain of the infinitesimal generator: the vectors `ψ` for which the punctured limit of
`generatorQuotient U ψ t` as `t → 0` exists.

Blueprint reference: `def:hall-10.13`.
-/
def generatorDomain (U : ℝ → (H ≃ₗᵢ[ℂ] H)) : Submodule ℂ H where
  carrier := {ψ | ∃ χ : H, Tendsto (generatorQuotient U ψ) (𝓝[≠] 0) (𝓝 χ)}
  add_mem' := by
    rintro φ ψ ⟨χ₁, h₁⟩ ⟨χ₂, h₂⟩
    exact ⟨χ₁ + χ₂, (funext (generatorQuotient_add U φ ψ)).symm ▸ h₁.add h₂⟩
  zero_mem' := ⟨0, by
    have : generatorQuotient U 0 = fun _ => 0 := funext fun t => by simp [generatorQuotient]
    exact this ▸ tendsto_const_nhds⟩
  smul_mem' := by
    rintro c ψ ⟨χ, h⟩
    exact ⟨c • χ, (funext (generatorQuotient_smul U c ψ)).symm ▸ h.const_smul c⟩

/--
The *infinitesimal generator* of `U`: `A ψ = lim_{t → 0, t ≠ 0} (1/i) (U t ψ - ψ)/t` on the
subspace `generatorDomain U` where the limit exists. No continuity or density is assumed;
density of the domain for a strongly continuous group is `lmm:hall-10.18`.

Blueprint reference: `def:hall-10.13`.
-/
noncomputable def generator (U : ℝ → (H ≃ₗᵢ[ℂ] H)) : H →ₗ.[ℂ] H where
  domain := generatorDomain U
  toFun :=
    { toFun := fun ψ => limUnder (𝓝[≠] (0 : ℝ)) (generatorQuotient U ψ)
      map_add' := fun φ ψ => by
        obtain ⟨χ₁, h₁⟩ := φ.2
        obtain ⟨χ₂, h₂⟩ := ψ.2
        have h : Tendsto (generatorQuotient U ((φ + ψ : generatorDomain U) : H)) (𝓝[≠] 0)
            (𝓝 (χ₁ + χ₂)) :=
          (funext (generatorQuotient_add U φ ψ)).symm ▸ h₁.add h₂
        rw [h.limUnder_eq, h₁.limUnder_eq, h₂.limUnder_eq]
      map_smul' := fun c ψ => by
        obtain ⟨χ, h⟩ := ψ.2
        have h' : Tendsto (generatorQuotient U ((c • ψ : generatorDomain U) : H)) (𝓝[≠] 0)
            (𝓝 (c • χ)) :=
          (funext (generatorQuotient_smul U c ψ)).symm ▸ h.const_smul c
        rw [h'.limUnder_eq, h.limUnder_eq, RingHom.id_apply] }

theorem generator_domain (U : ℝ → (H ≃ₗᵢ[ℂ] H)) : (generator U).domain = generatorDomain U :=
  rfl

/--
A one-parameter unitary group is strongly continuous as soon as it is strongly continuous
at `0`: `U s ψ → ψ` as `s → 0`, for every `ψ`.

Blueprint reference: `lmm:strongly-continuous-iff-at-zero`.
-/
theorem isStronglyContinuous_iff_tendsto_zero {U : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hU : IsOneParameterUnitaryGroup U) :
    IsStronglyContinuous U ↔ ∀ ψ : H, Tendsto (fun s : ℝ => U s ψ) (𝓝 0) (𝓝 ψ) := by
  refine ⟨fun h ψ => by simpa [hU.map_zero] using (h ψ).tendsto 0,
    fun h ψ => continuous_iff_continuousAt.2 fun t => ?_⟩
  have h1 : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.2 tendsto_id
  have h2 := ((U t).continuous.tendsto ψ).comp ((h ψ).comp h1)
  refine h2.congr fun s => ?_
  simp only [Function.comp_apply, ← hU.map_add, add_sub_cancel]

/--
The group law forces `U(t)* = U(-t)`, in inner-product form:
`⟪φ, U t ψ⟫ = ⟪U (-t) φ, ψ⟫`.

Blueprint reference: `lmm:unitary-group-inner-adjoint`.
-/
theorem IsOneParameterUnitaryGroup.inner_apply {U : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hU : IsOneParameterUnitaryGroup U) (t : ℝ) (φ ψ : H) :
    ⟪φ, U t ψ⟫_ℂ = ⟪U (-t) φ, ψ⟫_ℂ := by
  have h : U t (U (-t) φ) = φ := by rw [← hU.map_add, add_neg_cancel, hU.map_zero]
  rw [← (U t).inner_map_map (U (-t) φ), h]

/--
The adjoint of `U t` is `U (-t)`.

Blueprint reference: `lmm:unitary-group-inner-adjoint`.
-/
theorem IsOneParameterUnitaryGroup.adjoint_eq [CompleteSpace H] {U : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hU : IsOneParameterUnitaryGroup U) (t : ℝ) :
    ContinuousLinearMap.adjoint (U t).toLinearIsometry.toContinuousLinearMap =
      (U (-t)).toLinearIsometry.toContinuousLinearMap := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_).symm
  exact (hU.inner_apply t x y).symm

/--
Characterization of the generator: `ψ ∈ Dom(A)` with `A ψ = χ` if and only if the
difference quotient `(1/i) (U t ψ - ψ)/t` tends to `χ` as `t → 0`, `t ≠ 0`.

Blueprint reference: `lmm:generator-spec`.
-/
theorem exists_generator_eq_iff (U : ℝ → (H ≃ₗᵢ[ℂ] H)) (ψ χ : H) :
    (∃ h : ψ ∈ (generator U).domain, generator U ⟨ψ, h⟩ = χ) ↔
      Tendsto (generatorQuotient U ψ) (𝓝[≠] 0) (𝓝 χ) := by
  constructor
  · rintro ⟨⟨χ', h⟩, rfl⟩
    change Tendsto _ _ (𝓝 (limUnder (𝓝[≠] (0 : ℝ)) (generatorQuotient U ψ)))
    rwa [h.limUnder_eq]
  · intro h
    exact ⟨⟨χ, h⟩, h.limUnder_eq⟩

private theorem inner_generatorQuotient {U : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hU : IsOneParameterUnitaryGroup U) (φ ψ : H) (t : ℝ) :
    ⟪φ, generatorQuotient U ψ t⟫_ℂ = ⟪generatorQuotient U φ (-t), ψ⟫_ℂ := by
  simp only [generatorQuotient, inner_smul_right, inner_smul_left, inner_sub_right,
    inner_sub_left, hU.inner_apply t φ ψ]
  congr 1
  simp [map_inv₀]

/--
The generator of a one-parameter unitary group satisfies the symmetry identity
`⟪φ, A ψ⟫ = ⟪A φ, ψ⟫` on its domain, which is symmetry in the density-free sense of
`Unbounded.IsSymmetric`.

Blueprint reference: `lmm:generator-symmetry-identity`.
-/
theorem isSymmetric_generator {U : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hU : IsOneParameterUnitaryGroup U) : Unbounded.IsSymmetric (generator U) := by
  intro φ ψ
  have hφ := (exists_generator_eq_iff U φ (generator U φ)).1 ⟨φ.2, rfl⟩
  have hψ := (exists_generator_eq_iff U ψ (generator U ψ)).1 ⟨ψ.2, rfl⟩
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[≠] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun t ht => neg_ne_zero.2 ht)
  exact tendsto_nhds_unique (tendsto_const_nhds.inner hψ)
    (((hφ.comp hneg).inner tendsto_const_nhds).congr fun t =>
      (inner_generatorQuotient hU _ _ t).symm)

/--
The scalar equation `y' = c y`: a differentiable `y : ℝ → ℂ` with `y' = c y` is
`y t = y 0 * exp (c t)`.

Blueprint reference: `lmm:linear-ode-scalar`.
-/
theorem eq_mul_exp_of_hasDerivAt {y : ℝ → ℂ} {c : ℂ} (hy : ∀ t, HasDerivAt y (c * y t) t)
    (t : ℝ) : y t = y 0 * Complex.exp (c * t) := by
  have hz : ∀ s : ℝ, HasDerivAt (fun s : ℝ => y s * Complex.exp (-c * s)) 0 s := by
    intro s
    have he : HasDerivAt (fun s : ℝ => Complex.exp (-c * s))
        (Complex.exp (-c * s) * (-c * 1)) s :=
      (((hasDerivAt_id s).ofReal_comp).const_mul (-c)).cexp
    convert (hy s).mul he using 1
    ring
  have hconst := is_const_of_deriv_eq_zero (fun s => (hz s).differentiableAt)
    (fun s => (hz s).deriv) t 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hconst
  rw [← hconst, mul_assoc, ← Complex.exp_add]
  simp

/--
Orbits through the generator's domain are differentiable: for `ψ ∈ Dom(A)`,
`s ↦ U s ψ` has derivative `i U t (A ψ)` at every `t`.

Blueprint reference: `lmm:orbit-hasDerivAt`.
-/
theorem IsOneParameterUnitaryGroup.hasDerivAt_orbit {U : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hU : IsOneParameterUnitaryGroup U) (ψ : (generator U).domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => U s ψ) (Complex.I • U t (generator U ψ)) t := by
  obtain ⟨χ, hχ⟩ := ψ.2
  have hA : generator U ψ = χ := hχ.limUnder_eq
  rw [hasDerivAt_iff_tendsto_slope_zero, hA]
  have h1 : Tendsto (fun h : ℝ => U t (Complex.I • generatorQuotient U ψ h)) (𝓝[≠] 0)
      (𝓝 (U t (Complex.I • χ))) :=
    ((U t).continuous.tendsto _).comp (hχ.const_smul Complex.I)
  rw [← map_smul]
  refine h1.congr' (eventually_nhdsWithin_of_forall fun h (hh : h ≠ 0) => ?_)
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hh
  simp only [generatorQuotient, smul_smul, hU.map_add t h, ← map_sub, ← map_smul,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  congr 2
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ Complex.I_ne_zero, one_mul]
  push_cast
  rfl

/--
The group commutes with its generator: for `ψ ∈ Dom(A)`, `U t ψ ∈ Dom(A)` and
`A (U t ψ) = U t (A ψ)`.

Blueprint reference: `lmm:generator-commutes`.
-/
theorem IsOneParameterUnitaryGroup.generator_apply_comm {U : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hU : IsOneParameterUnitaryGroup U) (ψ : (generator U).domain) (t : ℝ) :
    ∃ h : U t ψ ∈ (generator U).domain, generator U ⟨U t ψ, h⟩ = U t (generator U ψ) := by
  refine (exists_generator_eq_iff U _ _).mpr ?_
  have hq : generatorQuotient U (U t ψ) = fun h => U t (generatorQuotient U ψ h) := by
    funext h
    simp only [generatorQuotient, map_sub, map_smul, ← hU.map_add, add_comm h t]
  rw [hq]
  exact ((U t).continuous.tendsto _).comp ((exists_generator_eq_iff U _ _).mp ⟨ψ.2, rfl⟩)

/--
The group preserves the generator's domain and differentiates to it: for `ψ ∈ Dom(A)` and
every `t`, `U t ψ ∈ Dom(A)` and `s ↦ U s ψ` has derivative `i U t (A ψ) = i A (U t ψ)` at `t`.

The blueprint assumes `U` strongly continuous; the proof does not use it, so the hypothesis
is omitted.

Blueprint reference: `lmm:hall-10.17`.
-/
theorem IsOneParameterUnitaryGroup.hasDerivAt_orbit_generator {U : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hU : IsOneParameterUnitaryGroup U) (ψ : (generator U).domain) (t : ℝ) :
    ∃ h : U t ψ ∈ (generator U).domain,
      HasDerivAt (fun s : ℝ => U s ψ) (Complex.I • generator U ⟨U t ψ, h⟩) t ∧
        generator U ⟨U t ψ, h⟩ = U t (generator U ψ) := by
  obtain ⟨h, e⟩ := hU.generator_apply_comm ψ t
  exact ⟨h, e ▸ hU.hasDerivAt_orbit ψ t, e⟩

/--
The trivial family `t ↦ 1` is a one-parameter unitary group.

Blueprint reference: `lmm:generator-const`.
-/
theorem isOneParameterUnitaryGroup_refl :
    IsOneParameterUnitaryGroup (fun _ : ℝ => LinearIsometryEquiv.refl ℂ H) := by
  sorry

/--
The trivial family `t ↦ 1` is strongly continuous.

Blueprint reference: `lmm:generator-const`.
-/
theorem isStronglyContinuous_refl :
    IsStronglyContinuous (fun _ : ℝ => LinearIsometryEquiv.refl ℂ H) := by
  sorry

/--
The generator of the trivial group `t ↦ 1` is `0`, with domain `H`.

Blueprint reference: `lmm:generator-const`.
-/
theorem generator_refl : generator (fun _ : ℝ => LinearIsometryEquiv.refl ℂ H) = 0 := by
  sorry

/--
Conjugating a one-parameter unitary group by a unitary `W` gives a one-parameter unitary group
`t ↦ W U(t) W⁻¹`.

Blueprint reference: `lmm:conj-unitary-group`.
-/
theorem IsOneParameterUnitaryGroup.conj {U : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hU : IsOneParameterUnitaryGroup U) (W : H ≃ₗᵢ[ℂ] H) :
    IsOneParameterUnitaryGroup fun t => (W.symm.trans (U t)).trans W := by
  sorry

/--
Conjugation by a unitary preserves strong continuity.

Blueprint reference: `lmm:conj-unitary-group`.
-/
theorem IsStronglyContinuous.conj {U : ℝ → (H ≃ₗᵢ[ℂ] H)} (hU : IsStronglyContinuous U)
    (W : H ≃ₗᵢ[ℂ] H) : IsStronglyContinuous fun t => (W.symm.trans (U t)).trans W := by
  sorry

/--
The domain of the generator of `t ↦ W U(t) W⁻¹` is `W · Dom(A)`, `A` the generator of `U`.
No group law is needed: the difference quotient at `ψ` is `W` applied to that of `U` at
`W⁻¹ ψ`.

Blueprint reference: `lmm:generator-conj`.
-/
theorem mem_generator_conj_domain_iff (U : ℝ → (H ≃ₗᵢ[ℂ] H)) (W : H ≃ₗᵢ[ℂ] H) (ψ : H) :
    ψ ∈ (generator fun t => (W.symm.trans (U t)).trans W).domain ↔
      W.symm ψ ∈ (generator U).domain := by
  sorry

/--
The generator of `t ↦ W U(t) W⁻¹` is `W A W⁻¹`, `A` the generator of `U`.

Blueprint reference: `lmm:generator-conj`.
-/
theorem generator_conj_apply (U : ℝ → (H ≃ₗᵢ[ℂ] H)) (W : H ≃ₗᵢ[ℂ] H) (ψ : H)
    (h : ψ ∈ (generator fun t => (W.symm.trans (U t)).trans W).domain)
    (h' : W.symm ψ ∈ (generator U).domain) :
    (generator fun t => (W.symm.trans (U t)).trans W) ⟨ψ, h⟩ =
      W (generator U ⟨W.symm ψ, h'⟩) := by
  sorry

end Stone
end Spectral
end Physicslib4
