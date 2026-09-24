/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Unbounded.AbstractCalculus

/-!
# The Cayley transform and the spectral theorem for unbounded self-adjoint operators

The scalar Cayley map `C(x) = (x + i)/(x - i)` is a bijection of `ℝ` onto the unit circle
minus the point `1`, with inverse `D(u) = i (u + 1)/(u - 1)`. Substituting a self-adjoint
unbounded operator `A` for `x` produces a *bounded* unitary — hence normal — operator `U`,
to which the spectral theorem for bounded normal operators applies; transporting the
resulting projection-valued measure back along `C` gives the spectral measure of `A`.

## Main definitions

* `cayleyMap`, `cayleyInv`, `unitCircleMinusOne` — the scalar maps.
* `IsCayleyTransform` — `U` is the Cayley transform of `A`, built from the resolvent
  `B = (A - i 1)⁻¹`.
* `restrictPVM`, `mapPVM` — restriction and transport of a projection-valued measure.
* `cayleyPVM` — the projection-valued measure on `ℝ` obtained from that of `U`.

## Main statements

* `unitary_mul_adjoint` — a unitary operator is normal.
* `bijOn_cayleyMap` and companions — the Cayley map and its inverse.
* `exists_isCayleyTransform` — the Cayley transform exists and is unitary, `U - 1` is
  injective with range `Dom(A)`, and `A = i (U + 1)(U - 1)⁻¹`.
* `mem_spectrum_iff_cayleyMap_mem_spectrum` — spectral mapping for the Cayley transform.
* `cayleyPVM_apply_singleton_one` — `μ^U({1}) = 0`.
* `pmapIntegral_cayleyInv_eq` — `A = ∫ D dμ^U`.
* `pmapIntegral_cayleyPVM_id` — `A = ∫ λ dμ^A`.
* `existsUnique_spectralMeasure_unbounded` — **the spectral theorem for unbounded
  self-adjoint operators**, with concentration on the spectrum.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace LinearPMap
open Filter Topology ContinuousLinearMap MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
### Unitary operators
-/

/--
A unitary operator satisfies `U* U = U U* = 1`; in particular it is normal.

Blueprint reference: `lmm:unitary-is-normal`.
-/
theorem unitary_mul_adjoint {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H)) :
    ContinuousLinearMap.adjoint U * U = 1 ∧ U * ContinuousLinearMap.adjoint U = 1 ∧
      IsStarNormal U := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  refine ⟨Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU, ⟨?_⟩⟩
  rw [Commute, SemiconjBy, Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU]

/-!
### The scalar Cayley map
-/

/-- The unit circle with the point `1` removed. -/
def unitCircleMinusOne : Set ℂ := {u : ℂ | ‖u‖ = 1} \ {1}

/--
The Cayley map `C(x) = (x + i)/(x - i)`.

Blueprint reference: `lmm:cayley-map`.
-/
noncomputable def cayleyMap (x : ℝ) : ℂ := ((x : ℂ) + Complex.I) / ((x : ℂ) - Complex.I)

/--
The inverse Cayley map `D(u) = i (u + 1)/(u - 1)`, valued in `ℝ` because `D` is
real-valued on the unit circle minus `1`.

Blueprint reference: `lmm:cayley-map`.
-/
noncomputable def cayleyInv (u : ℂ) : ℝ := (Complex.I * (u + 1) / (u - 1)).re

/--
`C` lands in the unit circle minus `1`.

Blueprint reference: `lmm:cayley-map`.
-/
theorem cayleyMap_mem (x : ℝ) : cayleyMap x ∈ unitCircleMinusOne := by
  have h : (x : ℂ) - Complex.I ≠ 0 := fun h => by simpa using congrArg Complex.im h
  refine ⟨?_, fun h1 => ?_⟩
  · have : ‖(x : ℂ) + Complex.I‖ = ‖(x : ℂ) - Complex.I‖ := by
      rw [← Complex.norm_conj]; simp [sub_eq_add_neg]
    simp only [Set.mem_setOf_eq, cayleyMap, norm_div, this]
    exact div_self (norm_ne_zero_iff.mpr h)
  · simp only [Set.mem_singleton_iff, cayleyMap, div_eq_one_iff_eq h] at h1
    have := congrArg Complex.im h1
    norm_num at this

/--
`C` is continuous, hence Borel measurable.

Blueprint reference: `lmm:cayley-map`.
-/
theorem continuous_cayleyMap : Continuous cayleyMap :=
  Continuous.div (by fun_prop) (by fun_prop)
    fun x h => by simpa using congrArg Complex.im h

/--
`D` is continuous on its domain, hence Borel measurable there.

Blueprint reference: `lmm:cayley-map`.
-/
theorem continuousOn_cayleyInv : ContinuousOn cayleyInv unitCircleMinusOne :=
  Complex.continuous_re.comp_continuousOn <|
    ContinuousOn.div (by fun_prop) (by fun_prop)
      fun u hu h => hu.2 (sub_eq_zero.mp h)

/--
On the unit circle minus `1`, `i (u+1)/(u-1)` is real, so `cayleyInv` loses no information.

Blueprint reference: `lmm:cayley-map`.
-/
theorem cayleyInv_ofReal {u : ℂ} (hu : u ∈ unitCircleMinusOne) :
    ((cayleyInv u : ℝ) : ℂ) = Complex.I * (u + 1) / (u - 1) := by
  obtain ⟨hn, h1⟩ := hu
  have hu1 : u - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hu0 : u ≠ 0 := by rintro rfl; simp at hn
  have hc : (starRingEnd ℂ) u = u⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]; simp
  have hu1' : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  exact Complex.conj_eq_iff_re.mp (by
    simp only [map_div₀, map_mul, map_add, map_sub, map_one, Complex.conj_I, hc]
    field_simp
    ring)

/--
`D ∘ C = id` on `ℝ`.

Blueprint reference: `lmm:cayley-map`.
-/
theorem cayleyInv_cayleyMap (x : ℝ) : cayleyInv (cayleyMap x) = x := by
  have h : (x : ℂ) - Complex.I ≠ 0 := fun h => by simpa using congrArg Complex.im h
  have hp : cayleyMap x + 1 = 2 * x / ((x : ℂ) - Complex.I) := by
    rw [cayleyMap, div_add_one h]; ring
  have hm : cayleyMap x - 1 = 2 * Complex.I / ((x : ℂ) - Complex.I) := by
    rw [cayleyMap, div_sub_one h]; ring
  have : Complex.I * (cayleyMap x + 1) / (cayleyMap x - 1) = x := by
    rw [hp, hm, mul_div_assoc, div_div_div_cancel_right₀ h]
    field_simp
  simp [cayleyInv, this]

/--
`C ∘ D = id` on the unit circle minus `1`.

Blueprint reference: `lmm:cayley-map`.
-/
theorem cayleyMap_cayleyInv {u : ℂ} (hu : u ∈ unitCircleMinusOne) :
    cayleyMap (cayleyInv u) = u := by
  have hu1 : u - 1 ≠ 0 := sub_ne_zero.mpr hu.2
  rw [cayleyMap, cayleyInv_ofReal hu]
  have hp : Complex.I * (u + 1) / (u - 1) + Complex.I = 2 * Complex.I * u / (u - 1) := by
    field_simp; ring
  have hm : Complex.I * (u + 1) / (u - 1) - Complex.I = 2 * Complex.I / (u - 1) := by
    field_simp; ring
  rw [hp, hm, div_div_div_cancel_right₀ hu1]
  field_simp

/--
`C` is a bijection of `ℝ` onto the unit circle minus `1`.

Blueprint reference: `lmm:cayley-map`.
-/
theorem bijOn_cayleyMap : Set.BijOn cayleyMap Set.univ unitCircleMinusOne :=
  Set.InvOn.bijOn (f' := cayleyInv)
    ⟨fun x _ => cayleyInv_cayleyMap x, fun _ hu => cayleyMap_cayleyInv hu⟩
    (fun x _ => cayleyMap_mem x) (fun _ _ => Set.mem_univ _)

/-!
### The Cayley transform of a self-adjoint operator
-/

/--
`U` is the *Cayley transform* of the self-adjoint operator `A`, built from the bounded
resolvent `B = (A - i 1)⁻¹`: `U ψ = (A + i 1) B ψ`.

Blueprint reference: `thrm:hall-10.28`.
-/
structure IsCayleyTransform (A : H →ₗ.[ℂ] H) (B U : H →L[ℂ] H) : Prop where
  /-- `B` is the bounded two-sided inverse of `A - i 1`. -/
  isResolvent : IsResolvent A Complex.I B
  /-- `U = (A + i 1) B`. -/
  apply_eq : ∀ ψ : H, U ψ = A ⟨B ψ, isResolvent.mem_domain ψ⟩ + Complex.I • B ψ

/--
**The Cayley transform.** For a self-adjoint `A` the point `i` lies in the resolvent set,
and the resulting `U`:

1. is unitary;
2. has `U - 1` injective;
3. has `Range(U - 1) = Dom(A)`, with `A ψ = i (U + 1)(U - 1)⁻¹ ψ` there;
4. satisfies `U - 1 = 2i (A - i 1)⁻¹`.

Blueprint reference: `thrm:hall-10.28`.
-/
theorem exists_isCayleyTransform {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    ∃ B U : H →L[ℂ] H, IsCayleyTransform A B U ∧
      U ∈ unitary (H →L[ℂ] H) ∧
      Function.Injective ⇑(U - 1) ∧
      Set.range ⇑(U - 1) = (A.domain : Set H) ∧
      (∀ (χ : H) (h : (U - 1) χ ∈ A.domain),
        A ⟨(U - 1) χ, h⟩ = Complex.I • (U + 1) χ) ∧
      U - 1 = (2 * Complex.I) • B := by
  sorry

/--
Spectral mapping for the Cayley transform: `λ ∈ σ(A)` iff `C(λ) ∈ σ(U)`, and hence
`C(σ(A)) = σ(U) \ {1}`.

Blueprint reference: `lmm:cayley-spectral-mapping`.
-/
theorem mem_spectrum_iff_cayleyMap_mem_spectrum [Nontrivial H] {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) {B U : H →L[ℂ] H} (hU : IsCayleyTransform A B U) (lam : ℝ) :
    (lam : ℂ) ∈ pmapSpectrum A ↔ cayleyMap lam ∈ spectrum ℂ U := by
  sorry

/--
Consequently `C` maps `σ(A)` onto `σ(U) \ {1}`.

Blueprint reference: `lmm:cayley-spectral-mapping`.
-/
theorem cayleyMap_image_spectrum [Nontrivial H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {B U : H →L[ℂ] H} (hU : IsCayleyTransform A B U) :
    cayleyMap '' {lam : ℝ | (lam : ℂ) ∈ pmapSpectrum A} = spectrum ℂ U \ {1} := by
  sorry

/-!
### Transport of projection-valued measures
-/

section Transport

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]

/--
The restriction of a projection-valued measure to a measurable subset carrying full mass.

Blueprint reference: `lmm:borel-bijection-transports-pvm` (Part 1).
-/
noncomputable def restrictPVM (μ : ProjectionValuedMeasure Y H) {Y₀ : Set Y}
    (hY₀ : MeasurableSet Y₀) (hmass : μ Y₀ᶜ = 0) : ProjectionValuedMeasure Y₀ H where
  toFun E := μ (Subtype.val '' E)
  isStarProjection' := by sorry
  notMeasurable' := by sorry
  univ' := by sorry
  hasSum' := by sorry
  inter' := by sorry

/--
The transport of a projection-valued measure along a measurable bijection with measurable
inverse.

Blueprint reference: `lmm:borel-bijection-transports-pvm` (Part 2).
-/
noncomputable def mapPVM (μ : ProjectionValuedMeasure Y H) (T : Y → Z) (hT : Measurable T)
    (hbij : Function.Bijective T) (_hinv : Measurable (Equiv.ofBijective T hbij).symm) :
    ProjectionValuedMeasure Z H where
  toFun F := μ (T ⁻¹' F)
  isStarProjection' := by sorry
  notMeasurable' := by sorry
  univ' := by sorry
  hasSum' := by sorry
  inter' := by sorry

@[simp]
theorem mapPVM_apply (μ : ProjectionValuedMeasure Y H) (T : Y → Z) (hT : Measurable T)
    (hbij : Function.Bijective T) (hinv : Measurable (Equiv.ofBijective T hbij).symm)
    (F : Set Z) : mapPVM μ T hT hbij hinv F = μ (T ⁻¹' F) := rfl

/--
The scalar measures of the transported projection-valued measure are the pushforwards.

Blueprint reference: `lmm:borel-bijection-transports-pvm` (Part 2).
-/
theorem assoc_mapPVM (μ : ProjectionValuedMeasure Y H) (T : Y → Z) (hT : Measurable T)
    (hbij : Function.Bijective T) (hinv : Measurable (Equiv.ofBijective T hbij).symm) (ψ : H) :
    (mapPVM μ T hT hbij hinv).assoc ψ = (μ.assoc ψ).map T := by
  sorry

end Transport

/-!
### The spectral measure of an unbounded self-adjoint operator
-/

/--
`μ^U` assigns no mass to `{1}`, so `D` — undefined there — is defined almost everywhere
for every `μ^U_ψ`.

Blueprint reference: `lmm:cayley-omits-one`.
-/
theorem spectralMeasure_singleton_one_eq_zero [Nontrivial H] {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) {B U : H →L[ℂ] H} (hU : IsCayleyTransform A B U)
    {μU : ProjectionValuedMeasure (spectrum ℂ U) H}
    (hμU : μU.integral (fun u => (u : ℂ)) = U) :
    μU {u : spectrum ℂ U | (u : ℂ) = 1} = 0 := by
  sorry

/--
`A` is recovered from `U` by integrating `D` against `μ^U`, with equality of domains.

Blueprint reference: `prpstn:hall-10.29`.
-/
theorem pmapIntegral_cayleyInv_eq [Nontrivial H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {B U : H →L[ℂ] H} (hU : IsCayleyTransform A B U)
    {μU : ProjectionValuedMeasure (spectrum ℂ U) H}
    (hμU : μU.integral (fun u => (u : ℂ)) = U) :
    pmapIntegral μU (fun u => ((cayleyInv (u : ℂ) : ℝ) : ℂ)) = A := by
  sorry

/--
The projection-valued measure on `ℝ` obtained by transporting `μ^U` along the Cayley map:
`μ^A(E) = μ^U(C(E))`, spelled as the preimage of `E` under `D`. Non-measurable `E` are sent
to `0`, as a projection-valued measure requires; the preimage of a non-Borel set under `D`
can still carry mass.

Blueprint reference: `thrm:hall-10.30`.
-/
noncomputable def cayleyPVM {U : H →L[ℂ] H} (μU : ProjectionValuedMeasure (spectrum ℂ U) H) :
    ProjectionValuedMeasure ℝ H where
  toFun E := by
    classical
    exact if MeasurableSet E then μU {u : spectrum ℂ U | cayleyInv (u : ℂ) ∈ E} else 0
  isStarProjection' := by sorry
  notMeasurable' := by sorry
  univ' := by sorry
  hasSum' := by sorry
  inter' := by sorry

theorem cayleyPVM_apply {U : H →L[ℂ] H} (μU : ProjectionValuedMeasure (spectrum ℂ U) H)
    {E : Set ℝ} (hE : MeasurableSet E) :
    cayleyPVM μU E = μU {u : spectrum ℂ U | cayleyInv (u : ℂ) ∈ E} := by
  classical
  exact if_pos hE

/--
Transporting the spectral measure of `U` through the Cayley map gives a projection-valued
measure on `ℝ` integrating the identity to `A`.

Blueprint reference: `thrm:hall-10.30`.
-/
theorem pmapIntegral_cayleyPVM_id [Nontrivial H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {B U : H →L[ℂ] H} (hU : IsCayleyTransform A B U)
    {μU : ProjectionValuedMeasure (spectrum ℂ U) H}
    (hμU : μU.integral (fun u => (u : ℂ)) = U) :
    pmapIntegral (cayleyPVM μU) (fun x : ℝ => (x : ℂ)) = A := by
  sorry

/--
**Spectral theorem for unbounded self-adjoint operators.** An unbounded self-adjoint
operator on `H` is the integral of the identity function against a unique projection-valued
measure on `ℝ`.

Blueprint reference: `thrm:hall-10.4`.
-/
theorem existsUnique_spectralMeasure_unbounded {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    ∃! μ : ProjectionValuedMeasure ℝ H,
      pmapIntegral μ (fun x : ℝ => (x : ℂ)) = A := by
  sorry

/--
The spectral measure is concentrated on the spectrum.

Blueprint reference: `thrm:hall-10.4`.
-/
theorem spectralMeasure_concentrated {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {μ : ProjectionValuedMeasure ℝ H} (hμ : pmapIntegral μ (fun x : ℝ => (x : ℂ)) = A) :
    μ {x : ℝ | (x : ℂ) ∉ pmapSpectrum A} = 0 ∧
      ∀ E : Set ℝ, MeasurableSet E → μ E = μ (E ∩ {x : ℝ | (x : ℂ) ∈ pmapSpectrum A}) := by
  sorry

end Unbounded
end Spectral
end Physicslib4
