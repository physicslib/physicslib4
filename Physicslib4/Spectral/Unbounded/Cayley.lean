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
* `spectralMeasure_singleton_one_eq_zero` — `μ^U({1}) = 0`.
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

omit [CompleteSpace H] in
/--
For a symmetric `A` and `ψ ∈ Dom(A)`, `‖(A + i 1) ψ‖ = ‖(A - i 1) ψ‖`: both squares equal
`‖A ψ‖² + ‖ψ‖²`, the cross terms cancelling by symmetry.

Blueprint reference: `thrm:hall-10.28`.
-/
theorem norm_add_I_smul_eq_norm_sub_I_smul {A : H →ₗ.[ℂ] H} (hsym : IsSymmetric A)
    (ψ : A.domain) : ‖A ψ + Complex.I • (ψ : H)‖ = ‖A ψ - Complex.I • (ψ : H)‖ := by
  have him : (⟪A ψ, (ψ : H)⟫_ℂ).im = 0 := by
    have h := congrArg Complex.im (inner_conj_symm (𝕜 := ℂ) (A ψ) (ψ : H))
    rw [hsym ψ ψ, Complex.conj_im] at h
    linarith
  have hcross : RCLike.re ⟪A ψ, Complex.I • (ψ : H)⟫_ℂ = 0 := by
    rw [inner_smul_right]; simp [him]
  have h1 := @norm_add_sq ℂ _ _ _ _ (A ψ) (Complex.I • (ψ : H))
  have h2 := @norm_sub_sq ℂ _ _ _ _ (A ψ) (Complex.I • (ψ : H))
  rw [hcross] at h1 h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by linarith)

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
  have hsym : IsSymmetric A :=
    (isSymmetric_iff_le_adjoint hA.dense_domain).mpr (LinearPMap.isSelfAdjoint_def.mp hA).ge
  obtain ⟨B, hB⟩ := mem_pmapResolventSet_of_im_ne_zero hA (lam := Complex.I) (by simp)
  obtain ⟨B', hB'⟩ := mem_pmapResolventSet_of_im_ne_zero hA (lam := -Complex.I) (by simp)
  have happly : ∀ ψ : H, (1 + (2 * Complex.I) • B) ψ =
      A ⟨B ψ, hB.mem_domain ψ⟩ + Complex.I • B ψ := fun ψ => by
    have h := hB.rightInverse ψ
    rw [add_apply, one_apply_eq_self, smul_apply]
    linear_combination (norm := module) (-1 : ℂ) • h
  set U : H →L[ℂ] H := 1 + (2 * Complex.I) • B with hUdef
  have hU1 : U - 1 = (2 * Complex.I) • B := by rw [hUdef]; abel
  have hBinj : Function.Injective B := fun x y hxy => by
    rw [← hB.rightInverse x, ← hB.rightInverse y]; simp_rw [hxy]
  have hnorm : ∀ ψ, ‖U ψ‖ = ‖ψ‖ := fun ψ => by
    rw [happly]
    exact (norm_add_I_smul_eq_norm_sub_I_smul hsym ⟨B ψ, hB.mem_domain ψ⟩).trans
      (congrArg norm (hB.rightInverse ψ))
  have hsurj : Function.Surjective U := fun φ => by
    refine ⟨A ⟨B' φ, hB'.mem_domain φ⟩ - Complex.I • B' φ, ?_⟩
    have h := hB.leftInverse ⟨B' φ, hB'.mem_domain φ⟩
    simp only at h
    rw [happly]
    simp_rw [h]
    simpa [sub_eq_add_neg] using hB'.rightInverse φ
  refine ⟨B, U, ⟨hB, happly⟩, ?_, ?_, ?_, ?_, hU1⟩
  · let e : H ≃ₗᵢ[ℂ] H :=
      LinearIsometryEquiv.ofSurjective ⟨(U : H →ₗ[ℂ] H), hnorm⟩ hsurj
    exact (Unitary.linearIsometryEquiv.symm e).2
  · rw [hU1]
    exact fun x y hxy => hBinj (smul_right_injective H (by simp) hxy)
  · ext x
    rw [hU1]
    refine ⟨?_, fun hx => ?_⟩
    · rintro ⟨y, rfl⟩
      exact A.domain.smul_mem _ (hB.mem_domain y)
    · refine ⟨(2 * Complex.I)⁻¹ • (A ⟨x, hx⟩ - Complex.I • x), ?_⟩
      rw [smul_apply, map_smul, hB.leftInverse ⟨x, hx⟩, smul_inv_smul₀ (by simp)]
  · intro χ h
    have hx : (⟨(U - 1) χ, h⟩ : A.domain) = (2 * Complex.I) • ⟨B χ, hB.mem_domain χ⟩ := by
      ext; simp [hU1]
    have h1 := hB.rightInverse χ
    rw [hx, LinearPMap.map_smul, add_apply, one_apply_eq_self, happly]
    linear_combination (norm := module) Complex.I • h1

omit [CompleteSpace H] in
/--
The Cayley factorisation `U - c 1 = (1 - c)(A - z 1)(A - i 1)⁻¹`, with `c = (z + i)/(z - i)`,
transfers resolvents: `z` is in the resolvent set of `A` iff `c` is in that of `U`, for
every complex `z ≠ i`.

Blueprint reference: `lmm:cayley-spectral-mapping`.
-/
private theorem mem_pmapResolventSet_iff_cayley {A : H →ₗ.[ℂ] H} {B U : H →L[ℂ] H}
    (hU : IsCayleyTransform A B U) {z : ℂ} (hz : z ≠ Complex.I) :
    z ∈ pmapResolventSet A ↔ (z + Complex.I) / (z - Complex.I) ∈ resolventSet ℂ U := by
  set c := (z + Complex.I) / (z - Complex.I)
  have hzi : z - Complex.I ≠ 0 := sub_ne_zero.mpr hz
  set k : ℂ := 1 - c
  have hk : k ≠ 0 := by
    have : k = -2 * Complex.I / (z - Complex.I) := by simp only [k, c]; field_simp; ring
    rw [this]; exact div_ne_zero (by simp) hzi
  have hs : Complex.I + c * Complex.I = -(k * z) := by simp only [k, c]; field_simp; ring
  have hB := hU.isResolvent
  -- The key identity `(U - c) ψ = k (A - z) B ψ`.
  have key : ∀ ψ : H, U ψ - c • ψ = k • (A ⟨B ψ, hB.mem_domain ψ⟩ - z • B ψ) := by
    intro ψ
    have hψ := hB.rightInverse ψ
    have h1 : U ψ - c • ψ = (A ⟨B ψ, hB.mem_domain ψ⟩ + Complex.I • B ψ) -
        c • (A ⟨B ψ, hB.mem_domain ψ⟩ - Complex.I • B ψ) := by rw [hU.apply_eq, hψ]
    rw [h1]
    linear_combination (norm := module) hs • B ψ
  -- On `Dom(A)`: `(U - c)(A - i) φ = k (A - z) φ`.
  have key' : ∀ φ : A.domain, U (A φ - Complex.I • (φ : H)) - c • (A φ - Complex.I • (φ : H)) =
      k • (A φ - z • (φ : H)) := by
    intro φ
    rw [key]
    have hφ : (⟨B (A φ - Complex.I • (φ : H)), hB.mem_domain _⟩ : A.domain) = φ :=
      Subtype.ext (hB.leftInverse φ)
    rw [hφ, hB.leftInverse φ]
  rw [← pmapResolventSet_toPMap_top]
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨k⁻¹ • (1 + (z - Complex.I) • R), fun _ => Submodule.mem_top, fun ψ => ?_,
      fun ψ => ?_⟩
    · change U (k⁻¹ • (ψ + (z - Complex.I) • R ψ)) - c • (k⁻¹ • (ψ + (z - Complex.I) • R ψ)) = ψ
      have hψ := hR.rightInverse ψ
      set φ : A.domain := ⟨R ψ, hR.mem_domain ψ⟩
      have e : ψ + (z - Complex.I) • R ψ = A φ - Complex.I • (φ : H) := by
        change _ = A φ - Complex.I • R ψ
        linear_combination (norm := module) -hψ
      rw [e, map_smul, smul_comm c k⁻¹, ← smul_sub, key', hψ, smul_smul, inv_mul_cancel₀ hk,
        one_smul]
    · change k⁻¹ • ((U ψ - c • ψ) + (z - Complex.I) • R (U ψ - c • ψ)) = ψ
      have hl : R (A ⟨B ψ, hB.mem_domain ψ⟩ - z • B ψ) = B ψ := hR.leftInverse _
      rw [key, map_smul, hl, smul_comm (z - Complex.I) k, ← smul_add, smul_smul,
        inv_mul_cancel₀ hk, one_smul]
      conv_rhs => rw [← hB.rightInverse ψ]
      module
  · rintro ⟨T, hT⟩
    have hTr : ∀ ψ, U (T ψ) - c • T ψ = ψ := hT.rightInverse
    have hTl : ∀ w, T (U w - c • w) = w := fun w => hT.leftInverse ⟨w, Submodule.mem_top⟩
    refine ⟨(k • B).comp T, fun ψ => A.domain.smul_mem k (hB.mem_domain (T ψ)),
      fun ψ => ?_, fun φ => ?_⟩
    · have e : (⟨((k • B).comp T) ψ, A.domain.smul_mem k (hB.mem_domain (T ψ))⟩ : A.domain) =
          k • ⟨B (T ψ), hB.mem_domain (T ψ)⟩ := rfl
      rw [e, LinearPMap.map_smul]
      change k • A ⟨B (T ψ), _⟩ - z • (k • B (T ψ)) = ψ
      rw [smul_comm z k, ← smul_sub, ← key, hTr]
    · have h2 : T (k • (A φ - z • (φ : H))) = A φ - Complex.I • (φ : H) := by
        rw [← key' φ]; exact hTl _
      change k • B (T (A φ - z • (φ : H))) = φ
      rw [← map_smul B, ← map_smul T, h2]
      exact hB.leftInverse φ

/--
Spectral mapping for the Cayley transform: `λ ∈ σ(A)` iff `C(λ) ∈ σ(U)`, and hence
`C(σ(A)) = σ(U) \ {1}`.

Blueprint reference: `lmm:cayley-spectral-mapping`.
-/
theorem mem_spectrum_iff_cayleyMap_mem_spectrum {A : H →ₗ.[ℂ] H}
    (_hA : IsSelfAdjoint A) {B U : H →L[ℂ] H} (hU : IsCayleyTransform A B U) (lam : ℝ) :
    (lam : ℂ) ∈ pmapSpectrum A ↔ cayleyMap lam ∈ spectrum ℂ U :=
  not_congr (mem_pmapResolventSet_iff_cayley hU fun h => by simpa using congrArg Complex.im h)

/--
Consequently `C` maps `σ(A)` onto `σ(U) \ {1}`.

Blueprint reference: `lmm:cayley-spectral-mapping`.
-/
theorem cayleyMap_image_spectrum {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {B U : H →L[ℂ] H} (hU : IsCayleyTransform A B U) :
    cayleyMap '' {lam : ℝ | (lam : ℂ) ∈ pmapSpectrum A} = spectrum ℂ U \ {1} := by
  ext u
  constructor
  · rintro ⟨lam, hlam, rfl⟩
    exact ⟨(mem_spectrum_iff_cayleyMap_mem_spectrum hA hU lam).mp hlam, (cayleyMap_mem lam).2⟩
  · rintro ⟨hu, hu1⟩
    have hu1' : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
    set z : ℂ := Complex.I * (u + 1) / (u - 1)
    have hzi : z - Complex.I = 2 * Complex.I / (u - 1) := by simp only [z]; field_simp; ring
    have hz : z ≠ Complex.I := fun h => by
      have := hzi; rw [h, sub_self] at this
      exact (div_ne_zero (by simp) hu1') this.symm
    have hcz : (z + Complex.I) / (z - Complex.I) = u := by
      have hp : z + Complex.I = 2 * Complex.I * u / (u - 1) := by simp only [z]; field_simp; ring
      rw [hp, hzi, div_div_div_cancel_right₀ hu1']
      field_simp
    have hzA : z ∈ pmapSpectrum A := fun h =>
      hu (hcz ▸ (mem_pmapResolventSet_iff_cayley hU hz).mp h)
    have hre : ((z.re : ℝ) : ℂ) = z :=
      Complex.ext rfl (by simpa using (pmapSpectrum_subset_real hA hzA).symm)
    refine ⟨z.re, by simpa [hre] using hzA, ?_⟩
    change ((z.re : ℂ) + Complex.I) / ((z.re : ℂ) - Complex.I) = u
    rw [hre, hcz]

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
  isStarProjection' E := μ.isStarProjection_apply _
  notMeasurable' E hE := μ.apply_of_not_measurableSet fun h =>
    hE (Set.preimage_image_eq E Subtype.val_injective ▸ measurable_subtype_coe h)
  univ' := by
    have hempty : μ (∅ : Set Y) = 0 := by
      rw [← Set.inter_empty Y₀ᶜ, μ.apply_inter hY₀.compl MeasurableSet.empty, hmass, zero_mul]
    ext v
    let E : ℕ → Set Y := fun j => if j = 0 then Y₀ else if j = 1 then Y₀ᶜ else ∅
    have hE : ∀ j, MeasurableSet (E j) := fun j => by
      simp only [E]; split_ifs <;> simp [hY₀, hY₀.compl]
    have hdisj : Pairwise (fun i j => Disjoint (E i) (E j)) := by
      intro i j hij
      simp only [E]
      split_ifs <;> first | omega | simp [disjoint_compl_right, disjoint_compl_left]
    have hU : (⋃ j, E j) = Set.univ := by
      refine Set.eq_univ_of_forall fun y => Set.mem_iUnion.mpr ?_
      by_cases hy : y ∈ Y₀
      · exact ⟨0, by simp [E, hy]⟩
      · exact ⟨1, by simp [E, hy]⟩
    have h := μ.hasSum_apply E hE hdisj v
    rw [hU] at h
    have hf : (fun j => μ (E j) v) = fun j => if j = 0 then μ Y₀ v else 0 := by
      funext j
      simp only [E]
      split_ifs <;> simp [hmass, hempty]
    rw [hf] at h
    simpa using (h.unique (hasSum_ite_eq 0 (μ Y₀ v))).symm
  hasSum' E hE hdisj v := by
    have h := μ.hasSum_apply (fun j => Subtype.val '' E j)
      (fun j => hY₀.subtype_image (hE j))
      (fun i j hij => (hdisj hij).image Set.injOn_subtype_val (Set.subset_univ _)
        (Set.subset_univ _)) v
    rwa [← Set.image_iUnion] at h
  inter' E F hE hF := by
    simp only [Set.image_inter Subtype.val_injective]
    exact μ.apply_inter (hY₀.subtype_image hE) (hY₀.subtype_image hF)

/--
The transport of a projection-valued measure along a measurable bijection with measurable
inverse.

Blueprint reference: `lmm:borel-bijection-transports-pvm` (Part 2).
-/
noncomputable def mapPVM (μ : ProjectionValuedMeasure Y H) (T : Y → Z) (hT : Measurable T)
    (hbij : Function.Bijective T) (_hinv : Measurable (Equiv.ofBijective T hbij).symm) :
    ProjectionValuedMeasure Z H where
  toFun F := μ (T ⁻¹' F)
  isStarProjection' F := μ.isStarProjection_apply _
  notMeasurable' F hF := μ.apply_of_not_measurableSet fun h => hF <| by
    have := _hinv h
    rwa [← Set.preimage_comp, show T ∘ (Equiv.ofBijective T hbij).symm = id from
      funext (Equiv.ofBijective T hbij).apply_symm_apply, Set.preimage_id] at this
  univ' := μ.apply_univ
  hasSum' F hF hdisj v := by
    simpa [Set.preimage_iUnion] using
      μ.hasSum_apply (fun j => T ⁻¹' F j) (fun j => hT (hF j))
        (fun i j hij => (hdisj hij).preimage T) v
  inter' E F hE hF := μ.apply_inter (hT hE) (hT hF)

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
  ext F hF
  rw [Measure.map_apply hT hF, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (measure_ne_top _ _), ProjectionValuedMeasure.assoc_apply _ _ hF,
    ProjectionValuedMeasure.assoc_apply _ _ (hT hF), mapPVM_apply]

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
    (_hA : IsSelfAdjoint A) {B U : H →L[ℂ] H} (hU : IsCayleyTransform A B U)
    {μU : ProjectionValuedMeasure (spectrum ℂ U) H}
    (hμU : μU.integral (fun u => (u : ℂ)) = U) :
    μU {u : spectrum ℂ U | (u : ℂ) = 1} = 0 := by
  set E : Set (spectrum ℂ U) := {u | (u : ℂ) = 1}
  have hE : MeasurableSet E := measurable_subtype_coe (measurableSet_singleton (1 : ℂ))
  have hid : (fun u : spectrum ℂ U => (u : ℂ)) ∈ BddMeasurable (spectrum ℂ U) :=
    mem_bddMeasurable.mpr ⟨measurable_subtype_coe, ‖U‖, fun u => spectrum.norm_le_norm_of_mem u.2⟩
  have hind : E.indicator (1 : spectrum ℂ U → ℂ) ∈ BddMeasurable (spectrum ℂ U) :=
    mem_bddMeasurable.mpr ⟨measurable_const.indicator hE, 1, fun u => by
      by_cases hu : u ∈ E
      · simp [Set.indicator_of_mem hu]
      · simp [Set.indicator_of_notMem hu]⟩
  have hfun : (fun u : spectrum ℂ U => (u : ℂ)) * E.indicator 1 = E.indicator 1 := by
    funext u
    by_cases hu : u ∈ E
    · simp [Set.indicator_of_mem hu, show (u : ℂ) = 1 from hu]
    · simp [Set.indicator_of_notMem hu]
  have hUP : U * μU E = μU E := by
    calc U * μU E = μU.integral (fun u => (u : ℂ)) * μU.integral (E.indicator 1) := by
          rw [hμU, μU.integral_indicator hE]
      _ = μU E := by rw [← μU.integral_mul hid hind, hfun, μU.integral_indicator hE]
  -- `U - 1` is injective: `U ψ = ψ` forces `B ψ = 0`, hence `ψ = 0`.
  have hinj : ∀ ψ : H, U ψ = ψ → ψ = 0 := by
    intro ψ h
    have h1 := hU.apply_eq ψ
    have h2 := hU.isResolvent.rightInverse ψ
    have hB : B ψ = 0 := by
      generalize A ⟨B ψ, _⟩ = a at h1 h2
      have e : (2 * Complex.I) • B ψ = (a + Complex.I • B ψ) - (a - Complex.I • B ψ) := by
        rw [mul_smul, two_smul]; abel
      rw [← h1, h, h2, sub_self] at e
      exact (smul_eq_zero.mp e).resolve_left (by simp)
    rw [← h2]
    have : (⟨B ψ, hU.isResolvent.mem_domain ψ⟩ : A.domain) = 0 := Subtype.ext hB
    rw [this, hB]
    simp
  ext ψ
  simp only [zero_apply]
  exact hinj _ (by simpa using congrArg (fun T => T ψ) hUP)

/-- `D` is Borel measurable on all of `ℂ`. -/
theorem measurable_cayleyInv : Measurable cayleyInv :=
  Complex.measurable_re.comp
    ((measurable_const.mul (measurable_id.add_const 1)).div (measurable_id.sub_const 1))

/-- A self-adjoint operator has no proper self-adjoint extension. -/
theorem eq_of_le_of_isSelfAdjoint {T S : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T)
    (hS : IsSelfAdjoint S) (h : T ≤ S) : T = S := by
  have hadj := adjoint_le_adjoint_of_le hT.dense_domain h
  rw [LinearPMap.isSelfAdjoint_def.mp hS, LinearPMap.isSelfAdjoint_def.mp hT] at hadj
  exact le_antisymm h hadj

omit [CompleteSpace H] in
/-- The Cayley transform `U` is determined by `A`. -/
theorem IsCayleyTransform.unitary_eq {A : H →ₗ.[ℂ] H} {B U B' U' : H →L[ℂ] H}
    (hU : IsCayleyTransform A B U) (hU' : IsCayleyTransform A B' U') : U = U' := by
  obtain rfl : B = B' := (existsUnique_isResolvent ⟨B, hU.isResolvent⟩).unique
    hU.isResolvent hU'.isResolvent
  exact ContinuousLinearMap.ext fun ψ => by rw [hU.apply_eq, hU'.apply_eq]

/--
For unitary `U` with `μ^U({1}) = 0` and `ψ = (U - 1) χ`: `ψ ∈ W_D` and
`(∫ D dμ^U) ψ = i (U + 1) χ`, since `D(u) (u - 1) = i (u + 1)` off `u = 1`.
-/
theorem pmapIntegral_cayleyInv_apply_sub_one {U : H →L[ℂ] H} (hUu : U ∈ unitary (H →L[ℂ] H))
    {μU : ProjectionValuedMeasure (spectrum ℂ U) H}
    (hμU : μU.integral (fun u => (u : ℂ)) = U)
    (h1 : μU {u : spectrum ℂ U | (u : ℂ) = 1} = 0) (χ : H) :
    ∃ hψ : (U - 1) χ ∈ integralDomain μU (fun u => ((cayleyInv (u : ℂ) : ℝ) : ℂ)),
      pmapIntegral μU (fun u => ((cayleyInv (u : ℂ) : ℝ) : ℂ)) ⟨(U - 1) χ, hψ⟩ =
        Complex.I • (U + 1) χ := by
  set D : spectrum ℂ U → ℂ := fun u => ((cayleyInv (u : ℂ) : ℝ) : ℂ)
  have hsph : ∀ u : spectrum ℂ U, ‖(u : ℂ)‖ = 1 := fun u => by
    simpa using spectrum.subset_circle_of_unitary (𝕜 := ℂ) hUu u.2
  have hDm : Measurable D :=
    Complex.measurable_ofReal.comp (measurable_cayleyInv.comp measurable_subtype_coe)
  set h : spectrum ℂ U → ℂ := fun u => (u : ℂ) - 1
  set g : spectrum ℂ U → ℂ := fun u => Complex.I * ((u : ℂ) + 1)
  have hid : (fun u : spectrum ℂ U => (u : ℂ)) ∈ BddMeasurable (spectrum ℂ U) :=
    ⟨measurable_subtype_coe, 1, fun u => (hsph u).le⟩
  have hone : (1 : spectrum ℂ U → ℂ) ∈ BddMeasurable (spectrum ℂ U) :=
    ⟨measurable_const, 1, fun u => by simp⟩
  have hh' : h = (fun u : spectrum ℂ U => (u : ℂ)) + (-1 : ℂ) • 1 := by
    funext u; simp [h, sub_eq_add_neg]
  have hg' : g = Complex.I • ((fun u : spectrum ℂ U => (u : ℂ)) + 1) := by
    funext u; simp [g]
  have hh : h ∈ BddMeasurable (spectrum ℂ U) :=
    hh' ▸ (BddMeasurable _).add_mem hid ((BddMeasurable _).smul_mem _ hone)
  have hg : g ∈ BddMeasurable (spectrum ℂ U) :=
    hg' ▸ (BddMeasurable _).smul_mem _ ((BddMeasurable _).add_mem hid hone)
  have hhint : μU.integral h = U - 1 := by
    rw [hh', μU.integral_add hid ((BddMeasurable _).smul_mem _ hone), μU.integral_smul _ hone,
      μU.integral_one, hμU, neg_one_smul, sub_eq_add_neg]
  have hgint : μU.integral g = Complex.I • (U + 1) := by
    rw [hg', μU.integral_smul _ ((BddMeasurable _).add_mem hid hone),
      μU.integral_add hid hone, μU.integral_one, hμU]
  -- pointwise facts
  have hDh : ∀ u : spectrum ℂ U, (u : ℂ) ≠ 1 → D u * h u = g u := fun u hu => by
    have hu1 : (u : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hu
    simp only [D, h, g, cayleyInv_ofReal (⟨hsph u, hu⟩ : (u : ℂ) ∈ unitCircleMinusOne)]
    field_simp
  have hgb : ∀ u, ‖g u‖ ≤ 2 := fun u => by
    simp only [g, norm_mul, Complex.norm_I, one_mul]
    exact (norm_add_le _ _).trans (by rw [hsph u, norm_one]; norm_num)
  have hDhb : ∀ u, ‖D u * h u‖ ≤ 2 := fun u => by
    by_cases hu : (u : ℂ) = 1
    · simp [h, hu]
    · rw [hDh u hu]; exact hgb u
  rw [← hhint]
  have hmem : μU.integral h χ ∈ integralDomain μU D := by
    refine ⟨hDm.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top,
      lintegral_assoc_integral_apply μU hh χ (hDm.enorm.pow_const _)]
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_ :
      _ ≤ ∫⁻ _, ENNReal.ofReal ((2 : ℝ) ^ 2) ∂(μU.assoc χ)) ?_
    · rw [← enorm_eq_nnnorm, ← ofReal_norm, ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [ENNReal.toReal_ofNat, Real.rpow_two, ← mul_pow, ← norm_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) (hDhb x) 2
    · rw [lintegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  refine ⟨hmem, ?_⟩
  -- `(∫ Dₙ dμ) ψ - i (U + 1) χ = (∫ (Dₙ h - g) dμ) χ → 0` for the truncations `Dₙ`
  set F : ℕ → spectrum ℂ U → ℂ := fun n => {x | ‖D x‖ < n}.indicator D
  have hF : ∀ n, F n ∈ BddMeasurable _ := indicator_lt_mem_bddMeasurable hDm
  have hFhb : ∀ n x, ‖F n x * h x‖ ≤ 2 := fun n x => by
    refine le_trans ?_ (hDhb x)
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    by_cases hx : ‖D x‖ < n <;> simp [F, hx]
  have hFh : ∀ n, F n * h ∈ BddMeasurable _ := fun n => ⟨(hF n).1.mul hh.1, 2, hFhb n⟩
  set k : ℕ → spectrum ℂ U → ℂ := fun n => F n * h + (-1 : ℂ) • g
  have hk : ∀ n, k n ∈ BddMeasurable _ := fun n =>
    (BddMeasurable _).add_mem (hFh n) ((BddMeasurable _).smul_mem _ hg)
  have hkey : ∀ n, μU.integral (F n) (μU.integral h χ) - Complex.I • (U + 1) χ =
      μU.integral (k n) χ := fun n => by
    rw [μU.integral_add (hFh n) ((BddMeasurable _).smul_mem _ hg), μU.integral_smul _ hg,
      μU.integral_mul (hF n) hh, hgint]
    simp only [add_apply, neg_apply, smul_apply, mul_apply_eq_comp, neg_one_smul,
      sub_eq_add_neg]
  have hkb : ∀ n x, ‖k n x‖ ≤ 4 := fun n x => by
    simp only [k, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
    refine (norm_add_le _ _).trans ?_
    rw [neg_one_mul, norm_neg]
    linarith [hFhb n x, hgb x]
  have hN : MeasurableSet {u : spectrum ℂ U | (u : ℂ) = 1} :=
    (measurableSet_singleton (1 : ℂ)).preimage measurable_subtype_coe
  have h1χ : μU.assoc χ {u : spectrum ℂ U | (u : ℂ) = 1} = 0 := by
    rw [assoc_apply_eq_norm_sq μU χ hN, h1]; simp
  have hae : ∀ᵐ x : spectrum ℂ U ∂(μU.assoc χ), (x : ℂ) ≠ 1 :=
    ae_iff.2 (measure_mono_null (fun x hx => not_not.mp hx) h1χ)
  have hsq : Tendsto (fun n => ∫ x, ‖k n x‖ ^ 2 ∂(μU.assoc χ)) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := μU.assoc χ)
      (F := fun n x => ‖k n x‖ ^ 2) (f := fun _ => (0 : ℝ)) (fun _ => (4 : ℝ) ^ 2)
      (fun n => ((hk n).1.norm.pow_const 2).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hkb n x) 2)
      (by
        filter_upwards [hae] with x hx
        obtain ⟨N, hN⟩ := exists_nat_gt ‖D x‖
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        have : ‖D x‖ < n := hN.trans_le (by exact_mod_cast hn)
        simp [k, F, this, hDh x hx])
    simpa using this
  have hlim : Tendsto (fun n => μU.integral (F n) (μU.integral h χ) -
      Complex.I • (U + 1) χ) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hn : ∀ n, ‖μU.integral (F n) (μU.integral h χ) - Complex.I • (U + 1) χ‖ =
        Real.sqrt (∫ x, ‖k n x‖ ^ 2 ∂(μU.assoc χ)) := fun n => by
      rw [hkey, ← norm_sq_integral_apply μU (hk n), Real.sqrt_sq (norm_nonneg _)]
    simp_rw [hn]
    simpa using hsq.sqrt
  have h2 := (tendsto_integral_truncation μU hDm ⟨_, hmem⟩).sub_const (Complex.I • (U + 1) χ)
  exact sub_eq_zero.mp (tendsto_nhds_unique h2 hlim)

/--
`A` is recovered from `U` by integrating `D` against `μ^U`, with equality of domains.

Blueprint reference: `prpstn:hall-10.29`.
-/
theorem pmapIntegral_cayleyInv_eq [Nontrivial H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {B U : H →L[ℂ] H} (hU : IsCayleyTransform A B U)
    {μU : ProjectionValuedMeasure (spectrum ℂ U) H}
    (hμU : μU.integral (fun u => (u : ℂ)) = U) :
    pmapIntegral μU (fun u => ((cayleyInv (u : ℂ) : ℝ) : ℂ)) = A := by
  obtain ⟨B', U', hU', hUu, -, hran, hAeq, -⟩ := exists_isCayleyTransform hA
  obtain rfl := hU'.unitary_eq hU
  have hD : Measurable fun u : spectrum ℂ U' => ((cayleyInv (u : ℂ) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_cayleyInv.comp measurable_subtype_coe)
  have key := pmapIntegral_cayleyInv_apply_sub_one hUu hμU
    (spectralMeasure_singleton_one_eq_zero hA hU hμU)
  refine (eq_of_le_of_isSelfAdjoint hA
    (isSelfAdjoint_pmapIntegral_of_real μU hD fun u => Complex.ofReal_im _) ⟨fun x hx => ?_,
      fun x y hxy => ?_⟩).symm
  · obtain ⟨χ, rfl⟩ : x ∈ Set.range ⇑(U' - 1) := hran ▸ hx
    exact (key χ).1
  · obtain ⟨χ, hχ⟩ : (x : H) ∈ Set.range ⇑(U' - 1) := hran ▸ x.2
    obtain ⟨hψ, he⟩ := key χ
    have hx : A x = A ⟨(U' - 1) χ, hχ ▸ x.2⟩ := congrArg A (Subtype.ext hχ.symm)
    have hy : y = ⟨(U' - 1) χ, hψ⟩ := Subtype.ext (hxy.symm.trans hχ.symm)
    rw [hx, hAeq, hy, he]

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
  isStarProjection' E := by
    split_ifs
    · exact μU.isStarProjection_apply _
    · exact IsStarProjection.zero _
  notMeasurable' E hE := if_neg hE
  univ' := by simp
  hasSum' E hE hdisj v := by
    have hD : Measurable fun u : spectrum ℂ U => cayleyInv (u : ℂ) := by
      unfold cayleyInv; fun_prop
    simp only [hE, MeasurableSet.iUnion hE, if_true]
    convert μU.hasSum_apply (fun j => {u : spectrum ℂ U | cayleyInv (u : ℂ) ∈ E j})
      (fun j => hD (hE j)) (fun i j hij => (hdisj hij).preimage _) v using 3
    ext u
    simp
  inter' E F hE hF := by
    have hD : Measurable fun u : spectrum ℂ U => cayleyInv (u : ℂ) := by
      unfold cayleyInv; fun_prop
    simp only [hE, hF, hE.inter hF, if_true]
    exact μU.apply_inter (hD hE) (hD hF)

theorem cayleyPVM_apply {U : H →L[ℂ] H} (μU : ProjectionValuedMeasure (spectrum ℂ U) H)
    {E : Set ℝ} (hE : MeasurableSet E) :
    cayleyPVM μU E = μU {u : spectrum ℂ U | cayleyInv (u : ℂ) ∈ E} := by
  classical
  exact if_pos hE

/-- The scalar measures of `μ^A` are the pushforwards of those of `μ^U` along `D`. -/
theorem assoc_cayleyPVM {U : H →L[ℂ] H} (μU : ProjectionValuedMeasure (spectrum ℂ U) H)
    (ψ : H) :
    (cayleyPVM μU).assoc ψ = (μU.assoc ψ).map fun u : spectrum ℂ U => cayleyInv (u : ℂ) := by
  have hD : Measurable fun u : spectrum ℂ U => cayleyInv (u : ℂ) :=
    measurable_cayleyInv.comp measurable_subtype_coe
  ext E hE
  rw [Measure.map_apply hD hE, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (measure_ne_top _ _), ProjectionValuedMeasure.assoc_apply _ _ hE,
    ProjectionValuedMeasure.assoc_apply _ _ (hD hE), cayleyPVM_apply μU hE]
  rfl

/-- `∫ λ dμ^A = ∫ D dμ^U`, with equality of domains, by change of variables. -/
theorem pmapIntegral_cayleyPVM_id_eq {U : H →L[ℂ] H}
    (μU : ProjectionValuedMeasure (spectrum ℂ U) H) :
    pmapIntegral (cayleyPVM μU) (fun x : ℝ => (x : ℂ)) =
      pmapIntegral μU (fun u => ((cayleyInv (u : ℂ) : ℝ) : ℂ)) := by
  have hD : Measurable fun u : spectrum ℂ U => cayleyInv (u : ℂ) :=
    measurable_cayleyInv.comp measurable_subtype_coe
  have hdom : integralDomain μU (fun u => ((cayleyInv (u : ℂ) : ℝ) : ℂ)) =
      integralDomain (cayleyPVM μU) (fun x : ℝ => (x : ℂ)) := by
    ext ψ
    rw [mem_integralDomain, mem_integralDomain, assoc_cayleyPVM,
      memLp_map_measure_iff Complex.measurable_ofReal.aestronglyMeasurable hD.aemeasurable]
    rfl
  refine (eq_pmapIntegral_of_inner_self _ Complex.measurable_ofReal _ hdom fun ψ => ?_).symm
  have hDc : Measurable fun u : spectrum ℂ U => ((cayleyInv (u : ℂ) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp hD
  rw [inner_self_pmapIntegral _ hDc, assoc_cayleyPVM,
    integral_map hD.aemeasurable Complex.measurable_ofReal.aestronglyMeasurable]

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
  rw [pmapIntegral_cayleyPVM_id_eq, pmapIntegral_cayleyInv_eq hA hU hμU]

section Pushforward

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]

/--
The push-forward of a projection-valued measure along a measurable map (not necessarily
bijective): `F ↦ μ(T⁻¹ F)` on measurable `F`, and `0` elsewhere.

Blueprint reference: `thrm:hall-10.4` (Step 3 of the uniqueness proof).
-/
noncomputable def pushforwardPVM (μ : ProjectionValuedMeasure Y H) (T : Y → Z)
    (hT : Measurable T) : ProjectionValuedMeasure Z H where
  toFun F := by
    classical
    exact if MeasurableSet F then μ (T ⁻¹' F) else 0
  isStarProjection' F := by
    split_ifs
    · exact μ.isStarProjection_apply _
    · exact IsStarProjection.zero _
  notMeasurable' F hF := if_neg hF
  univ' := by simp
  hasSum' E hE hdisj v := by
    simp only [hE, MeasurableSet.iUnion hE, if_true, Set.preimage_iUnion]
    exact μ.hasSum_apply _ (fun j => hT (hE j)) (fun i j hij => (hdisj hij).preimage T) v
  inter' E F hE hF := by
    simp only [hE, hF, hE.inter hF, if_true, Set.preimage_inter]
    exact μ.apply_inter (hT hE) (hT hF)

theorem pushforwardPVM_apply (μ : ProjectionValuedMeasure Y H) {T : Y → Z}
    (hT : Measurable T) {F : Set Z} (hF : MeasurableSet F) :
    pushforwardPVM μ T hT F = μ (T ⁻¹' F) := by
  classical
  exact if_pos hF

/-- Change of variables for the bounded integral: `∫ g d(T_* μ) = ∫ g ∘ T dμ`. -/
theorem integral_pushforwardPVM (μ : ProjectionValuedMeasure Y H) {T : Y → Z}
    (hT : Measurable T) {g : Z → ℂ} (hg : g ∈ BddMeasurable Z) :
    (pushforwardPVM μ T hT).integral g = μ.integral (g ∘ T) := by
  have hgT : g ∘ T ∈ BddMeasurable Y :=
    ⟨hg.1.comp hT, hg.2.choose, fun y => hg.2.choose_spec (T y)⟩
  have hassoc : ∀ ψ : H, (pushforwardPVM μ T hT).assoc ψ = (μ.assoc ψ).map T := fun ψ => by
    ext F hF
    rw [Measure.map_apply hT hF, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (measure_ne_top _ _), ProjectionValuedMeasure.assoc_apply _ _ hF,
      ProjectionValuedMeasure.assoc_apply _ _ (hT hF), pushforwardPVM_apply μ hT hF]
  refine ContinuousLinearMap.coe_injective ((ext_inner_map _ _).mp fun ψ => ?_)
  change ⟪(pushforwardPVM μ T hT).integral g ψ, ψ⟫_ℂ = ⟪μ.integral (g ∘ T) ψ, ψ⟫_ℂ
  rw [← inner_conj_symm]
  conv_rhs => rw [← inner_conj_symm]
  rw [ProjectionValuedMeasure.inner_integral _ hg, hassoc,
    integral_map hT.aemeasurable hg.1.aestronglyMeasurable,
    ProjectionValuedMeasure.inner_integral _ hgT]
  rfl

end Pushforward

/--
If `∫ λ dμ = A` and `B = (A - i 1)⁻¹`, then `∫ (λ - i)⁻¹ dμ = B`.

Blueprint reference: `thrm:hall-10.4` (Step 1 of the uniqueness proof).
-/
theorem integral_inv_sub_I_eq_resolvent {A : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hB : IsResolvent A Complex.I B) {μ : ProjectionValuedMeasure ℝ H}
    (hμ : pmapIntegral μ (fun x : ℝ => (x : ℂ)) = A) :
    μ.integral (fun x : ℝ => ((x : ℂ) - Complex.I)⁻¹) = B := by
  subst hμ
  ext η
  obtain ⟨hψ, he⟩ := pmapIntegral_sub_smul_integral_inv μ Complex.measurable_ofReal
    (fun x => Complex.ofReal_im x) (c := Complex.I) (by simp) η
  have := hB.leftInverse ⟨_, hψ⟩
  simp only at this
  rw [he] at this
  exact this.symm

/--
If `∫ λ dμ = A`, then `∫ C dμ = U` for the Cayley map `C` and the Cayley transform `U`
of `A`, since `C = 1 + 2i (λ - i)⁻¹` and `U = 1 + 2i (A - i 1)⁻¹`.

Blueprint reference: `thrm:hall-10.4` (Step 2 of the uniqueness proof).
-/
theorem integral_cayleyMap_eq_unitary {A : H →ₗ.[ℂ] H} {B U : H →L[ℂ] H}
    (hU : IsCayleyTransform A B U) (hU1 : U - 1 = (2 * Complex.I) • B)
    {μ : ProjectionValuedMeasure ℝ H} (hμ : pmapIntegral μ (fun x : ℝ => (x : ℂ)) = A) :
    μ.integral (fun x : ℝ => cayleyMap x) = U := by
  set r : ℝ → ℂ := fun x => ((x : ℂ) - Complex.I)⁻¹
  have hne : ∀ x : ℝ, (x : ℂ) - Complex.I ≠ 0 := fun x h => by
    simpa using congrArg Complex.im h
  have hr : r ∈ BddMeasurable ℝ := ⟨(Complex.measurable_ofReal.sub_const _).inv, 1, fun x => by
    simp only [r, norm_inv]
    refine inv_le_one_of_one_le₀ ?_
    simpa using Complex.abs_im_le_norm ((x : ℂ) - Complex.I)⟩
  have hone : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := ⟨measurable_const, 1, fun x => by simp⟩
  have hC : (fun x : ℝ => cayleyMap x) = 1 + (2 * Complex.I) • r := by
    funext x
    simp only [cayleyMap, r, Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hne x]
    ring
  rw [hC, μ.integral_add hone ((BddMeasurable ℝ).smul_mem _ hr), μ.integral_one,
    μ.integral_smul _ hr, integral_inv_sub_I_eq_resolvent hU.isResolvent hμ, ← hU1]
  abel

/--
Uniqueness: any projection-valued measure on `ℝ` integrating the identity to `A` is the
Cayley transport `μ^A` of the spectral measure `μ^U` of the Cayley transform `U`.

Blueprint reference: `thrm:hall-10.4` (Steps 3 and 4 of the uniqueness proof).
-/
theorem eq_cayleyPVM_of_pmapIntegral_eq {A : H →ₗ.[ℂ] H} {B U : H →L[ℂ] H}
    (hU : IsCayleyTransform A B U) (hUu : U ∈ unitary (H →L[ℂ] H))
    (hU1 : U - 1 = (2 * Complex.I) • B)
    {μU : ProjectionValuedMeasure (spectrum ℂ U) H}
    (hμU : μU.integral (fun u => (u : ℂ)) = U)
    {μ : ProjectionValuedMeasure ℝ H} (hμ : pmapIntegral μ (fun x : ℝ => (x : ℂ)) = A) :
    μ = cayleyPVM μU := by
  set Y : Set ℂ := Metric.sphere 0 1
  have hsub : spectrum ℂ U ⊆ Y := spectrum.subset_circle_of_unitary hUu
  set T : ℝ → Y := fun x => ⟨cayleyMap x, by simpa [Y] using (cayleyMap_mem x).1⟩
  have hT : Measurable T := continuous_cayleyMap.measurable.subtype_mk
  have hid : (fun y : Y => (y : ℂ)) ∈ BddMeasurable Y :=
    ⟨measurable_subtype_coe, 1, fun y => by simp [Y]⟩
  have hν : (pushforwardPVM μ T hT).integral (fun y : Y => (y : ℂ)) = U := by
    rw [integral_pushforwardPVM μ hT hid]
    exact integral_cayleyMap_eq_unitary hU hU1 hμ
  refine ProjectionValuedMeasure.ext fun E => ?_
  by_cases hE : MeasurableSet E
  · have hF : MeasurableSet {y : Y | cayleyInv (y : ℂ) ∈ E} :=
      (measurable_cayleyInv.comp measurable_subtype_coe) hE
    have h := eq_of_integral_id_eq_ambient (unitary_mul_adjoint hUu).2.2 (isCompact_sphere 0 1)
      hsub hμU hν hF
    rw [pushforwardPVM_apply μ hT hF] at h
    have hpre : T ⁻¹' {y : Y | cayleyInv (y : ℂ) ∈ E} = E := by
      ext x
      simp [T, cayleyInv_cayleyMap]
    rw [hpre] at h
    rw [h, cayleyPVM_apply μU hE]
    rfl
  · rw [μ.apply_of_not_measurableSet hE, (cayleyPVM μU).apply_of_not_measurableSet hE]

/--
**Spectral theorem for unbounded self-adjoint operators.** An unbounded self-adjoint
operator on `H` is the integral of the identity function against a unique projection-valued
measure on `ℝ`.

Blueprint reference: `thrm:hall-10.4`.
-/
theorem existsUnique_spectralMeasure_unbounded {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    ∃! μ : ProjectionValuedMeasure ℝ H,
      pmapIntegral μ (fun x : ℝ => (x : ℂ)) = A := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · have hop : Subsingleton (H →L[ℂ] H) :=
      ⟨fun S T => ContinuousLinearMap.ext fun x => Subsingleton.elim _ _⟩
    let μ0 : ProjectionValuedMeasure ℝ H :=
      { toFun := fun _ => 0
        isStarProjection' := fun _ => IsStarProjection.zero _
        notMeasurable' := fun _ _ => rfl
        univ' := Subsingleton.elim _ _
        hasSum' := fun E _ _ v => by
          simp only [zero_apply]
          exact hasSum_zero
        inter' := fun _ _ _ _ => (mul_zero _).symm }
    refine ⟨μ0, ?_, fun ν _ => ProjectionValuedMeasure.ext fun E => Subsingleton.elim _ _⟩
    exact LinearPMap.ext (Subsingleton.elim _ _) fun x y _ => Subsingleton.elim _ _
  · obtain ⟨B, U, hU, hUu, -, -, -, hU1⟩ := exists_isCayleyTransform hA
    obtain ⟨μU, hμU, -⟩ := existsUnique_spectralMeasure_normal (unitary_mul_adjoint hUu).2.2
    exact ⟨cayleyPVM μU, pmapIntegral_cayleyPVM_id hA hU hμU,
      fun μ hμ => eq_cayleyPVM_of_pmapIntegral_eq hU hUu hU1 hμU hμ⟩

/--
The spectral measure is concentrated on the spectrum.

Blueprint reference: `thrm:hall-10.4`.
-/
theorem spectralMeasure_concentrated {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {μ : ProjectionValuedMeasure ℝ H} (hμ : pmapIntegral μ (fun x : ℝ => (x : ℂ)) = A) :
    μ {x : ℝ | (x : ℂ) ∉ pmapSpectrum A} = 0 ∧
      ∀ E : Set ℝ, MeasurableSet E → μ E = μ (E ∩ {x : ℝ | (x : ℂ) ∈ pmapSpectrum A}) := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · have hop : Subsingleton (H →L[ℂ] H) :=
      ⟨fun S T => ContinuousLinearMap.ext fun x => Subsingleton.elim _ _⟩
    exact ⟨Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  obtain ⟨B, U, hU, hUu, -, -, -, hU1⟩ := exists_isCayleyTransform hA
  obtain ⟨μU, hμU, -⟩ := existsUnique_spectralMeasure_normal (unitary_mul_adjoint hUu).2.2
  obtain rfl := eq_cayleyPVM_of_pmapIntegral_eq hU hUu hU1 hμU hμ
  set S : Set ℝ := {x : ℝ | (x : ℂ) ∈ pmapSpectrum A}
  have hSeq : S = cayleyMap ⁻¹' spectrum ℂ U := by
    ext x
    exact mem_spectrum_iff_cayleyMap_mem_spectrum hA hU x
  have hSm : MeasurableSet S :=
    hSeq ▸ ((spectrum.isClosed U).preimage continuous_cayleyMap).measurableSet
  have hD : Measurable fun u : spectrum ℂ U => cayleyInv (u : ℂ) :=
    measurable_cayleyInv.comp measurable_subtype_coe
  have h1 := spectralMeasure_singleton_one_eq_zero hA hU hμU
  have hN : MeasurableSet {u : spectrum ℂ U | (u : ℂ) = 1} :=
    (measurableSet_singleton (1 : ℂ)).preimage measurable_subtype_coe
  have hcompl : cayleyPVM μU Sᶜ = 0 := by
    rw [cayleyPVM_apply μU hSm.compl]
    set G : Set (spectrum ℂ U) := {u | cayleyInv (u : ℂ) ∈ Sᶜ}
    have hG : G ∩ {u : spectrum ℂ U | (u : ℂ) = 1} = G := by
      refine Set.inter_eq_left.mpr fun u hu => ?_
      by_contra hu1
      have hmem : (u : ℂ) ∈ unitCircleMinusOne :=
        ⟨by simpa using spectrum.subset_circle_of_unitary (𝕜 := ℂ) hUu u.2, hu1⟩
      apply hu
      change ((cayleyInv (u : ℂ) : ℝ) : ℂ) ∈ pmapSpectrum A
      rw [mem_spectrum_iff_cayleyMap_mem_spectrum hA hU, cayleyMap_cayleyInv hmem]
      exact u.2
    have hGm : MeasurableSet G := hD hSm.compl
    rw [← hG, μU.apply_inter hGm hN, h1, mul_zero]
  refine ⟨hcompl, fun E hE => ?_⟩
  set μ := cayleyPVM μU
  have hind : ∀ {F : Set ℝ}, MeasurableSet F → F.indicator (1 : ℝ → ℂ) ∈ BddMeasurable ℝ :=
    fun hF => indicator_one_mem_bddMeasurable_iff.mpr hF
  have hsplit : E.indicator (1 : ℝ → ℂ) =
      (E ∩ S).indicator 1 + (E ∩ Sᶜ).indicator 1 := by
    funext x
    by_cases hx : x ∈ E <;> by_cases hs : x ∈ S <;> simp [hx, hs]
  have hzero : μ (E ∩ Sᶜ) = 0 := by rw [μ.apply_inter hE hSm.compl, hcompl, mul_zero]
  rw [← μ.integral_indicator hE, hsplit, μ.integral_add (hind (hE.inter hSm))
    (hind (hE.inter hSm.compl)), μ.integral_indicator (hE.inter hSm),
    μ.integral_indicator (hE.inter hSm.compl), hzero, add_zero]

end Unbounded
end Spectral
end Physicslib4
