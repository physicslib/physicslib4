/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Spectrum
import Physicslib4.Spectral.Unbounded.Basic

/-!
# The spectrum of an unbounded operator

For an unbounded operator `T`, a scalar `λ` lies in the resolvent set when `T - λ 1` has
a *bounded two-sided inverse defined on all of `H` and landing in `Dom(T)`*; the spectrum
is the complement. Since `T - λ 1` is only defined on `Dom(T)`, this is spelled out as a
structure `IsResolvent` rather than as invertibility in a ring, so the names here are
`pmapResolventSet` and `pmapSpectrum` to keep them apart from Mathlib's `resolventSet`
and `spectrum` for bounded operators; `pmapResolventSet_toPMap_top` shows the two notions
agree on bounded operators.

## Main statements

* `existsUnique_isResolvent` — the inverse is unique when it exists.
* `pmapResolventSet_toPMap_top`, `pmapSpectrum_toPMap_top` — the two notions of spectrum
  agree for a bounded operator.
* `sq_norm_le_of_isSymmetric` — the `b²` inequality for a symmetric unbounded operator.
* `pmapSpectrum_subset_real` — the spectrum of an unbounded self-adjoint operator is real.
* `isEssentiallySelfAdjoint_iff_dense_range` — essential self-adjointness via dense range.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace LinearPMap
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
`B` is a bounded two-sided inverse of `T - λ 1`: it maps all of `H` into `Dom(T)`,
inverts `T - λ 1` on the right everywhere, and on the left on `Dom(T)`.

Blueprint reference: `def:hall-9.16`.
-/
structure IsResolvent (T : H →ₗ.[ℂ] H) (lam : ℂ) (B : H →L[ℂ] H) : Prop where
  /-- `B` lands in `Dom(T)`. -/
  mem_domain : ∀ ψ : H, B ψ ∈ T.domain
  /-- `(T - λ 1) B ψ = ψ` for all `ψ ∈ H`. -/
  rightInverse : ∀ ψ : H, T ⟨B ψ, mem_domain ψ⟩ - lam • B ψ = ψ
  /-- `B (T - λ 1) ψ = ψ` for all `ψ ∈ Dom(T)`. -/
  leftInverse : ∀ ψ : T.domain, B (T ψ - lam • (ψ : H)) = (ψ : H)

/--
The resolvent set of an unbounded operator.

Blueprint reference: `def:hall-9.16`.
-/
def pmapResolventSet (T : H →ₗ.[ℂ] H) : Set ℂ := {lam | ∃ B : H →L[ℂ] H, IsResolvent T lam B}

/--
The spectrum of an unbounded operator: the complement of its resolvent set.

Blueprint reference: `def:hall-9.16`.
-/
def pmapSpectrum (T : H →ₗ.[ℂ] H) : Set ℂ := (pmapResolventSet T)ᶜ

omit [CompleteSpace H] in
/--
The bounded inverse of `T - λ 1` is unique when it exists; this is what licenses the
notation `(T - λ 1)⁻¹`.

Blueprint reference: `lmm:uniqueness-of-resolvent`.
-/
theorem existsUnique_isResolvent {T : H →ₗ.[ℂ] H} {lam : ℂ} (h : lam ∈ pmapResolventSet T) :
    ∃! B : H →L[ℂ] H, IsResolvent T lam B := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, hB, fun B' hB' => ContinuousLinearMap.ext fun ψ => ?_⟩
  simpa [hB'.rightInverse ψ] using (hB.leftInverse ⟨B' ψ, hB'.mem_domain ψ⟩).symm

omit [CompleteSpace H] in
/--
For a bounded operator, regarded as an unbounded operator with domain all of `H`, the
unbounded resolvent set agrees with Mathlib's `resolventSet`.

Blueprint reference: `lmm:spectrum-notions-agree`.
-/
theorem pmapResolventSet_toPMap_top (A : H →L[ℂ] H) :
    pmapResolventSet ((A : H →ₗ[ℂ] H).toPMap ⊤) = resolventSet ℂ A := by
  ext lam
  simp only [pmapResolventSet, resolventSet, Set.mem_setOf_eq, isUnit_iff_exists,
    Algebra.algebraMap_eq_smul_one]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨-B, ?_, ?_⟩
    · ext ψ
      have := hB.rightInverse ψ
      simp only [LinearMap.toPMap_apply, ContinuousLinearMap.coe_coe] at this
      simp only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self, neg_apply,
        map_neg]
      convert this using 1; abel
    · ext ψ
      have := hB.leftInverse ⟨ψ, Submodule.mem_top⟩
      simp only [LinearMap.toPMap_apply, ContinuousLinearMap.coe_coe] at this
      simp only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self, neg_apply]
      rw [← map_neg, neg_sub, this]
  · rintro ⟨b, h1, h2⟩
    refine ⟨-b, ⟨fun _ => Submodule.mem_top, fun ψ => ?_, fun ψ => ?_⟩⟩
    · have := congrArg (fun f : H →L[ℂ] H => f ψ) h1
      simp only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] at this
      simp only [LinearMap.toPMap_apply, ContinuousLinearMap.coe_coe, neg_apply, map_neg,
        smul_neg]
      convert this using 1; abel
    · have := congrArg (fun f : H →L[ℂ] H => f ψ) h2
      simp only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] at this
      simp only [LinearMap.toPMap_apply, ContinuousLinearMap.coe_coe, neg_apply]
      rw [← map_neg, neg_sub, this]

omit [CompleteSpace H] in
/--
Consequently the two notions of spectrum agree for a bounded operator.

Blueprint reference: `lmm:spectrum-notions-agree`.
-/
theorem pmapSpectrum_toPMap_top (A : H →L[ℂ] H) :
    pmapSpectrum ((A : H →ₗ[ℂ] H).toPMap ⊤) = spectrum ℂ A := by
  rw [pmapSpectrum, pmapResolventSet_toPMap_top]; rfl

omit [CompleteSpace H] in
/--
The `b²` inequality for a symmetric unbounded operator: for `λ = a + i b` with `a, b`
real, `b² ‖ψ‖² ≤ ‖(T - λ 1) ψ‖²` for every `ψ ∈ Dom(T)`.

This is the unbounded, merely-symmetric counterpart of `lmm:hall-7.8`
(`Physicslib4.Spectral.sq_norm_sub_smul_apply_le`).

Blueprint reference: `lmm:b-squared-inequality-symmetric`.
-/
theorem sq_norm_le_of_isSymmetric {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T) (a b : ℝ)
    (ψ : T.domain) :
    b ^ 2 * ‖(ψ : H)‖ ^ 2 ≤ ‖T ψ - ((a : ℂ) + (b : ℂ) * Complex.I) • (ψ : H)‖ ^ 2 := by
  have him : (⟪T ψ, (ψ : H)⟫_ℂ).im = 0 := by
    have h := congrArg Complex.im (inner_conj_symm (𝕜 := ℂ) (T ψ) (ψ : H))
    rw [hsym ψ ψ, Complex.conj_im] at h
    linarith
  have hsplit : T ψ - ((a : ℂ) + (b : ℂ) * Complex.I) • (ψ : H) =
      (T ψ - (a : ℂ) • (ψ : H)) - ((b : ℂ) * Complex.I) • (ψ : H) := by
    rw [add_smul]; abel
  have hcross : RCLike.re ⟪T ψ - (a : ℂ) • (ψ : H), ((b : ℂ) * Complex.I) • (ψ : H)⟫_ℂ = 0 := by
    rw [inner_smul_right, inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_re, Complex.mul_im, him, ← Complex.ofReal_pow]
  have hnorm : ‖((b : ℂ) * Complex.I) • (ψ : H)‖ ^ 2 = b ^ 2 * ‖(ψ : H)‖ ^ 2 := by
    rw [norm_smul, mul_pow, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  rw [hsplit, @norm_sub_sq ℂ, hcross, hnorm]
  nlinarith [sq_nonneg ‖T ψ - (a : ℂ) • (ψ : H)‖]

omit [CompleteSpace H] in
/--
For a symmetric `T`, `|Im λ| ‖ψ‖ ≤ ‖(T - λ 1) ψ‖` for every `ψ ∈ Dom(T)`: the square root
of the `b²` inequality `sq_norm_le_of_isSymmetric`.

Blueprint reference: `thrm:hall-9.17`.
-/
theorem abs_im_mul_norm_le_of_isSymmetric {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T) (lam : ℂ)
    (ψ : T.domain) : |lam.im| * ‖(ψ : H)‖ ≤ ‖T ψ - lam • (ψ : H)‖ := by
  have h := sq_norm_le_of_isSymmetric hsym lam.re lam.im ψ
  rw [Complex.re_add_im] at h
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp
    (by rwa [mul_pow, sq_abs])

omit [CompleteSpace H] in
/--
For a symmetric `T` and non-real `λ`, the operator `T - λ 1` is injective.

Blueprint reference: `thrm:hall-9.17`.
-/
theorem ker_subSmul_eq_bot {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T) {lam : ℂ}
    (hlam : lam.im ≠ 0) : ker (subSmul T lam) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun ψ hψ => ?_
  obtain ⟨h, h0⟩ := mem_ker.mp hψ
  have hb := abs_im_mul_norm_le_of_isSymmetric hsym lam ⟨ψ, h⟩
  change _ ≤ ‖subSmul T lam ⟨ψ, h⟩‖ at hb
  rw [h0, norm_zero] at hb
  have hpos : 0 < |lam.im| := abs_pos.mpr hlam
  exact norm_eq_zero.mp (le_antisymm (by nlinarith [norm_nonneg ψ]) (norm_nonneg _))

/--
For a self-adjoint `T` and non-real `λ`, the operator `T - λ 1` maps `Dom(T)` onto `H`.

Blueprint reference: `thrm:hall-9.17`.
-/
theorem range_subSmul_eq_top {T : H →ₗ.[ℂ] H} (hsa : IsSelfAdjoint T) {lam : ℂ}
    (hlam : lam.im ≠ 0) : range (subSmul T lam) = ⊤ := by
  have hT : HasDenseDomain T := hsa.dense_domain
  have hadj : T† = T := LinearPMap.isSelfAdjoint_def.mp hsa
  have hsym : IsSymmetric T := (isSymmetric_iff_le_adjoint hT).mpr hadj.ge
  have hdense : Dense ((range (subSmul T lam) : Submodule ℂ H) : Set H) :=
    dense_iff_orthogonal_eq_bot.mpr <| by
      rw [orthogonal_range_subSmul hT, hadj]
      exact ker_subSmul_eq_bot hsym (by simpa using hlam)
  have hclosed := isClosed_range_subSmul hsa.isClosed lam (abs_pos.mpr hlam)
    (abs_im_mul_norm_le_of_isSymmetric hsym lam)
  rw [← hclosed.submodule_topologicalClosure_eq]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mp hdense

/--
For a self-adjoint `T`, every non-real `λ` lies in the resolvent set of `T`: the inverse
of the bijection `T - λ 1 : Dom(T) → H` is bounded by `1 / |Im λ|`.

Blueprint reference: `thrm:hall-9.17`.
-/
theorem mem_pmapResolventSet_of_im_ne_zero {T : H →ₗ.[ℂ] H} (hsa : IsSelfAdjoint T)
    {lam : ℂ} (hlam : lam.im ≠ 0) : lam ∈ pmapResolventSet T := by
  have hT : HasDenseDomain T := hsa.dense_domain
  have hsym : IsSymmetric T :=
    (isSymmetric_iff_le_adjoint hT).mpr (LinearPMap.isSelfAdjoint_def.mp hsa).ge
  set f : T.domain →ₗ[ℂ] H := (subSmul T lam).toFun
  have hinj : Function.Injective f := (injective_iff_map_eq_zero f).mpr fun x hx => by
    have h : (x : H) ∈ ker (subSmul T lam) := mem_ker.mpr ⟨x.2, hx⟩
    rw [ker_subSmul_eq_bot hsym hlam] at h
    exact Subtype.ext ((Submodule.mem_bot ℂ).mp h)
  have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp (range_subSmul_eq_top hsa hlam)
  set e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  have hpos : 0 < |lam.im| := abs_pos.mpr hlam
  have hbound (x : H) : ‖(e.symm x : H)‖ ≤ |lam.im|⁻¹ * ‖x‖ := by
    rw [le_inv_mul_iff₀ hpos]
    have h := abs_im_mul_norm_le_of_isSymmetric hsym lam (e.symm x)
    have hx : f (e.symm x) = x := e.apply_symm_apply x
    exact h.trans_eq (congrArg norm hx)
  refine ⟨(T.domain.subtype ∘ₗ e.symm.toLinearMap).mkContinuous _ hbound,
    fun ψ => (e.symm ψ).2, fun ψ => e.apply_symm_apply ψ,
    fun ψ => congrArg Subtype.val (e.symm_apply_apply ψ)⟩

/--
The spectrum of an unbounded self-adjoint operator is contained in the real line.

(Density of `Dom(T)` is not a separate hypothesis: it follows from self-adjointness, see
`LinearPMap.IsSelfAdjoint.dense_domain`.)

Blueprint reference: `thrm:hall-9.17`.
-/
theorem pmapSpectrum_subset_real {T : H →ₗ.[ℂ] H} (hsa : IsSelfAdjoint T) :
    pmapSpectrum T ⊆ {z : ℂ | z.im = 0} :=
  fun _ hz => by_contra fun him => hz (mem_pmapResolventSet_of_im_ne_zero hsa him)

/--
If `T` is essentially self-adjoint and `λ` is non-real, the range of `T - λ 1` is dense.

Blueprint reference: `thrm:hall-9.21` (forward direction).
-/
theorem dense_range_subSmul_of_isEssentiallySelfAdjoint {T : H →ₗ.[ℂ] H}
    (hT : HasDenseDomain T) (h : IsEssentiallySelfAdjoint T) {lam : ℂ} (hlam : lam.im ≠ 0) :
    Dense ((range (subSmul T lam) : Submodule ℂ H) : Set H) := by
  have hadj : T† = T.closure := by
    rw [← adjoint_closure_eq_adjoint hT h.isClosable]
    exact LinearPMap.isSelfAdjoint_def.mp h.isSelfAdjoint_closure
  refine dense_iff_orthogonal_eq_bot.mpr ?_
  rw [orthogonal_range_subSmul hT, hadj]
  exact ker_subSmul_eq_bot (isSymmetric_closure h.isSymmetric h.isClosable) (by simpa using hlam)

/--
If `S` is a closed symmetric extension of `T` and `λ` is non-real, density of the range of
`T - λ 1` forces `S - λ 1` to map `Dom(S)` onto `H`.

Blueprint reference: `thrm:hall-9.21`.
-/
theorem range_subSmul_eq_top_of_le {T S : H →ₗ.[ℂ] H} (hS : S.IsClosed) (hsymS : IsSymmetric S)
    (hTS : T ≤ S) {lam : ℂ} (hlam : lam.im ≠ 0)
    (hd : Dense ((range (subSmul T lam) : Submodule ℂ H) : Set H)) :
    range (subSmul S lam) = ⊤ := by
  have hle : range (subSmul T lam) ≤ range (subSmul S lam) := by
    rintro _ ⟨x, rfl⟩
    refine mem_range.mpr ⟨⟨x, hTS.1 x.2⟩, ?_⟩
    change S _ - lam • (x : H) = T x - lam • (x : H)
    rw [hTS.2 (x := x) (y := ⟨x, hTS.1 x.2⟩) rfl]; rfl
  have hclosed := isClosed_range_subSmul hS lam (abs_pos.mpr hlam)
    (abs_im_mul_norm_le_of_isSymmetric hsymS lam)
  rw [← hclosed.submodule_topologicalClosure_eq]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mp (hd.mono hle)

/--
If `S ≤ S*`, `S - μ 1` maps onto `H` and `S* - μ 1` is injective, then `S` is self-adjoint.

Blueprint reference: `thrm:hall-9.21`.
-/
theorem adjoint_eq_of_range_eq_top {S : H →ₗ.[ℂ] H} (hle : S ≤ S†) {mu : ℂ}
    (hr : range (subSmul S mu) = ⊤) (hk : ker (subSmul (S†) mu) = ⊥) : S† = S := by
  have hdom : S†.domain ≤ S.domain := fun ξ hξ => by
    obtain ⟨χ, hχ⟩ := mem_range.mp
      (hr ▸ Submodule.mem_top : subSmul (S†) mu ⟨ξ, hξ⟩ ∈ range (subSmul S mu))
    have hχ' : (χ : H) ∈ S†.domain := hle.1 χ.2
    have h0 : ξ - (χ : H) ∈ ker (subSmul (S†) mu) := by
      refine mem_ker.mpr ⟨S†.domain.sub_mem hξ hχ', ?_⟩
      change S† (⟨ξ, hξ⟩ - ⟨χ, hχ'⟩) - mu • (ξ - (χ : H)) = 0
      rw [LinearPMap.map_sub, ← hle.2 (x := χ) (y := ⟨χ, hχ'⟩) rfl, smul_sub,
        sub_sub_sub_comm]
      change subSmul (S†) mu ⟨ξ, hξ⟩ - subSmul S mu χ = 0
      rw [hχ, sub_self]
    rw [hk, Submodule.mem_bot, sub_eq_zero] at h0
    exact h0 ▸ χ.2
  exact (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

/--
A symmetric operator is essentially self-adjoint if and only if the ranges of `T - i 1`
and `T + i 1` are both dense in `H`. (Here `T + i 1` is `subSmul T (-i)`.)

Blueprint reference: `thrm:hall-9.21`.
-/
theorem isEssentiallySelfAdjoint_iff_dense_range {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hsym : IsSymmetric T) :
    IsEssentiallySelfAdjoint T ↔
      Dense ((range (subSmul T Complex.I) : Submodule ℂ H) : Set H) ∧
        Dense ((range (subSmul T (-Complex.I)) : Submodule ℂ H) : Set H) := by
  refine ⟨fun h => ⟨dense_range_subSmul_of_isEssentiallySelfAdjoint hT h (by simp),
    dense_range_subSmul_of_isEssentiallySelfAdjoint hT h (by simp)⟩, fun ⟨hI, hnI⟩ => ?_⟩
  have hc := isClosable_of_isSymmetric hT hsym
  have hsymS := isSymmetric_closure hsym hc
  have hleS : T.closure ≤ T.closure† :=
    (isSymmetric_iff_le_adjoint (hasDenseDomain_closure hT hc)).mp hsymS
  have hr := range_subSmul_eq_top_of_le hc.closure_isClosed hsymS T.le_closure (by simp) hnI
  have hk : ker (subSmul (T.closure†) (-Complex.I)) = ⊥ := by
    have := dense_iff_orthogonal_eq_bot.mp hI
    rwa [orthogonal_range_subSmul hT, Complex.conj_I, ← adjoint_closure_eq_adjoint hT hc] at this
  exact ⟨hsym, hc, LinearPMap.isSelfAdjoint_def.mpr (adjoint_eq_of_range_eq_top hleS hr hk)⟩

end Unbounded
end Spectral
end Physicslib4
