/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Stone.Density
import Physicslib4.Spectral.Stone.Exponential

/-!
# Stone's theorem

Every strongly continuous one-parameter unitary group `U` on a Hilbert space is `e^{itA}` for
a unique self-adjoint operator `A`, its infinitesimal generator (blueprint §10.4.5,
Theorem `thrm:hall-10.15`).

The generator is essentially self-adjoint (its deficiency subspaces are trivial, by an ODE
argument along orbits); the orbits of `U` and of `e^{itA^cl}` agree on the generator's domain
(their difference has constant norm); so `U(t) = e^{itA^cl}` by density, and the generator of
`e^{itA^cl}` is `A^cl` (Proposition `prpstn:hall-10.14`), whence `A = A^cl`.

## Main statements

* `isEssentiallySelfAdjoint_generator` — the generator is essentially self-adjoint.
* `stone` — **Stone's theorem**.
-/

namespace Physicslib4
namespace Spectral
namespace Stone

open scoped InnerProductSpace LinearPMap Topology
open Filter Unbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
An ODE along orbits: if `A* ψ = (ε i) ψ` and `φ ∈ Dom(A)`, then `y(t) = ⟪U(t) φ, ψ⟫` satisfies
`y' = ε y`. The blueprint takes `ε = ±1`; the computation holds for every `ε ∈ ℂ`.

Blueprint reference: `lmm:orbit-inner-ode`.
-/
theorem hasDerivAt_inner_orbit {U : ℝ → (H ≃ₗᵢ[ℂ] H)} (hU : IsOneParameterUnitaryGroup U)
    (hc : IsStronglyContinuous U) (ε : ℂ) {ψ : H} (hψ : ψ ∈ (generator U)†.domain)
    (hAψ : (generator U)† ⟨ψ, hψ⟩ = (ε * Complex.I) • ψ) (φ : (generator U).domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ⟪U s φ, ψ⟫_ℂ) (ε * ⟪U t φ, ψ⟫_ℂ) t := by
  obtain ⟨h, hd, -⟩ := hU.hasDerivAt_orbit_generator φ t
  have hadj := LinearPMap.adjoint_isFormalAdjoint (hasDenseDomain_generator hU hc) ⟨ψ, hψ⟩
    ⟨U t φ, h⟩
  rw [hAψ] at hadj
  have key : ⟪generator U ⟨U t φ, h⟩, ψ⟫_ℂ = ε * Complex.I * ⟪U t φ, ψ⟫_ℂ := by
    rw [← inner_conj_symm, ← hadj, inner_smul_left, map_mul, inner_conj_symm]
    simp [Complex.conj_I]
  convert hd.inner ℂ (hasDerivAt_const t ψ) using 1
  simp only [inner_zero_right, zero_add, inner_smul_left, key, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/--
Bounded solutions of `y' = ε y` vanish at `0`. The blueprint takes `ε = ±1`; any nonzero real
`ε` will do.

Blueprint reference: `lmm:bounded-exp-solution-zero`.
-/
theorem eq_zero_of_hasDerivAt_of_bounded {y : ℝ → ℂ} {ε : ℝ} (hε : ε ≠ 0)
    (hy : ∀ t, HasDerivAt y ((ε : ℂ) * y t) t) (hb : ∃ C, ∀ t, ‖y t‖ ≤ C) : y 0 = 0 := by
  obtain ⟨C, hC⟩ := hb
  by_contra h0
  have hn : 0 < ‖y 0‖ := norm_pos_iff.2 h0
  have key : ∀ s, ‖y 0‖ * Real.exp s ≤ C := fun s => by
    have := hC (s / ε)
    rw [eq_mul_exp_of_hasDerivAt hy, norm_mul, Complex.norm_exp] at this
    convert this using 3
    rw [← Complex.ofReal_mul, Complex.ofReal_re, mul_div_cancel₀ _ hε]
  have h1 := key (C / ‖y 0‖)
  have h2 := Real.add_one_le_exp (C / ‖y 0‖)
  have h3 : ‖y 0‖ * (C / ‖y 0‖ + 1) = C + ‖y 0‖ := by field_simp
  nlinarith

/--
The deficiency subspaces of the generator are trivial: `Ker(A* - i 1) = {0}` and
`Ker(A* + i 1) = {0}`.

Blueprint reference: `lmm:generator-ker-adjoint-trivial`.
-/
theorem ker_adjoint_generator_subSmul_eq_bot {U : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hU : IsOneParameterUnitaryGroup U) (hc : IsStronglyContinuous U) :
    ker (subSmul (generator U)† Complex.I) = ⊥ ∧ ker (subSmul (generator U)† (-Complex.I)) = ⊥ := by
  have key : ∀ ε : ℝ, ε ≠ 0 → ker (subSmul (generator U)† ((ε : ℂ) * Complex.I)) = ⊥ := by
    intro ε hε
    rw [Submodule.eq_bot_iff]
    intro ψ hψ
    obtain ⟨hd, h0⟩ := mem_ker.1 hψ
    have hAψ : (generator U)† ⟨ψ, hd⟩ = ((ε : ℂ) * Complex.I) • ψ :=
      sub_eq_zero.1 (by rw [subSmul_apply] at h0; exact h0)
    have horth : ψ ∈ (generator U).domainᗮ := by
      rw [Submodule.mem_orthogonal]
      intro φ hφ
      have := eq_zero_of_hasDerivAt_of_bounded hε
        (fun t => hasDerivAt_inner_orbit hU hc ε hd hAψ ⟨φ, hφ⟩ t)
        ⟨‖φ‖ * ‖ψ‖, fun t => (norm_inner_le_norm _ _).trans (by rw [LinearIsometryEquiv.norm_map])⟩
      simpa [hU.map_zero] using this
    rwa [dense_iff_orthogonal_eq_bot.1 (hasDenseDomain_generator hU hc)] at horth
  refine ⟨?_, ?_⟩
  · simpa using key 1 one_ne_zero
  · simpa using key (-1) (by norm_num)

/--
The generator of a strongly continuous one-parameter unitary group is essentially self-adjoint:
symmetric, closable, with self-adjoint closure. Its density is `hasDenseDomain_generator`.

Blueprint reference: `lmm:generator-essentially-self-adjoint`.
-/
theorem isEssentiallySelfAdjoint_generator {U : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hU : IsOneParameterUnitaryGroup U) (hc : IsStronglyContinuous U) :
    IsEssentiallySelfAdjoint (generator U) := by
  have hT := hasDenseDomain_generator hU hc
  obtain ⟨h1, h2⟩ := ker_adjoint_generator_subSmul_eq_bot hU hc
  rw [isEssentiallySelfAdjoint_iff_dense_range hT (isSymmetric_generator hU),
    dense_iff_orthogonal_eq_bot, dense_iff_orthogonal_eq_bot,
    orthogonal_range_subSmul hT, orthogonal_range_subSmul hT, map_neg, Complex.conj_I, neg_neg]
  exact ⟨h2, h1⟩

/--
The difference `w(t) = U(t) ψ - e^{itA^cl} ψ` of the orbits of `ψ ∈ Dom(A)` lies in
`Dom(A^cl)` and has derivative `i A^cl w(t)`.

Blueprint reference: `lmm:orbit-difference-hasDerivAt`.
-/
theorem hasDerivAt_orbit_sub_expUnitary {U : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hU : IsOneParameterUnitaryGroup U) (hc : IsStronglyContinuous U)
    (ψ : (generator U).domain) (t : ℝ) :
    ∃ h : U t ψ - expUnitary (isEssentiallySelfAdjoint_generator hU hc).isSelfAdjoint_closure t ψ ∈
        (generator U).closure.domain,
      HasDerivAt (fun s : ℝ => U s ψ -
          expUnitary (isEssentiallySelfAdjoint_generator hU hc).isSelfAdjoint_closure s ψ)
        (Complex.I • (generator U).closure ⟨_, h⟩) t := by
  have aux : ∀ {W : ℝ → (H ≃ₗᵢ[ℂ] H)} {B : H →ₗ.[ℂ] H}, IsOneParameterUnitaryGroup W →
      generator W = B → ∀ (φ : H) (hφ : φ ∈ B.domain), ∃ h : W t φ ∈ B.domain,
        HasDerivAt (fun s : ℝ => W s φ) (Complex.I • B ⟨W t φ, h⟩) t := by
    intro W B hW hB φ hφ
    subst hB
    obtain ⟨h, d, -⟩ := hW.hasDerivAt_orbit_generator ⟨φ, hφ⟩ t
    exact ⟨h, d⟩
  set hcl := (isEssentiallySelfAdjoint_generator hU hc).isSelfAdjoint_closure
  obtain ⟨hV, -, hgen⟩ := generator_expUnitary hcl
  have hle := (generator U).le_closure
  obtain ⟨h1, d1, -⟩ := hU.hasDerivAt_orbit_generator ψ t
  obtain ⟨h2, d2⟩ := aux hV hgen ψ (hle.1 ψ.2)
  have e1 : generator U ⟨U t ψ, h1⟩ = (generator U).closure ⟨U t ψ, hle.1 h1⟩ := hle.2 rfl
  refine ⟨Submodule.sub_mem _ (hle.1 h1) h2, ?_⟩
  convert d1.sub d2 using 1
  rw [e1, ← smul_sub, ← LinearPMap.map_sub]
  rfl

omit [CompleteSpace H] in
/--
A solution of `w' = i C w` with `C` symmetric and `w(0) = 0` vanishes identically, since
`‖w(t)‖²` is constant.

Blueprint reference: `lmm:norm-const-of-symmetric-derivative`.
-/
theorem eq_zero_of_hasDerivAt_of_isSymmetric {C : H →ₗ.[ℂ] H} (hC : IsSymmetric C) {w : ℝ → H}
    (hw : ∀ t, ∃ h : w t ∈ C.domain, HasDerivAt w (Complex.I • C ⟨w t, h⟩) t) (h0 : w 0 = 0)
    (t : ℝ) : w t = 0 := by
  have hd : ∀ s, HasDerivAt (fun s => ⟪w s, w s⟫_ℂ) 0 s := by
    intro s
    obtain ⟨h, hs⟩ := hw s
    convert hs.inner ℂ hs using 1
    rw [inner_smul_left, inner_smul_right, hC ⟨w s, h⟩ ⟨w s, h⟩, Complex.conj_I]
    ring
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simp only [h0, inner_zero_left] at hconst
  exact inner_self_eq_zero.mp hconst

/--
The orbits of `U` and of `e^{itA^cl}` agree on the generator's domain.

Blueprint reference: `lmm:orbits-agree-on-domain`.
-/
theorem orbit_eq_expUnitary_closure {U : ℝ → (H ≃ₗᵢ[ℂ] H)} (hU : IsOneParameterUnitaryGroup U)
    (hc : IsStronglyContinuous U) (ψ : (generator U).domain) (t : ℝ) :
    U t ψ = expUnitary (isEssentiallySelfAdjoint_generator hU hc).isSelfAdjoint_closure t ψ := by
  have hsa := (isEssentiallySelfAdjoint_generator hU hc).isSelfAdjoint_closure
  have hC : IsSymmetric (generator U).closure :=
    (isSymmetric_iff_le_adjoint hsa.dense_domain).mpr (LinearPMap.isSelfAdjoint_def.mp hsa).ge
  refine sub_eq_zero.mp (eq_zero_of_hasDerivAt_of_isSymmetric hC
    (hasDerivAt_orbit_sub_expUnitary hU hc ψ) ?_ t)
  simp only [hU.map_zero, (isOneParameterUnitaryGroup_expUnitary hsa).map_zero, sub_self]

omit [CompleteSpace H] in
/--
Bounded operators agreeing on a dense subspace are equal.

Blueprint reference: `lmm:agree-on-dense-subspace`.
-/
theorem eq_of_eqOn_dense {S T : H →L[ℂ] H} {D : Submodule ℂ H} (hD : Dense (D : Set H))
    (h : ∀ ψ ∈ D, S ψ = T ψ) : S = T :=
  DFunLike.coe_injective (Continuous.ext_on hD S.continuous T.continuous h)

/--
**Stone's theorem.** The infinitesimal generator `A` of a strongly continuous one-parameter
unitary group `U` is densely defined and self-adjoint, and `U(t) = e^{itA}` for all `t`.
Moreover `A` is the only self-adjoint operator with this property.

Blueprint reference: `thrm:hall-10.15`.
-/
theorem stone {U : ℝ → (H ≃ₗᵢ[ℂ] H)} (hU : IsOneParameterUnitaryGroup U)
    (hc : IsStronglyContinuous U) :
    ∃ hA : IsSelfAdjoint (generator U), HasDenseDomain (generator U) ∧
      (∀ t, U t = expUnitary hA t) ∧
      ∀ (B : H →ₗ.[ℂ] H) (hB : IsSelfAdjoint B), (∀ t, U t = expUnitary hB t) →
        B = generator U := by
  have hcl := (isEssentiallySelfAdjoint_generator hU hc).isSelfAdjoint_closure
  have hUV : U = expUnitary hcl := by
    funext t
    have h := eq_of_eqOn_dense (S := (U t).toContinuousLinearEquiv.toContinuousLinearMap)
      (T := (expUnitary hcl t).toContinuousLinearEquiv.toContinuousLinearMap)
      (hasDenseDomain_generator hU hc) fun ψ hψ => orbit_eq_expUnitary_closure hU hc ⟨ψ, hψ⟩ t
    exact LinearIsometryEquiv.ext fun x => congrArg (fun f => f x) h
  have hgen := (generator_expUnitary hcl).2.2
  rw [← hUV] at hgen
  have hcongr : ∀ {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B), A = B →
      expUnitary hA = expUnitary hB := by
    rintro A B hA hB rfl; rfl
  have hA : IsSelfAdjoint (generator U) := by rw [hgen]; exact hcl
  refine ⟨hA, hasDenseDomain_generator hU hc, fun t => ?_, fun B hB hUB => ?_⟩
  · rw [hcongr hA hcl hgen, ← hUV]
  · rw [show U = expUnitary hB from funext hUB]
    exact ((generator_expUnitary hB).2.2).symm

end Stone
end Spectral
end Physicslib4
