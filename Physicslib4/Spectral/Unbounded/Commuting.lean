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
  have hCs : ∀ y, C.symm (C.symm y) = y := fun y => by
    rw [C.symm_apply_eq.2 (hC y).symm, C.symm_apply_eq.2 (hC (C y)).symm, hC]
  have hmem : ∀ x, x ∈ (antiunitaryConj (C.trans U) (antiunitaryConj C A)).domain ↔
      U.symm x ∈ A.domain := fun x => by
    change C.symm (C.symm (U.symm x)) ∈ A.domain ↔ _
    rw [hCs]
  refine LinearPMap.ext (Submodule.ext fun x => (hmem x).trans
    ⟨fun h => by simpa using (hU.1 _ h).1, fun h => (hU.2 x h).1⟩) fun x hx hx' => ?_
  obtain ⟨h, hA⟩ := hU.2 x hx'
  change U (C (C (A ⟨C.symm (C.symm (U.symm x)), _⟩))) = _
  rw [hC]
  have : (⟨C.symm (C.symm (U.symm x)), by simpa [hCs] using h⟩ : A.domain) =
      ⟨U.symm x, h⟩ := Subtype.ext (hCs _)
  rw [this, hA, LinearIsometryEquiv.apply_symm_apply]

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
  obtain ⟨h₁, e₁⟩ := functionalCalculus_antiunitaryConj C hA
  obtain ⟨h₂, e₂⟩ := functionalCalculus_antiunitaryConj (C.trans U) h₁
  rw [e₁ f hf, e₂ f hf]
  clear e₂
  revert h₂
  rw [antiunitaryConj_trans_antiunitaryConj_of_commute U C hC hU]
  exact fun _ => rfl

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
  intro y hy
  have key : ∀ x : c.domain, ⟪V (c† ⟨y, hy⟩), (x : H)⟫_ℂ = ⟪V y, c x⟫_ℂ := by
    rintro ⟨x, hx⟩
    obtain ⟨h, hcx⟩ := hV x hx
    have h1 := LinearPMap.adjoint_isFormalAdjoint hc ⟨y, hy⟩ ⟨V.symm x, h⟩
    simp only at h1
    rw [← V.inner_map_map (c† ⟨y, hy⟩) (V.symm x), V.apply_symm_apply] at h1
    rw [h1, hcx, ← V.inner_map_map y, V.apply_symm_apply]
  exact ⟨LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩,
    LinearPMap.adjoint_apply_eq hc _ key⟩

/--
If the unitary `U` commutes with a densely defined `c`, then `U` commutes with `c†`.

Blueprint: lmm:commuting-unitary-adjoint
-/
theorem adjoint_commute_of_commute {c : H →ₗ.[ℂ] H} (hc : HasDenseDomain c) (U : H ≃ₗᵢ[ℂ] H)
    (hU : UnitaryCommutes U c) :
    UnitaryCommutes U c† :=
  ⟨adjoint_commute_of_symm_commute hc U hU.2, adjoint_commute_of_symm_commute hc U.symm hU.1⟩

/--
If the unitary `U` commutes with a densely defined `c`, then `U` commutes with `c†c`.

Blueprint: lmm:commuting-unitary-adjoint-product
-/
theorem adjointMulSelf_commute_of_commute {c : H →ₗ.[ℂ] H} (hc : HasDenseDomain c)
    (U : H ≃ₗᵢ[ℂ] H)
    (hU : UnitaryCommutes U c) :
    UnitaryCommutes U (adjointMulSelf c) := by
  have key : ∀ V : H → H,
      (∀ x (hx : x ∈ c.domain), ∃ h : V x ∈ c.domain, c ⟨V x, h⟩ = V (c ⟨x, hx⟩)) →
      (∀ x (hx : x ∈ c†.domain), ∃ h : V x ∈ c†.domain, c† ⟨V x, h⟩ = V (c† ⟨x, hx⟩)) →
      ∀ x (hx : x ∈ (adjointMulSelf c).domain), ∃ h : V x ∈ (adjointMulSelf c).domain,
        adjointMulSelf c ⟨V x, h⟩ = V (adjointMulSelf c ⟨x, hx⟩) := by
    intro V h1 h2 x hx
    obtain ⟨hxc, hcx⟩ := (mem_domain_pmapMul_iff _ _ x).1 hx
    obtain ⟨h, e⟩ := h1 x hxc
    obtain ⟨h', e'⟩ := h2 _ hcx
    have hd : V x ∈ (adjointMulSelf c).domain :=
      (mem_domain_pmapMul_iff _ _ _).2 ⟨h, e ▸ h'⟩
    refine ⟨hd, ?_⟩
    change pmapMul (c†) c ⟨V x, hd⟩ = V (pmapMul (c†) c ⟨x, hx⟩)
    rw [pmapMul_apply _ _ ⟨V x, hd⟩ (e ▸ h'), pmapMul_apply _ _ ⟨x, hx⟩ hcx, ← e']
    congr 2
  have hU' := adjoint_commute_of_commute hc U hU
  exact ⟨key U hU.1 hU'.1, key U.symm hU.2 hU'.2⟩

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
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis ℂ H
  let C : H ≃ₗᵢ⋆[ℂ] H := (b.repr.trans (starₗᵢ ℂ)).trans b.repr.symm
  have hC : ∀ x, C (C x) = x := fun x => by simp [C]
  have hfm : Measurable f := by
    simpa [Function.comp_def] using Complex.measurable_re.comp hf.1
  have hA := isSelfAdjoint_adjointMulSelf hc hcl
  have e := antiunitaryConj_trans_functionalCalculus_of_commute U C hC hA.1
    (adjointMulSelf_commute_of_commute hc U hU) hfm
  set F := functionalCalculus hA.1 fun x => (f x : ℂ)
  have hCs : ∀ y, C.symm (C.symm y) = y := fun y => by
    rw [C.symm_apply_eq.2 (hC y).symm, C.symm_apply_eq.2 (hC (C y)).symm, hC]
  rintro ⟨ψ, hψ⟩
  have hmem : U ψ ∈ (antiunitaryConj (C.trans U) (antiunitaryConj C F)).domain := by
    change C.symm (C.symm (U.symm (U ψ))) ∈ F.domain
    rwa [U.symm_apply_apply, hCs]
  refine ⟨by rw [e] at hmem; exact hmem, ?_⟩
  have key : ∀ (G : H →ₗ.[ℂ] H) (hG : G = F) (h : U ψ ∈ G.domain),
      G ⟨U ψ, h⟩ = F ⟨U ψ, hG ▸ h⟩ := by
    rintro G rfl h; rfl
  rw [← key _ e hmem]
  change U (C (C (F ⟨C.symm (C.symm (U.symm (U ψ))), _⟩))) = _
  rw [hC]
  congr 2
  exact Subtype.ext (by simp only [U.symm_apply_apply, hCs])

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
  refine ⟨fun n hn => ?_, fun x => ?_⟩
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hc : Continuous (fun x : ℝ => (n / (n + Real.sqrt x) : ℝ)) :=
      continuous_const.div (continuous_const.add Real.continuous_sqrt) fun x => by positivity
    have hc2 := Real.continuous_sqrt.mul hc
    refine ⟨hc, hc.measurable, hc2, hc2.measurable, fun x => ?_⟩
    have hs := Real.sqrt_nonneg x
    have hpos : 0 < (n : ℝ) + Real.sqrt x := by positivity
    have h1 : (n : ℝ) / (n + Real.sqrt x) ≤ 1 := (div_le_one hpos).2 (by linarith)
    have h0 : 0 < (n : ℝ) / (n + Real.sqrt x) := div_pos hn' hpos
    refine ⟨h0, h1, mul_nonneg hs h0.le, ?_, mul_le_of_le_one_right hs h1⟩
    rw [mul_div_assoc', div_le_iff₀ hpos]
    nlinarith
  · have h := tendsto_natCast_div_add_atTop (𝕜 := ℝ) (Real.sqrt x)
    exact ⟨h, by simpa using h.const_mul (Real.sqrt x)⟩

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
  set hA := (isSelfAdjoint_adjointMulSelf hc hcl).1
  -- a bounded real function of `D` is everywhere defined with norm at most its bound
  have key : ∀ {f : ℝ → ℝ} {M : ℝ}, Measurable f → (∀ x, |f x| ≤ M) →
      (functionalCalculus hA fun x => (f x : ℂ)).domain = ⊤ ∧
      ∀ ψ : (functionalCalculus hA fun x => (f x : ℂ)).domain,
        ‖functionalCalculus hA (fun x => (f x : ℂ)) ψ‖ ≤ M * ‖(ψ : H)‖ := by
    intro f M hf hM
    have hM' : ∀ x, ‖((f x : ℝ) : ℂ)‖ ≤ M := fun x => by rw [Complex.norm_real]; exact hM x
    have hb : (fun x => (f x : ℂ)) ∈ BddMeasurable ℝ :=
      ⟨Complex.measurable_ofReal.comp hf, M, hM'⟩
    obtain ⟨hdom, heq⟩ := functionalCalculus_of_bddMeasurable hA hb
    refine ⟨hdom, ?_⟩
    rw [heq]
    intro ψ
    exact ((spectralMeasure hA).integral _).le_opNorm (ψ : H) |>.trans
      (mul_le_mul_of_nonneg_right
        (((spectralMeasure hA).norm_integral_le hb).trans (ciSup_le hM')) (norm_nonneg _))
  obtain ⟨-, hhm, -, hkm, hb⟩ := approximant_functions.1 n hn
  obtain ⟨hR, hRn⟩ := key hhm (M := 1) fun x => by
    rw [abs_of_pos (hb x).1]; exact (hb x).2.1
  obtain ⟨hK, hKn⟩ := key hkm (M := n) fun x => by
    rw [abs_of_nonneg (hb x).2.2.1]; exact (hb x).2.2.2.1
  exact ⟨hR, hK, (isSelfAdjoint_functionalCalculus_of_real hA hhm).1,
    fun ψ => by simpa using hRn ψ, hKn⟩

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
  set hA := (isSelfAdjoint_adjointMulSelf hc hcl).1
  set μ := spectralMeasure hA
  obtain ⟨-, hhm, -, hkm, hb⟩ := approximant_functions.1 n hn
  have hsq : Measurable fun x : ℝ => ((Real.sqrt x : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have hhc : Measurable fun x : ℝ => ((n / (n + Real.sqrt x) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp hhm
  have hbh : (fun x : ℝ => ((n / (n + Real.sqrt x) : ℝ) : ℂ)) ∈ BddMeasurable ℝ :=
    ⟨hhc, 1, fun x => by rw [Complex.norm_real, Real.norm_of_nonneg (hb x).1.le]; exact (hb x).2.1⟩
  have hkb : ∀ x : ℝ, ‖(((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ)) : ℂ)‖ ≤ n := fun x => by
    rw [Complex.norm_real, Real.norm_of_nonneg (hb x).2.2.1]; exact (hb x).2.2.2.1
  have hbk : (fun x : ℝ => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ)) ∈
      BddMeasurable ℝ := ⟨Complex.measurable_ofReal.comp hkm, n, hkb⟩
  have hR : ψ ∈ integralDomain μ fun x : ℝ => ((n / (n + Real.sqrt x) : ℝ) : ℂ) := by
    rw [integralDomain_eq_top_of_bddMeasurable _ hbh]; trivial
  have hK : ψ ∈ integralDomain μ
      fun x : ℝ => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ) := by
    rw [integralDomain_eq_top_of_bddMeasurable _ hbk]; trivial
  have hfun : ((fun x : ℝ => ((Real.sqrt x : ℝ) : ℂ)) *
      fun x : ℝ => ((n / (n + Real.sqrt x) : ℝ) : ℂ)) =
        fun x : ℝ => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ) :=
    funext fun x => by simp
  have hy : pmapIntegral μ (fun x : ℝ => ((n / (n + Real.sqrt x) : ℝ) : ℂ)) ⟨ψ, hR⟩ ∈
      integralDomain μ fun x : ℝ => ((Real.sqrt x : ℝ) : ℂ) :=
    (pmapIntegral_mem_integralDomain_iff μ hsq hhc ⟨ψ, hR⟩).2 (hfun ▸ hK)
  obtain ⟨hfg, hcomp⟩ := (pmapIntegral_comp μ hsq hhc).2 ⟨ψ, hR⟩ hy
  have hdom := (absoluteValue_domain hc hcl).2.2.1
  have h₂ : pmapIntegral μ (fun x : ℝ => ((n / (n + Real.sqrt x) : ℝ) : ℂ)) ⟨ψ, hR⟩ ∈
      c.domain := hdom ▸ hy
  -- `(√· · h_n)(D) ψ = k_n(D) ψ`
  have key : ∀ (F : ℝ → ℂ) (hF : F = fun x : ℝ => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ))
      (h : ψ ∈ integralDomain μ F), pmapIntegral μ F ⟨ψ, h⟩ = pmapIntegral μ _ ⟨ψ, hK⟩ := by
    intro F hF h; subst hF; rfl
  have heq : absoluteValue c hc hcl ⟨_, hy⟩ =
      pmapIntegral μ (fun x : ℝ => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ))
        ⟨ψ, hK⟩ :=
    hcomp.symm.trans (key _ hfun hfg)
  refine ⟨hR, hK, hy, h₂, heq, ?_, ?_⟩
  · exact ((absoluteValue_domain hc hcl).2.2.2 _ hy h₂).symm.trans (congrArg norm heq)
  · obtain ⟨-, hKeq⟩ := functionalCalculus_of_bddMeasurable hA hbk
    have hle : ∀ φ : (functionalCalculus hA
        fun x : ℝ => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ)).domain,
        ‖functionalCalculus hA
          (fun x : ℝ => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ)) φ‖ ≤
          n * ‖(φ : H)‖ := by
      rw [hKeq]
      intro φ
      exact ((spectralMeasure hA).integral _).le_opNorm (φ : H) |>.trans
        (mul_le_mul_of_nonneg_right
          (((spectralMeasure hA).norm_integral_le hbk).trans (ciSup_le hkb)) (norm_nonneg _))
    exact hle ⟨ψ, hK⟩

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
  set hA := (isSelfAdjoint_adjointMulSelf hc hcl).1
  set μ := spectralMeasure hA
  have hsm : Measurable Real.sqrt := Real.continuous_sqrt.measurable
  have hb : ∀ (n : ℕ) (x : ℝ),
      0 ≤ (n / (n + Real.sqrt x) : ℝ) ∧ (n / (n + Real.sqrt x) : ℝ) ≤ 1 := fun n x =>
    ⟨by positivity, div_le_one_of_le₀ (by linarith [Real.sqrt_nonneg x]) (by positivity)⟩
  have hhm : ∀ n : ℕ, Measurable fun x : ℝ => (n / (n + Real.sqrt x) : ℝ) := fun n =>
    measurable_const.div (measurable_const.add hsm)
  have hbh : ∀ n : ℕ, (fun x : ℝ => ((n / (n + Real.sqrt x) : ℝ) : ℂ)) ∈ BddMeasurable ℝ :=
    fun n => ⟨Complex.measurable_ofReal.comp (hhm n), 1, fun x => by
      rw [Complex.norm_real, Real.norm_of_nonneg (hb n x).1]; exact (hb n x).2⟩
  have hkle : ∀ (n : ℕ) (x : ℝ), ‖((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ)‖ ≤
      ‖((Real.sqrt x : ℝ) : ℂ)‖ := fun n x => by
    rw [Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (hb n x).1),
      Real.norm_of_nonneg (Real.sqrt_nonneg x)]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg x) (hb n x).2
  have hbk : ∀ n : ℕ,
      (fun x : ℝ => ((Real.sqrt x * (n / (n + Real.sqrt x)) : ℝ) : ℂ)) ∈ BddMeasurable ℝ :=
    fun n => ⟨Complex.measurable_ofReal.comp (hsm.mul (hhm n)), n, fun x => by
      rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (hb n x).1)]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact ((approximant_functions.1 n hn).2.2.2.2 x).2.2.2.1⟩
  -- a bounded function acts through the bounded spectral integral
  have hev : ∀ {f : ℝ → ℂ} (_ : f ∈ BddMeasurable ℝ) (ψ : H) (hψ : ψ ∈ integralDomain μ f),
      pmapIntegral μ f ⟨ψ, hψ⟩ = μ.integral f ψ := by
    intro f hf ψ hψ
    obtain ⟨-, hext⟩ := LinearPMap.ext_iff.mp (pmapIntegral_of_bddMeasurable μ hf)
    rw [@hext ψ hψ Submodule.mem_top]
    rfl
  have hmem : ∀ {f : ℝ → ℂ} (_ : f ∈ BddMeasurable ℝ) (ψ : H), ψ ∈ integralDomain μ f :=
    fun hf ψ => (integralDomain_eq_top_of_bddMeasurable μ hf).symm ▸ Submodule.mem_top
  refine ⟨fun φ => ⟨fun n => hmem (hbh n) φ, ?_⟩, fun ψ hψ =>
    ⟨fun n => hmem (hbk n) ψ, (absoluteValue_domain hc hcl).2.2.1.symm ▸ hψ, ?_⟩⟩
  · have h1 : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := ⟨measurable_const, 1, fun x => by simp⟩
    have := tendsto_integral_apply_of_dominated μ h1.1 ⟨φ, hmem h1 φ⟩ hbh
      (fun x => by
        have := (Complex.continuous_ofReal.tendsto _).comp (approximant_functions.2 x).1
        rwa [Complex.ofReal_one] at this)
      (fun n x => by
        rw [Complex.norm_real, Real.norm_of_nonneg (hb n x).1]; simpa using (hb n x).2)
    have e : pmapIntegral μ 1 ⟨φ, hmem h1 φ⟩ = φ := by
      rw [hev h1 φ (hmem h1 φ), μ.integral_one]; rfl
    convert this using 2 with n
    · exact hev (hbh n) φ _
    · exact e.symm
  · have hsq : Measurable fun x : ℝ => ((Real.sqrt x : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp hsm
    have := tendsto_integral_apply_of_dominated μ hsq
      ⟨ψ, (show ψ ∈ (absoluteValue c hc hcl).domain from
        (absoluteValue_domain hc hcl).2.2.1.symm ▸ hψ)⟩
      hbk (fun x => (Complex.continuous_ofReal.tendsto _).comp (approximant_functions.2 x).2)
      hkle
    exact this.congr fun n => (hev (hbk n) ψ _).symm

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
  set R := functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
    fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)
  have hdom : ∀ ψ : H, ψ ∈ R.domain := fun ψ => (approximant_range hc hcl n hn ψ).1
  have hcd : ∀ ψ : R.domain, R ψ ∈ c.domain := fun ψ =>
    (approximant_range hc hcl n hn ψ).2.2.2.1
  let g : H →ₗ[ℂ] H :=
    { toFun := fun ψ => c ⟨R ⟨ψ, hdom ψ⟩, hcd _⟩
      map_add' := fun a b => by
        rw [← c.map_add]; congr 1; ext; simp only [Submodule.coe_add]; rw [← R.map_add]; rfl
      map_smul' := fun a b => by
        rw [← c.map_smul]; congr 1; ext; simp only [Submodule.coe_smul]; rw [← R.map_smul]; rfl }
  have hg : ∀ ψ, ‖g ψ‖ ≤ n * ‖ψ‖ := fun ψ => by
    obtain ⟨_, _, _, _, _, h1, h2⟩ := approximant_range hc hcl n hn ψ
    exact (le_of_eq h1).trans h2
  have hsym : IsSymmetric R := by
    have hR := (isSelfAdjoint_functionalCalculus_of_real (isSelfAdjoint_adjointMulSelf hc hcl).1
      (approximant_functions.1 n hn).2.1).1
    have hd : HasDenseDomain R := by
      rw [HasDenseDomain, show R.domain = ⊤ from eq_top_iff.2 fun ψ _ => hdom ψ]
      exact dense_univ
    exact (isSymmetric_iff_le_adjoint hd).2 (LinearPMap.isSelfAdjoint_def.1 hR).ge
  refine ⟨g.mkContinuous n hg, fun ψ => ⟨hcd ψ, rfl⟩, fun y hy => ?_,
    LinearMap.mkContinuous_norm_le g (Nat.cast_nonneg n) hg, fun φ => ⟨hdom _, ?_⟩⟩
  · ext ψ
    exact (hy ⟨ψ, hdom ψ⟩).2
  · refine ext_inner_right ℂ fun v => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    have h1 := LinearPMap.adjoint_isFormalAdjoint hc φ ⟨R ⟨v, hdom v⟩, hcd _⟩
    exact h1.symm.trans (hsym ⟨_, hdom _⟩ ⟨v, hdom v⟩)

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
  intro ψ
  obtain ⟨-, hhm, -, -, hb⟩ := approximant_functions.1 n hn
  have hbh : (fun t : ℝ => ((n / (n + Real.sqrt t) : ℝ) : ℂ)) ∈ BddMeasurable ℝ :=
    ⟨Complex.measurable_ofReal.comp hhm, 1, fun t => by
      rw [Complex.norm_real, Real.norm_of_nonneg (hb t).1.le]; exact (hb t).2.1⟩
  have hdom := (functionalCalculus_of_bddMeasurable (isSelfAdjoint_adjointMulSelf hc hcl).1 hbh).1
  have hψ : ψ ∈ (functionalCalculus (isSelfAdjoint_adjointMulSelf hc hcl).1
      fun t => ((n / (n + Real.sqrt t) : ℝ) : ℂ)).domain := hdom ▸ trivial
  obtain ⟨h1, e1⟩ := hx ⟨ψ, hψ⟩
  obtain ⟨h3, e3⟩ := functionalCalculus_adjointMulSelf_commute_of_commute hc hcl U hU hbh ⟨ψ, hψ⟩
  obtain ⟨h2, e2⟩ := hx ⟨U ψ, h3⟩
  obtain ⟨h4, e4⟩ := hU.1 _ h1
  rw [show x ψ = _ from e1, show x (U ψ) = _ from e2, ← e4]
  congr 2
  exact e3.symm

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
  set μ := spectralMeasure hA
  have hF : Measurable fun x => (f x : ℂ) := Complex.measurable_ofReal.comp hf
  have hsq : ((fun x => (f x : ℂ)) * fun x => (f x : ℂ)) = fun x => ((f x ^ 2 : ℝ) : ℂ) := by
    funext x; simp [sq]
  have hdom : integralDomain μ (fun x => ((f x ^ 2 : ℝ) : ℂ)) ≤
      integralDomain μ (fun x => (f x : ℂ)) := by
    intro ψ hψ
    rw [mem_integralDomain] at hψ ⊢
    have : MeasureTheory.IsFiniteMeasure (μ.assoc ψ) :=
      ⟨by rw [assoc_univ_eq]; exact ENNReal.ofReal_lt_top⟩
    refine (hψ.add (MeasureTheory.memLp_const (1 : ℂ))).of_le hF.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h1 : ‖((f x ^ 2 : ℝ) : ℂ) + 1‖ = f x ^ 2 + 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [Pi.add_apply, h1, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [sq_abs (f x), abs_nonneg (f x)]
  have hcomp := pmapIntegral_comp μ hF hF
  refine ⟨hdom, LinearPMap.ext ?_ ?_⟩
  · ext ψ
    rw [mem_domain_pmapMul_iff]
    have := Set.ext_iff.1 hcomp.1 ψ
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe, hsq] at this
    exact this.trans ⟨fun h => h.2, fun h => ⟨hdom h, h⟩⟩
  · intro ψ h1 h2
    obtain ⟨hx, hy⟩ := (mem_domain_pmapMul_iff _ _ _).1 h1
    rw [pmapMul_apply _ _ ⟨ψ, h1⟩ hy]
    obtain ⟨hfg, e⟩ := hcomp.2 ⟨ψ, hx⟩ hy
    have key : ∀ (g : ℝ → ℂ) (_ : g = fun x => ((f x ^ 2 : ℝ) : ℂ))
        (h : ψ ∈ integralDomain μ g), pmapIntegral μ g ⟨ψ, h⟩ =
          functionalCalculus hA (fun x => ((f x ^ 2 : ℝ) : ℂ)) ⟨ψ, h2⟩ := by
      rintro _ rfl _; rfl
    exact e.symm.trans (key _ hsq hfg)

/--
For a positive, self-adjoint, injective `A`, `A^{-1/2} A^{-1/2} = A⁻¹`, including domains.

Blueprint: lmm:inverse-square-root-product
-/
theorem pmapMul_inv_sqrt_functionalCalculus {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hpos : IsPositive A) (hinj : ker A = ⊥) :
    pmapMul (functionalCalculus hA fun x => (((Real.sqrt x)⁻¹ : ℝ) : ℂ))
        (functionalCalculus hA fun x => (((Real.sqrt x)⁻¹ : ℝ) : ℂ)) =
      A.inverse := by
  have hf : Measurable fun x : ℝ => (Real.sqrt x)⁻¹ := Real.continuous_sqrt.measurable.inv
  rw [(pmapMul_functionalCalculus_self hA hf).2, inverse_eq_functionalCalculus_inv hA hinj]
  refine pmapIntegral_congr_of_null _
    (Complex.measurable_ofReal.comp (hf.pow_const 2))
    (Complex.measurable_ofReal.comp measurable_inv) measurableSet_Iio
    (spectralMeasure_Iio_zero_eq_zero_of_isPositive hA hpos) fun x hx => ?_
  rw [Set.mem_Iio, not_lt] at hx
  rw [inv_pow, Real.sq_sqrt hx]

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
