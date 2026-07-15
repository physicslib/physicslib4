/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.Irreducibility
import Physicslib4.GNS.CauchySchwarz
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Towards the GNS Radon-Nikodym correspondence

For a state `ω` with cyclic GNS representation `(H, π, Ω)` and a positive linear
functional `ψ` dominated by `ω` (`0 ≤ ψ(a* a) ≤ ω(a* a)`), the classical
Radon-Nikodym theorem produces a unique operator `0 ≤ T ≤ 1` in the commutant of
`π(A)` with `ψ(a) = ⟪Ω, T π(a) Ω⟫`. The operator is the bounded sesquilinear form
`(π(a)Ω, π(b)Ω) ↦ ψ(a* b)` represented via Riesz.

This file establishes the analytic crux on which that construction rests: the form
is **well-defined and bounded**, namely

`‖ψ(a* b)‖ ≤ ‖π(a)Ω‖ · ‖π(b)Ω‖`,

obtained from the Cauchy-Schwarz inequality for `ψ` together with domination
(`ψ ≤ ω`) and the GNS reproducing identity `ω(x* x) = ‖π(x)Ω‖²`. As an immediate
consequence the form depends only on the vectors `π(a)Ω, π(b)Ω`, not on the
representatives `a, b`.
-/

namespace Physicslib4
namespace GNS

open scoped ComplexOrder InnerProductSpace

variable {A : Type*} [CStarAlgebra A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The GNS reproducing identity in real-part form: `ω(x* x) = ‖π(x)Ω‖²`. -/
theorem reproducing_norm_sq {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) (x : A) :
    (ω (star x * x)).re = ‖π x Ω‖ ^ 2 := by
  have heq : (ω (star x * x) : ℂ) = ⟪π x Ω, π x Ω⟫_ℂ := by
    have hsplit : π (star x * x) Ω = π (star x) (π x Ω) := by
      rw [map_mul, mul_apply_eq_comp]
    have hadjeq : ContinuousLinearMap.adjoint (π x) = π (star x) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, map_star]
    rw [hrep, hsplit, ← hadjeq, ContinuousLinearMap.adjoint_inner_right]
  rw [heq]
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (π x Ω)

/-- **The GNS form is bounded.** For a positive functional `ψ` dominated by the
state `ω`, the off-diagonal values satisfy
`‖ψ(star a * b)‖² ≤ ‖π a Ω‖² · ‖π b Ω‖²`. -/
theorem gns_form_normSq_le {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    {ψ : A →L[ℂ] ℂ} (hψpos : ∀ a : A, 0 ≤ ψ (star a * a))
    (hψdom : ∀ a : A, ψ (star a * a) ≤ ω (star a * a)) (a b : A) :
    Complex.normSq (ψ (star a * b)) ≤ ‖π a Ω‖ ^ 2 * ‖π b Ω‖ ^ 2 := by
  have hpos' : ∀ c : A, 0 ≤ (ψ : A →ₗ[ℂ] ℂ) (star c * c) := by
    intro c; simpa using hψpos c
  have hcs := cauchy_schwarz_inequality (ψ : A →ₗ[ℂ] ℂ) hpos' a b
  simp only [ContinuousLinearMap.coe_coe] at hcs
  have hda : (ψ (star a * a)).re ≤ (ω (star a * a)).re := (Complex.le_def.mp (hψdom a)).1
  have hdb : (ψ (star b * b)).re ≤ (ω (star b * b)).re := (Complex.le_def.mp (hψdom b)).1
  have hpb : 0 ≤ (ψ (star b * b)).re := (Complex.le_def.mp (hψpos b)).1
  have hoa : 0 ≤ (ω (star a * a)).re := (Complex.le_def.mp (ω.isPositive a)).1
  calc Complex.normSq (ψ (star a * b))
      ≤ (ψ (star a * a)).re * (ψ (star b * b)).re := hcs
    _ ≤ (ω (star a * a)).re * (ω (star b * b)).re := mul_le_mul hda hdb hpb hoa
    _ = ‖π a Ω‖ ^ 2 * ‖π b Ω‖ ^ 2 := by
        rw [reproducing_norm_sq hrep a, reproducing_norm_sq hrep b]

/-- **The GNS form is bounded (norm form).** `‖ψ(star a * b)‖ ≤ ‖π a Ω‖ · ‖π b Ω‖`. -/
theorem gns_form_norm_le {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    {ψ : A →L[ℂ] ℂ} (hψpos : ∀ a : A, 0 ≤ ψ (star a * a))
    (hψdom : ∀ a : A, ψ (star a * a) ≤ ω (star a * a)) (a b : A) :
    ‖ψ (star a * b)‖ ≤ ‖π a Ω‖ * ‖π b Ω‖ := by
  have h := gns_form_normSq_le hrep hψpos hψdom a b
  rw [Complex.normSq_eq_norm_sq] at h
  have hnn : (0 : ℝ) ≤ ‖π a Ω‖ * ‖π b Ω‖ := by positivity
  rw [show ‖π a Ω‖ ^ 2 * ‖π b Ω‖ ^ 2 = (‖π a Ω‖ * ‖π b Ω‖) ^ 2 by ring] at h
  have hsqrt := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hnn] at hsqrt

/-- **The GNS form is well-defined on vectors.** If `π a Ω = π a' Ω`, then
`ψ(star a * b) = ψ(star a' * b)` for every `b`: the form `ψ(star · * ·)` depends
only on the GNS vectors, not on their algebra representatives. -/
theorem gns_form_well_defined {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    {ψ : A →L[ℂ] ℂ} (hψpos : ∀ a : A, 0 ≤ ψ (star a * a))
    (hψdom : ∀ a : A, ψ (star a * a) ≤ ω (star a * a))
    {a a' : A} (haa : π a Ω = π a' Ω) (b : A) :
    ψ (star a * b) = ψ (star a' * b) := by
  have hzero : π (a - a') Ω = 0 := by rw [map_sub, sub_apply, haa, sub_self]
  have hb := gns_form_norm_le hrep hψpos hψdom (a - a') b
  rw [hzero, norm_zero, zero_mul] at hb
  have hψz : ψ (star (a - a') * b) = 0 := norm_le_zero_iff.mp hb
  have hsub0 : ψ (star a * b) - ψ (star a' * b) = 0 := by
    rw [← map_sub]
    have heq : star a * b - star a' * b = star (a - a') * b := by
      rw [star_sub, sub_mul]
    rw [heq]; exact hψz
  exact sub_eq_zero.mp hsub0

open InnerProductSpace

/-- The cyclic map `a ↦ π a Ω` as a `ℂ`-linear map `A →ₗ[ℂ] H`. -/
noncomputable def cycLM (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H) : A →ₗ[ℂ] H where
  toFun a := π a Ω
  map_add' x y := by simp [map_add, add_apply]
  map_smul' c x := by simp [map_smul, smul_apply]

@[simp] theorem cycLM_apply (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H) (a : A) :
    cycLM π Ω a = π a Ω := rfl

theorem cycLM_denseRange {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H} (hcyc : IsCyclicVector π Ω) :
    DenseRange (cycLM π Ω) := hcyc

/-- The linear functional `a ↦ conj (ψ (star a * b))` on `A`, linear in `a`. -/
noncomputable def rnFun (ψ : A →L[ℂ] ℂ) (b : A) : A →ₗ[ℂ] ℂ where
  toFun a := (starRingEnd ℂ) (ψ (star a * b))
  map_add' x y := by simp [star_add, add_mul, map_add]
  map_smul' c x := by
    change (starRingEnd ℂ) (ψ (star (c • x) * b)) = c * (starRingEnd ℂ) (ψ (star x * b))
    rw [star_smul, smul_mul_assoc, map_smul, smul_eq_mul, map_mul, RCLike.star_def,
      Complex.conj_conj]

@[simp] theorem rnFun_apply (ψ : A →L[ℂ] ℂ) (b a : A) :
    rnFun ψ b a = (starRingEnd ℂ) (ψ (star a * b)) := rfl

theorem rnFun_bound {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    {ψ : A →L[ℂ] ℂ} (hψpos : ∀ a : A, 0 ≤ ψ (star a * a))
    (hψdom : ∀ a : A, ψ (star a * a) ≤ ω (star a * a)) (b : A) :
    ∃ C, ∀ a, ‖rnFun ψ b a‖ ≤ C * ‖cycLM π Ω a‖ := by
  refine ⟨‖π b Ω‖, fun a => ?_⟩
  rw [rnFun_apply, RCLike.norm_conj, cycLM_apply, mul_comm]
  exact gns_form_norm_le hrep hψpos hψdom a b

/-- The Riesz vector representing `a ↦ ψ(star a * b)` on the GNS space. -/
noncomputable def rnVec (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H) (ψ : A →L[ℂ] ℂ) (b : A) : H :=
  (toDual ℂ H).symm ((rnFun ψ b).extendOfNorm (cycLM π Ω))

/-- **The reproducing identity (dense level).** `⟪π a Ω, rnVec π Ω ψ b⟫ = ψ(star a * b)`. -/
theorem rnVec_inner {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hcyc : IsCyclicVector π Ω) (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    {ψ : A →L[ℂ] ℂ} (hψpos : ∀ a : A, 0 ≤ ψ (star a * a))
    (hψdom : ∀ a : A, ψ (star a * a) ≤ ω (star a * a)) (a b : A) :
    ⟪π a Ω, rnVec π Ω ψ b⟫_ℂ = ψ (star a * b) := by
  have hsym : ⟪rnVec π Ω ψ b, π a Ω⟫_ℂ = (starRingEnd ℂ) (ψ (star a * b)) := by
    rw [rnVec, toDual_symm_apply]
    have hext := (rnFun ψ b).extendOfNorm_eq (cycLM_denseRange hcyc)
      (rnFun_bound hrep hψpos hψdom b) a
    rw [cycLM_apply] at hext
    rw [hext, rnFun_apply]
  have hconj : ⟪π a Ω, rnVec π Ω ψ b⟫_ℂ = (starRingEnd ℂ) ⟪rnVec π Ω ψ b, π a Ω⟫_ℂ :=
    (inner_conj_symm (π a Ω) (rnVec π Ω ψ b)).symm
  rw [hconj, hsym, Complex.conj_conj]

/-- The Riesz vector is bounded by the cyclic vector norm. -/
theorem rnVec_norm_le {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hcyc : IsCyclicVector π Ω) (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    {ψ : A →L[ℂ] ℂ} (hψpos : ∀ a : A, 0 ≤ ψ (star a * a))
    (hψdom : ∀ a : A, ψ (star a * a) ≤ ω (star a * a)) (b : A) :
    ‖rnVec π Ω ψ b‖ ≤ ‖π b Ω‖ := by
  rw [rnVec, LinearIsometryEquiv.norm_map]
  refine (rnFun ψ b).opNorm_extendOfNorm_le (cycLM_denseRange hcyc) (norm_nonneg _) (fun a => ?_)
  rw [rnFun_apply, RCLike.norm_conj, cycLM_apply, mul_comm]
  exact gns_form_norm_le hrep hψpos hψdom a b

omit [CStarAlgebra A] [CompleteSpace H] in
/-- Two vectors agreeing in all inner products against a dense range are equal. -/
private theorem eq_of_dense_inner_right {f : A → H} (hf : DenseRange f) {x y : H}
    (h : ∀ i, ⟪f i, x⟫_ℂ = ⟪f i, y⟫_ℂ) : x = y := by
  have hz : ∀ i, ⟪f i, x - y⟫_ℂ = 0 := fun i => by rw [inner_sub_right, h i, sub_self]
  have hcont : Continuous (fun w : H => ⟪w, x - y⟫_ℂ) := continuous_id.inner continuous_const
  have heqon : Set.EqOn (fun w : H => ⟪w, x - y⟫_ℂ) (fun _ => (0 : ℂ)) (Set.range f) := by
    rintro _ ⟨i, rfl⟩; exact hz i
  have hxy : x - y = 0 :=
    inner_self_eq_zero.mp (congrFun (Continuous.ext_on hf hcont continuous_const heqon) (x - y))
  exact sub_eq_zero.mp hxy

/-- The assignment `b ↦ rnVec π Ω ψ b`, bundled as a `ℂ`-linear map (linearity is
forced by the reproducing identity and density of the cyclic vectors). -/
noncomputable def rnLM {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hcyc : IsCyclicVector π Ω) (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    {ψ : A →L[ℂ] ℂ} (hψpos : ∀ a : A, 0 ≤ ψ (star a * a))
    (hψdom : ∀ a : A, ψ (star a * a) ≤ ω (star a * a)) : A →ₗ[ℂ] H where
  toFun b := rnVec π Ω ψ b
  map_add' b b' := by
    refine eq_of_dense_inner_right (cycLM_denseRange hcyc) (fun a => ?_)
    simp only [cycLM_apply, inner_add_right, rnVec_inner hcyc hrep hψpos hψdom, mul_add, map_add]
  map_smul' c b := by
    refine eq_of_dense_inner_right (cycLM_denseRange hcyc) (fun a => ?_)
    simp only [cycLM_apply, RingHom.id_apply, inner_smul_right,
      rnVec_inner hcyc hrep hψpos hψdom, mul_smul_comm, map_smul, smul_eq_mul]

/-- The **Radon-Nikodym operator** `T` of a dominated functional `ψ`. -/
noncomputable def rnOp {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hcyc : IsCyclicVector π Ω) (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    {ψ : A →L[ℂ] ℂ} (hψpos : ∀ a : A, 0 ≤ ψ (star a * a))
    (hψdom : ∀ a : A, ψ (star a * a) ≤ ω (star a * a)) : H →L[ℂ] H :=
  (rnLM hcyc hrep hψpos hψdom).extendOfNorm (cycLM π Ω)

/-- **The reproducing identity for the Radon-Nikodym operator.**
`⟪π a Ω, T (π b Ω)⟫ = ψ(star a * b)`. -/
theorem rnOp_inner {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hcyc : IsCyclicVector π Ω) (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    {ψ : A →L[ℂ] ℂ} (hψpos : ∀ a : A, 0 ≤ ψ (star a * a))
    (hψdom : ∀ a : A, ψ (star a * a) ≤ ω (star a * a)) (a b : A) :
    ⟪π a Ω, rnOp hcyc hrep hψpos hψdom (π b Ω)⟫_ℂ = ψ (star a * b) := by
  have hbound : ∃ C, ∀ x, ‖rnLM hcyc hrep hψpos hψdom x‖ ≤ C * ‖cycLM π Ω x‖ :=
    ⟨1, fun x => by rw [one_mul, cycLM_apply]; exact rnVec_norm_le hcyc hrep hψpos hψdom x⟩
  have hext := (rnLM hcyc hrep hψpos hψdom).extendOfNorm_eq (cycLM_denseRange hcyc) hbound b
  rw [cycLM_apply] at hext
  change ⟪π a Ω, (rnLM hcyc hrep hψpos hψdom).extendOfNorm (cycLM π Ω) (π b Ω)⟫_ℂ = _
  rw [hext]
  exact rnVec_inner hcyc hrep hψpos hψdom a b

/-- **The Radon-Nikodym operator commutes with the representation.** -/
theorem rnOp_commute {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hcyc : IsCyclicVector π Ω) (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    {ψ : A →L[ℂ] ℂ} (hψpos : ∀ a : A, 0 ≤ ψ (star a * a))
    (hψdom : ∀ a : A, ψ (star a * a) ≤ ω (star a * a)) (c : A) :
    π c * rnOp hcyc hrep hψpos hψdom = rnOp hcyc hrep hψpos hψdom * π c := by
  set T := rnOp hcyc hrep hψpos hψdom with hT_def
  have hadjeq : ContinuousLinearMap.adjoint (π c) = π (star c) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, map_star]
  have key : ∀ b : A, (π c) (T (π b Ω)) = T ((π c) (π b Ω)) := by
    intro b
    refine eq_of_dense_inner_right (cycLM_denseRange hcyc) (fun a => ?_)
    simp only [cycLM_apply]
    have hRHS : T ((π c) (π b Ω)) = T (π (c * b) Ω) := by
      congr 1; rw [← mul_apply_eq_comp, ← map_mul]
    rw [hRHS, rnOp_inner hcyc hrep hψpos hψdom a (c * b),
      ← ContinuousLinearMap.adjoint_inner_left, hadjeq,
      show (π (star c)) (π a Ω) = π (star c * a) Ω from by
        rw [← mul_apply_eq_comp, ← map_mul],
      rnOp_inner hcyc hrep hψpos hψdom (star c * a) b]
    congr 1
    rw [star_mul, star_star, mul_assoc]
  have hfun : (fun y => (π c) (T y)) = (fun y => T ((π c) y)) := by
    refine Continuous.ext_on (cycLM_denseRange hcyc) ((π c).continuous.comp T.continuous)
      (T.continuous.comp (π c).continuous) ?_
    rintro _ ⟨b, rfl⟩
    simpa using key b
  apply ContinuousLinearMap.ext
  intro y
  rw [mul_apply_eq_comp, mul_apply_eq_comp]
  exact congrFun hfun y

/-- **The reproducing identity for the state.** `ψ(a) = ⟪Ω, T (π a Ω)⟫`. -/
theorem rnOp_reproducing {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hcyc : IsCyclicVector π Ω) (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    {ψ : A →L[ℂ] ℂ} (hψpos : ∀ a : A, 0 ≤ ψ (star a * a))
    (hψdom : ∀ a : A, ψ (star a * a) ≤ ω (star a * a)) (a : A) :
    (ψ a : ℂ) = ⟪Ω, rnOp hcyc hrep hψpos hψdom (π a Ω)⟫_ℂ := by
  have h := rnOp_inner hcyc hrep hψpos hψdom 1 a
  rw [map_one, one_apply_eq_self, star_one, one_mul] at h
  exact h.symm

/-- **Irreducible ⟹ pure.** If the GNS representation of `ω` is irreducible, then
`ω` is pure: every dominated positive functional is a scalar multiple of `ω`. The
Radon-Nikodym operator of a dominated `ψ` commutes with `π`, hence is a scalar by
irreducibility, and the reproducing identity makes `ψ` proportional to `ω`. -/
theorem isPure_of_isIrreducible {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hcyc : IsCyclicVector π Ω) (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ)
    (hirr : IsIrreducible π) : IsPure ω := by
  intro ψ hψpos hψdom
  obtain ⟨c, hc⟩ := hirr (rnOp hcyc hrep hψpos hψdom)
    (fun a => rnOp_commute hcyc hrep hψpos hψdom a)
  refine ⟨c, fun a => ?_⟩
  rw [rnOp_reproducing hcyc hrep hψpos hψdom a, hc,
    smul_apply, one_apply_eq_self, inner_smul_right, ← hrep a]

/-- **The full GNS purity ⟺ irreducibility equivalence.** A state `ω` is pure if
and only if its cyclic GNS representation is irreducible. -/
theorem isPure_iff_isIrreducible {ω : State A} {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {Ω : H}
    (hcyc : IsCyclicVector π Ω) (hrep : ∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) :
    IsPure ω ↔ IsIrreducible π :=
  ⟨fun hpure => isIrreducible_of_isPure hcyc hrep hpure,
   fun hirr => isPure_of_isIrreducible hcyc hrep hirr⟩

/-- **The GNS representation of a pure state is a factor.** For a pure state `ω`
there is a cyclic GNS triple `(H, π, Ω)` reproducing `ω` whose generated von
Neumann algebra `π(A)''` has *trivial center*: the center
`π(A)'' ∩ (π(A)'')'` equals the scalar operators. This combines the GNS
construction, purity ⟹ irreducibility (`isPure_iff_isIrreducible`), and
`center_gnsVonNeumann_eq_of_isIrreducible`. -/
theorem exists_gns_factor_of_isPure.{u} {A : Type u} [CStarAlgebra A]
    {ω : State A} (hpure : IsPure ω) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        IsCyclicVector π Ω ∧
        (∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        gnsVonNeumann π ∩ Set.centralizer (gnsVonNeumann π)
          = {T : H →L[ℂ] H | ∃ c : ℂ, T = c • 1} := by
  obtain ⟨H, i1, i2, i3, π, Ω, hcyc, hrepro, _⟩ := gns_construction ω
  exact ⟨H, i1, i2, i3, π, Ω, hcyc, hrepro,
    center_gnsVonNeumann_eq_of_isIrreducible ((isPure_iff_isIrreducible hcyc hrepro).mp hpure)⟩

/-- **The GNS representation of a pure state generates all of `B(H)`.** For a pure
state `ω` there is a cyclic GNS triple `(H, π, Ω)` reproducing `ω` whose generated von
Neumann algebra is the whole of `B(H)`: `π(A)'' = B(H)`. This is the density
(bicommutant-theorem) sharpening of `exists_gns_factor_of_isPure`, combining the GNS
construction, purity ⟹ irreducibility (`isPure_iff_isIrreducible`), and the density form
`gnsVonNeumann_eq_univ_of_isIrreducible`. -/
theorem exists_gns_generates_all_of_isPure.{u} {A : Type u} [CStarAlgebra A]
    {ω : State A} (hpure : IsPure ω) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        IsCyclicVector π Ω ∧
        (∀ a : A, (ω a : ℂ) = ⟪Ω, π a Ω⟫_ℂ) ∧
        gnsVonNeumann π = Set.univ := by
  obtain ⟨H, i1, i2, i3, π, Ω, hcyc, hrepro, _⟩ := gns_construction ω
  exact ⟨H, i1, i2, i3, π, Ω, hcyc, hrepro,
    gnsVonNeumann_eq_univ_of_isIrreducible ((isPure_iff_isIrreducible hcyc hrepro).mp hpure)⟩

end GNS
end Physicslib4
