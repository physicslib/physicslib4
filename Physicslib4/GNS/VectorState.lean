/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Vector functionals on a C*-algebra of operators

For a norm-closed unital `*`-subalgebra `𝔄` of `B(H)` and a unit vector `Ω`, the vector functional
`ω_Ω(x) = ⟪Ω, xΩ⟫` is a positive continuous linear functional of norm `1` on the C*-algebra `𝔄`
(`StarSubalgebra.cstarAlgebra`). The functional is written inline as
`fun x : 𝔄 => ⟪Ω, (x : H →L[ℂ] H) Ω⟫` in the lemmas, and bundled as the state `vectorState`
when `𝔄` is norm-closed.
-/

namespace Physicslib4.GNS

open scoped InnerProductSpace ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a unital `*`-subalgebra `𝔄` of `B(H)` and `‖Ω‖ = 1`, `x ↦ ⟪Ω, xΩ⟫` is a
continuous linear functional on `𝔄` with `‖ω_Ω‖ ≤ 1` and `0 ≤ ω_Ω(x* x)`.
Blueprint: lmm:vector-functional-state -/
theorem exists_vectorFunctional (𝔄 : StarSubalgebra ℂ (H →L[ℂ] H)) {Ω : H} (hΩ : ‖Ω‖ = 1) :
    ∃ ω : 𝔄 →L[ℂ] ℂ, (∀ x : 𝔄, ω x = ⟪Ω, (x : H →L[ℂ] H) Ω⟫_ℂ) ∧ ‖ω‖ ≤ 1 ∧
      ∀ x : 𝔄, 0 ≤ ω (star x * x) := by
  refine ⟨(innerSL ℂ Ω).comp ((ContinuousLinearMap.apply ℂ H Ω).comp
    { toLinearMap := 𝔄.subtype.toAlgHom.toLinearMap, cont := continuous_subtype_val }),
    fun _ => rfl, ?_, fun x => ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    change ‖⟪Ω, (x : H →L[ℂ] H) Ω⟫_ℂ‖ ≤ 1 * ‖x‖
    calc ‖⟪Ω, (x : H →L[ℂ] H) Ω⟫_ℂ‖ ≤ ‖Ω‖ * ‖(x : H →L[ℂ] H) Ω‖ := norm_inner_le_norm _ _
      _ ≤ ‖Ω‖ * (‖(x : H →L[ℂ] H)‖ * ‖Ω‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = 1 * ‖x‖ := by rw [hΩ]; simp
  · change 0 ≤ ⟪Ω, star (x : H →L[ℂ] H) ((x : H →L[ℂ] H) Ω)⟫_ℂ
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    exact pow_nonneg (RCLike.ofReal_nonneg.mpr (norm_nonneg _)) 2

/-- With `𝔄` and `Ω` as in `exists_vectorFunctional`, the vector functional has norm `1`.
Blueprint: lmm:vector-functional-norm-one -/
theorem norm_vectorFunctional (𝔄 : StarSubalgebra ℂ (H →L[ℂ] H)) {Ω : H} (hΩ : ‖Ω‖ = 1)
    (ω : 𝔄 →L[ℂ] ℂ) (hω : ∀ x : 𝔄, ω x = ⟪Ω, (x : H →L[ℂ] H) Ω⟫_ℂ) :
    ‖ω‖ = 1 := by
  sorry

/-- The *vector state* `ω_Ω(x) = ⟪Ω, xΩ⟫` of a unit vector `Ω` on a norm-closed unital
`*`-subalgebra `𝔄` of `B(H)`, a C*-algebra by `StarSubalgebra.cstarAlgebra`. Positivity is
`exists_vectorFunctional` and normalisation is `norm_vectorFunctional`.
Blueprint: def:vector-state -/
noncomputable def vectorState (𝔄 : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (𝔄 : Set (H →L[ℂ] H))]
    (Ω : H) (hΩ : ‖Ω‖ = 1) : State 𝔄 where
  toContinuousLinearMap := (innerSL ℂ Ω).comp ((ContinuousLinearMap.apply ℂ H Ω).comp
    { toLinearMap := 𝔄.subtype.toAlgHom.toLinearMap, cont := continuous_subtype_val })
  isPositive x := by
    obtain ⟨ω, hω, -, hpos⟩ := exists_vectorFunctional 𝔄 hΩ
    change 0 ≤ ⟪Ω, ((star x * x : 𝔄) : H →L[ℂ] H) Ω⟫_ℂ
    rw [← hω]
    exact hpos x
  isNormalized := norm_vectorFunctional 𝔄 hΩ _ fun _ => rfl

/-- The vector state takes the value `⟪Ω, xΩ⟫` at `x`. -/
@[simp]
theorem vectorState_apply (𝔄 : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (𝔄 : Set (H →L[ℂ] H))]
    {Ω : H} (hΩ : ‖Ω‖ = 1) (x : 𝔄) :
    vectorState 𝔄 Ω hΩ x = ⟪Ω, (x : H →L[ℂ] H) Ω⟫_ℂ :=
  rfl

end Physicslib4.GNS
