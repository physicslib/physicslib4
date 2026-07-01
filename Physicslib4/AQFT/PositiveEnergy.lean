/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Operators.Conjugation
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positive energy of a one-parameter unitary group

The **positive-energy** (spectrum) condition for a strongly continuous one-parameter
unitary group on a Hilbert space, in the *bounded-generator scaffold* form: the group is
`t ↦ exp(i t P)` for a positive bounded operator `P`. This is spacetime-agnostic — it is
shared by the Minkowski (translation) and curved (Killing-flow) spectrum conditions.

The generator of a physical translation/Killing flow is unbounded, so requiring `P`
bounded is a genuine restriction; the faithful unbounded form needs Stone's theorem and
unbounded self-adjoint operators, which Mathlib does not yet provide.

## Main results

* `Physicslib4.AQFT.IsPositiveEnergy` — the bounded-generator positive-energy condition.
* `isPositiveEnergy_const_refl` — the trivial group has positive energy.
* `exp_generator_unique` — the generator is unique.
* `IsPositiveEnergy.conj` — positive energy is a unitary invariant.
* `IsPositiveEnergy.strongContinuous` — a positive-energy group is strongly continuous.
-/

namespace Physicslib4
namespace AQFT

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Positive-energy condition (bounded-generator scaffold).** A one-parameter
unitary group `V : ℝ → (H ≃ₗᵢ[ℂ] H)` has *positive energy* when its generator is a
positive bounded operator: there is `P : H →L[ℂ] H` with `P.IsPositive` (hence
self-adjoint, with non-negative spectrum) such that `V t = exp(i t P)` for every
`t`.

The generator of a physical translation is unbounded, so requiring `P` bounded is a
restriction; the faithful unbounded form needs Stone's theorem and unbounded
self-adjoint operators, absent from Mathlib. The positivity `P.IsPositive` is the
energy-positivity that the spectrum condition asserts. -/
def IsPositiveEnergy (V : ℝ → (H ≃ₗᵢ[ℂ] H)) : Prop :=
  ∃ P : H →L[ℂ] H, P.IsPositive ∧
    ∀ (t : ℝ) (x : H), V t x = NormedSpace.exp (((t : ℂ) * Complex.I) • P) x

omit [CompleteSpace H] in
/-- The constant (trivial) unitary group `t ↦ id` has positive energy, with zero
generator `P = 0`: `exp(0) = 1 = id`, and `0` is a positive operator. -/
theorem isPositiveEnergy_const_refl :
    IsPositiveEnergy (fun _ : ℝ => LinearIsometryEquiv.refl ℂ H) := by
  refine ⟨0, ContinuousLinearMap.isPositive_zero, fun t x => ?_⟩
  simp [smul_zero, NormedSpace.exp_zero]

/-- **Uniqueness of the positive-energy generator.** If two bounded generators induce
the same one-parameter unitary group — `exp(i t P) = exp(i t Q)` for all `t` — they are
equal. Differentiating at `t = 0` gives `i \cdot P = i \cdot Q`, hence `P = Q`;
positivity is not needed. So the generator witnessing `IsPositiveEnergy` is unique. -/
theorem exp_generator_unique {P Q : H →L[ℂ] H}
    (h : ∀ (t : ℝ) (x : H),
      NormedSpace.exp (((t : ℂ) * Complex.I) • P) x
        = NormedSpace.exp (((t : ℂ) * Complex.I) • Q) x) :
    P = Q := by
  have hfun : (fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • P))
      = (fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • Q)) := by
    funext t; exact ContinuousLinearMap.ext (h t)
  have hderiv : ∀ R : H →L[ℂ] H,
      HasDerivAt (fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • R))
        (Complex.I • R) 0 := by
    intro R
    have hc := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • R) (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hc
    have hfeq : (fun u : ℝ => NormedSpace.exp (u • (Complex.I • R)))
        = (fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • R)) := by
      funext u; rw [← Complex.coe_smul, smul_smul]
    rwa [hfeq] at hc
  have hP := hderiv P
  have hQ := hderiv Q
  rw [hfun] at hP
  have key : Complex.I • P = Complex.I • Q := hP.unique hQ
  exact smul_right_injective (H →L[ℂ] H) Complex.I_ne_zero key

/-- **Positive energy is a unitary invariant.** If a one-parameter unitary group `V`
has positive energy, so does its conjugate `t ↦ W ∘ V t ∘ W⁻¹` by a unitary `W`, with
generator `W P W⁻¹` (positive, being the unitary conjugate of the positive generator
`P`). Physically: the spectrum condition does not depend on the choice of unitary
frame. -/
theorem IsPositiveEnergy.conj (W : H ≃ₗᵢ[ℂ] H) {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : IsPositiveEnergy V) :
    IsPositiveEnergy (fun t => (W.symm.trans (V t)).trans W) := by
  obtain ⟨P, hPpos, hPexp⟩ := hV
  refine ⟨lieConj W P, ?_, fun t x => ?_⟩
  · refine ContinuousLinearMap.isPositive_def.mpr ⟨fun a b => ?_, fun x => ?_⟩
    · simp only [ContinuousLinearMap.coe_coe, lieConj_apply]
      calc ⟪W (P (W.symm a)), b⟫_ℂ
          = ⟪W (P (W.symm a)), W (W.symm b)⟫_ℂ := by rw [W.apply_symm_apply]
        _ = ⟪P (W.symm a), W.symm b⟫_ℂ := W.inner_map_map _ _
        _ = ⟪W.symm a, P (W.symm b)⟫_ℂ := (ContinuousLinearMap.isPositive_def.mp hPpos).1 _ _
        _ = ⟪W (W.symm a), W (P (W.symm b))⟫_ℂ := (W.inner_map_map _ _).symm
        _ = ⟪a, W (P (W.symm b))⟫_ℂ := by rw [W.apply_symm_apply]
    · rw [ContinuousLinearMap.reApplyInnerSelf_apply, lieConj_apply]
      have key : ⟪W (P (W.symm x)), x⟫_ℂ = ⟪P (W.symm x), W.symm x⟫_ℂ := by
        rw [← W.inner_map_map (P (W.symm x)) (W.symm x), W.apply_symm_apply]
      rw [key]
      have hpp := (ContinuousLinearMap.isPositive_def.mp hPpos).2 (W.symm x)
      rwa [ContinuousLinearMap.reApplyInnerSelf_apply] at hpp
  · change ((W.symm.trans (V t)).trans W) x
        = NormedSpace.exp (((t : ℂ) * Complex.I) • lieConj W P) x
    rw [← lieConj_smul, exp_lieConj, lieConj_apply,
      LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply,
      hPexp t (W.symm x)]

/-- **A positive-energy group is strongly continuous.** The bounded-generator scaffold
`V t = exp(i t P)` is automatically strongly continuous: `t ↦ V t x` is continuous for
every `x`, since `t ↦ (i t) • P` is continuous and the operator exponential is
continuous. This justifies describing a positive-energy group as a *strongly continuous*
one-parameter unitary group. -/
theorem IsPositiveEnergy.strongContinuous {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : IsPositiveEnergy V) (x : H) : Continuous (fun t : ℝ => V t x) := by
  obtain ⟨P, _, hPexp⟩ := hV
  haveI : NormedAlgebra ℚ (H →L[ℂ] H) :=
    NormedAlgebra.restrictScalars ℚ ℂ (H →L[ℂ] H)
  have hfun : (fun t : ℝ => V t x)
      = fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • P) x := by
    funext t; exact hPexp t x
  rw [hfun]
  have harg : Continuous (fun t : ℝ => ((t : ℂ) * Complex.I) • P) :=
    (Complex.continuous_ofReal.mul continuous_const).smul continuous_const
  exact (NormedSpace.exp_continuous.comp harg).clm_apply continuous_const

end AQFT
end Physicslib4
