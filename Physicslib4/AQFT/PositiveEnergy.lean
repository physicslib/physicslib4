/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Stone.Bounded
import Physicslib4.Spectral.Stone.Theorem
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positive energy of a one-parameter unitary group

The **positive-energy** (spectrum) condition for a one-parameter unitary group on a Hilbert
space: the group is strongly continuous and its infinitesimal generator is a positive
operator. By Stone's theorem the generator is then self-adjoint and `V(t) = e^{itA}`
(`isPositiveEnergy_iff_exists_exp`). This is spacetime-agnostic: it is shared by the
Minkowski (translation) and curved (Killing-flow) spectrum conditions.

## Main results

* `Physicslib4.AQFT.IsPositiveEnergy` — the positive-energy condition.
* `isPositiveEnergy_const_refl` — the trivial group has positive energy.
* `generator_eq_of_eq_expUnitary` — the generator is the unique `B` with `V(t) = e^{itB}`.
* `IsPositiveEnergy.conj` — positive energy is a unitary invariant.
* `IsPositiveEnergy.strongContinuous` — a positive-energy group is strongly continuous.
* `isPositiveEnergy_exp` — the bounded case `V(t) = exp(itP)`, `P ≥ 0`.
* `isPositiveEnergy_iff_exists_exp` — the exponential form, via Stone's theorem.
-/

namespace Physicslib4
namespace AQFT

open scoped InnerProductSpace
open Spectral.Stone

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Positive-energy condition.** A family `V : ℝ → (H ≃ₗᵢ[ℂ] H)` of unitaries has
*positive energy* when it is a strongly continuous one-parameter unitary group whose
infinitesimal generator `A` is a positive operator: `A` is symmetric and `⟪ψ, A ψ⟫ ≥ 0` on
`Dom(A)`. By Stone's theorem `A` is then self-adjoint and `V(t) = e^{itA}`
(`isPositiveEnergy_iff_exists_exp`). The positivity of the generator is the
energy-positivity asserted by the spectrum condition.

Blueprint reference: `def:positive-energy`. -/
structure IsPositiveEnergy (V : ℝ → (H ≃ₗᵢ[ℂ] H)) : Prop where
  /-- `V` is a one-parameter unitary group. -/
  isOneParameterUnitaryGroup : IsOneParameterUnitaryGroup V
  /-- `V` is strongly continuous. -/
  isStronglyContinuous : IsStronglyContinuous V
  /-- The infinitesimal generator of `V` is a positive operator. -/
  isPositive_generator : Spectral.Unbounded.IsPositive (generator V)

omit [CompleteSpace H] in
/-- The constant (trivial) unitary group `t ↦ id` has positive energy, with generator `0`
on all of `H`.

Blueprint reference: `lmm:positive-energy-const`. -/
theorem isPositiveEnergy_const_refl :
    IsPositiveEnergy (fun _ : ℝ => LinearIsometryEquiv.refl ℂ H) := by
  refine ⟨isOneParameterUnitaryGroup_refl, isStronglyContinuous_refl, ?_⟩
  rw [generator_refl]
  refine ⟨fun x y => ?_, fun ψ => ?_⟩ <;> simp

/-- **Uniqueness of a bounded generator.** If two bounded operators induce the same
one-parameter unitary group — `exp(i t P) = exp(i t Q)` for all `t` — they are equal.
Differentiating at `t = 0` gives `i P = i Q`, hence `P = Q`. The unbounded form is
`generator_eq_of_eq_expUnitary`.

Blueprint reference: `lmm:exp-generator-unique`. -/
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

/-- **Uniqueness of the generator.** If `V(t) = e^{itB}` for all `t`, with `B`
self-adjoint, then `B` is the infinitesimal generator of `V`, with equality of domains. In
particular the positive operator witnessing positive energy is unique.

Blueprint reference: `lmm:exp-generator-unique`. -/
theorem generator_eq_of_eq_expUnitary {V : ℝ → (H ≃ₗᵢ[ℂ] H)} {B : H →ₗ.[ℂ] H}
    (hB : IsSelfAdjoint B) (h : ∀ t, V t = expUnitary hB t) : generator V = B := by
  obtain rfl : V = expUnitary hB := funext h
  exact (generator_expUnitary hB).2.2

omit [CompleteSpace H] in
/-- **Positive energy is a unitary invariant.** If `V` has positive energy, so does its
conjugate `t ↦ W ∘ V t ∘ W⁻¹` by a unitary `W`, with generator `W A W⁻¹` on `W · Dom(A)`.
Physically: the spectrum condition does not depend on the choice of unitary frame.

Blueprint reference: `lmm:positive-energy-conj`. -/
theorem IsPositiveEnergy.conj (W : H ≃ₗᵢ[ℂ] H) {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : IsPositiveEnergy V) :
    IsPositiveEnergy (fun t => (W.symm.trans (V t)).trans W) :=
  ⟨hV.isOneParameterUnitaryGroup.conj W, hV.isStronglyContinuous.conj W,
    hV.isPositive_generator.of_conj W (mem_generator_conj_domain_iff V W)
      (generator_conj_apply V W)⟩

omit [CompleteSpace H] in
/-- **A positive-energy group is strongly continuous**: `t ↦ V t x` is continuous for every
`x`. This is part of the definition.

Blueprint reference: `lmm:positive-energy-strong-continuous`. -/
theorem IsPositiveEnergy.strongContinuous {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : IsPositiveEnergy V) (x : H) : Continuous (fun t : ℝ => V t x) :=
  hV.isStronglyContinuous x

/-- **The bounded case.** If `P` is a bounded positive operator and `V(t) = exp(itP)` (the
norm-convergent exponential series), then `V` has positive energy, with generator `P` on
all of `H`.

Blueprint reference: `lmm:positive-energy-exp-bounded`. -/
theorem isPositiveEnergy_exp {P : H →L[ℂ] H} (hP : P.IsPositive) {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : ∀ (t : ℝ) (x : H), V t x = NormedSpace.exp (((t : ℂ) * Complex.I) • P) x) :
    IsPositiveEnergy V := by
  obtain ⟨V', hV', hgrp⟩ := exists_isOneParameterUnitaryGroup_exp hP.isSelfAdjoint
  obtain rfl : V = V' :=
    funext fun t => LinearIsometryEquiv.ext fun x => (hV t x).trans (hV' t x).symm
  exact ⟨hgrp, isStronglyContinuous_of_eq_exp hV,
    (generator_eq_of_eq_exp hV) ▸ (Spectral.Unbounded.isPositive_toPMap_iff P).mpr hP⟩

/-- **Positive energy in exponential form.** `V` has positive energy if and only if there is
a positive self-adjoint operator `A` with `V(t) = e^{itA}` for all `t`.

Blueprint reference: `thrm:positive-energy-iff-exp`. -/
theorem isPositiveEnergy_iff_exists_exp {V : ℝ → (H ≃ₗᵢ[ℂ] H)} :
    IsPositiveEnergy V ↔ ∃ (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A),
      Spectral.Unbounded.IsPositive A ∧ ∀ t, V t = expUnitary hA t := by
  refine ⟨fun hV => ?_, fun ⟨A, hA, hpos, h⟩ => ?_⟩
  · obtain ⟨hA, -, hexp, -⟩ := stone hV.isOneParameterUnitaryGroup hV.isStronglyContinuous
    exact ⟨generator V, hA, hV.isPositive_generator, hexp⟩
  · obtain rfl : V = expUnitary hA := funext h
    obtain ⟨hgrp, hc, hgen⟩ := generator_expUnitary hA
    exact ⟨hgrp, hc, hgen.symm ▸ hpos⟩

end AQFT
end Physicslib4
