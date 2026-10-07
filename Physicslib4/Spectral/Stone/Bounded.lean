/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Stone.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The unitary group of a bounded self-adjoint operator

For a bounded operator `P`, `t ↦ exp(itP)` (the norm-convergent exponential series) is
differentiable at `0` with derivative `iP`; for self-adjoint `P` it is a one-parameter unitary
group, strongly continuous, with generator `P` on all of `H` (blueprint §10.4.1).
-/

namespace Physicslib4
namespace Spectral
namespace Stone

open scoped InnerProductSpace LinearPMap Topology
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
`t ↦ exp(itP)` is differentiable at `0` in the operator norm, with derivative `iP`.

Blueprint reference: `lmm:exp-bounded-hasDerivAt`.
-/
theorem hasDerivAt_exp_smul_I (P : H →L[ℂ] H) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • P)) (Complex.I • P) 0 := by
  have hc := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • P) (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hc
  have hfeq : (fun u : ℝ => NormedSpace.exp (u • (Complex.I • P)))
      = (fun t : ℝ => NormedSpace.exp (((t : ℂ) * Complex.I) • P)) := by
    funext u; rw [← Complex.coe_smul, smul_smul]
  rwa [hfeq] at hc

/--
For bounded self-adjoint `P`, `t ↦ exp(itP)` is a one-parameter unitary group: each
`exp(itP)` is unitary, and the resulting family of linear isometry equivalences satisfies the
group law.

Blueprint reference: `lmm:exp-bounded-unitary-group`.
-/
theorem exists_isOneParameterUnitaryGroup_exp {P : H →L[ℂ] H} (hP : IsSelfAdjoint P) :
    ∃ V : ℝ → (H ≃ₗᵢ[ℂ] H), (∀ (t : ℝ) (x : H),
        V t x = NormedSpace.exp (((t : ℂ) * Complex.I) • P) x) ∧
      IsOneParameterUnitaryGroup V := by
  let _ : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ (H →L[ℂ] H)
  have mem : ∀ t : ℝ, NormedSpace.exp (((t : ℂ) * Complex.I) • P) ∈ unitary (H →L[ℂ] H) :=
    fun t => NormedSpace.exp_mem_unitary_of_mem_skewAdjoint <| by
      rw [skewAdjoint.mem_iff, star_smul, hP.star_eq, star_mul', Complex.star_def,
        Complex.conj_ofReal, Complex.conj_I, ← neg_smul]
      congr 1; ring
  refine ⟨fun t => Unitary.linearIsometryEquiv ⟨_, mem t⟩, fun t x => rfl, ⟨fun ψ => ?_, ?_⟩⟩
  · change NormedSpace.exp ((((0 : ℝ) : ℂ) * Complex.I) • P) ψ = ψ
    simp
  · intro s t ψ
    change NormedSpace.exp ((((s + t : ℝ) : ℂ) * Complex.I) • P) ψ
      = NormedSpace.exp (((s : ℂ) * Complex.I) • P)
          (NormedSpace.exp (((t : ℂ) * Complex.I) • P) ψ)
    have hc : Commute (((s : ℂ) * Complex.I) • P) (((t : ℂ) * Complex.I) • P) :=
      ((Commute.refl P).smul_left _).smul_right _
    rw [show (((s + t : ℝ) : ℂ) * Complex.I) • P
        = ((s : ℂ) * Complex.I) • P + ((t : ℂ) * Complex.I) • P by
          push_cast; rw [← add_smul, add_mul],
      NormedSpace.exp_add_of_commute hc]
    rfl

/--
A unitary family `V` with `V t = exp(itP)` is strongly continuous. The blueprint takes `P`
self-adjoint, which is what makes `exp(itP)` unitary; here unitarity is carried by the type
of `V`, so no hypothesis on `P` is needed.

Blueprint reference: `lmm:generator-exp-bounded`.
-/
theorem isStronglyContinuous_of_eq_exp {P : H →L[ℂ] H} {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : ∀ (t : ℝ) (x : H), V t x = NormedSpace.exp (((t : ℂ) * Complex.I) • P) x) :
    IsStronglyContinuous V := by
  have : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ (H →L[ℂ] H)
  intro ψ
  simp_rw [hV]
  exact (NormedSpace.exp_continuous.comp
    ((Complex.continuous_ofReal.mul continuous_const).smul continuous_const)).clm_apply
    continuous_const

/--
A unitary family `V` with `V t = exp(itP)` has generator `P`, with domain `H`. As for
`isStronglyContinuous_of_eq_exp`, no hypothesis on `P` is needed.

Blueprint reference: `lmm:generator-exp-bounded`.
-/
theorem generator_eq_of_eq_exp {P : H →L[ℂ] H} {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : ∀ (t : ℝ) (x : H), V t x = NormedSpace.exp (((t : ℂ) * Complex.I) • P) x) :
    generator V = (P : H →ₗ[ℂ] H).toPMap ⊤ := by
  have key : ∀ ψ : H, Tendsto (generatorQuotient V ψ) (𝓝[≠] 0) (𝓝 (P ψ)) := by
    intro ψ
    have hd := (hasDerivAt_exp_smul_I P).tendsto_slope_zero
    have h2 := (((ContinuousLinearMap.apply ℂ H ψ).continuous.tendsto _).comp hd).const_smul
      Complex.I⁻¹
    have h3 : Complex.I⁻¹ • (ContinuousLinearMap.apply ℂ H ψ) (Complex.I • P) = P ψ := by
      simp [smul_smul]
    rw [h3] at h2
    refine h2.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
    simp [generatorQuotient, hV, ← Complex.coe_smul, smul_smul, mul_comm]
  refine LinearPMap.ext (Submodule.eq_top_iff'.2 fun ψ =>
    ((exists_generator_eq_iff V ψ (P ψ)).2 (key ψ)).1) fun x _ _ => ?_
  obtain ⟨_, e⟩ := (exists_generator_eq_iff V x (P x)).2 (key x)
  exact e

end Stone
end Spectral
end Physicslib4
