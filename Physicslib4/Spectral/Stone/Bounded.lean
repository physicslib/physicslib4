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
  sorry

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
  sorry

/--
A unitary family `V` with `V t = exp(itP)` is strongly continuous. The blueprint takes `P`
self-adjoint, which is what makes `exp(itP)` unitary; here unitarity is carried by the type
of `V`, so no hypothesis on `P` is needed.

Blueprint reference: `lmm:generator-exp-bounded`.
-/
theorem isStronglyContinuous_of_eq_exp {P : H →L[ℂ] H} {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : ∀ (t : ℝ) (x : H), V t x = NormedSpace.exp (((t : ℂ) * Complex.I) • P) x) :
    IsStronglyContinuous V := by
  sorry

/--
A unitary family `V` with `V t = exp(itP)` has generator `P`, with domain `H`. As for
`isStronglyContinuous_of_eq_exp`, no hypothesis on `P` is needed.

Blueprint reference: `lmm:generator-exp-bounded`.
-/
theorem generator_eq_of_eq_exp {P : H →L[ℂ] H} {V : ℝ → (H ≃ₗᵢ[ℂ] H)}
    (hV : ∀ (t : ℝ) (x : H), V t x = NormedSpace.exp (((t : ℂ) * Complex.I) • P) x) :
    generator V = (P : H →ₗ[ℂ] H).toPMap ⊤ := by
  sorry

end Stone
end Spectral
end Physicslib4
