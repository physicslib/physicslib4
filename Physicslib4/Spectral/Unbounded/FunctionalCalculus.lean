/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Unbounded.Cayley

/-!
# The functional calculus of an unbounded self-adjoint operator

The spectral theorem for unbounded self-adjoint operators
(`existsUnique_spectralMeasure_unbounded`) supplies, for a self-adjoint `A`, a unique
projection-valued measure `μ^A` on `ℝ` with `∫ λ dμ^A(λ) = A`. This file names that measure
and defines `f(A) := ∫ f dμ^A` for measurable `f : ℝ → ℂ`, with domain `W_f`.

## Main definitions

* `spectralMeasure hA` — the spectral measure `μ^A` of a self-adjoint operator `A`.
* `functionalCalculus hA f` — the (possibly unbounded) operator `f(A)`.

## Main statements

* `pmapIntegral_spectralMeasure` — `∫ λ dμ^A = A`.
* `eq_spectralMeasure_of_pmapIntegral` — uniqueness of `μ^A`.
* `functionalCalculus_of_bddMeasurable` — for bounded measurable `f`, `W_f = H` and `f(A)`
  is the bounded integral of `f` against `μ^A`.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/--
The *spectral measure* `μ^A` of a self-adjoint operator `A`: the unique projection-valued
measure on the Borel sets of `ℝ` with `∫ λ dμ^A(λ) = A`, supplied by
`existsUnique_spectralMeasure_unbounded`.

Blueprint reference: `def:spectral-measure`.
-/
noncomputable def spectralMeasure (hA : IsSelfAdjoint A) : ProjectionValuedMeasure ℝ H :=
  (existsUnique_spectralMeasure_unbounded hA).exists.choose

/--
The spectral measure integrates the identity function to `A`.

Blueprint reference: `def:spectral-measure`.
-/
theorem pmapIntegral_spectralMeasure (hA : IsSelfAdjoint A) :
    pmapIntegral (spectralMeasure hA) (fun x : ℝ => (x : ℂ)) = A :=
  (existsUnique_spectralMeasure_unbounded hA).exists.choose_spec

/--
The spectral measure is the only projection-valued measure on `ℝ` integrating the identity
function to `A`.

Blueprint reference: `def:spectral-measure`.
-/
theorem eq_spectralMeasure_of_pmapIntegral (hA : IsSelfAdjoint A)
    {μ : ProjectionValuedMeasure ℝ H} (hμ : pmapIntegral μ (fun x : ℝ => (x : ℂ)) = A) :
    μ = spectralMeasure hA :=
  (existsUnique_spectralMeasure_unbounded hA).unique hμ (pmapIntegral_spectralMeasure hA)

/--
`Dom(A) = W_ι` for the identity function `ι(λ) = λ`: the vectors `ψ` with
`∫ λ² dμ^A_ψ(λ) < ∞`.

Blueprint reference: `def:spectral-measure`.
-/
theorem domain_eq_integralDomain_spectralMeasure (hA : IsSelfAdjoint A) :
    A.domain = integralDomain (spectralMeasure hA) (fun x : ℝ => (x : ℂ)) := by
  conv_lhs => rw [← pmapIntegral_spectralMeasure hA]
  rfl

/--
The *functional calculus* of a self-adjoint operator `A`: for measurable `f : ℝ → ℂ`,
`f(A) := ∫ f dμ^A`, a possibly unbounded operator with domain `W_f`
(`functionalCalculus_domain`). Measurability of `f` is not part of the definition; the
results about `f(A)` assume it where they need it.

Blueprint reference: `def:hall-10.5`.
-/
noncomputable def functionalCalculus (hA : IsSelfAdjoint A) (f : ℝ → ℂ) : H →ₗ.[ℂ] H :=
  pmapIntegral (spectralMeasure hA) f

/--
The domain of `f(A)` is `W_f`, the vectors `ψ` with `∫ |f|² dμ^A_ψ < ∞`.

Blueprint reference: `def:hall-10.5`.
-/
theorem functionalCalculus_domain (hA : IsSelfAdjoint A) (f : ℝ → ℂ) :
    (functionalCalculus hA f).domain = integralDomain (spectralMeasure hA) f :=
  rfl

/--
For the identity function, the functional calculus recovers `A`.

Blueprint reference: `def:hall-10.5`.
-/
theorem functionalCalculus_id (hA : IsSelfAdjoint A) :
    functionalCalculus hA (fun x : ℝ => (x : ℂ)) = A :=
  pmapIntegral_spectralMeasure hA

/--
For bounded measurable `f`, `W_f = H` and `f(A)` is the bounded integral `∫ f dμ^A` of
`f` against the spectral measure; in particular `f(A)` is bounded and everywhere defined.

Blueprint reference: `lmm:functional-calculus-bounded`.
-/
theorem functionalCalculus_of_bddMeasurable (hA : IsSelfAdjoint A) {f : ℝ → ℂ}
    (hf : f ∈ BddMeasurable ℝ) :
    (functionalCalculus hA f).domain = ⊤ ∧
      functionalCalculus hA f = (((spectralMeasure hA).integral f : H →ₗ[ℂ] H).toPMap ⊤) :=
  ⟨integralDomain_eq_top_of_bddMeasurable _ hf, pmapIntegral_of_bddMeasurable _ hf⟩

end Unbounded
end Spectral
end Physicslib4
