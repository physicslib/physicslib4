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
The spectral measure μ(A) of a self-adjoint operator A: the unique projection-valued measure on
the Borel sets of ℝ with ∫ λ dμ(A)(λ) = A.

For a Borel set E, μ(A)(E) is the projection onto the states in which a measurement of A gives
a value in E with certainty, and E ↦ ⟨ψ, μ(A)(E)ψ⟩ is the probability distribution of A in the
unit vector ψ. Its defining property is `pmapIntegral_spectralMeasure`, its uniqueness
`eq_spectralMeasure_of_pmapIntegral`, and Dom(A) is the set of ψ with ∫ λ² finite against that
distribution (`domain_eq_integralDomain_spectralMeasure`).

Implementation note: the measure is the one supplied by the spectral theorem
`existsUnique_spectralMeasure_unbounded`, extracted with `Exists.choose`; by uniqueness no
choice is involved in its value.

Blueprint: def:spectral-measure
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
The functional calculus of a self-adjoint operator A: the operator f(A) = ∫ f(λ) dμ(A)(λ) for a
measurable function f : ℝ → ℂ, possibly unbounded, with domain the vectors ψ for which
∫ |f|² is finite against the spectral distribution of ψ.

This gives a meaning to any measurable function of an observable: the Hamiltonian H gives the
time evolution e^(−itH), a position operator gives the projections onto regions of space, and
so on. When f(λ) = λ one recovers A itself (`functionalCalculus_id`). A bounded f gives a
bounded operator defined on all of H, equal to the bounded integral of f against μ(A)
(`functionalCalculus_of_bddMeasurable`); this is the case of the unitary group e^(itA) of
Stone's theorem.

Implementation note: the operator is `pmapIntegral` for `spectralMeasure`, with domain
`integralDomain` (`functionalCalculus_domain`). Measurability of f is not part of the
definition; the results about f(A) assume it where they need it. The properties proved for
`pmapIntegral` transfer to it through this definition.

Blueprint: def:hall-10.5
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
For a bounded measurable function f, the operator f(A) is defined on all of H and equals the
bounded integral of f against the spectral measure of A.

So for bounded f the unbounded and the bounded theories agree: f(A) is an ordinary bounded
operator, and the properties of the bounded integral apply to it
(`ProjectionValuedMeasure.integral_mul`, `ProjectionValuedMeasure.integral_conj`,
`ProjectionValuedMeasure.norm_integral_le`). The unitary group e^(itA) of Stone's theorem is of this
kind.

Implementation note: the conclusion has two parts, the domain being `⊤` and the equality of
f(A) with the bounded integral `(spectralMeasure hA).integral f`, regarded as a partial linear
map with domain `⊤` (`LinearMap.toPMap`).

Blueprint: lmm:functional-calculus-bounded
-/
theorem functionalCalculus_of_bddMeasurable (hA : IsSelfAdjoint A) {f : ℝ → ℂ}
    (hf : f ∈ BddMeasurable ℝ) :
    (functionalCalculus hA f).domain = ⊤ ∧
      functionalCalculus hA f = (((spectralMeasure hA).integral f : H →ₗ[ℂ] H).toPMap ⊤) :=
  ⟨integralDomain_eq_top_of_bddMeasurable _ hf, pmapIntegral_of_bddMeasurable _ hf⟩

end Unbounded
end Spectral
end Physicslib4
