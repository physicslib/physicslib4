/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spectral.Unbounded.FunctionalCalculus

/-!
# Composition in the unbounded functional calculus

For a projection-valued measure `μ` and measurable functions `f, g`, this file states the
composition law `f(μ) g(μ) ⊆ (fg)(μ)` with its domain identity, together with the facts it
rests on: dominated convergence for the spectral integral, composition with a bounded function on
the left, the associated measure `μ_{h(μ)ψ} = |h|² μ_ψ` for unbounded `h`, and the commutation of
`h(μ)` with the spectral projections. For a self-adjoint `A` and a real measurable `f`, it states
that `f(A)` is self-adjoint and closed, and that `Dom A ∩ Dom f(A)` is a core for `f(A)`.

Throughout, `h(μ)` is `pmapIntegral μ h`, with domain `W_h = integralDomain μ h`, and for bounded
`u` the bounded operator `u(μ)` is `μ.integral u`.
-/

namespace Physicslib4
namespace Spectral
namespace Unbounded

open scoped InnerProductSpace LinearPMap ENNReal NNReal
open Filter Topology ContinuousLinearMap MeasureTheory

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μ : ProjectionValuedMeasure X H)

/--
Let `h` be measurable, `ψ ∈ W_h`, and let `hₙ` be bounded measurable functions with `hₙ → h`
pointwise and `|hₙ| ≤ |h|`. With the truncations `tₙ = h · 1_{|h| < n}`, the distance
`‖hₙ(μ)ψ - tₙ(μ)ψ‖` tends to `0`.

Blueprint: lmm:fc-difference-to-truncation
-/
theorem tendsto_norm_integral_sub_truncation {h : X → ℂ} (hh : Measurable h)
    (ψ : integralDomain μ h) {hn : ℕ → X → ℂ} (hbdd : ∀ n, hn n ∈ BddMeasurable X)
    (hlim : ∀ x, Tendsto (fun n => hn n x) atTop (𝓝 (h x)))
    (hle : ∀ n x, ‖hn n x‖ ≤ ‖h x‖) :
    Tendsto (fun n : ℕ => ‖μ.integral (hn n) (ψ : H) -
      μ.integral ({x | ‖h x‖ < n}.indicator h) (ψ : H)‖) atTop (𝓝 0) := by
  sorry

/--
Dominated convergence for the spectral integral: let `h` be measurable, `ψ ∈ W_h`, and let `hₙ`
be bounded measurable functions with `hₙ → h` pointwise and `|hₙ| ≤ |h|`. Then
`hₙ(μ)ψ → h(μ)ψ`.

Blueprint: lmm:fc-dominated-convergence
-/
theorem tendsto_integral_apply_of_dominated {h : X → ℂ} (hh : Measurable h)
    (ψ : integralDomain μ h) {hn : ℕ → X → ℂ} (hbdd : ∀ n, hn n ∈ BddMeasurable X)
    (hlim : ∀ x, Tendsto (fun n => hn n x) atTop (𝓝 (h x)))
    (hle : ∀ n x, ‖hn n x‖ ≤ ‖h x‖) :
    Tendsto (fun n => μ.integral (hn n) (ψ : H)) atTop (𝓝 (pmapIntegral μ h ψ)) := by
  sorry

/--
Composition with a bounded function on the left: for bounded measurable `u`, measurable `h` and
`ψ ∈ W_h`, the vector `ψ` lies in `W_{uh}` and `u(μ) h(μ) ψ = (uh)(μ) ψ`.

Blueprint: lmm:fc-bounded-left-composition
-/
theorem integral_apply_pmapIntegral {u h : X → ℂ} (hu : u ∈ BddMeasurable X)
    (hh : Measurable h) (ψ : integralDomain μ h) :
    ∃ hψ : (ψ : H) ∈ integralDomain μ (u * h),
      μ.integral u (pmapIntegral μ h ψ) = pmapIntegral μ (u * h) ⟨ψ, hψ⟩ := by
  sorry

/--
The associated measure of `h(μ)ψ`, for measurable and not necessarily bounded `h` and
`ψ ∈ W_h`, is the measure with density `|h|²` with respect to `μ_ψ`: for every measurable `E`,
`μ_{h(μ)ψ}(E) = ∫_E |h|² dμ_ψ`.

Implementation note: the statement is the equality of measures with `Measure.withDensity`; the
per-set form follows from `MeasureTheory.withDensity_apply`.

Blueprint: lmm:fc-associated-measure
-/
theorem assoc_pmapIntegral {h : X → ℂ} (hh : Measurable h) (ψ : integralDomain μ h) :
    μ.assoc (pmapIntegral μ h ψ) =
      (μ.assoc (ψ : H)).withDensity fun x => (‖h x‖₊ : ℝ≥0∞) ^ 2 := by
  sorry

/--
For measurable `f, g` and `ψ ∈ W_g`, the vector `g(μ)ψ` lies in `W_f` if and only if `ψ` lies
in `W_{fg}`.

Blueprint: lmm:fc-composition-domain
-/
theorem pmapIntegral_mem_integralDomain_iff {f g : X → ℂ} (hf : Measurable f)
    (hg : Measurable g) (ψ : integralDomain μ g) :
    pmapIntegral μ g ψ ∈ integralDomain μ f ↔ (ψ : H) ∈ integralDomain μ (f * g) := by
  sorry

/--
The composition law: for measurable `f, g`, the operator `(fg)(μ)` extends `f(μ) g(μ)`, and the
domain of `f(μ) g(μ)` is `W_g ∩ W_{fg}`.

Implementation note: the product `f(μ) g(μ)` is not a bundled operator here. Its domain is the
set of `ψ ∈ W_g` with `g(μ)ψ ∈ W_f`, and the first conjunct identifies this set with
`W_g ∩ W_{fg}`. The second conjunct is the extension property: on that domain, `ψ ∈ W_{fg}` and
`(fg)(μ)ψ = f(μ)(g(μ)ψ)`. For a self-adjoint `A` this gives `f(A) g(A) ⊆ (fg)(A)` through
`functionalCalculus`, which is `pmapIntegral` of the spectral measure.

Blueprint: thrm:fc-composition
-/
theorem pmapIntegral_comp {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g) :
    {ψ : H | ∃ hψ : ψ ∈ integralDomain μ g, pmapIntegral μ g ⟨ψ, hψ⟩ ∈ integralDomain μ f} =
        ((integralDomain μ g : Submodule ℂ H) : Set H) ∩ (integralDomain μ (f * g) : Set H) ∧
      ∀ (ψ : integralDomain μ g) (hy : pmapIntegral μ g ψ ∈ integralDomain μ f),
        ∃ hfg : (ψ : H) ∈ integralDomain μ (f * g),
          pmapIntegral μ (f * g) ⟨ψ, hfg⟩ = pmapIntegral μ f ⟨_, hy⟩ := by
  sorry

/--
The spectral projections commute with `h(μ)`: for measurable `h`, `ψ ∈ W_h` and measurable `E`,
the vector `μ(E)ψ` lies in `W_h` and `h(μ) μ(E) ψ = μ(E) h(μ) ψ`.

Blueprint: lmm:fc-commutes-with-projections
-/
theorem pmapIntegral_apply_projection {h : X → ℂ} (hh : Measurable h) (ψ : integralDomain μ h)
    {E : Set X} (hE : MeasurableSet E) :
    ∃ hn : μ E ψ ∈ integralDomain μ h,
      pmapIntegral μ h ⟨_, hn⟩ = μ E (pmapIntegral μ h ψ) := by
  sorry

variable {A : H →ₗ.[ℂ] H}

/--
For a self-adjoint `A` and a measurable real-valued `f : ℝ → ℝ`, the operator `f(A)` is
self-adjoint, hence closed.

Implementation note: `f(A)` is `functionalCalculus hA` applied to `f` composed with the
inclusion `ℝ → ℂ`.

Blueprint: lmm:fc-real-closed
-/
theorem isSelfAdjoint_functionalCalculus_of_real (hA : IsSelfAdjoint A) {f : ℝ → ℝ}
    (hf : Measurable f) :
    IsSelfAdjoint (functionalCalculus hA fun x => (f x : ℂ)) ∧
      (functionalCalculus hA fun x => (f x : ℂ)).IsClosed := by
  sorry

/--
For a self-adjoint `A` and a measurable real-valued `f : ℝ → ℝ`, the subspace
`Dom(A) ∩ Dom(f(A))` is a core for the closed operator `f(A)`. More precisely, for
`ψ ∈ Dom(f(A))` and `Eₙ = {λ | |λ| < n}`, the vectors `μ^A(Eₙ)ψ` lie in `Dom(A) ∩ Dom(f(A))`,
`μ^A(Eₙ)ψ → ψ` and `f(A) μ^A(Eₙ)ψ → f(A)ψ`.

Implementation note: the core property is Mathlib's `LinearPMap.HasCore`, which says that the
closure of the restriction of `f(A)` to the subspace is `f(A)`; the blueprint's notion of a core
(`def:core`) is not given a separate Lean definition. The intersection `Dom(A) ∩ Dom(f(A))` is
the submodule infimum `A.domain ⊓ (functionalCalculus hA _).domain`.

Blueprint: lmm:fc-core
-/
theorem hasCore_functionalCalculus (hA : IsSelfAdjoint A) {f : ℝ → ℝ} (hf : Measurable f) :
    (functionalCalculus hA fun x => (f x : ℂ)).HasCore
        (A.domain ⊓ (functionalCalculus hA fun x => (f x : ℂ)).domain) ∧
      ∀ ψ : (functionalCalculus hA fun x => (f x : ℂ)).domain,
        ∃ hn : ∀ n : ℕ, spectralMeasure hA {x | |x| < n} (ψ : H) ∈
            A.domain ⊓ (functionalCalculus hA fun x => (f x : ℂ)).domain,
          Tendsto (fun n : ℕ => spectralMeasure hA {x | |x| < n} (ψ : H)) atTop (𝓝 ψ) ∧
          Tendsto (fun n : ℕ => functionalCalculus hA (fun x => (f x : ℂ))
              ⟨_, (hn n).2⟩) atTop
            (𝓝 (functionalCalculus hA (fun x => (f x : ℂ)) ψ)) := by
  sorry

end Unbounded
end Spectral
end Physicslib4
