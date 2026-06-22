/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.GNS.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The KMS (analyticity) condition for a one-parameter automorphism group

This file defines the Kubo-Martin-Schwinger (KMS) condition for a state on a
unital C*-algebra `A` with respect to a one-parameter group of `*`-automorphisms
`α : ℝ → (A ≃⋆ₐ[ℂ] A)`. The KMS condition is the algebraic characterization of
thermal equilibrium; crucially, it is phrased purely as an *analyticity*
statement about correlation functions and so needs no unbounded-operator theory
(no Stone theorem, no spectral measures).

## Main definitions

* `Physicslib4.AQFT.kmsStrip`, `kmsStripInterior`: the closed/open horizontal
  strip `0 ≤ Im z ≤ β` (resp. `0 < Im z < β`) in `ℂ`.
* `Physicslib4.AQFT.IsOneParameterAut`: the predicate that `α` is a one-parameter
  group of automorphisms (`α 0 = id`, `α (s+t) = α s ∘ α t`).
* `Physicslib4.AQFT.IsKMSState`: a state `ω` is `(α, β)`-KMS if for every
  `a, b ∈ A` the function `t ↦ ω(a · α_t b)` is the boundary value of a function
  holomorphic on the open strip and continuous on its closure, whose other
  boundary value is `t ↦ ω(α_t b · a)`.

## Notes

This is the analytic form of the KMS condition (Bratteli-Robinson): at inverse
temperature `β > 0`, `ω` is KMS iff for all `a, b` there is `F` continuous on the
strip `{0 ≤ Im z ≤ β}`, holomorphic in the interior, with `F(t) = ω(a α_t b)`
and `F(t + iβ) = ω(α_t b · a)`. KMS states are automatically `α`-invariant; that
and other consequences are left for later development.
-/

namespace Physicslib4
namespace AQFT

open Physicslib4.GNS

variable {A : Type*} [CStarAlgebra A]

/-- The closed KMS strip `{z : ℂ | 0 ≤ Im z ≤ β}`. -/
def kmsStrip (β : ℝ) : Set ℂ := {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β}

/-- The open KMS strip `{z : ℂ | 0 < Im z < β}` (the interior of `kmsStrip β`). -/
def kmsStripInterior (β : ℝ) : Set ℂ := {z : ℂ | 0 < z.im ∧ z.im < β}

/-- A family `α : ℝ → (A ≃⋆ₐ[ℂ] A)` is a *one-parameter group of automorphisms*
if it sends `0` to the identity and is additive in the parameter:
`α 0 = id` and `α (s + t) = α s ∘ α t`. -/
def IsOneParameterAut (α : ℝ → (A ≃⋆ₐ[ℂ] A)) : Prop :=
  (∀ a : A, α 0 a = a) ∧ (∀ (s t : ℝ) (a : A), α (s + t) a = α s (α t a))

/-- **The KMS condition.** A state `ω` on `A` is `(α, β)`-KMS for a one-parameter
automorphism group `α` at inverse temperature `β` if, for every `a, b : A`, the
correlation function `t ↦ ω(a · α_t b)` extends to a function `F` on the closed
strip `0 ≤ Im z ≤ β` that is continuous there, holomorphic on the open strip,
and whose boundary value on `Im z = β` is `t ↦ ω(α_t b · a)`. -/
def IsKMSState (α : ℝ → (A ≃⋆ₐ[ℂ] A)) (β : ℝ) (ω : State A) : Prop :=
  ∀ a b : A, ∃ F : ℂ → ℂ,
    ContinuousOn F (kmsStrip β) ∧
    DifferentiableOn ℂ F (kmsStripInterior β) ∧
    (∀ t : ℝ, F (t : ℂ) = (ω (a * α t b) : ℂ)) ∧
    (∀ t : ℝ, F ((t : ℂ) + (β : ℂ) * Complex.I) = (ω (α t b * a) : ℂ))

end AQFT
end Physicslib4
