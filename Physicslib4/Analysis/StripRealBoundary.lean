/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Analysis.StripPeriodicExtension

/-!
# Functions real on both edges of a strip

For `β > 0` let `Σ_β = {0 ≤ Im z ≤ β}` and `Σ°_β = {0 < Im z < β}`, written literally as
`AQFT.kmsStrip β` is. This file states that a function continuous and bounded on `Σ_β`,
holomorphic on `Σ°_β` and real on both boundary lines is constant on `Σ_β`. The proof goes
through the Schwarz reflection `Φ_f` of `f` across the real axis and its shift
`Ψ(z) = Φ_f(z - iβ)`, which has equal boundary values on `Σ_{2β}`.

## Notation

* `Φ[f]` is the Schwarz reflection `Φ_f(z) = conj (f (conj z))` for `Im z < 0` and
  `Φ_f(z) = f(z)` otherwise.
* "`f(t)` is real" is written `(f t).im = 0`.
-/

namespace Physicslib4

/-- The closed strip `{z | 0 ≤ Im z ≤ β}`. -/
local notation "Σ[" β "]" => Set.ofPred fun z : ℂ => 0 ≤ Complex.im z ∧ Complex.im z ≤ β

/-- The open strip `{z | 0 < Im z < β}`. -/
local notation "Σ°[" β "]" => Set.ofPred fun z : ℂ => 0 < Complex.im z ∧ Complex.im z < β

/-- The Schwarz reflection `Φ_f` of `f` across the real axis. -/
local notation "Φ[" f "]" =>
  fun z : ℂ => ite (Complex.im z < 0) (starRingEnd ℂ (f (starRingEnd ℂ z))) (f z)

/-- If `f` is continuous on `Σ_β` and real on the real axis, its Schwarz reflection `Φ_f` is
continuous on `{-β ≤ Im z ≤ β}`.

Blueprint: lmm:strip-reflection-continuous -/
theorem continuousOn_stripReflection {β : ℝ} (hβ : 0 < β) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Σ[β])) (hreal : ∀ t : ℝ, (f t).im = 0) :
    ContinuousOn Φ[f] {z : ℂ | -β ≤ z.im ∧ z.im ≤ β} := by
  sorry

/-- If `f` is continuous on `Σ_β`, holomorphic on `Σ°_β` and real on the real axis, its Schwarz
reflection `Φ_f` is holomorphic on `{-β < Im z < β}`.

Blueprint: lmm:strip-reflection-holomorphic -/
theorem differentiableOn_stripReflection {β : ℝ} (hβ : 0 < β) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Σ[β])) (hfd : DifferentiableOn ℂ f (Σ°[β]))
    (hreal : ∀ t : ℝ, (f t).im = 0) :
    DifferentiableOn ℂ Φ[f] {z : ℂ | -β < z.im ∧ z.im < β} := by
  sorry

/-- If `f` is continuous and bounded on `Σ_β`, holomorphic on `Σ°_β` and real on the real axis,
the shifted reflection `Ψ(z) = Φ_f(z - iβ)` is continuous and bounded on `Σ_{2β}` and holomorphic
on `Σ°_{2β}`.

Blueprint: lmm:strip-shifted-reflection-regular -/
theorem stripShiftedReflection_regular {β : ℝ} (hβ : 0 < β) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Σ[β])) (hfb : ∃ C : ℝ, ∀ z ∈ Σ[β], ‖f z‖ ≤ C)
    (hfd : DifferentiableOn ℂ f (Σ°[β])) (hreal : ∀ t : ℝ, (f t).im = 0) :
    ContinuousOn (fun z : ℂ => Φ[f] (z - (β : ℂ) * Complex.I)) (Σ[2 * β]) ∧
      (∃ C : ℝ, ∀ z ∈ Σ[2 * β], ‖Φ[f] (z - (β : ℂ) * Complex.I)‖ ≤ C) ∧
      DifferentiableOn ℂ (fun z : ℂ => Φ[f] (z - (β : ℂ) * Complex.I))
        (Σ°[2 * β]) := by
  sorry

/-- If `f` is real on the upper line `Im z = β`, the shifted reflection `Ψ(z) = Φ_f(z - iβ)` has
`Ψ(t) = f(t + iβ) = Ψ(t + 2iβ)` for every real `t`.

Blueprint: lmm:strip-real-boundary-periodic -/
theorem stripShiftedReflection_boundary {β : ℝ} (hβ : 0 < β) {f : ℂ → ℂ}
    (hreal : ∀ t : ℝ, (f ((t : ℂ) + (β : ℂ) * Complex.I)).im = 0) (t : ℝ) :
    Φ[f] ((t : ℂ) - (β : ℂ) * Complex.I) = f ((t : ℂ) + (β : ℂ) * Complex.I) ∧
      Φ[f] ((t : ℂ) + (2 * β : ℝ) * Complex.I - (β : ℂ) * Complex.I) =
        f ((t : ℂ) + (β : ℂ) * Complex.I) := by
  sorry

/-- A function continuous and bounded on `Σ_β`, holomorphic on `Σ°_β` and real on both boundary
lines `Im z = 0` and `Im z = β` is constant on `Σ_β`.

Blueprint: lmm:strip-real-boundary-constant -/
theorem eq_of_real_strip_boundary {β : ℝ} (hβ : 0 < β) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Σ[β])) (hfb : ∃ C : ℝ, ∀ z ∈ Σ[β], ‖f z‖ ≤ C)
    (hfd : DifferentiableOn ℂ f (Σ°[β])) (hreal₀ : ∀ t : ℝ, (f t).im = 0)
    (hrealβ : ∀ t : ℝ, (f ((t : ℂ) + (β : ℂ) * Complex.I)).im = 0) :
    ∀ z ∈ Σ[β], f z = f 0 := by
  sorry

end Physicslib4
