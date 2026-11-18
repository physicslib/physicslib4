/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Analysis.StripPeriodicExtension
import Mathlib.Analysis.Calculus.Deriv.Star

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
  have hcl : closure {z : ℂ | z.im < 0} ⊆ {z : ℂ | z.im ≤ 0} :=
    closure_lt_subset_le Complex.continuous_im continuous_const
  have hcl' : closure {z : ℂ | ¬ z.im < 0} ⊆ {z : ℂ | 0 ≤ z.im} := by
    simp_rw [not_lt]
    exact (isClosed_le continuous_const Complex.continuous_im).closure_subset
  refine ContinuousOn.if ?_ ?_ ?_
  · intro z ⟨_, hz⟩
    have h0 : z.im = 0 := frontier_lt_subset_eq Complex.continuous_im continuous_const hz
    have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simpa using h0)
    rw [hz', Complex.conj_ofReal, Complex.conj_eq_iff_im]
    exact hreal _
  · refine (Complex.continuous_conj.comp_continuousOn (hf.comp
      Complex.continuous_conj.continuousOn ?_))
    intro z ⟨hz, hz'⟩
    have := hcl hz'
    simp only [Set.mem_ofPred_eq] at hz this
    exact ⟨by simp; linarith, by simp; linarith⟩
  · refine hf.mono ?_
    intro z ⟨hz, hz'⟩
    exact ⟨hcl' hz', hz.2⟩

/-- If `f` is continuous on `Σ_β`, holomorphic on `Σ°_β` and real on the real axis, its Schwarz
reflection `Φ_f` is holomorphic on `{-β < Im z < β}`.

Blueprint: lmm:strip-reflection-holomorphic -/
theorem differentiableOn_stripReflection {β : ℝ} (hβ : 0 < β) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Σ[β])) (hfd : DifferentiableOn ℂ f (Σ°[β]))
    (hreal : ∀ t : ℝ, (f t).im = 0) :
    DifferentiableOn ℂ Φ[f] {z : ℂ | -β < z.im ∧ z.im < β} := by
  have hU : IsOpen {z : ℂ | -β < z.im ∧ z.im < β} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hO : IsOpen (Σ°[β]) :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  refine differentiableOn_if_of_eqOn_horizontal_line hU 0 ?_ ?_ ?_ ?_ ?_
  · refine Complex.continuous_conj.comp_continuousOn
      (hf.comp Complex.continuous_conj.continuousOn ?_)
    intro z ⟨⟨_, h2⟩, h3⟩
    simp only [Set.mem_ofPred_eq] at h3
    exact ⟨by simp; linarith, by simp; linarith⟩
  · exact hf.mono fun z ⟨⟨_, h2⟩, h3⟩ => ⟨h3, h2.le⟩
  · intro z ⟨⟨h1, _⟩, h3⟩
    simp only [Set.mem_ofPred_eq] at h3
    have hz : starRingEnd ℂ z ∈ Σ°[β] := ⟨by simp; linarith, by simp; linarith⟩
    have hd := (hfd.differentiableAt (hO.mem_nhds hz)).conj_conj
    rw [Complex.conj_conj] at hd
    exact DifferentiableAt.differentiableWithinAt hd
  · intro z ⟨⟨_, h2⟩, h3⟩
    exact (hfd.differentiableAt (hO.mem_nhds ⟨h3, h2⟩)).differentiableWithinAt
  · intro z _ h0
    have hz : z = (z.re : ℂ) := Complex.ext rfl (by simpa using h0)
    rw [hz, Complex.conj_ofReal, Complex.conj_eq_iff_im]
    exact hreal _

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
  have him : ∀ z : ℂ, (z - (β : ℂ) * Complex.I).im = z.im - β := fun z => by simp
  obtain ⟨C, hC⟩ := hfb
  refine ⟨?_, ⟨C, fun z hz => ?_⟩, ?_⟩
  · refine (continuousOn_stripReflection hβ hf hreal).comp
      (continuous_id.sub continuous_const).continuousOn fun z hz => ?_
    obtain ⟨h1, h2⟩ := hz
    simp only [Set.mem_ofPred_eq, him]
    constructor <;> linarith
  · obtain ⟨h1, h2⟩ := hz
    dsimp only
    split_ifs with h <;> rw [him] at h
    · rw [Complex.norm_conj]
      exact hC _ ⟨by simp; linarith, by simp; linarith⟩
    · exact hC _ ⟨by rw [him]; linarith, by rw [him]; linarith⟩
  · refine (differentiableOn_stripReflection hβ hf hfd hreal).comp
      (differentiableOn_id.sub (differentiableOn_const _)) fun z hz => ?_
    obtain ⟨h1, h2⟩ := hz
    simp only [Set.mem_ofPred_eq, him]
    constructor <;> linarith

/-- If `f` is real on the upper line `Im z = β`, the shifted reflection `Ψ(z) = Φ_f(z - iβ)` has
`Ψ(t) = f(t + iβ) = Ψ(t + 2iβ)` for every real `t`.

Blueprint: lmm:strip-real-boundary-periodic -/
theorem stripShiftedReflection_boundary {β : ℝ} (hβ : 0 < β) {f : ℂ → ℂ}
    (hreal : ∀ t : ℝ, (f ((t : ℂ) + (β : ℂ) * Complex.I)).im = 0) (t : ℝ) :
    Φ[f] ((t : ℂ) - (β : ℂ) * Complex.I) = f ((t : ℂ) + (β : ℂ) * Complex.I) ∧
      Φ[f] ((t : ℂ) + (2 * β : ℝ) * Complex.I - (β : ℂ) * Complex.I) =
        f ((t : ℂ) + (β : ℂ) * Complex.I) := by
  have h1 : ((t : ℂ) - (β : ℂ) * Complex.I).im < 0 := by simpa using hβ
  have h2 : starRingEnd ℂ ((t : ℂ) - (β : ℂ) * Complex.I) = (t : ℂ) + (β : ℂ) * Complex.I := by
    simp [map_sub]
  have h3 : (t : ℂ) + ((2 * β : ℝ) : ℂ) * Complex.I - (β : ℂ) * Complex.I =
      (t : ℂ) + (β : ℂ) * Complex.I := by push_cast; ring
  refine ⟨?_, ?_⟩
  · simp only [h1, h2, ↓reduceIte]
    exact Complex.conj_eq_iff_im.mpr (hreal t)
  · have h4 : ¬((t : ℂ) + (β : ℂ) * Complex.I).im < 0 := by simpa using hβ.le
    simp only [h3, h4, ↓reduceIte]

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
