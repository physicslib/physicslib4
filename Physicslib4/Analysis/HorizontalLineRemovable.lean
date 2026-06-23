/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Towards horizontal-line removability (Morera-based)

This file develops building blocks for the **horizontal-line removable
singularity** theorem: a function continuous on an open set `U` and holomorphic
on `U` minus a horizontal line is holomorphic on all of `U`. That theorem is the
missing prerequisite for the strip Schwarz reflection used in the KMS
invariance proof (`StripLiouville`).

## This file (foundation)

* `Physicslib4.rectIntegralReal`: the contour integral of `f` over the boundary
  of the axis-parallel rectangle `[a,b] × [c,d]` (Cauchy-Goursat normal form,
  matching `Complex.integral_boundary_rect_eq_zero_*`), parameterized by *real*
  bounds.
* `Physicslib4.rectIntegralReal_horizontal_split`: **additivity across a
  horizontal split** - the rectangle integral over `[a,b] × [c,d]` is the sum of
  those over `[a,b] × [c,ℓ]` and `[a,b] × [ℓ,d]`. The shared horizontal edge at
  `im = ℓ` cancels; the vertical edges combine via interval-integral additivity.
* `Physicslib4.rectIntegralReal_eq_zero_of_continuousOn_of_differentiableOn`: the
  Cauchy-Goursat theorem in `rectIntegralReal` form.
* `Physicslib4.rectIntegralReal_eq_zero_of_continuousOn_off_horizontal_line`:
  **straddling-rectangle vanishing** - if `f` is continuous on the closed
  rectangle and holomorphic off the line `im = ℓ` (with `c ≤ ℓ ≤ d`), then
  `rectIntegralReal = 0`, by splitting at `ℓ` (`_horizontal_split`) and applying
  Cauchy-Goursat to each sub-rectangle (continuous on closure, holomorphic on
  interior, which avoids the line).

## Roadmap (subsequent building blocks, not in this file)

1. **Morera glue**: vanishing rectangle integrals over all sub-rectangles give a
   primitive, hence holomorphy (`Complex.IsConservativeOn` / Morera).
2. **Removability**: assemble the straddling vanishing + Morera into "continuous
   on `U`, holomorphic off the line ⟹ holomorphic on `U`".
3. **Strip Schwarz reflection**: use removability to build the `iβ`-periodic
   entire extension, discharging `StripLiouville` (and KMS invariance) via
   `Physicslib4.AQFT.stripLiouville_of_entire_extension`.
-/

namespace Physicslib4

open scoped Interval
open MeasureTheory Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The contour integral of `f` over the boundary of the axis-parallel rectangle
`[a, b] × [c, d]` (with real bounds), in the Cauchy-Goursat normal form: bottom
edge minus top edge, plus `I ·` (right edge minus left edge). -/
noncomputable def rectIntegralReal (f : ℂ → E) (a b c d : ℝ) : E :=
  (∫ x : ℝ in a..b, f (↑x + ↑c * Complex.I)) -
      (∫ x : ℝ in a..b, f (↑x + ↑d * Complex.I)) +
    Complex.I • (∫ y : ℝ in c..d, f (↑b + ↑y * Complex.I)) -
    Complex.I • (∫ y : ℝ in c..d, f (↑a + ↑y * Complex.I))

/-- **Additivity of the rectangle contour integral across a horizontal split.**
Splitting `[a,b] × [c,d]` along the horizontal line `im = ℓ` into a lower
rectangle `[a,b] × [c,ℓ]` and an upper rectangle `[a,b] × [ℓ,d]`, the boundary
integrals add: the contributions of the shared edge `im = ℓ` cancel (it is
traversed in opposite directions), and the left/right edges combine by
interval-integral additivity. The hypotheses are interval-integrability of the
two vertical-edge integrands on each piece. -/
theorem rectIntegralReal_horizontal_split (f : ℂ → E) (a b c d ℓ : ℝ)
    (hrL : IntervalIntegrable (fun y : ℝ => f (↑b + ↑y * Complex.I)) volume c ℓ)
    (hrU : IntervalIntegrable (fun y : ℝ => f (↑b + ↑y * Complex.I)) volume ℓ d)
    (hlL : IntervalIntegrable (fun y : ℝ => f (↑a + ↑y * Complex.I)) volume c ℓ)
    (hlU : IntervalIntegrable (fun y : ℝ => f (↑a + ↑y * Complex.I)) volume ℓ d) :
    rectIntegralReal f a b c d
      = rectIntegralReal f a b c ℓ + rectIntegralReal f a b ℓ d := by
  simp only [rectIntegralReal]
  rw [← intervalIntegral.integral_add_adjacent_intervals hrL hrU,
    ← intervalIntegral.integral_add_adjacent_intervals hlL hlU, smul_add, smul_add]
  abel

/-- **Cauchy-Goursat theorem in `rectIntegralReal` form.** If `f` is continuous
on the closed rectangle `[a,b] × [c,d]` and holomorphic on its interior, the
boundary contour integral vanishes. -/
theorem rectIntegralReal_eq_zero_of_continuousOn_of_differentiableOn (f : ℂ → E)
    (a b c d : ℝ)
    (Hc : ContinuousOn f (Set.uIcc a b ×ℂ Set.uIcc c d))
    (Hd : DifferentiableOn ℂ f
      (Set.Ioo (min a b) (max a b) ×ℂ Set.Ioo (min c d) (max c d))) :
    rectIntegralReal f a b c d = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f
    ⟨a, c⟩ ⟨b, d⟩ Hc Hd

/-- **Straddling-rectangle vanishing.** If `f` is continuous on the closed
rectangle `[a,b] × [c,d]` and holomorphic everywhere on it *except possibly on
the horizontal line* `im = ℓ` (with `c ≤ ℓ ≤ d`), then its boundary contour
integral still vanishes. The proof splits the rectangle at `ℓ` into a lower and
an upper piece (`rectIntegralReal_horizontal_split`); each piece is continuous on
its closure and holomorphic on its interior (whose imaginary parts are strictly
on one side of `ℓ`, hence avoid the line), so Cauchy-Goursat applies to each. -/
theorem rectIntegralReal_eq_zero_of_continuousOn_off_horizontal_line (f : ℂ → E)
    (a b c d ℓ : ℝ) (hab : a ≤ b) (hcℓ : c ≤ ℓ) (hℓd : ℓ ≤ d)
    (Hc : ContinuousOn f (Set.uIcc a b ×ℂ Set.uIcc c d))
    (Hd : DifferentiableOn ℂ f
      ((Set.Icc a b ×ℂ Set.Icc c d) \ {z : ℂ | z.im = ℓ})) :
    rectIntegralReal f a b c d = 0 := by
  have hcd : c ≤ d := hcℓ.trans hℓd
  -- `ℓ` lies in `[c,d]`, and the two sub-intervals sit inside `[c,d]`.
  have hℓ_mem : ℓ ∈ Set.uIcc c d := Set.mem_uIcc.mpr (Or.inl ⟨hcℓ, hℓd⟩)
  have hcℓ_sub : Set.uIcc c ℓ ⊆ Set.uIcc c d :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc hℓ_mem
  have hℓd_sub : Set.uIcc ℓ d ⊆ Set.uIcc c d :=
    Set.uIcc_subset_uIcc hℓ_mem Set.right_mem_uIcc
  -- Continuity of the vertical-edge integrands, used to discharge integrability.
  have hedge : ∀ t : ℝ, t ∈ Set.uIcc a b → ∀ s : Set ℝ, s ⊆ Set.uIcc c d →
      ContinuousOn (fun y : ℝ => f (↑t + ↑y * Complex.I)) s := by
    intro t ht s hs
    refine Hc.comp ?_ ?_
    · exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
    · intro y hy
      rw [Complex.mem_reProdIm]
      exact ⟨by simpa using ht, by simpa using hs hy⟩
  -- Monotonicity of the closed rectangle in the imaginary factor.
  have hsubC : ∀ s : Set ℝ, s ⊆ Set.uIcc c d →
      (Set.uIcc a b ×ℂ s) ⊆ (Set.uIcc a b ×ℂ Set.uIcc c d) := by
    intro s hs z hz
    rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨hz.1, hs hz.2⟩
  -- Split the rectangle integral at the line `im = ℓ`.
  rw [rectIntegralReal_horizontal_split f a b c d ℓ
    ((hedge b Set.right_mem_uIcc _ hcℓ_sub).intervalIntegrable)
    ((hedge b Set.right_mem_uIcc _ hℓd_sub).intervalIntegrable)
    ((hedge a Set.left_mem_uIcc _ hcℓ_sub).intervalIntegrable)
    ((hedge a Set.left_mem_uIcc _ hℓd_sub).intervalIntegrable)]
  -- The lower piece `[a,b] × [c,ℓ]`: holomorphic interior has `im < ℓ`.
  have hlow : rectIntegralReal f a b c ℓ = 0 := by
    refine rectIntegralReal_eq_zero_of_continuousOn_of_differentiableOn f a b c ℓ
      (Hc.mono (hsubC _ hcℓ_sub)) (Hd.mono ?_)
    rw [min_eq_left hab, max_eq_right hab, min_eq_left hcℓ, max_eq_right hcℓ]
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    obtain ⟨hre, him⟩ := hz
    refine Set.mem_diff_of_mem (Complex.mem_reProdIm.mpr ⟨Set.Ioo_subset_Icc_self hre, ?_⟩) ?_
    · exact Set.mem_Icc.mpr ⟨him.1.le, him.2.le.trans hℓd⟩
    · simp only [Set.mem_setOf_eq]; exact ne_of_lt him.2
  -- The upper piece `[a,b] × [ℓ,d]`: holomorphic interior has `im > ℓ`.
  have hupp : rectIntegralReal f a b ℓ d = 0 := by
    refine rectIntegralReal_eq_zero_of_continuousOn_of_differentiableOn f a b ℓ d
      (Hc.mono (hsubC _ hℓd_sub)) (Hd.mono ?_)
    rw [min_eq_left hab, max_eq_right hab, min_eq_left hℓd, max_eq_right hℓd]
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    obtain ⟨hre, him⟩ := hz
    refine Set.mem_diff_of_mem (Complex.mem_reProdIm.mpr ⟨Set.Ioo_subset_Icc_self hre, ?_⟩) ?_
    · exact Set.mem_Icc.mpr ⟨hcℓ.trans him.1.le, him.2.le⟩
    · simp only [Set.mem_setOf_eq]; exact (ne_of_lt him.1).symm
  rw [hlow, hupp, add_zero]

end Physicslib4
