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

## Roadmap (subsequent building blocks, not in this file)

1. **Straddling-rectangle vanishing**: if `f` is continuous on the closed
   rectangle and holomorphic off the line `im = ℓ`, then `rectIntegralReal = 0` -
   by splitting at `ℓ` (this file's `_horizontal_split`) and applying
   Cauchy-Goursat to each sub-rectangle (continuous on closure, holomorphic on
   interior, which avoids the line).
2. **Morera glue**: vanishing rectangle integrals over all sub-rectangles give a
   primitive, hence holomorphy (`Complex.IsConservativeOn` / Morera).
3. **Removability**: assemble 1+2 into "continuous on `U`, holomorphic off the
   line ⟹ holomorphic on `U`".
4. **Strip Schwarz reflection**: use removability to build the `iβ`-periodic
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

end Physicslib4
