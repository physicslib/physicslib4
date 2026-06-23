/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Towards horizontal-line removability (Morera-based)

This file proves the **horizontal-line removable singularity** theorem: a
function continuous on an open set `U` and holomorphic on `U` minus a horizontal
line is holomorphic on all of `U`
(`differentiableOn_of_continuousOn_off_horizontal_line`). That theorem is the
missing prerequisite for the strip Schwarz reflection used in the KMS
invariance proof (`StripLiouville`).

## Foundation (rectangle contour integrals)

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

## Morera glue and removability

* `Physicslib4.wedgeIntegral_add_wedgeIntegral_eq_rectIntegralReal`: the bridge
  to Mathlib's Morera API - the sum of the two opposite wedge integrals
  (`Complex.wedgeIntegral`) equals our `rectIntegralReal`.
* `Physicslib4.rectIntegralReal_eq_zero_of_subset`: every closed rectangle in `U`
  has vanishing boundary integral (any corner ordering, any line position),
  reducing to ordered bounds via `rectIntegralReal_swap_re/_swap_im`.
* `Physicslib4.differentiableOn_of_continuousOn_off_horizontal_line`: **the
  removable-singularity theorem**, via Morera
  (`Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`).

## Roadmap (remaining, not in this file)

* **Strip Schwarz reflection**: use removability to build the `iβ`-periodic
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

/-- Swapping the real bounds negates the rectangle contour integral. -/
theorem rectIntegralReal_swap_re (f : ℂ → E) (a b c d : ℝ) :
    rectIntegralReal f b a c d = -rectIntegralReal f a b c d := by
  simp only [rectIntegralReal, intervalIntegral.integral_symm a b]
  abel

/-- Swapping the imaginary bounds negates the rectangle contour integral. -/
theorem rectIntegralReal_swap_im (f : ℂ → E) (a b c d : ℝ) :
    rectIntegralReal f a b d c = -rectIntegralReal f a b c d := by
  simp only [rectIntegralReal, intervalIntegral.integral_symm c d, smul_neg]
  abel

/-- The sum of the two opposite wedge integrals equals the rectangle contour
integral. This is the bridge between Mathlib's `Complex.IsConservativeOn`
(phrased via `wedgeIntegral`) and our `rectIntegralReal`: the two wedges trace
the four edges of the rectangle, with the shared diagonal-free edges combining
into the full boundary. -/
theorem wedgeIntegral_add_wedgeIntegral_eq_rectIntegralReal (f : ℂ → E) (z w : ℂ) :
    wedgeIntegral z w f + wedgeIntegral w z f
      = rectIntegralReal f z.re w.re z.im w.im := by
  simp only [wedgeIntegral, rectIntegralReal]
  rw [intervalIntegral.integral_symm z.re w.re, intervalIntegral.integral_symm z.im w.im,
    smul_neg]
  abel

/-- **Rectangle integrals vanish on a set, off a horizontal line.** If `f` is
continuous on a set `U` and holomorphic on `U` minus the horizontal line
`im = ℓ`, then the boundary integral of `f` over *any* closed rectangle contained
in `U` vanishes - regardless of corner ordering and of where the line sits
relative to the rectangle. The proof reduces to ordered bounds via the swap
lemmas, then splits into three positions of `ℓ`: inside `[c,d]` (straddling
vanishing) or outside on either side (plain Cauchy-Goursat, the interior
avoiding the line). -/
theorem rectIntegralReal_eq_zero_of_subset {U : Set ℂ} (ℓ : ℝ)
    (f : ℂ → E) (hc : ContinuousOn f U)
    (hd : DifferentiableOn ℂ f (U \ {z : ℂ | z.im = ℓ}))
    (a b c d : ℝ) (hsub : (Set.uIcc a b ×ℂ Set.uIcc c d) ⊆ U) :
    rectIntegralReal f a b c d = 0 := by
  have ordered : ∀ a b c d : ℝ, a ≤ b → c ≤ d →
      (Set.uIcc a b ×ℂ Set.uIcc c d) ⊆ U → rectIntegralReal f a b c d = 0 := by
    intro a b c d hab hcd hsub
    have hcont : ContinuousOn f (Set.uIcc a b ×ℂ Set.uIcc c d) := hc.mono hsub
    -- membership of the open interior in the closed rectangle (`⊆ U`)
    have hmem_open : ∀ z : ℂ, z.re ∈ Set.Ioo a b → z.im ∈ Set.Ioo c d →
        z ∈ Set.uIcc a b ×ℂ Set.uIcc c d := by
      intro z hre him
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hab, Set.uIcc_of_le hcd]
      exact ⟨Set.Ioo_subset_Icc_self hre, Set.Ioo_subset_Icc_self him⟩
    rcases le_total c ℓ with hcℓ | hℓc
    · rcases le_total ℓ d with hℓd | hdℓ
      · -- `c ≤ ℓ ≤ d`: straddling vanishing
        refine rectIntegralReal_eq_zero_of_continuousOn_off_horizontal_line f a b c d ℓ
          hab hcℓ hℓd hcont (hd.mono (fun z hz => ?_))
        refine Set.mem_diff_of_mem (hsub ?_) hz.2
        rw [Complex.mem_reProdIm, Set.uIcc_of_le hab, Set.uIcc_of_le hcd]
        exact Complex.mem_reProdIm.mp hz.1
      · -- `d < ℓ`: line above the rectangle, plain Cauchy-Goursat
        refine rectIntegralReal_eq_zero_of_continuousOn_of_differentiableOn f a b c d
          hcont (hd.mono ?_)
        rw [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd]
        intro z hz
        rw [Complex.mem_reProdIm] at hz
        exact Set.mem_diff_of_mem (hsub (hmem_open z hz.1 hz.2)) (ne_of_lt (hz.2.2.trans_le hdℓ))
    · -- `ℓ < c`: line below the rectangle, plain Cauchy-Goursat
      refine rectIntegralReal_eq_zero_of_continuousOn_of_differentiableOn f a b c d
        hcont (hd.mono ?_)
      rw [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd]
      intro z hz
      rw [Complex.mem_reProdIm] at hz
      exact Set.mem_diff_of_mem (hsub (hmem_open z hz.1 hz.2))
        (ne_of_lt (lt_of_le_of_lt hℓc hz.2.1)).symm
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
  · exact ordered a b c d hab hcd hsub
  · have h := ordered a b d c hab hcd (by rw [Set.uIcc_comm d c]; exact hsub)
    rw [rectIntegralReal_swap_im] at h
    exact neg_eq_zero.mp h
  · have h := ordered b a c d hab hcd (by rw [Set.uIcc_comm b a]; exact hsub)
    rw [rectIntegralReal_swap_re] at h
    exact neg_eq_zero.mp h
  · have h := ordered b a d c hab hcd
      (by rw [Set.uIcc_comm b a, Set.uIcc_comm d c]; exact hsub)
    rw [rectIntegralReal_swap_re, rectIntegralReal_swap_im, neg_neg] at h
    exact h

/-- **Horizontal-line removable singularity (Morera).** If `f` is continuous on
an open set `U` and holomorphic on `U` minus the horizontal line `im = ℓ`, then
`f` is holomorphic on all of `U`. The line is removed: continuity across it plus
holomorphy on either side forces differentiability on it.

The proof is Morera's theorem in the form
`Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`: it suffices
that `f` is conservative on `U`, i.e. every rectangle boundary integral vanishes,
which is `rectIntegralReal_eq_zero_of_subset`. -/
theorem differentiableOn_of_continuousOn_off_horizontal_line [CompleteSpace E] {U : Set ℂ}
    (hU : IsOpen U) (ℓ : ℝ) (f : ℂ → E) (hc : ContinuousOn f U)
    (hd : DifferentiableOn ℂ f (U \ {z : ℂ | z.im = ℓ})) :
    DifferentiableOn ℂ f U := by
  rw [← Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU]
  refine ⟨?_, hc⟩
  intro z w hzw
  simp only [Complex.Rectangle] at hzw
  rw [eq_neg_iff_add_eq_zero, wedgeIntegral_add_wedgeIntegral_eq_rectIntegralReal]
  exact rectIntegralReal_eq_zero_of_subset ℓ f hc hd z.re w.re z.im w.im hzw

end Physicslib4
