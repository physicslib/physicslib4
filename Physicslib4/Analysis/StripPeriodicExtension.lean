/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Analysis.HorizontalLineRemovable
import Mathlib.Analysis.Complex.Liouville

/-!
# The `iβ`-periodic entire extension (strip Schwarz reflection)

Given a function `F` continuous on the closed strip `0 ≤ Im z ≤ β`, holomorphic
on the open strip, and with equal boundary values `F(t) = F(t + iβ)` on the real
axis, this file constructs a **bounded entire extension** `H` agreeing with `F`
on `ℝ`.

The extension is the `iβ`-periodic continuation: `H z = F (z - ⌊Im z / β⌋ · iβ)`,
which folds every point back into the fundamental strip. It is:

* **continuous** everywhere - across each gluing line `Im z = kβ` the boundary
  values match by periodicity (`ContinuousOn.if`);
* **holomorphic off the lines** - on each open strip it is `F` composed with a
  holomorphic shift into the open fundamental strip;
* **holomorphic on the lines** - by the horizontal-line removable singularity
  theorem `differentiableOn_of_continuousOn_off_horizontal_line`;
* **bounded** - its values are `F`-values on the fundamental strip.

The headline result `exists_bounded_entire_extension_of_strip_periodic` is exactly
the construction that `Physicslib4.AQFT.stripLiouville_of_entire_extension`
consumes, so it discharges the `StripLiouville` principle (and hence KMS
invariance) for `β > 0`.
-/

namespace Physicslib4

open Complex Set Filter Topology Metric

/-- Characterisation of `⌊x / β⌋ = m` for `β > 0`: it is `mβ ≤ x < (m+1)β`. -/
theorem floor_div_eq_iff {β : ℝ} (hβ : 0 < β) (x : ℝ) (m : ℤ) :
    ⌊x / β⌋ = m ↔ (m : ℝ) * β ≤ x ∧ x < ((m : ℝ) + 1) * β := by
  rw [Int.floor_eq_iff, le_div_iff₀ hβ, div_lt_iff₀ hβ]

/-- The imaginary part of a vertical integer-multiple shift. -/
theorem sub_intMul_im (k : ℤ) (β : ℝ) (w : ℂ) :
    (w - ((k : ℤ) : ℂ) * ((β : ℂ) * Complex.I)).im = w.im - (k : ℝ) * β := by
  simp [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.intCast_re,
    Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]

/-- The real part of a vertical integer-multiple shift is unchanged. -/
theorem sub_intMul_re (k : ℤ) (β : ℝ) (w : ℂ) :
    (w - ((k : ℤ) : ℂ) * ((β : ℂ) * Complex.I)).re = w.re := by
  simp [Complex.sub_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]

-- The half-plane topology helpers (`isOpen_setOf_im_lt`, `closure_setOf_im_lt`,
-- `closure_setOf_not_im_lt`, `frontier_setOf_im_lt`) now live in
-- `Physicslib4.Analysis.HorizontalLineRemovable` alongside the general gluing lemma.

variable {β : ℝ}

/-- The vertical fold shift `z ↦ z - ⌊Im z / β⌋ · iβ`. -/
noncomputable def pshift (β : ℝ) (z : ℂ) : ℂ :=
  z - ((⌊z.im / β⌋ : ℤ) : ℂ) * ((β : ℂ) * Complex.I)

/-- The `iβ`-periodic extension `z ↦ F (pshift β z)`. -/
noncomputable def pext (β : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ := F (pshift β z)

theorem pshift_im (β : ℝ) (z : ℂ) :
    (pshift β z).im = z.im - (⌊z.im / β⌋ : ℝ) * β := by
  rw [pshift, sub_intMul_im]

/-- The folded point lies in the fundamental strip `0 ≤ Im ≤ β` (in fact `< β`). -/
theorem pshift_im_mem (hβ : 0 < β) (z : ℂ) :
    0 ≤ (pshift β z).im ∧ (pshift β z).im < β := by
  have h := (floor_div_eq_iff hβ z.im ⌊z.im / β⌋).mp rfl
  rw [pshift_im]
  refine ⟨by linarith [h.1], ?_⟩
  have e : ((⌊z.im / β⌋ : ℝ) + 1) * β = (⌊z.im / β⌋ : ℝ) * β + β := by ring
  linarith [h.2]

section
variable {F : ℂ → ℂ}

/-- **Off the gluing lines**, the periodic extension is differentiable: near any
point whose fold lands strictly inside the open strip, the floor is locally
constant, so the extension is `F` composed with a holomorphic shift. -/
theorem pext_differentiableAt_offline (hβ : 0 < β)
    (hdiff : DifferentiableOn ℂ F {z : ℂ | 0 < z.im ∧ z.im < β})
    {z : ℂ} (hz : 0 < (pshift β z).im) :
    DifferentiableAt ℂ (pext β F) z := by
  set m := ⌊z.im / β⌋ with hm
  have hbounds := (floor_div_eq_iff hβ z.im m).mp hm.symm
  have hzlt : (pshift β z).im < β := (pshift_im_mem hβ z).2
  have hpsim : (pshift β z).im = z.im - (m : ℝ) * β := pshift_im β z
  set V := {w : ℂ | (m : ℝ) * β < w.im ∧ w.im < ((m : ℝ) + 1) * β} with hV
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hzV : z ∈ V := by
    refine ⟨?_, hbounds.2⟩
    have hz' := hz; rw [hpsim] at hz'; linarith [hz']
  have heq : (pext β F) =ᶠ[𝓝 z] fun w => F (w - (m : ℂ) * ((β : ℂ) * Complex.I)) := by
    refine Filter.eventuallyEq_of_mem (hVopen.mem_nhds hzV) (fun w hw => ?_)
    have hfw : ⌊w.im / β⌋ = m := (floor_div_eq_iff hβ w.im m).mpr ⟨le_of_lt hw.1, hw.2⟩
    simp only [pext, pshift, hfw]
  rw [heq.differentiableAt_iff]
  have hmem : z - (m : ℂ) * ((β : ℂ) * Complex.I) ∈ {w : ℂ | 0 < w.im ∧ w.im < β} := by
    change 0 < (z - (m : ℂ) * ((β : ℂ) * Complex.I)).im ∧
      (z - (m : ℂ) * ((β : ℂ) * Complex.I)).im < β
    have hval : (z - (m : ℂ) * ((β : ℂ) * Complex.I)).im = (pshift β z).im := rfl
    rw [hval]; exact ⟨hz, hzlt⟩
  have hFdiff : DifferentiableAt ℂ F (z - (m : ℂ) * ((β : ℂ) * Complex.I)) :=
    hdiff.differentiableAt
      (((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)).mem_nhds hmem)
  exact hFdiff.comp z (differentiableAt_id.sub_const _)

/-- **On a gluing line**, the periodic extension is differentiable: on a ball
around the point it equals a two-piece function glued across the line, which is
continuous (boundary values match by periodicity) and holomorphic off the line,
hence holomorphic by the removable-singularity theorem. -/
theorem pext_differentiableAt_online (hβ : 0 < β)
    (hcont : ContinuousOn F {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β})
    (hdiff : DifferentiableOn ℂ F {z : ℂ | 0 < z.im ∧ z.im < β})
    (hper : ∀ t : ℝ, F (t : ℂ) = F ((t : ℂ) + (β : ℂ) * Complex.I))
    {z₀ : ℂ} (hz₀ : (pshift β z₀).im = 0) :
    DifferentiableAt ℂ (pext β F) z₀ := by
  set n₀ := ⌊z₀.im / β⌋ with hn₀
  have hz₀im : z₀.im = (n₀ : ℝ) * β := by
    have := pshift_im β z₀; rw [hz₀] at this; linarith
  set c := (n₀ : ℝ) * β with hc
  set B := Metric.ball z₀ β with hB
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hz₀B : z₀ ∈ B := Metric.mem_ball_self hβ
  have hbound : ∀ w ∈ B, |w.im - z₀.im| < β := by
    intro w hw
    have hdist : dist w z₀ < β := by rwa [Metric.mem_ball] at hw
    calc |w.im - z₀.im| = |(w - z₀).im| := by rw [Complex.sub_im]
      _ ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
      _ = dist w z₀ := (Complex.dist_eq _ _).symm
      _ < β := hdist
  have hfloor_lo : ∀ w ∈ B, w.im < c → ⌊w.im / β⌋ = n₀ - 1 := by
    intro w hwB hwlt
    have hb := hbound w hwB; rw [abs_lt, hz₀im] at hb
    refine (floor_div_eq_iff hβ w.im (n₀ - 1)).mpr ⟨?_, ?_⟩
    · push_cast
      have e : ((n₀ : ℝ) - 1) * β = (n₀ : ℝ) * β - β := by ring
      linarith [hb.1]
    · push_cast
      have e : ((n₀ : ℝ) - 1 + 1) * β = (n₀ : ℝ) * β := by ring
      rw [hc] at hwlt; linarith [hwlt]
  have hfloor_hi : ∀ w ∈ B, c ≤ w.im → ⌊w.im / β⌋ = n₀ := by
    intro w hwB hwge
    have hb := hbound w hwB; rw [abs_lt, hz₀im] at hb
    refine (floor_div_eq_iff hβ w.im n₀).mpr ⟨?_, ?_⟩
    · rw [← hc]; exact hwge
    · have e : ((n₀ : ℝ) + 1) * β = (n₀ : ℝ) * β + β := by ring
      linarith [hb.2]
  set g := fun w : ℂ => F (w - ((n₀ - 1 : ℤ) : ℂ) * ((β : ℂ) * Complex.I)) with hgdef
  set h := fun w : ℂ => F (w - ((n₀ : ℤ) : ℂ) * ((β : ℂ) * Complex.I)) with hhdef
  have hHeq : ∀ w ∈ B, pext β F w = if w.im < c then g w else h w := by
    intro w hwB
    by_cases hwc : w.im < c
    · rw [if_pos hwc]; simp only [pext, pshift, hfloor_lo w hwB hwc, hgdef]
    · rw [if_neg hwc]; rw [not_lt] at hwc
      simp only [pext, pshift, hfloor_hi w hwB hwc, hhdef]
  -- continuity of the glued model on the ball
  have hcont' : ContinuousOn (pext β F) B := by
    have hif : ContinuousOn (fun w => if w.im < c then g w else h w) B := by
      apply ContinuousOn.if
      · -- agreement on the line `Im = c`
        intro w hw
        rw [Set.mem_inter_iff, frontier_setOf_im_lt, Set.mem_setOf_eq] at hw
        obtain ⟨_, hwc⟩ := hw
        have e1 : w - ((n₀ - 1 : ℤ) : ℂ) * ((β : ℂ) * Complex.I)
            = (↑w.re : ℂ) + (↑β : ℂ) * Complex.I := by
          apply Complex.ext
          · rw [sub_intMul_re]
            simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im]
          · rw [sub_intMul_im]
            have hr : (↑w.re + ↑β * Complex.I : ℂ).im = β := by
              simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
                Complex.I_re, Complex.I_im]
            rw [hr]; push_cast; rw [hwc, hc]; ring
        have e2 : w - ((n₀ : ℤ) : ℂ) * ((β : ℂ) * Complex.I) = (↑w.re : ℂ) := by
          apply Complex.ext
          · rw [sub_intMul_re]; simp
          · rw [sub_intMul_im, Complex.ofReal_im, hwc, hc]; ring
        simp only [hgdef, hhdef, e1, e2]
        exact (hper w.re).symm
      · -- lower piece continuous on `Im ≤ c`
        rw [closure_setOf_im_lt, hgdef]
        have hinner : ContinuousOn
            (fun w : ℂ => w - ((n₀ - 1 : ℤ) : ℂ) * ((β : ℂ) * Complex.I))
            (B ∩ {w : ℂ | w.im ≤ c}) := (continuous_id.sub continuous_const).continuousOn
        have hmaps : Set.MapsTo
            (fun w : ℂ => w - ((n₀ - 1 : ℤ) : ℂ) * ((β : ℂ) * Complex.I))
            (B ∩ {w : ℂ | w.im ≤ c}) {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β} := by
          intro w hw
          obtain ⟨hwB, hwle⟩ := hw
          rw [Set.mem_setOf_eq] at hwle
          have hb := hbound w hwB; rw [abs_lt, hz₀im] at hb
          rw [Set.mem_setOf_eq, sub_intMul_im]
          push_cast
          have e : ((n₀ : ℝ) - 1) * β = (n₀ : ℝ) * β - β := by ring
          rw [hc] at hwle
          exact ⟨by linarith [hb.1], by linarith [hwle]⟩
        exact hcont.comp hinner hmaps
      · -- upper piece continuous on `c ≤ Im`
        rw [closure_setOf_not_im_lt, hhdef]
        have hinner : ContinuousOn
            (fun w : ℂ => w - ((n₀ : ℤ) : ℂ) * ((β : ℂ) * Complex.I))
            (B ∩ {w : ℂ | c ≤ w.im}) := (continuous_id.sub continuous_const).continuousOn
        have hmaps : Set.MapsTo
            (fun w : ℂ => w - ((n₀ : ℤ) : ℂ) * ((β : ℂ) * Complex.I))
            (B ∩ {w : ℂ | c ≤ w.im}) {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β} := by
          intro w hw
          obtain ⟨hwB, hwge⟩ := hw
          rw [Set.mem_setOf_eq] at hwge
          have hb := hbound w hwB; rw [abs_lt, hz₀im] at hb
          rw [Set.mem_setOf_eq, sub_intMul_im]
          rw [hc] at hwge
          refine ⟨by linarith [hwge], ?_⟩
          have e : ((n₀ : ℝ) + 1) * β = (n₀ : ℝ) * β + β := by ring
          linarith [hb.2]
        exact hcont.comp hinner hmaps
    exact hif.congr (fun w hw => hHeq w hw)
  -- holomorphy off the line, by reusing the off-line lemma at each such point
  have hdiff' : DifferentiableOn ℂ (pext β F) (B \ {w : ℂ | w.im = c}) := by
    intro w hw
    refine (pext_differentiableAt_offline hβ hdiff ?_).differentiableWithinAt
    obtain ⟨hwB, hwne⟩ := hw
    rw [Set.mem_setOf_eq] at hwne
    rw [pshift_im]
    have hb := hbound w hwB; rw [abs_lt, hz₀im] at hb
    rcases lt_or_gt_of_ne hwne with hlt | hgt
    · rw [hfloor_lo w hwB hlt]; push_cast
      have e : ((n₀ : ℝ) - 1) * β = (n₀ : ℝ) * β - β := by ring
      linarith [hb.1]
    · rw [hfloor_hi w hwB (le_of_lt hgt)]
      rw [hc] at hgt; linarith [hgt]
  have hdiffBall : DifferentiableOn ℂ (pext β F) B :=
    differentiableOn_of_continuousOn_off_horizontal_line hBopen c (pext β F) hcont' hdiff'
  exact hdiffBall.differentiableAt (hBopen.mem_nhds hz₀B)

/-- The periodic extension is entire. -/
theorem pext_differentiable (hβ : 0 < β)
    (hcont : ContinuousOn F {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β})
    (hdiff : DifferentiableOn ℂ F {z : ℂ | 0 < z.im ∧ z.im < β})
    (hper : ∀ t : ℝ, F (t : ℂ) = F ((t : ℂ) + (β : ℂ) * Complex.I)) :
    Differentiable ℂ (pext β F) := by
  intro z
  rcases eq_or_lt_of_le (pshift_im_mem hβ z).1 with hzeq | hzlt
  · exact pext_differentiableAt_online hβ hcont hdiff hper hzeq.symm
  · exact pext_differentiableAt_offline hβ hdiff hzlt

/-- **The `iβ`-periodic bounded entire extension.** A function continuous on the
closed strip `0 ≤ Im ≤ β`, holomorphic on the open strip, bounded, and with equal
boundary values `F(t) = F(t + iβ)`, admits a bounded entire extension agreeing
with it on the real axis. -/
theorem exists_bounded_entire_extension_of_strip_periodic (hβ : 0 < β)
    (hcont : ContinuousOn F {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β})
    (hdiff : DifferentiableOn ℂ F {z : ℂ | 0 < z.im ∧ z.im < β})
    (hper : ∀ t : ℝ, F (t : ℂ) = F ((t : ℂ) + (β : ℂ) * Complex.I))
    (hbdd : ∃ C : ℝ, ∀ z ∈ {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β}, ‖F z‖ ≤ C) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ Bornology.IsBounded (Set.range H) ∧
      ∀ t : ℝ, H (t : ℂ) = F (t : ℂ) := by
  refine ⟨pext β F, pext_differentiable hβ hcont hdiff hper, ?_, ?_⟩
  · rw [isBounded_iff_forall_norm_le]
    obtain ⟨C, hC⟩ := hbdd
    refine ⟨C, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hC (pshift β z) ⟨(pshift_im_mem hβ z).1, le_of_lt (pshift_im_mem hβ z).2⟩
  · intro t
    have hfl : ⌊((t : ℝ) : ℂ).im / β⌋ = 0 := by rw [Complex.ofReal_im, zero_div, Int.floor_zero]
    simp only [pext, pshift, hfl, Int.cast_zero, zero_mul, sub_zero]

/-- The periodic extension agrees with `F` on the (half-open) fundamental strip
`0 ≤ Im z < β`, where the fold is the identity. -/
theorem pext_eq_of_mem_strip (hβ : 0 < β) {z : ℂ} (h0 : 0 ≤ z.im) (hβz : z.im < β) :
    pext β F z = F z := by
  have hfl : ⌊z.im / β⌋ = 0 :=
    (floor_div_eq_iff hβ z.im 0).mpr
      ⟨by simp only [Int.cast_zero, zero_mul]; exact h0,
       by simp only [Int.cast_zero, zero_add, one_mul]; exact hβz⟩
  simp only [pext, pshift, hfl, Int.cast_zero, zero_mul, sub_zero]

/-- **Vanishing from zero boundary values.** A function continuous and bounded on
the closed strip `0 ≤ Im z ≤ β`, holomorphic on the open strip, whose boundary
values on *both* lines vanish, is identically zero on the strip. The periodic
extension is then a bounded entire function (its boundary values agree), hence
constant by Liouville, and the constant is its value `F(0) = 0`. -/
theorem eq_zero_on_strip_of_zero_boundary (hβ : 0 < β)
    (hcont : ContinuousOn F {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β})
    (hdiff : DifferentiableOn ℂ F {z : ℂ | 0 < z.im ∧ z.im < β})
    (hbdd : ∃ C : ℝ, ∀ z ∈ {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β}, ‖F z‖ ≤ C)
    (hbot : ∀ t : ℝ, F (t : ℂ) = 0)
    (htop : ∀ t : ℝ, F ((t : ℂ) + (β : ℂ) * Complex.I) = 0)
    {z : ℂ} (hz0 : 0 ≤ z.im) (hzβ : z.im ≤ β) : F z = 0 := by
  have hper : ∀ t : ℝ, F (t : ℂ) = F ((t : ℂ) + (β : ℂ) * Complex.I) := by
    intro t; rw [hbot, htop]
  have hdiffH : Differentiable ℂ (pext β F) := pext_differentiable hβ hcont hdiff hper
  have hbddH : Bornology.IsBounded (Set.range (pext β F)) := by
    rw [isBounded_iff_forall_norm_le]
    obtain ⟨C, hC⟩ := hbdd
    exact ⟨C, by
      rintro _ ⟨w, rfl⟩
      exact hC (pshift β w) ⟨(pshift_im_mem hβ w).1, le_of_lt (pshift_im_mem hβ w).2⟩⟩
  have hF0 : F (0 : ℂ) = 0 := by have := hbot 0; rwa [Complex.ofReal_zero] at this
  rcases eq_or_lt_of_le hzβ with hzeq | hzlt
  · have hzrepr : z = (↑z.re : ℂ) + (↑β : ℂ) * Complex.I := by
      apply Complex.ext
      · simp
      · simpa using hzeq
    rw [hzrepr]; exact htop z.re
  · have hHz : pext β F z = F z := pext_eq_of_mem_strip hβ hz0 hzlt
    have hH0 : pext β F (0 : ℂ) = F (0 : ℂ) := pext_eq_of_mem_strip hβ (by simp) (by simpa using hβ)
    have hconst : pext β F z = pext β F 0 :=
      Differentiable.apply_eq_apply_of_bounded hdiffH hbddH _ _
    rw [hHz, hH0, hF0] at hconst
    exact hconst

end

/-- **Uniqueness from boundary values.** Two functions continuous and bounded on
the closed strip `0 ≤ Im z ≤ β`, holomorphic on the open strip, that agree on
*both* boundary lines, agree on the whole closed strip. (Their difference has
zero boundary values, so vanishes by `eq_zero_on_strip_of_zero_boundary`.) -/
theorem eqOn_strip_of_eq_boundary {β : ℝ} (hβ : 0 < β) {F G : ℂ → ℂ}
    (hFc : ContinuousOn F {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β})
    (hFd : DifferentiableOn ℂ F {z : ℂ | 0 < z.im ∧ z.im < β})
    (hFb : ∃ C : ℝ, ∀ z ∈ {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β}, ‖F z‖ ≤ C)
    (hGc : ContinuousOn G {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β})
    (hGd : DifferentiableOn ℂ G {z : ℂ | 0 < z.im ∧ z.im < β})
    (hGb : ∃ C : ℝ, ∀ z ∈ {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β}, ‖G z‖ ≤ C)
    (hbot : ∀ t : ℝ, F (t : ℂ) = G (t : ℂ))
    (htop : ∀ t : ℝ,
      F ((t : ℂ) + (β : ℂ) * Complex.I) = G ((t : ℂ) + (β : ℂ) * Complex.I))
    {z : ℂ} (hz0 : 0 ≤ z.im) (hzβ : z.im ≤ β) : F z = G z := by
  have hbdd : ∃ C : ℝ, ∀ z ∈ {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β}, ‖F z - G z‖ ≤ C := by
    obtain ⟨CF, hCF⟩ := hFb; obtain ⟨CG, hCG⟩ := hGb
    exact ⟨CF + CG, fun z hz => (norm_sub_le _ _).trans (add_le_add (hCF z hz) (hCG z hz))⟩
  have hzero := eq_zero_on_strip_of_zero_boundary (F := fun z => F z - G z) hβ
    (hFc.sub hGc) (hFd.sub hGd) hbdd
    (fun s => by simp only [hbot s, sub_self])
    (fun s => by simp only [htop s, sub_self]) hz0 hzβ
  exact sub_eq_zero.mp hzero

end Physicslib4
