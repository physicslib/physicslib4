/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Analysis.HorizontalLineRemovable

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

/-- The half-plane `{Im z < c}` is open. -/
theorem isOpen_setOf_im_lt (c : ℝ) : IsOpen {z : ℂ | z.im < c} :=
  isOpen_lt Complex.continuous_im continuous_const

/-- Closure of the open lower half-plane `{Im z < c}` is `{Im z ≤ c}`. -/
theorem closure_setOf_im_lt (c : ℝ) :
    closure {z : ℂ | z.im < c} = {z : ℂ | z.im ≤ c} := by
  apply Subset.antisymm
  · exact closure_minimal (Set.setOf_subset_setOf.mpr fun z h => le_of_lt h)
      (isClosed_le Complex.continuous_im continuous_const)
  · intro z hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨z - (ε / 2 : ℝ) * Complex.I, ?_, ?_⟩
    · change (z - (ε / 2 : ℝ) * Complex.I).im < c
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
      have : z.im ≤ c := hz
      linarith
    · rw [Complex.dist_eq]
      have he : z - (z - (ε / 2 : ℝ) * Complex.I) = (ε / 2 : ℝ) * Complex.I := by ring
      rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith

/-- Closure of `{¬ (Im z < c)}` is `{c ≤ Im z}`. -/
theorem closure_setOf_not_im_lt (c : ℝ) :
    closure {z : ℂ | ¬ (z.im < c)} = {z : ℂ | c ≤ z.im} := by
  have h : {z : ℂ | ¬ (z.im < c)} = {z : ℂ | c ≤ z.im} := by ext z; simp [not_lt]
  rw [h, (isClosed_le continuous_const Complex.continuous_im).closure_eq]

/-- Frontier of `{Im z < c}` is the line `{Im z = c}`. -/
theorem frontier_setOf_im_lt (c : ℝ) :
    frontier {z : ℂ | z.im < c} = {z : ℂ | z.im = c} := by
  rw [show frontier {z : ℂ | z.im < c}
      = closure {z : ℂ | z.im < c} \ interior {z : ℂ | z.im < c} from rfl,
    closure_setOf_im_lt, (isOpen_setOf_im_lt c).interior_eq]
  ext z
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_lt]
  exact ⟨fun ⟨h1, h2⟩ => le_antisymm h1 h2, fun h => ⟨h.le, h.ge⟩⟩

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

end

end Physicslib4
