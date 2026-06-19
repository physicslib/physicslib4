/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Minkowski

/-!
# Directedness of the Alexandrov basis of standard Minkowski spacetime

Any two Alexandrov-basis "diamonds" `I⁺(p₁) ∩ I⁻(q₁)` and `I⁺(p₂) ∩ I⁻(q₂)`
of standard Minkowski spacetime are contained in a common diamond. This is the
geometric prerequisite for showing the union of local images in a quasilocal
algebra is directed (and hence a `*`-subalgebra), needed to lift the covariance
action.

## Main results

* `Physicslib4.Spacetime.minkowskiForwardCone_subset` /
  `minkowskiBackwardCone_subset`: transitivity (nesting) of the coordinate
  forward / backward Minkowski cones.
* `Physicslib4.Spacetime.exists_common_past` / `exists_common_future`: any two
  points have a common chronological predecessor / successor.
* `Physicslib4.Spacetime.alexandrovBasis_directed`: directedness of the
  Alexandrov basis under inclusion.
-/

namespace Physicslib4
namespace Spacetime

open scoped ComplexOrder

/-- A Cauchy-Schwarz style inequality: the sum of two future-timelike spatial
displacements stays inside the cone of the sum of the time displacements. -/
private theorem cone_add_aux {x y z u v w A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h1 : x ^ 2 + y ^ 2 + z ^ 2 < A ^ 2) (h2 : u ^ 2 + v ^ 2 + w ^ 2 < B ^ 2) :
    (x + u) ^ 2 + (y + v) ^ 2 + (z + w) ^ 2 < (A + B) ^ 2 := by
  nlinarith [sq_nonneg (A * u - B * x), sq_nonneg (A * v - B * y),
    sq_nonneg (A * w - B * z), mul_pos hA hB, mul_pos hA hA, mul_pos hB hB, h1, h2]

/-- **Forward-cone transitivity.** If `p' ∈ I⁺(p)` then `I⁺(p') ⊆ I⁺(p)`. -/
theorem minkowskiForwardCone_subset {p p' : SpacetimeModel}
    (h : p' ∈ minkowskiForwardCone p) :
    minkowskiForwardCone p' ⊆ minkowskiForwardCone p := by
  obtain ⟨h0, hc⟩ := h
  rintro r ⟨hr0, hrc⟩
  refine ⟨h0.trans hr0, ?_⟩
  have h1 : (p' 1 - p 1) ^ 2 + (p' 2 - p 2) ^ 2 + (p' 3 - p 3) ^ 2
      < (p' 0 - p 0) ^ 2 := by linarith [hc]
  have h2 : (r 1 - p' 1) ^ 2 + (r 2 - p' 2) ^ 2 + (r 3 - p' 3) ^ 2
      < (r 0 - p' 0) ^ 2 := by linarith [hrc]
  have haux := cone_add_aux (sub_pos.mpr h0) (sub_pos.mpr hr0) h1 h2
  nlinarith [haux]

/-- **Backward-cone transitivity.** If `q' ∈ I⁻(q)` then `I⁻(q') ⊆ I⁻(q)`. -/
theorem minkowskiBackwardCone_subset {q q' : SpacetimeModel}
    (h : q' ∈ minkowskiBackwardCone q) :
    minkowskiBackwardCone q' ⊆ minkowskiBackwardCone q := by
  intro p hp
  rw [minkowskiBackwardCone_eq, Set.mem_setOf_eq] at hp h ⊢
  exact minkowskiForwardCone_subset hp h

/-- Coordinatewise evaluation of a point supported on the time axis. -/
private theorem single_time_apply (c : ℝ) :
    (EuclideanSpace.single (0 : Fin 4) c) 0 = c ∧
    (EuclideanSpace.single (0 : Fin 4) c) 1 = 0 ∧
    (EuclideanSpace.single (0 : Fin 4) c) 2 = 0 ∧
    (EuclideanSpace.single (0 : Fin 4) c) 3 = 0 :=
  ⟨by rw [PiLp.single_apply, if_pos rfl],
   by rw [PiLp.single_apply, if_neg (by decide)],
   by rw [PiLp.single_apply, if_neg (by decide)],
   by rw [PiLp.single_apply, if_neg (by decide)]⟩

/-- **Existence of a common chronological predecessor.** Any two points lie in
the chronological future of a single point. -/
theorem exists_common_past (p₁ p₂ : SpacetimeModel) :
    ∃ p, p₁ ∈ minkowskiForwardCone p ∧ p₂ ∈ minkowskiForwardCone p := by
  set s₁ : ℝ := (p₁ 1) ^ 2 + (p₁ 2) ^ 2 + (p₁ 3) ^ 2 with hs₁
  set s₂ : ℝ := (p₂ 1) ^ 2 + (p₂ 2) ^ 2 + (p₂ 3) ^ 2 with hs₂
  set R : ℝ := Real.sqrt (s₁ + s₂) + 1 with hR
  set p : SpacetimeModel := EuclideanSpace.single (0 : Fin 4)
    (min (p₁ 0) (p₂ 0) - R) with hp
  obtain ⟨hp0, hp1, hp2, hp3⟩ := single_time_apply (min (p₁ 0) (p₂ 0) - R)
  rw [← hp] at hp0 hp1 hp2 hp3
  have hs1nn : 0 ≤ s₁ := by rw [hs₁]; positivity
  have hs2nn : 0 ≤ s₂ := by rw [hs₂]; positivity
  have hRbig : s₁ + s₂ < R ^ 2 := by
    rw [hR]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ s₁ + s₂ by positivity),
      Real.sqrt_nonneg (s₁ + s₂)]
  have hRpos : 0 < R := by rw [hR]; positivity
  refine ⟨p, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hp0]; nlinarith [min_le_left (p₁ 0) (p₂ 0), hRpos]
  · rw [hp0, hp1, hp2, hp3]
    have hge : R ≤ p₁ 0 - (min (p₁ 0) (p₂ 0) - R) := by
      have := min_le_left (p₁ 0) (p₂ 0); linarith
    nlinarith [hge, hRpos, hRbig, hs2nn, hs₁]
  · rw [hp0]; nlinarith [min_le_right (p₁ 0) (p₂ 0), hRpos]
  · rw [hp0, hp1, hp2, hp3]
    have hge : R ≤ p₂ 0 - (min (p₁ 0) (p₂ 0) - R) := by
      have := min_le_right (p₁ 0) (p₂ 0); linarith
    nlinarith [hge, hRpos, hRbig, hs1nn, hs₂]

/-- **Existence of a common chronological successor.** Any two points lie in
the chronological past of a single point. -/
theorem exists_common_future (q₁ q₂ : SpacetimeModel) :
    ∃ q, q₁ ∈ minkowskiBackwardCone q ∧ q₂ ∈ minkowskiBackwardCone q := by
  set s₁ : ℝ := (q₁ 1) ^ 2 + (q₁ 2) ^ 2 + (q₁ 3) ^ 2 with hs₁
  set s₂ : ℝ := (q₂ 1) ^ 2 + (q₂ 2) ^ 2 + (q₂ 3) ^ 2 with hs₂
  set R : ℝ := Real.sqrt (s₁ + s₂) + 1 with hR
  set q : SpacetimeModel := EuclideanSpace.single (0 : Fin 4)
    (max (q₁ 0) (q₂ 0) + R) with hq
  obtain ⟨hq0, hq1, hq2, hq3⟩ := single_time_apply (max (q₁ 0) (q₂ 0) + R)
  rw [← hq] at hq0 hq1 hq2 hq3
  have hs1nn : 0 ≤ s₁ := by rw [hs₁]; positivity
  have hs2nn : 0 ≤ s₂ := by rw [hs₂]; positivity
  have hRbig : s₁ + s₂ < R ^ 2 := by
    rw [hR]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ s₁ + s₂ by positivity),
      Real.sqrt_nonneg (s₁ + s₂)]
  have hRpos : 0 < R := by rw [hR]; positivity
  refine ⟨q, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hq0]; nlinarith [le_max_left (q₁ 0) (q₂ 0), hRpos]
  · rw [hq0, hq1, hq2, hq3]
    have hge : R ≤ max (q₁ 0) (q₂ 0) + R - q₁ 0 := by
      have := le_max_left (q₁ 0) (q₂ 0); linarith
    nlinarith [hge, hRpos, hRbig, hs2nn, hs₁]
  · rw [hq0]; nlinarith [le_max_right (q₁ 0) (q₂ 0), hRpos]
  · rw [hq0, hq1, hq2, hq3]
    have hge : R ≤ max (q₁ 0) (q₂ 0) + R - q₂ 0 := by
      have := le_max_right (q₁ 0) (q₂ 0); linarith
    nlinarith [hge, hRpos, hRbig, hs1nn, hs₂]

/-- **Directedness of the Alexandrov basis.** Any two Alexandrov-basis diamonds
of standard Minkowski spacetime are contained in a common diamond. -/
theorem alexandrovBasis_directed {B₁ B₂ : Set SpacetimeModel}
    (h₁ : B₁ ∈ alexandrovBasis StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation)
    (h₂ : B₂ ∈ alexandrovBasis StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation) :
    ∃ B ∈ alexandrovBasis StandardMinkowskiSpacetime standardMinkowskiTimeOrientation,
      B₁ ⊆ B ∧ B₂ ⊆ B := by
  obtain ⟨p₁, q₁, rfl⟩ := h₁
  obtain ⟨p₂, q₂, rfl⟩ := h₂
  obtain ⟨p, hp1, hp2⟩ := exists_common_past p₁ p₂
  obtain ⟨q, hq1, hq2⟩ := exists_common_future q₁ q₂
  refine ⟨_, ⟨p, q, rfl⟩, ?_, ?_⟩
  · intro x hx
    simp only [chronologicalFuture_standardMinkowski,
      chronologicalPast_standardMinkowski] at hx ⊢
    exact ⟨minkowskiForwardCone_subset hp1 hx.1, minkowskiBackwardCone_subset hq1 hx.2⟩
  · intro x hx
    simp only [chronologicalFuture_standardMinkowski,
      chronologicalPast_standardMinkowski] at hx ⊢
    exact ⟨minkowskiForwardCone_subset hp2 hx.1, minkowskiBackwardCone_subset hq2 hx.2⟩

end Spacetime
end Physicslib4
