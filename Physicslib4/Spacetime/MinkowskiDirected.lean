/-
Copyright (c) 2026 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Community
-/
import Physicslib4.Spacetime.Minkowski
import Mathlib.Topology.Bases

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

/-! ### The Alexandrov diamonds form a genuine topological basis on standard Minkowski -/

/-- **Past interpolation.** If `x` is in the forward cones of `p₁` and `p₂`, there is
a point `a` in both forward cones with `x` in the forward cone of `a` (i.e.
`p₁, p₂ ≪ a ≪ x`). Take `a = x - ε • e₀` for small `ε > 0`: the spatial separation
from each `pᵢ` is unchanged, so the timelike condition survives, and `x - a = ε e₀` is
future-timelike. -/
theorem exists_past_between_standardMinkowski {p₁ p₂ x : SpacetimeModel}
    (h₁ : x ∈ minkowskiForwardCone p₁) (h₂ : x ∈ minkowskiForwardCone p₂) :
    ∃ a, a ∈ minkowskiForwardCone p₁ ∧ a ∈ minkowskiForwardCone p₂ ∧
      x ∈ minkowskiForwardCone a := by
  obtain ⟨h₁0, h₁c⟩ := h₁
  obtain ⟨h₂0, h₂c⟩ := h₂
  set T₁ := x 0 - p₁ 0 with hT₁
  set T₂ := x 0 - p₂ 0 with hT₂
  set S₁ := (x 1 - p₁ 1)^2 + (x 2 - p₁ 2)^2 + (x 3 - p₁ 3)^2 with hS₁
  set S₂ := (x 1 - p₂ 1)^2 + (x 2 - p₂ 2)^2 + (x 3 - p₂ 3)^2 with hS₂
  have hT₁pos : 0 < T₁ := sub_pos.mpr h₁0
  have hT₂pos : 0 < T₂ := sub_pos.mpr h₂0
  have hS₁ltT₁sq : S₁ < T₁ ^ 2 := by
    dsimp [S₁, T₁] at h₁c ⊢
    linarith
  have hS₂ltT₂sq : S₂ < T₂ ^ 2 := by
    dsimp [S₂, T₂] at h₂c ⊢
    linarith
  set δ₁ := T₁ ^ 2 - S₁ with hδ₁
  set δ₂ := T₂ ^ 2 - S₂ with hδ₂
  have hδ₁pos : 0 < δ₁ := by rw [hδ₁]; linarith
  have hδ₂pos : 0 < δ₂ := by rw [hδ₂]; linarith
  have hS₁_nonneg : 0 ≤ S₁ := by rw [hS₁]; positivity
  have hS₂_nonneg : 0 ≤ S₂ := by rw [hS₂]; positivity
  have hδ₁leT₁sq : δ₁ ≤ T₁ ^ 2 := by rw [hδ₁]; linarith
  have hδ₂leT₂sq : δ₂ ≤ T₂ ^ 2 := by rw [hδ₂]; linarith
  have hδ₁_div_pos : 0 < δ₁ / (2 * T₁) := div_pos hδ₁pos (by positivity)
  have hδ₂_div_pos : 0 < δ₂ / (2 * T₂) := div_pos hδ₂pos (by positivity)
  set ε := min (δ₁ / (2 * T₁)) (δ₂ / (2 * T₂)) with hε
  have hεpos : 0 < ε := by
    rw [hε]
    exact lt_min_iff.mpr ⟨hδ₁_div_pos, hδ₂_div_pos⟩
  have hε_le_δ₁_div : ε ≤ δ₁ / (2 * T₁) := by
    rw [hε]; exact min_le_left _ _
  have hε_le_δ₂_div : ε ≤ δ₂ / (2 * T₂) := by
    rw [hε]; exact min_le_right _ _
  have hε_mul₁ : 2 * T₁ * ε ≤ δ₁ := by
    have hpos : 0 < 2 * T₁ := by positivity
    calc
      2 * T₁ * ε ≤ 2 * T₁ * (δ₁ / (2 * T₁)) :=
        mul_le_mul_of_nonneg_left hε_le_δ₁_div (by positivity)
      _ = δ₁ := by field_simp [hpos.ne.symm]
  have hε_mul₂ : 2 * T₂ * ε ≤ δ₂ := by
    have hpos : 0 < 2 * T₂ := by positivity
    calc
      2 * T₂ * ε ≤ 2 * T₂ * (δ₂ / (2 * T₂)) :=
        mul_le_mul_of_nonneg_left hε_le_δ₂_div (by positivity)
      _ = δ₂ := by field_simp [hpos.ne.symm]
  have hε_lt_T₁ : ε < T₁ := by
    by_contra! h
    have h2T₁ε_ge_2T₁sq : 2 * T₁ * ε ≥ 2 * T₁ ^ 2 := by
      calc
        2 * T₁ * ε ≥ 2 * T₁ * T₁ := mul_le_mul_of_nonneg_left h (by positivity)
        _ = 2 * T₁ ^ 2 := by ring
    have hchain : 2 * T₁ ^ 2 ≤ T₁ ^ 2 := by
      calc
        2 * T₁ ^ 2 ≤ 2 * T₁ * ε := h2T₁ε_ge_2T₁sq
        _ ≤ δ₁ := hε_mul₁
        _ ≤ T₁ ^ 2 := hδ₁leT₁sq
    have hpos : T₁ ^ 2 > 0 := pow_pos hT₁pos 2
    linarith
  have hε_lt_T₂ : ε < T₂ := by
    by_contra! h
    have h2T₂ε_ge_2T₂sq : 2 * T₂ * ε ≥ 2 * T₂ ^ 2 := by
      calc
        2 * T₂ * ε ≥ 2 * T₂ * T₂ := mul_le_mul_of_nonneg_left h (by positivity)
        _ = 2 * T₂ ^ 2 := by ring
    have hchain : 2 * T₂ ^ 2 ≤ T₂ ^ 2 := by
      calc
        2 * T₂ ^ 2 ≤ 2 * T₂ * ε := h2T₂ε_ge_2T₂sq
        _ ≤ δ₂ := hε_mul₂
        _ ≤ T₂ ^ 2 := hδ₂leT₂sq
    have hpos : T₂ ^ 2 > 0 := pow_pos hT₂pos 2
    linarith
  have hcone_ineq₁ : S₁ < (T₁ - ε) ^ 2 := by
    have hsqpos : 0 < ε ^ 2 := pow_pos hεpos 2
    have hsub : 2 * T₁ * ε - ε ^ 2 < δ₁ := by
      have htemp : 2 * T₁ * ε - ε ^ 2 < 2 * T₁ * ε := by linarith
      exact htemp.trans_le hε_mul₁
    have eqn : (T₁ - ε) ^ 2 - S₁ = δ₁ - (2 * T₁ * ε - ε ^ 2) := by
      rw [hδ₁]; ring
    linarith
  have hcone_ineq₂ : S₂ < (T₂ - ε) ^ 2 := by
    have hsqpos : 0 < ε ^ 2 := pow_pos hεpos 2
    have hsub : 2 * T₂ * ε - ε ^ 2 < δ₂ := by
      have htemp : 2 * T₂ * ε - ε ^ 2 < 2 * T₂ * ε := by linarith
      exact htemp.trans_le hε_mul₂
    have eqn : (T₂ - ε) ^ 2 - S₂ = δ₂ - (2 * T₂ * ε - ε ^ 2) := by
      rw [hδ₂]; ring
    linarith
  set a : SpacetimeModel := x - EuclideanSpace.single (0 : Fin 4) ε with ha
  have ha0 : a 0 = x 0 - ε := by
    rw [ha, PiLp.sub_apply, PiLp.single_apply, if_pos rfl]
  have ha1 : a 1 = x 1 := by
    rw [ha, PiLp.sub_apply, PiLp.single_apply, if_neg (by decide)]
    simp
  have ha2 : a 2 = x 2 := by
    rw [ha, PiLp.sub_apply, PiLp.single_apply, if_neg (by decide)]
    simp
  have ha3 : a 3 = x 3 := by
    rw [ha, PiLp.sub_apply, PiLp.single_apply, if_neg (by decide)]
    simp
  refine ⟨a, ?_, ?_, ?_⟩
  · -- a ∈ minkowskiForwardCone p₁
    rw [mem_minkowskiForwardCone, ha0, ha1, ha2, ha3]
    dsimp [T₁, S₁]
    constructor
    · linarith
    · linarith
  · -- a ∈ minkowskiForwardCone p₂
    rw [mem_minkowskiForwardCone, ha0, ha1, ha2, ha3]
    dsimp [T₂, S₂]
    constructor
    · linarith
    · linarith
  · -- x ∈ minkowskiForwardCone a
    rw [mem_minkowskiForwardCone, ha0, ha1, ha2, ha3]
    constructor
    · linarith
    · have : 0 < ε ^ 2 := pow_pos hεpos 2
      linarith

/-- **Future interpolation.** If `x` is in the backward cones of `q₁` and `q₂`, there
is a point `b` in both backward cones with `x` in the backward cone of `b` (i.e.
`x ≪ b ≪ q₁, q₂`). Dual to `exists_past_between_standardMinkowski`, with `b = x + ε • e₀`. -/
theorem exists_future_between_standardMinkowski {q₁ q₂ x : SpacetimeModel}
    (h₁ : x ∈ minkowskiBackwardCone q₁) (h₂ : x ∈ minkowskiBackwardCone q₂) :
    ∃ b, b ∈ minkowskiBackwardCone q₁ ∧ b ∈ minkowskiBackwardCone q₂ ∧
      x ∈ minkowskiBackwardCone b := by
  obtain ⟨h₁0, h₁c⟩ := h₁
  obtain ⟨h₂0, h₂c⟩ := h₂
  set T₁ := q₁ 0 - x 0 with hT₁
  set T₂ := q₂ 0 - x 0 with hT₂
  set S₁ := (q₁ 1 - x 1)^2 + (q₁ 2 - x 2)^2 + (q₁ 3 - x 3)^2 with hS₁
  set S₂ := (q₂ 1 - x 1)^2 + (q₂ 2 - x 2)^2 + (q₂ 3 - x 3)^2 with hS₂
  have hT₁pos : 0 < T₁ := sub_pos.mpr h₁0
  have hT₂pos : 0 < T₂ := sub_pos.mpr h₂0
  have hS₁ltT₁sq : S₁ < T₁ ^ 2 := by
    dsimp [S₁, T₁] at h₁c ⊢
    linarith
  have hS₂ltT₂sq : S₂ < T₂ ^ 2 := by
    dsimp [S₂, T₂] at h₂c ⊢
    linarith
  set δ₁ := T₁ ^ 2 - S₁ with hδ₁
  set δ₂ := T₂ ^ 2 - S₂ with hδ₂
  have hδ₁pos : 0 < δ₁ := by rw [hδ₁]; linarith
  have hδ₂pos : 0 < δ₂ := by rw [hδ₂]; linarith
  have hS₁_nonneg : 0 ≤ S₁ := by rw [hS₁]; positivity
  have hS₂_nonneg : 0 ≤ S₂ := by rw [hS₂]; positivity
  have hδ₁leT₁sq : δ₁ ≤ T₁ ^ 2 := by rw [hδ₁]; linarith
  have hδ₂leT₂sq : δ₂ ≤ T₂ ^ 2 := by rw [hδ₂]; linarith
  have hδ₁_div_pos : 0 < δ₁ / (2 * T₁) := div_pos hδ₁pos (by positivity)
  have hδ₂_div_pos : 0 < δ₂ / (2 * T₂) := div_pos hδ₂pos (by positivity)
  set ε := min (δ₁ / (2 * T₁)) (δ₂ / (2 * T₂)) with hε
  have hεpos : 0 < ε := by
    rw [hε]
    exact lt_min_iff.mpr ⟨hδ₁_div_pos, hδ₂_div_pos⟩
  have hε_le_δ₁_div : ε ≤ δ₁ / (2 * T₁) := by
    rw [hε]; exact min_le_left _ _
  have hε_le_δ₂_div : ε ≤ δ₂ / (2 * T₂) := by
    rw [hε]; exact min_le_right _ _
  have hε_mul₁ : 2 * T₁ * ε ≤ δ₁ := by
    have hpos : 0 < 2 * T₁ := by positivity
    calc
      2 * T₁ * ε ≤ 2 * T₁ * (δ₁ / (2 * T₁)) :=
        mul_le_mul_of_nonneg_left hε_le_δ₁_div (by positivity)
      _ = δ₁ := by field_simp [hpos.ne.symm]
  have hε_mul₂ : 2 * T₂ * ε ≤ δ₂ := by
    have hpos : 0 < 2 * T₂ := by positivity
    calc
      2 * T₂ * ε ≤ 2 * T₂ * (δ₂ / (2 * T₂)) :=
        mul_le_mul_of_nonneg_left hε_le_δ₂_div (by positivity)
      _ = δ₂ := by field_simp [hpos.ne.symm]
  have hε_lt_T₁ : ε < T₁ := by
    by_contra! h
    have h2T₁ε_ge_2T₁sq : 2 * T₁ * ε ≥ 2 * T₁ ^ 2 := by
      calc
        2 * T₁ * ε ≥ 2 * T₁ * T₁ := mul_le_mul_of_nonneg_left h (by positivity)
        _ = 2 * T₁ ^ 2 := by ring
    have hchain : 2 * T₁ ^ 2 ≤ T₁ ^ 2 := by
      calc
        2 * T₁ ^ 2 ≤ 2 * T₁ * ε := h2T₁ε_ge_2T₁sq
        _ ≤ δ₁ := hε_mul₁
        _ ≤ T₁ ^ 2 := hδ₁leT₁sq
    have hpos : T₁ ^ 2 > 0 := pow_pos hT₁pos 2
    linarith
  have hε_lt_T₂ : ε < T₂ := by
    by_contra! h
    have h2T₂ε_ge_2T₂sq : 2 * T₂ * ε ≥ 2 * T₂ ^ 2 := by
      calc
        2 * T₂ * ε ≥ 2 * T₂ * T₂ := mul_le_mul_of_nonneg_left h (by positivity)
        _ = 2 * T₂ ^ 2 := by ring
    have hchain : 2 * T₂ ^ 2 ≤ T₂ ^ 2 := by
      calc
        2 * T₂ ^ 2 ≤ 2 * T₂ * ε := h2T₂ε_ge_2T₂sq
        _ ≤ δ₂ := hε_mul₂
        _ ≤ T₂ ^ 2 := hδ₂leT₂sq
    have hpos : T₂ ^ 2 > 0 := pow_pos hT₂pos 2
    linarith
  have hcone_ineq₁ : S₁ < (T₁ - ε) ^ 2 := by
    have hsqpos : 0 < ε ^ 2 := pow_pos hεpos 2
    have hsub : 2 * T₁ * ε - ε ^ 2 < δ₁ := by
      have htemp : 2 * T₁ * ε - ε ^ 2 < 2 * T₁ * ε := by linarith
      exact htemp.trans_le hε_mul₁
    have eqn : (T₁ - ε) ^ 2 - S₁ = δ₁ - (2 * T₁ * ε - ε ^ 2) := by
      rw [hδ₁]; ring
    linarith
  have hcone_ineq₂ : S₂ < (T₂ - ε) ^ 2 := by
    have hsqpos : 0 < ε ^ 2 := pow_pos hεpos 2
    have hsub : 2 * T₂ * ε - ε ^ 2 < δ₂ := by
      have htemp : 2 * T₂ * ε - ε ^ 2 < 2 * T₂ * ε := by linarith
      exact htemp.trans_le hε_mul₂
    have eqn : (T₂ - ε) ^ 2 - S₂ = δ₂ - (2 * T₂ * ε - ε ^ 2) := by
      rw [hδ₂]; ring
    linarith
  set b : SpacetimeModel := x + EuclideanSpace.single (0 : Fin 4) ε with hb
  have hb0 : b 0 = x 0 + ε := by
    rw [hb, PiLp.add_apply, PiLp.single_apply, if_pos rfl]
  have hb1 : b 1 = x 1 := by
    rw [hb, PiLp.add_apply, PiLp.single_apply, if_neg (by decide)]
    simp
  have hb2 : b 2 = x 2 := by
    rw [hb, PiLp.add_apply, PiLp.single_apply, if_neg (by decide)]
    simp
  have hb3 : b 3 = x 3 := by
    rw [hb, PiLp.add_apply, PiLp.single_apply, if_neg (by decide)]
    simp
  refine ⟨b, ?_, ?_, ?_⟩
  · -- b ∈ minkowskiBackwardCone q₁
    rw [mem_minkowskiBackwardCone, hb0, hb1, hb2, hb3]
    dsimp [T₁, S₁]
    constructor
    · linarith
    · linarith
  · -- b ∈ minkowskiBackwardCone q₂
    rw [mem_minkowskiBackwardCone, hb0, hb1, hb2, hb3]
    dsimp [T₂, S₂]
    constructor
    · linarith
    · linarith
  · -- x ∈ minkowskiBackwardCone b
    rw [mem_minkowskiBackwardCone, hb0, hb1, hb2, hb3]
    constructor
    · linarith
    · have : 0 < ε ^ 2 := pow_pos hεpos 2
      linarith

/-- **Downward intersection property of the diamonds.** For two Alexandrov diamonds of
standard Minkowski and a point `x` in their intersection, there is a diamond `B₃` with
`x ∈ B₃ ⊆ B₁ ∩ B₂`. Uses past/future interpolation to build `B₃ = I⁺(a) ∩ I⁻(b)` and
cone-nesting for the containment. -/
theorem alexandrovBasis_exists_subset_inter_standardMinkowski
    (B₁ : Set SpacetimeModel)
    (h₁ : B₁ ∈ alexandrovBasis StandardMinkowskiSpacetime standardMinkowskiTimeOrientation)
    (B₂ : Set SpacetimeModel)
    (h₂ : B₂ ∈ alexandrovBasis StandardMinkowskiSpacetime standardMinkowskiTimeOrientation)
    (x : SpacetimeModel) (hx : x ∈ B₁ ∩ B₂) :
    ∃ B₃ ∈ alexandrovBasis StandardMinkowskiSpacetime standardMinkowskiTimeOrientation,
      x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂ := by
  obtain ⟨p₁, q₁, rfl⟩ := h₁
  obtain ⟨p₂, q₂, rfl⟩ := h₂
  simp only [chronologicalFuture_standardMinkowski, chronologicalPast_standardMinkowski] at hx
  obtain ⟨⟨hxp1, hxq1⟩, ⟨hxp2, hxq2⟩⟩ := hx
  obtain ⟨a, ha1, ha2, hax⟩ := exists_past_between_standardMinkowski hxp1 hxp2
  obtain ⟨b, hb1, hb2, hxb⟩ := exists_future_between_standardMinkowski hxq1 hxq2
  refine ⟨(chronologicalFuture StandardMinkowskiSpacetime standardMinkowskiTimeOrientation a ∩
    chronologicalPast StandardMinkowskiSpacetime standardMinkowskiTimeOrientation b),
    ⟨a, b, rfl⟩, ?_, ?_⟩
  · simp only [chronologicalFuture_standardMinkowski, chronologicalPast_standardMinkowski]
    exact ⟨hax, hxb⟩
  · intro y hy
    simp only [chronologicalFuture_standardMinkowski, chronologicalPast_standardMinkowski] at hy ⊢
    obtain ⟨hyf, hyb⟩ := hy
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact minkowskiForwardCone_subset ha1 hyf
    · exact minkowskiBackwardCone_subset hb1 hyb
    · exact minkowskiForwardCone_subset ha2 hyf
    · exact minkowskiBackwardCone_subset hb2 hyb

/-- **The Alexandrov diamonds are a topological basis on standard Minkowski.**
Unconditionally: covering holds because every point has a chronological past and
future point, and the downward intersection property is
`alexandrovBasis_exists_subset_inter_standardMinkowski`; the generation condition is
definitional. -/
theorem isTopologicalBasis_alexandrovBasis_standardMinkowski :
    @TopologicalSpace.IsTopologicalBasis SpacetimeModel
      (alexandrovTopology StandardMinkowskiSpacetime standardMinkowskiTimeOrientation)
      (alexandrovBasis StandardMinkowskiSpacetime standardMinkowskiTimeOrientation) := by
  have h1 : ∀ t₁ ∈ alexandrovBasis StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation,
      ∀ t₂ ∈ alexandrovBasis StandardMinkowskiSpacetime standardMinkowskiTimeOrientation,
      ∀ x ∈ t₁ ∩ t₂, ∃ t₃ ∈ alexandrovBasis StandardMinkowskiSpacetime
        standardMinkowskiTimeOrientation,
        x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂ :=
    alexandrovBasis_exists_subset_inter_standardMinkowski
  have h2 : ⋃₀ (alexandrovBasis StandardMinkowskiSpacetime
      standardMinkowskiTimeOrientation) = Set.univ := by
    apply Set.sUnion_eq_univ_iff.mpr
    intro x
    rcases exists_chronologicalPast_standardMinkowski x with ⟨a, ha⟩
    rcases exists_chronologicalFuture_standardMinkowski x with ⟨b, hb⟩
    refine ⟨chronologicalFuture StandardMinkowskiSpacetime standardMinkowskiTimeOrientation a ∩
      chronologicalPast StandardMinkowskiSpacetime standardMinkowskiTimeOrientation b, ?_, ?_⟩
    · exact ⟨a, b, rfl⟩
    · exact ⟨by
        simpa [chronologicalFuture, chronologicalPast] using ha,
      by
        simpa [chronologicalPast, chronologicalFuture] using hb⟩
  have h3 : alexandrovTopology StandardMinkowskiSpacetime standardMinkowskiTimeOrientation =
      TopologicalSpace.generateFrom
        (alexandrovBasis StandardMinkowskiSpacetime standardMinkowskiTimeOrientation) := rfl
  exact @TopologicalSpace.IsTopologicalBasis.mk SpacetimeModel
    (alexandrovTopology StandardMinkowskiSpacetime standardMinkowskiTimeOrientation)
    (alexandrovBasis StandardMinkowskiSpacetime standardMinkowskiTimeOrientation) h1 h2 h3

end Spacetime
end Physicslib4
