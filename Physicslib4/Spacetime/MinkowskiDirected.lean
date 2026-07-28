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
  -- Cauchy-Schwarz: `2AB (xu + yv + zw) ≤ B²(x²+y²+z²) + A²(u²+v²+w²) < 2A²B²`.
  have key : 2 * (A * B) * (x * u + y * v + z * w) < 2 * (A * B) * (A * B) := by
    linarith only [mul_lt_mul_of_pos_left h1 (pow_pos hB 2),
      mul_lt_mul_of_pos_left h2 (pow_pos hA 2), sq_nonneg (B * x - A * u),
      sq_nonneg (B * y - A * v), sq_nonneg (B * z - A * w)]
  linarith only [h1, h2,
    lt_of_mul_lt_mul_left key (mul_nonneg zero_le_two (mul_pos hA hB).le)]

/-- **Forward-cone transitivity.** If `p' ∈ I⁺(p)` then `I⁺(p') ⊆ I⁺(p)`. -/
theorem minkowskiForwardCone_subset {p p' : SpacetimeModel}
    (h : p' ∈ minkowskiForwardCone p) :
    minkowskiForwardCone p' ⊆ minkowskiForwardCone p := by
  obtain ⟨h0, hc⟩ := h
  rintro r ⟨hr0, hrc⟩
  refine ⟨h0.trans hr0, ?_⟩
  have h1 : (p' 1 - p 1) ^ 2 + (p' 2 - p 2) ^ 2 + (p' 3 - p 3) ^ 2
      < (p' 0 - p 0) ^ 2 := by linarith only [hc]
  have h2 : (r 1 - p' 1) ^ 2 + (r 2 - p' 2) ^ 2 + (r 3 - p' 3) ^ 2
      < (r 0 - p' 0) ^ 2 := by linarith only [hrc]
  linarith only [cone_add_aux (sub_pos.mpr h0) (sub_pos.mpr hr0) h1 h2]

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

/-- Nonnegativity of a three-term sum of squares (the spatial part of a displacement). -/
private theorem sq3_nonneg (a b c : ℝ) : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  positivity -- (extracted by Fuse golfer)

/-- If `u + v < R ^ 2` with `0 ≤ v` and `0 < R ≤ D`, then `u < D ^ 2`. -/
private theorem lt_sq_of_add_lt_sq {u v R D : ℝ} (hv : 0 ≤ v) (h : u + v < R ^ 2)
    (hR : 0 < R) (hD : R ≤ D) : u < D ^ 2 := by -- (extracted by Fuse golfer)
  linarith only [hv, h, mul_self_le_mul_self hR.le hD]

/-- Two nonnegative "spatial radii" are both dominated by the squared time separation
from a single sufficiently early time. -/
private theorem exists_time_shift_lt {a₁ a₂ s₁ s₂ : ℝ} (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂) :
    ∃ t : ℝ, t < a₁ ∧ t < a₂ ∧ s₁ < (a₁ - t) ^ 2 ∧ s₂ < (a₂ - t) ^ 2 := by
  -- (extracted by Fuse golfer)
  obtain ⟨R, hR, hRsq⟩ : ∃ R : ℝ, 0 < R ∧ s₁ + s₂ < R ^ 2 :=
    ⟨Real.sqrt (s₁ + s₂) + 1, by linarith only [Real.sqrt_nonneg (s₁ + s₂)], by
      linarith only [Real.sq_sqrt (by linarith only [h₁, h₂] : (0 : ℝ) ≤ s₁ + s₂),
        Real.sqrt_nonneg (s₁ + s₂)]⟩
  have k₁ := min_le_left a₁ a₂
  have k₂ := min_le_right a₁ a₂
  exact ⟨min a₁ a₂ - R, by linarith only [k₁, hR], by linarith only [k₂, hR],
    lt_sq_of_add_lt_sq h₂ hRsq hR (by linarith only [k₁]),
    lt_sq_of_add_lt_sq h₁ (by linarith only [hRsq]) hR (by linarith only [k₂])⟩

/-- Time-reversed form of `exists_time_shift_lt`: a single sufficiently late time. -/
private theorem exists_time_shift_gt {a₁ a₂ s₁ s₂ : ℝ} (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂) :
    ∃ t : ℝ, a₁ < t ∧ a₂ < t ∧ s₁ < (t - a₁) ^ 2 ∧ s₂ < (t - a₂) ^ 2 := by
  -- (extracted by Fuse golfer)
  obtain ⟨t, ht₁, ht₂, hc₁, hc₂⟩ := exists_time_shift_lt (a₁ := -a₁) (a₂ := -a₂) h₁ h₂
  refine ⟨-t, by linarith only [ht₁], by linarith only [ht₂], ?_, ?_⟩
  · rw [show -t - a₁ = -a₁ - t from by ring]; exact hc₁
  · rw [show -t - a₂ = -a₂ - t from by ring]; exact hc₂

/-- **Existence of a common chronological predecessor.** Any two points lie in
the chronological future of a single point. -/
theorem exists_common_past (p₁ p₂ : SpacetimeModel) :
    ∃ p, p₁ ∈ minkowskiForwardCone p ∧ p₂ ∈ minkowskiForwardCone p := by
  obtain ⟨t, ht₁, ht₂, hc₁, hc₂⟩ :=
    exists_time_shift_lt (a₁ := p₁ 0) (a₂ := p₂ 0)
      (s₁ := (p₁ 1) ^ 2 + (p₁ 2) ^ 2 + (p₁ 3) ^ 2)
      (s₂ := (p₂ 1) ^ 2 + (p₂ 2) ^ 2 + (p₂ 3) ^ 2) (sq3_nonneg _ _ _) (sq3_nonneg _ _ _)
  obtain ⟨e0, e1, e2, e3⟩ := single_time_apply t
  refine ⟨EuclideanSpace.single (0 : Fin 4) t, ⟨by rwa [e0], ?_⟩, ⟨by rwa [e0], ?_⟩⟩
  · rw [e0, e1, e2, e3]; simp only [sub_zero]; linarith only [hc₁]
  · rw [e0, e1, e2, e3]; simp only [sub_zero]; linarith only [hc₂]

/-- **Existence of a common chronological successor.** Any two points lie in
the chronological past of a single point. -/
theorem exists_common_future (q₁ q₂ : SpacetimeModel) :
    ∃ q, q₁ ∈ minkowskiBackwardCone q ∧ q₂ ∈ minkowskiBackwardCone q := by
  obtain ⟨t, ht₁, ht₂, hc₁, hc₂⟩ :=
    exists_time_shift_gt (a₁ := q₁ 0) (a₂ := q₂ 0)
      (s₁ := (q₁ 1) ^ 2 + (q₁ 2) ^ 2 + (q₁ 3) ^ 2)
      (s₂ := (q₂ 1) ^ 2 + (q₂ 2) ^ 2 + (q₂ 3) ^ 2) (sq3_nonneg _ _ _) (sq3_nonneg _ _ _)
  obtain ⟨e0, e1, e2, e3⟩ := single_time_apply t
  refine ⟨EuclideanSpace.single (0 : Fin 4) t, ⟨by rwa [e0], ?_⟩, ⟨by rwa [e0], ?_⟩⟩
  · rw [e0, e1, e2, e3]; simp only [zero_sub, neg_sq]; linarith only [hc₁]
  · rw [e0, e1, e2, e3]; simp only [zero_sub, neg_sq]; linarith only [hc₂]

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

/-- Coordinatewise evaluation of a translate along the time axis. -/
private theorem sub_single_time_apply (x : SpacetimeModel) (c : ℝ) :
    (x - EuclideanSpace.single (0 : Fin 4) c) 0 = x 0 - c ∧
    (x - EuclideanSpace.single (0 : Fin 4) c) 1 = x 1 ∧
    (x - EuclideanSpace.single (0 : Fin 4) c) 2 = x 2 ∧
    (x - EuclideanSpace.single (0 : Fin 4) c) 3 = x 3 := by
  -- (extracted by Fuse golfer)
  obtain ⟨e0, e1, e2, e3⟩ := single_time_apply c
  exact ⟨by rw [PiLp.sub_apply, e0], by rw [PiLp.sub_apply, e1, sub_zero],
    by rw [PiLp.sub_apply, e2, sub_zero], by rw [PiLp.sub_apply, e3, sub_zero]⟩

/-- Coordinatewise evaluation of a translate along the time axis. -/
private theorem add_single_time_apply (x : SpacetimeModel) (c : ℝ) :
    (x + EuclideanSpace.single (0 : Fin 4) c) 0 = x 0 + c ∧
    (x + EuclideanSpace.single (0 : Fin 4) c) 1 = x 1 ∧
    (x + EuclideanSpace.single (0 : Fin 4) c) 2 = x 2 ∧
    (x + EuclideanSpace.single (0 : Fin 4) c) 3 = x 3 := by
  -- (extracted by Fuse golfer)
  obtain ⟨e0, e1, e2, e3⟩ := single_time_apply c
  exact ⟨by rw [PiLp.add_apply, e0], by rw [PiLp.add_apply, e1, add_zero],
    by rw [PiLp.add_apply, e2, add_zero], by rw [PiLp.add_apply, e3, add_zero]⟩

/-- Shrinking a timelike separation: if `0 < ε ≤ (T ^ 2 - S) / (2 * T)` then `ε < T`
and the strict inequality `S < T ^ 2` survives replacing `T` by `T - ε`. -/
private theorem lt_and_lt_sub_sq_of_le_div {T S ε : ℝ} (hT : 0 < T) (hS : 0 ≤ S)
    (hε : 0 < ε) (hle : ε ≤ (T ^ 2 - S) / (2 * T)) : ε < T ∧ S < (T - ε) ^ 2 := by
  -- (extracted by Fuse golfer)
  have h2T : (0 : ℝ) < 2 * T := by linarith only [hT]
  have hmul : 2 * T * ε ≤ T ^ 2 - S :=
    calc 2 * T * ε ≤ 2 * T * ((T ^ 2 - S) / (2 * T)) :=
          mul_le_mul_of_nonneg_left hle h2T.le
      _ = T ^ 2 - S := by field_simp
  refine ⟨lt_of_mul_lt_mul_left ?_ h2T.le, by linarith only [hmul, pow_pos hε 2]⟩
  linarith only [hmul, hS, pow_pos hT 2]

/-- A single positive `ε` shrinks both of two timelike separations. -/
private theorem exists_eps_shrink {T₁ T₂ S₁ S₂ : ℝ} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂) (h₁ : S₁ < T₁ ^ 2) (h₂ : S₂ < T₂ ^ 2) :
    ∃ ε : ℝ, 0 < ε ∧ ε < T₁ ∧ ε < T₂ ∧ S₁ < (T₁ - ε) ^ 2 ∧ S₂ < (T₂ - ε) ^ 2 := by
  -- (extracted by Fuse golfer)
  have hpos : 0 < min ((T₁ ^ 2 - S₁) / (2 * T₁)) ((T₂ ^ 2 - S₂) / (2 * T₂)) :=
    lt_min (div_pos (by linarith only [h₁]) (by linarith only [hT₁]))
      (div_pos (by linarith only [h₂]) (by linarith only [hT₂]))
  obtain ⟨u₁, v₁⟩ := lt_and_lt_sub_sq_of_le_div hT₁ hS₁ hpos (min_le_left _ _)
  obtain ⟨u₂, v₂⟩ := lt_and_lt_sub_sq_of_le_div hT₂ hS₂ hpos (min_le_right _ _)
  exact ⟨_, hpos, u₁, u₂, v₁, v₂⟩

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
  obtain ⟨ε, hε, hε₁, hε₂, hc₁, hc₂⟩ :=
    exists_eps_shrink (T₁ := x 0 - p₁ 0) (T₂ := x 0 - p₂ 0)
      (S₁ := (x 1 - p₁ 1) ^ 2 + (x 2 - p₁ 2) ^ 2 + (x 3 - p₁ 3) ^ 2)
      (S₂ := (x 1 - p₂ 1) ^ 2 + (x 2 - p₂ 2) ^ 2 + (x 3 - p₂ 3) ^ 2)
      (sub_pos.mpr h₁0) (sub_pos.mpr h₂0) (sq3_nonneg _ _ _) (sq3_nonneg _ _ _)
      (by linarith only [h₁c]) (by linarith only [h₂c])
  obtain ⟨e0, e1, e2, e3⟩ := sub_single_time_apply x ε
  refine ⟨x - EuclideanSpace.single (0 : Fin 4) ε,
    ⟨by rw [e0]; linarith only [hε₁], ?_⟩, ⟨by rw [e0]; linarith only [hε₂], ?_⟩,
    ⟨by rw [e0]; linarith only [hε], ?_⟩⟩
  · rw [e0, e1, e2, e3]; linarith only [hc₁]
  · rw [e0, e1, e2, e3]; linarith only [hc₂]
  · rw [e0, e1, e2, e3]; linarith only [pow_pos hε 2]

/-- **Future interpolation.** If `x` is in the backward cones of `q₁` and `q₂`, there
is a point `b` in both backward cones with `x` in the backward cone of `b` (i.e.
`x ≪ b ≪ q₁, q₂`). Dual to `exists_past_between_standardMinkowski`, with `b = x + ε • e₀`. -/
theorem exists_future_between_standardMinkowski {q₁ q₂ x : SpacetimeModel}
    (h₁ : x ∈ minkowskiBackwardCone q₁) (h₂ : x ∈ minkowskiBackwardCone q₂) :
    ∃ b, b ∈ minkowskiBackwardCone q₁ ∧ b ∈ minkowskiBackwardCone q₂ ∧
      x ∈ minkowskiBackwardCone b := by
  obtain ⟨h₁0, h₁c⟩ := h₁
  obtain ⟨h₂0, h₂c⟩ := h₂
  obtain ⟨ε, hε, hε₁, hε₂, hc₁, hc₂⟩ :=
    exists_eps_shrink (T₁ := q₁ 0 - x 0) (T₂ := q₂ 0 - x 0)
      (S₁ := (q₁ 1 - x 1) ^ 2 + (q₁ 2 - x 2) ^ 2 + (q₁ 3 - x 3) ^ 2)
      (S₂ := (q₂ 1 - x 1) ^ 2 + (q₂ 2 - x 2) ^ 2 + (q₂ 3 - x 3) ^ 2)
      (sub_pos.mpr h₁0) (sub_pos.mpr h₂0) (sq3_nonneg _ _ _) (sq3_nonneg _ _ _)
      (by linarith only [h₁c]) (by linarith only [h₂c])
  obtain ⟨e0, e1, e2, e3⟩ := add_single_time_apply x ε
  refine ⟨x + EuclideanSpace.single (0 : Fin 4) ε,
    ⟨by rw [e0]; linarith only [hε₁], ?_⟩, ⟨by rw [e0]; linarith only [hε₂], ?_⟩,
    ⟨by rw [e0]; linarith only [hε], ?_⟩⟩
  · rw [e0, e1, e2, e3]; linarith only [hc₁]
  · rw [e0, e1, e2, e3]; linarith only [hc₂]
  · rw [e0, e1, e2, e3]; linarith only [pow_pos hε 2]

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
